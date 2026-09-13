! Namespace: mirrors clojure.lang.Namespace. Global registry of named,
! independent symbol -> value tables, found by name rather than nested
! lexically (that's Env's job, for let*/fn* locals). Every namespace
! auto-refers clojure.core, same as real Clojure's default -- no
! selective refer/exclude/require yet, just the one fallback.
!
! Deliberately simplified vs. real Clojure: a namespace's own bindings
! are stored directly as symbol -> value (an array_map_t, same shape as
! Env's bindings), not through a separate first-class Var indirection.
! clojure.lang.Var exists for metadata, #'foo, and thread-local dynamic
! bindings -- none of which this project needs yet; build it once
! something does.
module Namespace
  use values
  use PersistentArrayMap, only: array_map_empty, array_map_get, array_map_assoc, array_map_contains
  implicit none
  private

  character(len=*), parameter :: CORE_NS = "clojure.core"

  type :: ns_node
     integer :: refcount = 0
     character(len=:), allocatable :: name
     type(array_map_t) :: bindings
  end type ns_node

  type, public :: ns_ref
     type(ns_node), pointer :: ptr => null()
   contains
     final :: ns_ref_finalize
  end type ns_ref

  interface assignment(=)
     module procedure ns_ref_assign
  end interface assignment(=)

  ! The global registry (mirrors Namespace.namespaces, a static map in
  ! real Clojure). A handful of namespaces, not thousands -- a linear
  ! array is enough; revisit if that stops being true.
  type(ns_ref), allocatable, save :: registry(:)
  integer, save :: registry_count = 0

  ! *ns* -- mutable and global, not lexically scoped: (let [] (def x 1))
  ! really does define x at the top level, matching real Clojure.
  type(ns_ref), save :: current

  public :: assignment(=), CORE_NS
  public :: ns_find_or_create, ns_intern, ns_resolve, ns_get_own
  public :: ns_set_current, ns_current, ns_name_of

contains

  function symbol_key(name) result(k)
    character(len=*), intent(in) :: name
    type(cons_value) :: k
    k%tag = TAG_SYMBOL
    k%str_val = name
  end function symbol_key

  recursive function ns_find_or_create(name) result(ns)
    character(len=*), intent(in) :: name
    type(ns_ref) :: ns
    type(ns_node), pointer :: node
    integer :: i

    do i = 1, registry_count
       if (registry(i)%ptr%name == name) then
          ns = registry(i)
          return
       end if
    end do

    allocate(node)
    node%refcount = 1
    node%name = name
    node%bindings = array_map_empty()
    ns%ptr => node
    call registry_append(ns)
  end function ns_find_or_create

  subroutine registry_append(ns)
    type(ns_ref), intent(in) :: ns
    type(ns_ref), allocatable :: new_registry(:)
    integer :: i
    allocate(new_registry(registry_count + 1))
    do i = 1, registry_count
       new_registry(i) = registry(i)
    end do
    new_registry(registry_count + 1) = ns
    call move_alloc(new_registry, registry)
    registry_count = registry_count + 1
  end subroutine registry_append

  ! def!'s job: creates the binding if new, replaces it if not.
  subroutine ns_intern(ns, name, val)
    type(ns_ref), intent(in) :: ns
    character(len=*), intent(in) :: name
    type(cons_value), intent(in) :: val
    ns%ptr%bindings = array_map_assoc(ns%ptr%bindings, symbol_key(name), val)
  end subroutine ns_intern

  ! Only this namespace's own bindings -- no clojure.core fallback.
  function ns_get_own(ns, name, val) result(found)
    type(ns_ref), intent(in) :: ns
    character(len=*), intent(in) :: name
    type(cons_value), intent(out) :: val
    logical :: found
    type(cons_value) :: key
    found = .false.
    if (.not. associated(ns%ptr)) return
    key = symbol_key(name)
    found = array_map_contains(ns%ptr%bindings, key)
    if (found) val = array_map_get(ns%ptr%bindings, key)
  end function ns_get_own

  ! Full resolution: this namespace's own bindings, then clojure.core's
  ! (real Clojure's default auto-refer). owner names which namespace the
  ! binding actually came from -- syntax-quote qualification needs this
  ! (e.g. `+` from within `user` must qualify as clojure.core/+, not
  ! user/+). An explicitly qualified name ("ns/sym") looks only in that
  ! one namespace's own bindings, no auto-refer fallback -- you already
  ! said which namespace. "/" itself (the division symbol) is the one
  ! exception: a bare "/" is never split, matching real Clojure.
  recursive function ns_resolve(ns, name, val, owner) result(found)
    type(ns_ref), intent(in) :: ns
    character(len=*), intent(in) :: name
    type(cons_value), intent(out) :: val
    character(len=:), allocatable, intent(out) :: owner
    logical :: found
    integer :: slash

    owner = ""
    slash = 0
    if (name /= "/") slash = index(name, "/")
    if (slash > 0) then
       found = ns_get_own(ns_find_or_create(name(1:slash-1)), name(slash+1:), val)
       if (found) owner = name(1:slash-1)
       return
    end if

    found = ns_get_own(ns, name, val)
    if (found) then
       owner = ns%ptr%name
       return
    end if
    if (ns%ptr%name /= CORE_NS) then
       found = ns_get_own(ns_find_or_create(CORE_NS), name, val)
       if (found) owner = CORE_NS
    end if
  end function ns_resolve

  subroutine ns_set_current(ns)
    type(ns_ref), intent(in) :: ns
    current = ns
  end subroutine ns_set_current

  function ns_current() result(ns)
    type(ns_ref) :: ns
    ns = current
  end function ns_current

  function ns_name_of(ns) result(name)
    type(ns_ref), intent(in) :: ns
    character(len=:), allocatable :: name
    if (associated(ns%ptr)) then
       name = ns%ptr%name
    else
       name = ""
    end if
  end function ns_name_of

  ! ---- ns_ref refcounting (same handle-plus-node pattern as everything
  ! else -- see Values.f90's header) ----

  subroutine ns_ref_release(h)
    type(ns_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    ! Namespaces are never dropped once registered (mirrors real
    ! Clojure -- Namespace/remove is rare, explicit, and not needed
    ! here), so there's deliberately no free-at-zero here: the registry
    ! itself always holds one live reference to every namespace.
    h%ptr => null()
  end subroutine ns_ref_release

  impure elemental subroutine ns_ref_assign(lhs, rhs)
    type(ns_ref), intent(inout) :: lhs
    type(ns_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call ns_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine ns_ref_assign

  impure elemental subroutine ns_ref_finalize(h)
    type(ns_ref), intent(inout) :: h
    call ns_ref_release(h)
  end subroutine ns_ref_finalize

end module Namespace
