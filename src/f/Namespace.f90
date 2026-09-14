! Namespace: mirrors clojure.lang.Namespace. Global registry of named,
! independent symbol -> value tables, found by name rather than nested
! lexically (that's Env's job, for let*/fn* locals). Every namespace
! auto-refers clojure.core, same as real Clojure's default -- no
! selective refer/exclude/require yet, just the one fallback.
!
! Real Vars now: a namespace's own bindings are TAG_VAR cons_values
! (see Values.f90), each wrapping a mutable atom_ref as its root
! binding -- reused directly from Atom.f90 rather than a parallel
! type, since a Var's root binding IS "one genuinely mutable slot,
! shared by reference," exactly atom_ref's own shape. ns_get_own/
! ns_resolve transparently deref through the Var (a bare symbol use
! auto-derefs, matching real Clojure); ns_intern mutates an existing
! Var's root in place rather than replacing it, so identity survives
! redefinition (`(def x 1) (def x 2)` is the SAME Var throughout --
! matters once something holds onto a Var reference across a
! redefinition, e.g. a closure created before a later `(def)`).
! ns_get_own_var/ns_resolve_var return the Var itself, unresolved, for
! `(var sym)`/`#'sym`/`var-get`/`var-set`. Still no thread-local
! dynamic-binding stack (`binding`) -- that's the next piece to add,
! once it's needed; see NOTES.md.
module Namespace
  use values
  use Atom, only: atom_new, atom_deref, atom_reset
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
  public :: ns_find_or_create, ns_exists, ns_intern, ns_resolve, ns_get_own
  public :: ns_get_own_var, ns_resolve_var
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

  ! Like ns_find_or_create, but never creates -- used to tell "this
  ! symbol names a real namespace" (a (. Class (method args)) static
  ! call) apart from an ordinary local/value (an instance-position .
  ! call) without auto-vivifying a namespace for every random symbol
  ! that happens to appear in class position.
  function ns_exists(name) result(bool)
    character(len=*), intent(in) :: name
    logical :: bool
    integer :: i
    bool = .false.
    do i = 1, registry_count
       if (registry(i)%ptr%name == name) then
          bool = .true.
          return
       end if
    end do
  end function ns_exists

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

  ! Builds a fresh Var wrapping root, named for printing (#'ns/name).
  function make_var(ns_name, name, root) result(v)
    character(len=*), intent(in) :: ns_name, name
    type(cons_value), intent(in) :: root
    type(cons_value) :: v
    v = atom_new(root) ! reuses atom_ref's mutable-box machinery wholesale
    v%tag = TAG_VAR
    v%str_val = ns_name // "/" // name
  end function make_var

  ! def!'s job: creates the Var if new, mutates its root in place if
  ! not -- redefinition never changes a Var's identity, matching real
  ! Clojure (anything already holding this Var, once something does,
  ! sees the update).
  subroutine ns_intern(ns, name, val)
    type(ns_ref), intent(in) :: ns
    character(len=*), intent(in) :: name
    type(cons_value), intent(in) :: val
    type(cons_value) :: key, existing
    type(array_map_t) :: next_bindings
    key = symbol_key(name)
    if (array_map_contains(ns%ptr%bindings, key)) then
       existing = array_map_get(ns%ptr%bindings, key)
       if (existing%tag == TAG_VAR) then
          call atom_reset(existing, val)
          return
       end if
    end if
    ! never ns%ptr%bindings = array_map_assoc(ns%ptr%bindings, ...) --
    ! see Eval.f90's make_hashmap for why that self-referencing
    ! assignment silently drops the update.
    next_bindings = array_map_assoc(ns%ptr%bindings, key, make_var(ns%ptr%name, name, val))
    ns%ptr%bindings = next_bindings
  end subroutine ns_intern

  ! Only this namespace's own bindings -- no clojure.core fallback.
  ! Transparently derefs the Var: a bare symbol use auto-derefs,
  ! matching real Clojure (unlike an atom, which never does). See
  ! ns_get_own_var for the Var itself, unresolved.
  function ns_get_own(ns, name, val) result(found)
    type(ns_ref), intent(in) :: ns
    character(len=*), intent(in) :: name
    type(cons_value), intent(out) :: val
    logical :: found
    type(cons_value) :: stored
    found = ns_get_own_var(ns, name, stored)
    if (.not. found) return
    if (stored%tag == TAG_VAR) then
       val = atom_deref(stored)
    else
       val = stored
    end if
  end function ns_get_own

  ! Same lookup, but returns the raw Var (no deref) -- (var sym)/#'sym/
  ! var-get/var-set need the Var itself, not its current value.
  function ns_get_own_var(ns, name, val) result(found)
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
  end function ns_get_own_var

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

  ! Same resolution order as ns_resolve, but returns the Var itself
  ! (no deref) -- (var sym)/#'sym/var-get/var-set.
  recursive function ns_resolve_var(ns, name, val, owner) result(found)
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
       found = ns_get_own_var(ns_find_or_create(name(1:slash-1)), name(slash+1:), val)
       if (found) owner = name(1:slash-1)
       return
    end if

    found = ns_get_own_var(ns, name, val)
    if (found) then
       owner = ns%ptr%name
       return
    end if
    if (ns%ptr%name /= CORE_NS) then
       found = ns_get_own_var(ns_find_or_create(CORE_NS), name, val)
       if (found) owner = CORE_NS
    end if
  end function ns_resolve_var

  ! Also keeps *ns* (a real Var, in clojure.core, matching real
  ! Clojure) pointed at the current namespace's name -- real core.clj
  ! source references *ns* directly in several places (assert-args's
  ! own error messages among them). No first-class Namespace value
  ! type here (see Values.f90's own "not class(*)" design), so this is
  ! a symbol naming it rather than a real Namespace object -- enough
  ! for printing/string interpolation, not for real Namespace methods
  ! (.getMapping, .refer, ...) if something ever calls one on it.
  subroutine ns_set_current(ns)
    type(ns_ref), intent(in) :: ns
    type(cons_value) :: name_sym
    current = ns
    if (.not. associated(ns%ptr)) return
    name_sym%tag = TAG_SYMBOL
    name_sym%str_val = ns%ptr%name
    call ns_intern(ns_find_or_create(CORE_NS), "*ns*", name_sym)
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
