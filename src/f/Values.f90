! Core, mutually-recursive type definitions: cons_value (the tagged-union
! value every operation passes around) needs to hold a list/vector, and a
! list cell / vector-trie node needs to hold a cons_value. Fortran can
! only forward-reference a not-yet-defined type within the same module
! (and only via an allocatable/pointer component), so all of it lives
! here together. Operations live in their own files: PersistentList.f90,
! PersistentVector.f90, RT.f90.
module values
  implicit none

  ! Double precision, not the bare default `real`: every real scientific
  ! Fortran library (ChemSol included) works in real(8)/double precision
  ! throughout. A value type built for native interop has to match that
  ! from the start, not bolt it on after silently losing precision.
  integer, parameter :: dp = kind(1.0d0)

  integer, parameter :: TAG_NIL = 0
  integer, parameter :: TAG_BOOL = 1
  integer, parameter :: TAG_INT = 2
  integer, parameter :: TAG_REAL = 3
  integer, parameter :: TAG_STRING = 4
  integer, parameter :: TAG_SYMBOL = 5
  integer, parameter :: TAG_KEYWORD = 6
  integer, parameter :: TAG_LIST = 7
  integer, parameter :: TAG_VECTOR = 8
  integer, parameter :: TAG_HASHMAP = 9
  integer, parameter :: TAG_BUILTIN = 10 ! str_val holds the builtin's name; dispatched by Eval
  integer, parameter :: TAG_FN = 11 ! fn_val holds params/body/captured env; a real closure
  integer, parameter :: TAG_ATOM = 12 ! atom_val is a genuinely mutable box, shared by reference
  integer, parameter :: TAG_SET = 13 ! map_val backs it too -- every element mapped to itself,
                                      ! exactly like real Clojure's PersistentHashSet wraps a map

  integer, parameter :: BITS = 5
  integer, parameter :: BRANCH = 32
  integer, parameter :: MASK = 31

  ! Every value in the language. Only the field matching %tag is meaningful.
  type, public :: cons_value
     integer :: tag = TAG_NIL
     integer :: int_val = 0
     real(dp) :: real_val = 0.0_dp
     logical :: bool_val = .false.
     character(len=:), allocatable :: str_val   ! string/symbol/keyword text
     type(cons_ref), allocatable :: list_val
     type(vec_t), allocatable :: vector_val
     type(array_map_t), allocatable :: map_val
     type(closure_t), allocatable :: fn_val
     type(atom_ref), allocatable :: atom_val
     type(meta_ref), allocatable :: meta_val ! (with-meta x m)/(meta x) -- any value, any type
   contains
     final :: cons_value_finalize
  end type cons_value

  ! --- PersistentList backing: a real, refcounted cons cell ---
  type, public :: cons_cell
     integer :: refcount = 0
     type(cons_value) :: car
     type(cons_ref), allocatable :: cdr
     integer :: count = 0
  end type cons_cell

  type, public :: cons_ref
     type(cons_cell), pointer :: ptr => null()
   contains
     final :: cons_ref_finalize
  end type cons_ref

  ! --- PersistentVector backing: a 32-way branching trie ---
  type, public :: vec_node
     integer :: refcount = 0
     type(node_ref), allocatable :: children(:)
     type(cons_value), allocatable :: items(:)
  end type vec_node

  type, public :: node_ref
     type(vec_node), pointer :: ptr => null()
   contains
     final :: node_ref_finalize
  end type node_ref

  type, public :: vec_t
     integer :: count = 0
     integer :: shift = 0
     type(node_ref) :: root
  end type vec_t

  ! --- PersistentArrayMap backing: a flat, linear-scan k/v array. Real
  ! Clojure uses this same representation (not a hash trie) for maps up
  ! to 8 entries; every map in this project is that small for now, so
  ! there's no HAMT yet -- see PersistentArrayMap.f90.
  type, public :: array_map_node
     integer :: refcount = 0
     type(cons_value), allocatable :: keys(:)
     type(cons_value), allocatable :: vals(:)
  end type array_map_node

  type, public :: array_map_ref
     type(array_map_node), pointer :: ptr => null()
   contains
     final :: array_map_ref_finalize
  end type array_map_ref

  type, public :: array_map_t
     type(array_map_ref) :: root
  end type array_map_t

  ! --- Env backing: symbol -> value bindings with an outer chain. Lives
  ! here (not in Env.f90, which holds only the operations) because a
  ! closure (added alongside fn*) needs to capture an env_ref, and
  ! cons_value needs to hold a closure -- the same forward-reference
  ! constraint that keeps every other mutually-recursive type together.
  type :: env_node
     integer :: refcount = 0
     type(array_map_t) :: bindings
     type(env_ref), allocatable :: outer
  end type env_node

  type, public :: env_ref
     type(env_node), pointer :: ptr => null()
   contains
     final :: env_ref_finalize
  end type env_ref

  ! --- Extra arity clauses for a multi-arity fn* (see closure_t
  ! below), boxed behind a pointer for the same reason meta_ref is:
  ! a derived type can't hold an allocatable ARRAY of a type that
  ! (transitively, through closure_t) contains itself either --
  ! same self-referential-allocatable-plus-FINAL gfortran codegen bug
  ! as cons_value/meta_val, confirmed by hitting it here too (crashed
  ! only on gfortran; flang was unaffected). Nothing shares one of
  ! these across closures, so no refcount sharing is actually needed,
  ! but the ref/node shape is what already exists and is proven safe.
  type, public :: arity_clauses_node
     integer :: refcount = 0
     type(cons_value), allocatable :: params(:), bodies(:)
  end type arity_clauses_node

  type, public :: arity_clauses_ref
     type(arity_clauses_node), pointer :: ptr => null()
   contains
     final :: arity_clauses_ref_finalize
  end type arity_clauses_ref

  ! --- closure: params/body captured at (fn* ...) time, plus the env
  ! captured lexically. Defined last (not forward-referenced) since it
  ! embeds cons_value and env_ref directly rather than through a
  ! pointer -- both are already fully defined above by this point.
  ! is_macro: real Clojure hangs macro-ness off the Var's metadata, not
  ! the function value -- a macro-created function is an ordinary IFn.
  ! We don't have a separate Var (see Namespace.f90), so the closest
  ! analogue is a flag on the closure itself rather than a whole
  ! parallel TAG_MACRO duplicating TAG_FN's shape everywhere TAG_FN is
  ! handled. Still a simplification (real metadata is per-Var, so the
  ! same fn value could in principle be a macro under one name and not
  ! another; not a scenario anything here creates).
  ! extra: additional arity clauses for a multi-arity fn* (params/body
  ! above are the first clause). Real Clojure's (fn* ([a] ...) ([a b]
  ! ...)) syntax -- dispatched by argument count at call time (see
  ! select_clause in Eval.f90), not rewritten away at parse time, so
  ! this stays the one runtime closure representation for both single-
  ! and multi-arity fns.
  type, public :: closure_t
     type(cons_value) :: params
     type(cons_value) :: body
     type(arity_clauses_ref), allocatable :: extra
     type(env_ref) :: env
     logical :: is_macro = .false.
  end type closure_t

  ! --- Atom backing: one genuinely mutable slot, shared by reference.
  ! Mirrors clojure.lang.Atom. Unlike env, nothing else needs to hold an
  ! atom_ref directly (only ever through a cons_value), so it doesn't
  ! need to be defined this early -- kept next to closure_t anyway, by
  ! the same "defined last, embeds cons_value directly" reasoning.
  type, public :: atom_node
     integer :: refcount = 0
     type(cons_value) :: val
  end type atom_node

  type, public :: atom_ref
     type(atom_node), pointer :: ptr => null()
   contains
     final :: atom_ref_finalize
  end type atom_ref

  ! --- Metadata backing: (with-meta x m)/(meta x). Same shape as atom
  ! (a refcounted box holding one cons_value) even though nothing here
  ! mutates it -- a cons_value can't hold another cons_value directly as
  ! an allocatable component (self-referential allocatable + FINAL is a
  ! known gfortran codegen bug, confirmed by an isolated repro; flang is
  ! unaffected). Going through a pointer indirection, as every other
  ! recursive structure here already does, sidesteps it for free.
  type, public :: meta_node
     integer :: refcount = 0
     type(cons_value) :: val
  end type meta_node

  type, public :: meta_ref
     type(meta_node), pointer :: ptr => null()
   contains
     final :: meta_ref_finalize
  end type meta_ref

  interface assignment(=)
     module procedure cons_value_assign
     module procedure cons_ref_assign
     module procedure node_ref_assign
     module procedure vec_t_assign
     module procedure array_map_ref_assign
     module procedure array_map_t_assign
     module procedure env_ref_assign
     module procedure closure_t_assign
     module procedure atom_ref_assign
     module procedure meta_ref_assign
     module procedure arity_clauses_ref_assign
  end interface assignment(=)

  ! For test programs to confirm every box is eventually freed.
  integer, public :: cons_cell_total_allocated = 0
  integer, public :: cons_cell_total_freed = 0
  integer, public :: vec_node_total_allocated = 0
  integer, public :: vec_node_total_freed = 0
  integer, public :: array_map_node_total_allocated = 0
  integer, public :: array_map_node_total_freed = 0
  integer, public :: env_total_allocated = 0
  integer, public :: env_total_freed = 0
  integer, public :: atom_node_total_allocated = 0
  integer, public :: atom_node_total_freed = 0
  integer, public :: meta_node_total_allocated = 0
  integer, public :: meta_node_total_freed = 0
  integer, public :: arity_clauses_node_total_allocated = 0
  integer, public :: arity_clauses_node_total_freed = 0

  public :: assignment(=)
  public :: cons_value_release, cons_ref_release, node_ref_release, array_map_ref_release, env_ref_release, &
       atom_ref_release, meta_ref_release, arity_clauses_ref_release

contains

  ! ---- cons_value ----

  recursive subroutine cons_value_release(v)
    type(cons_value), intent(inout) :: v
    if (allocated(v%str_val)) deallocate(v%str_val)
    if (allocated(v%list_val)) then
       call cons_ref_release(v%list_val)
       deallocate(v%list_val)
    end if
    if (allocated(v%vector_val)) then
       call node_ref_release(v%vector_val%root)
       deallocate(v%vector_val)
    end if
    if (allocated(v%map_val)) then
       call array_map_ref_release(v%map_val%root)
       deallocate(v%map_val)
    end if
    if (allocated(v%fn_val)) deallocate(v%fn_val) ! cascades: releases params/body/env
    if (allocated(v%atom_val)) then
       call atom_ref_release(v%atom_val)
       deallocate(v%atom_val)
    end if
    if (allocated(v%meta_val)) then
       call meta_ref_release(v%meta_val)
       deallocate(v%meta_val)
    end if
    v%tag = TAG_NIL
  end subroutine cons_value_release

  impure elemental subroutine cons_value_assign(lhs, rhs)
    type(cons_value), intent(inout) :: lhs
    type(cons_value), intent(in) :: rhs
    call cons_value_release(lhs)
    lhs%tag = rhs%tag
    lhs%int_val = rhs%int_val
    lhs%real_val = rhs%real_val
    lhs%bool_val = rhs%bool_val
    if (allocated(rhs%str_val)) lhs%str_val = rhs%str_val
    if (allocated(rhs%list_val)) then
       allocate(lhs%list_val)
       lhs%list_val = rhs%list_val
    end if
    if (allocated(rhs%vector_val)) then
       allocate(lhs%vector_val)
       lhs%vector_val = rhs%vector_val
    end if
    if (allocated(rhs%map_val)) then
       allocate(lhs%map_val)
       lhs%map_val = rhs%map_val
    end if
    if (allocated(rhs%fn_val)) then
       allocate(lhs%fn_val)
       lhs%fn_val = rhs%fn_val
    end if
    if (allocated(rhs%atom_val)) then
       allocate(lhs%atom_val)
       lhs%atom_val = rhs%atom_val
    end if
    if (allocated(rhs%meta_val)) then
       allocate(lhs%meta_val)
       lhs%meta_val = rhs%meta_val
    end if
  end subroutine cons_value_assign

  impure elemental subroutine cons_value_finalize(v)
    type(cons_value), intent(inout) :: v
    call cons_value_release(v)
  end subroutine cons_value_finalize

  ! ---- cons_ref (PersistentList cells) ----

  recursive subroutine cons_ref_release(h)
    type(cons_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       call cons_value_release(h%ptr%car)
       if (allocated(h%ptr%cdr)) call cons_ref_release(h%ptr%cdr)
       deallocate(h%ptr)
       cons_cell_total_freed = cons_cell_total_freed + 1
    end if
    h%ptr => null()
  end subroutine cons_ref_release

  impure elemental subroutine cons_ref_assign(lhs, rhs)
    type(cons_ref), intent(inout) :: lhs
    type(cons_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call cons_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine cons_ref_assign

  impure elemental subroutine cons_ref_finalize(h)
    type(cons_ref), intent(inout) :: h
    call cons_ref_release(h)
  end subroutine cons_ref_finalize

  ! ---- node_ref (PersistentVector trie nodes) ----

  recursive subroutine node_ref_release(h)
    type(node_ref), intent(inout) :: h
    integer :: i
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       if (allocated(h%ptr%children)) then
          do i = 1, size(h%ptr%children)
             call node_ref_release(h%ptr%children(i))
          end do
       end if
       deallocate(h%ptr)
       vec_node_total_freed = vec_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine node_ref_release

  impure elemental subroutine node_ref_assign(lhs, rhs)
    type(node_ref), intent(inout) :: lhs
    type(node_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call node_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine node_ref_assign

  impure elemental subroutine node_ref_finalize(h)
    type(node_ref), intent(inout) :: h
    call node_ref_release(h)
  end subroutine node_ref_finalize

  ! ---- vec_t (embeds a node_ref, so needs its own assignment(=)) ----

  subroutine vec_t_assign(lhs, rhs)
    type(vec_t), intent(inout) :: lhs
    type(vec_t), intent(in) :: rhs
    lhs%count = rhs%count
    lhs%shift = rhs%shift
    lhs%root = rhs%root
  end subroutine vec_t_assign

  ! ---- array_map_ref (PersistentArrayMap backing) ----

  subroutine array_map_ref_release(h)
    type(array_map_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       deallocate(h%ptr)
       array_map_node_total_freed = array_map_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine array_map_ref_release

  impure elemental subroutine array_map_ref_assign(lhs, rhs)
    type(array_map_ref), intent(inout) :: lhs
    type(array_map_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call array_map_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine array_map_ref_assign

  impure elemental subroutine array_map_ref_finalize(h)
    type(array_map_ref), intent(inout) :: h
    call array_map_ref_release(h)
  end subroutine array_map_ref_finalize

  ! ---- array_map_t (embeds an array_map_ref, needs its own assignment(=)) ----

  subroutine array_map_t_assign(lhs, rhs)
    type(array_map_t), intent(inout) :: lhs
    type(array_map_t), intent(in) :: rhs
    lhs%root = rhs%root
  end subroutine array_map_t_assign

  ! ---- env_ref ----

  recursive subroutine env_ref_release(h)
    type(env_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       if (allocated(h%ptr%outer)) call env_ref_release(h%ptr%outer)
       deallocate(h%ptr)
       env_total_freed = env_total_freed + 1
    end if
    h%ptr => null()
  end subroutine env_ref_release

  impure elemental subroutine env_ref_assign(lhs, rhs)
    type(env_ref), intent(inout) :: lhs
    type(env_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call env_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine env_ref_assign

  impure elemental subroutine env_ref_finalize(h)
    type(env_ref), intent(inout) :: h
    call env_ref_release(h)
  end subroutine env_ref_finalize

  ! ---- closure_t (embeds cons_value and env_ref, needs its own
  ! assignment(=) -- default struct assignment doesn't cascade into an
  ! embedded type's own defined assignment) ----

  subroutine closure_t_assign(lhs, rhs)
    type(closure_t), intent(inout) :: lhs
    type(closure_t), intent(in) :: rhs
    lhs%params = rhs%params
    lhs%body = rhs%body
    if (allocated(rhs%extra)) then
       if (.not. allocated(lhs%extra)) allocate(lhs%extra)
       lhs%extra = rhs%extra
    else if (allocated(lhs%extra)) then
       deallocate(lhs%extra)
    end if
    lhs%env = rhs%env
    lhs%is_macro = rhs%is_macro
  end subroutine closure_t_assign

  ! ---- atom_ref ----

  subroutine atom_ref_release(h)
    type(atom_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       deallocate(h%ptr) ! cascades: releases h%ptr%val
       atom_node_total_freed = atom_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine atom_ref_release

  impure elemental subroutine atom_ref_assign(lhs, rhs)
    type(atom_ref), intent(inout) :: lhs
    type(atom_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call atom_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine atom_ref_assign

  impure elemental subroutine atom_ref_finalize(h)
    type(atom_ref), intent(inout) :: h
    call atom_ref_release(h)
  end subroutine atom_ref_finalize

  ! ---- meta_ref (same shape as atom_ref, nothing here mutates it) ----

  subroutine meta_ref_release(h)
    type(meta_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       deallocate(h%ptr) ! cascades: releases h%ptr%val
       meta_node_total_freed = meta_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine meta_ref_release

  impure elemental subroutine meta_ref_assign(lhs, rhs)
    type(meta_ref), intent(inout) :: lhs
    type(meta_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call meta_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine meta_ref_assign

  impure elemental subroutine meta_ref_finalize(h)
    type(meta_ref), intent(inout) :: h
    call meta_ref_release(h)
  end subroutine meta_ref_finalize

  ! ---- arity_clauses_ref (same shape as atom_ref/meta_ref) ----

  subroutine arity_clauses_ref_release(h)
    type(arity_clauses_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       deallocate(h%ptr) ! cascades: releases h%ptr%params/bodies
       arity_clauses_node_total_freed = arity_clauses_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine arity_clauses_ref_release

  impure elemental subroutine arity_clauses_ref_assign(lhs, rhs)
    type(arity_clauses_ref), intent(inout) :: lhs
    type(arity_clauses_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call arity_clauses_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine arity_clauses_ref_assign

  impure elemental subroutine arity_clauses_ref_finalize(h)
    type(arity_clauses_ref), intent(inout) :: h
    call arity_clauses_ref_release(h)
  end subroutine arity_clauses_ref_finalize

end module values
