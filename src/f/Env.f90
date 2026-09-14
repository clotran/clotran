! Env: symbol -> value bindings with an outer chain for lexical scope.
! Unlike everything else built so far, this is genuinely mutable --
! def!/let* change a binding in place, visible to every env_ref sharing
! that same env, matching real Clojure's environment semantics rather
! than the persistent-by-default rule everything else here follows.
!
! Types (env_node, env_ref) live in Values.f90 -- see its header.
module Env
  use values
  use PersistentArrayMap, only: array_map_empty, array_map_get, array_map_assoc, array_map_contains, &
       array_map_entries
  implicit none
  private

  ! env_ref/assignment(=) are defined in Values.f90 but re-declared public
  ! here too: a blanket `private` (above) hides even use-associated names
  ! from re-export unless explicitly listed, and every consumer of this
  ! module reaches env_ref and its assignment(=) through `use Env`.
  public :: env_ref, assignment(=)
  public :: env_new, env_set, env_get, env_find, env_rebind_fns, env_set_ns, env_defining_ns

contains

  function env_new(outer) result(e)
    type(env_ref), intent(in), optional :: outer
    type(env_ref) :: e
    type(env_node), pointer :: node

    allocate(node)
    node%refcount = 1
    env_total_allocated = env_total_allocated + 1
    node%bindings = array_map_empty()
    if (present(outer)) then
       if (associated(outer%ptr)) then
          allocate(node%outer)
          node%outer = outer
       end if
    end if
    e%ptr => node
  end function env_new

  ! def!/let* binding: mutates e in place.
  ! e itself is intent(in): this only mutates through the pointer (the
  ! shared env_node), never reassigns e%ptr, so callers holding e as
  ! intent(in) (eval, mid-recursion) can still call this.
  subroutine env_set(e, key, val)
    type(env_ref), intent(in) :: e
    type(cons_value), intent(in) :: key, val
    type(array_map_t) :: next_bindings
    ! never e%ptr%bindings = array_map_assoc(e%ptr%bindings, ...) -- see
    ! Eval.f90's make_hashmap for why that self-referencing assignment
    ! silently drops the update.
    next_bindings = array_map_assoc(e%ptr%bindings, key, val)
    e%ptr%bindings = next_bindings
  end subroutine env_set

  ! Rebinds every function-valued binding in THIS frame (not the outer
  ! chain) to val. A fn*'s own throwaway frame holds exactly its
  ! self-references -- "recur", plus the optional (fn* name ...) name,
  ! both bound to the closure itself -- so this is how a mutation of
  ! that closure reaches the body that calls itself. On the JVM the
  ! self-reference and the outer local are literally the same object;
  ! here they are separate copies, and this is what keeps them in step.
  subroutine env_rebind_fns(e, val)
    type(env_ref), intent(in) :: e
    type(cons_value), intent(in) :: val
    type(cons_value), allocatable :: keys(:), vals(:)
    type(array_map_t) :: next_bindings
    integer :: i
    if (.not. associated(e%ptr)) return
    call array_map_entries(e%ptr%bindings, keys, vals)
    do i = 1, size(keys)
       if (vals(i)%tag /= TAG_FN) cycle
       next_bindings = array_map_assoc(e%ptr%bindings, keys(i), val)
       e%ptr%bindings = next_bindings
    end do
  end subroutine env_rebind_fns

  ! Marks this frame as a closure's own frame, defined in namespace
  ! name. Only eval_fn calls this.
  subroutine env_set_ns(e, name)
    type(env_ref), intent(in) :: e
    character(len=*), intent(in) :: name
    if (associated(e%ptr)) e%ptr%ns_name = name
  end subroutine env_set_ns

  ! The innermost enclosing closure's defining namespace, or "" at top
  ! level. A plain field check per frame, deliberately not a binding
  ! lookup: this runs for every free symbol that isn't a local.
  recursive function env_defining_ns(e) result(name)
    type(env_ref), intent(in) :: e
    character(len=:), allocatable :: name
    name = ""
    if (.not. associated(e%ptr)) return
    if (allocated(e%ptr%ns_name)) then
       name = e%ptr%ns_name
       return
    end if
    if (allocated(e%ptr%outer)) name = env_defining_ns(e%ptr%outer)
  end function env_defining_ns

  ! Walks outward through the outer chain. found is .false. if key is
  ! unbound anywhere -- distinct from being bound to nil.
  recursive function env_find(e, key, val) result(found)
    type(env_ref), intent(in) :: e
    type(cons_value), intent(in) :: key
    type(cons_value), intent(out) :: val
    logical :: found

    found = .false.
    if (.not. associated(e%ptr)) return
    if (array_map_contains(e%ptr%bindings, key)) then
       val = array_map_get(e%ptr%bindings, key)
       found = .true.
    else if (allocated(e%ptr%outer)) then
       found = env_find(e%ptr%outer, key, val)
    end if
  end function env_find

  ! Convenience for callers that have already checked env_find (or don't
  ! care): nil if unbound.
  function env_get(e, key) result(val)
    type(env_ref), intent(in) :: e
    type(cons_value), intent(in) :: key
    type(cons_value) :: val
    logical :: found
    found = env_find(e, key, val)
  end function env_get

end module Env
