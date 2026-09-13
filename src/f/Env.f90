! Env: symbol -> value bindings with an outer chain for lexical scope.
! Unlike everything else built so far, this is genuinely mutable --
! def!/let* change a binding in place, visible to every env_ref sharing
! that same env, matching real Clojure's environment semantics rather
! than the persistent-by-default rule everything else here follows.
!
! Types (env_node, env_ref) live in Values.f90 -- see its header.
module Env
  use values
  use PersistentArrayMap, only: array_map_empty, array_map_get, array_map_assoc, array_map_contains
  implicit none
  private

  ! env_ref/assignment(=) are defined in Values.f90 but re-declared public
  ! here too: a blanket `private` (above) hides even use-associated names
  ! from re-export unless explicitly listed, and every consumer of this
  ! module reaches env_ref and its assignment(=) through `use Env`.
  public :: env_ref, assignment(=)
  public :: env_new, env_set, env_get, env_find

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
    e%ptr%bindings = array_map_assoc(e%ptr%bindings, key, val)
  end subroutine env_set

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
