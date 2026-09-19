! Env: the lexical environment, over the GC heap.
!
! Shape, matching GC.f90's comment on OBJ_ENV:
!
!   env   an object: slot 1 = bindings map, slot 2 = outer env,
!         i1 = defining namespace index
!
! A chain of frames, each a name -> value map, searched outward. A
! frame is reached by handle, which matters for one specific reason:
!
! An env is the thing a refcounting collector could NOT collect. `eval_fn` binds a
! closure into its own frame so `recur` can find it, and that frame is
! reachable from the closure -- a cycle. Refcounting leaks every such
! closure for the life of the process. Check 5 here is that cycle,
! built deliberately and then collected, which is the correctness half
! of why the GC exists at all (PLAN.md, "Decisions taken").
!
! env_set MUTATES the frame in place rather than returning a new one.
! That is deliberate: `def` and `let*` add to the
! frame a closure may already be holding, and everything sharing that
! frame must see the binding.
module Env
  use GC
  use PersistentArrayMap
  implicit none
  private

  public :: gce_new, gce_is, gce_set, gce_find, gce_get, gce_outer, &
       gce_set_ns, gce_defining_ns

contains

  ! outer may be nil, which makes this a root frame.
  function gce_new(outer, roots) result(e)
    type(gc_value), intent(in) :: outer
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: e, bindings
    type(gc_value), allocatable :: r2(:)
    r2 = with(roots, outer)
    bindings = gcm_empty(r2)
    e = gc_obj(OBJ_ENV, [bindings, outer], with(r2, bindings))
    call gc_set_i1(e, 0)
  end function gce_new

  function gce_is(e) result(yes)
    type(gc_value), intent(in) :: e
    logical :: yes
    yes = (gc_kind(e) == OBJ_ENV)
  end function gce_is

  function gce_outer(e) result(o)
    type(gc_value), intent(in) :: e
    type(gc_value) :: o
    o = gc_nil()
    if (gce_is(e)) o = gc_slot(e, 2)
  end function gce_outer

  ! Mutates this frame. Note the two-step: build the new bindings map
  ! FIRST, then store it. Never store into a slot from an expression
  ! that reads the same slot: a self-referencing assignment silently
  ! drops the update, for a handle just as much as for a pointer.
  subroutine gce_set(e, key, val, roots)
    type(gc_value), intent(in) :: e, key, val
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: next
    type(gc_value), allocatable :: r2(:)
    if (.not. gce_is(e)) return
    r2 = with(with(with(roots, e), key), val)
    next = gcm_assoc(gc_slot(e, 1), key, val, r2)
    call gc_set_slot(e, 1, next)
  end subroutine gce_set

  ! Walks outward. `found` is false when the key is unbound anywhere,
  ! which is DIFFERENT from being bound to nil -- the distinction the
  ! evaluator needs to tell "no such local" from "a local holding nil".
  !
  ! Iterative, not recursive: an env chain is as deep as the nesting of
  ! the program being evaluated, and this is on the hottest path in the
  ! interpreter.
  function gce_find(e, key, val) result(found)
    type(gc_value), intent(in) :: e, key
    type(gc_value), intent(out) :: val
    type(gc_value) :: frame
    logical :: found

    found = .false.
    val = gc_nil()
    frame = e
    do while (gce_is(frame))
       if (gcm_contains(gc_slot(frame, 1), key)) then
          val = gcm_get(gc_slot(frame, 1), key)
          found = .true.
          return
       end if
       frame = gc_slot(frame, 2)
    end do
  end function gce_find

  function gce_get(e, key) result(val)
    type(gc_value), intent(in) :: e, key
    type(gc_value) :: val
    logical :: found
    found = gce_find(e, key, val)
  end function gce_get

  ! The namespace a form in this env was DEFINED in, so a symbol
  ! resolves where it was written rather than where it is called --
  ! inherited from the outer chain when this frame has none of its own.
  subroutine gce_set_ns(e, idx)
    type(gc_value), intent(in) :: e
    integer, intent(in) :: idx
    if (gce_is(e)) call gc_set_i1(e, idx)
  end subroutine gce_set_ns

  function gce_defining_ns(e) result(idx)
    type(gc_value), intent(in) :: e
    type(gc_value) :: frame
    integer :: idx
    idx = 0
    frame = e
    do while (gce_is(frame))
       if (gc_i1(frame) /= 0) then
          idx = gc_i1(frame)
          return
       end if
       frame = gc_slot(frame, 2)
    end do
  end function gce_defining_ns

  function with(roots, v) result(out)
    type(gc_value), intent(in) :: roots(:), v
    type(gc_value), allocatable :: out(:)
    allocate(out(size(roots) + 1))
    out(1:size(roots)) = roots
    out(size(roots) + 1) = v
  end function with

end module Env
