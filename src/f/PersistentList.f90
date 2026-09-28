! PersistentList: the persistent list, over the GC heap.
!
! Shape, matching GC.f90's comment on OBJ_CONS:
!
!   cons   an object: slot 1 = car, slot 2 = cdr, i1 = count
!
! Count is cached on the cell, so
! `count` stays O(1) rather than walking the chain. That matters more
! here than it looks: `count` is called constantly by the evaluator on
! argument lists.
!
! The empty list is a SINGLETON, registered once as a GC global root.
! Real Clojure does the same (PersistentList.EMPTY), and it matters for
! more than allocation: `()` must be identical to `()` everywhere, and
! an empty list is not nil -- (seq ()) is nil but () itself is a list,
! which is why this is a real object and not GCT_NIL.
module PersistentList
  use GC
  implicit none
  private

  ! Index of the global-root slot holding the empty-list singleton.
  ! Zero until first use; see gcl_empty.
  type(gc_root), save :: empty_root

  public :: gcl_empty, gcl_cons, gcl_first, gcl_rest, gcl_count, gcl_is
  public :: gcl_image_write, gcl_image_read

contains
  subroutine gcl_image_write(u)
    integer, intent(in) :: u
    write(u) empty_root
  end subroutine gcl_image_write

  subroutine gcl_image_read(u)
    integer, intent(in) :: u
    read(u) empty_root
  end subroutine gcl_image_read


  ! Re-checks the slot rather than trusting the cached index: gc_init
  ! clears the global-root registry, but this module variable survives
  ! it, so a stale index would quietly stop being a singleton and hand
  ! back nil instead. Caught by check 4c. Cheap -- one kind test on a
  ! path that is otherwise a single array read.
  function gcl_empty(roots) result(v)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    type(gc_value) :: none(0)
    if (gc_root_live(empty_root)) then
       v = gc_root_get(empty_root)
       if (gc_kind(v) == OBJ_CONS) return
    end if
    v = gc_obj(OBJ_CONS, none, roots)
    call gc_set_i1(v, 0)
    call gc_global_keep(empty_root, v)
  end function gcl_empty

  function gcl_is(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    yes = (gc_kind(v) == OBJ_CONS)
  end function gcl_is

  function gcl_count(v) result(n)
    type(gc_value), intent(in) :: v
    integer :: n
    n = 0
    if (gcl_is(v)) n = gc_i1(v)
  end function gcl_count

  ! Prepends x. The tail is SHARED, never copied -- that is the whole
  ! point of a persistent list, and under tracing it needs no
  ! bookkeeping at all: the new cell simply refers to the old one.
  function gcl_cons(x, lst, roots) result(v)
    type(gc_value), intent(in) :: x, lst
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, tail
    type(gc_value), allocatable :: r2(:)
    integer :: n

    ! Consing onto anything that is not a list starts a fresh one, so
    ! (cons 1 nil) is (1) rather than an error -- same as Clojure.
    if (gcl_is(lst)) then
       tail = lst
       n = gc_i1(lst)
    else
       allocate(r2(size(roots) + 1))
       r2(1:size(roots)) = roots
       r2(size(roots) + 1) = x
       tail = gcl_empty(r2)
       n = 0
       deallocate(r2)
    end if

    allocate(r2(size(roots) + 2))
    r2(1:size(roots)) = roots
    r2(size(roots) + 1) = x
    r2(size(roots) + 2) = tail
    v = gc_obj(OBJ_CONS, [x, tail], r2)
    call gc_set_i1(v, n + 1)
  end function gcl_cons

  function gcl_first(v) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value) :: out
    out = gc_nil()
    if (.not. gcl_is(v)) return
    if (gc_i1(v) == 0) return
    out = gc_slot(v, 1)
  end function gcl_first

  ! Always a list, never nil -- Clojure's `rest`, as opposed to `next`.
  ! The rest of the empty list is the empty list.
  function gcl_rest(v, roots) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    out = gcl_empty(roots)
    if (.not. gcl_is(v)) return
    if (gc_i1(v) <= 1) return
    out = gc_slot(v, 2)
  end function gcl_rest

end module PersistentList
