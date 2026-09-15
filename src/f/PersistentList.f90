! PersistentList: a real cons-cell list -- O(1) cons, shared tails.
! Types (cons_cell, cons_ref) live in Values.f90. The generic,
! type-dispatching first/rest/count/etc. that anything actually calls
! live in RT.f90.
module PersistentList
  use values
  implicit none
  private

  public :: list_empty, cons, first, rest, list_count, list_of
  public :: has_list, val_lst, val_lst_first, val_lst_rest, val_lst_count, set_list

contains

  function list_empty() result(l)
    type(cons_ref) :: l
  end function list_empty

  ! Prepends x onto l, O(1): shares l's cells rather than copying them.
  function cons(x, l) result(new_l)
    type(cons_value), intent(in) :: x
    type(cons_ref), intent(in) :: l
    type(cons_ref) :: new_l
    type(cons_cell), pointer :: new_cell

    allocate(new_cell)
    new_cell%refcount = 1
    cons_cell_total_allocated = cons_cell_total_allocated + 1
    new_cell%car = x
    if (associated(l%ptr)) then
       new_cell%count = l%ptr%count + 1
       allocate(new_cell%cdr)
       new_cell%cdr = l
    else
       new_cell%count = 1
    end if
    new_l%ptr => new_cell
  end function cons

  function first(l) result(val)
    type(cons_ref), intent(in) :: l
    type(cons_value) :: val
    if (associated(l%ptr)) val = l%ptr%car
  end function first

  function rest(l) result(new_l)
    type(cons_ref), intent(in) :: l
    type(cons_ref) :: new_l
    ! Sequential guards, not `associated(l%ptr) .and. allocated(...)`:
    ! Fortran doesn't guarantee short-circuit evaluation, so that would
    ! dereference the null l%ptr anyway -- confirmed to crash.
    if (.not. associated(l%ptr)) return
    if (.not. allocated(l%ptr%cdr)) return
    new_l = l%ptr%cdr
  end function rest

  function list_count(l) result(n)
    type(cons_ref), intent(in) :: l
    integer :: n
    if (associated(l%ptr)) then
       n = l%ptr%count
    else
       n = 0
    end if
  end function list_count

  ! Builds a list from an array, items(1) first -- items(size) is cons'd
  ! on first so it ends up as the innermost/last cell.
  function list_of(items) result(l)
    type(cons_value), intent(in) :: items(:)
    type(cons_ref) :: l
    integer :: i
    l = list_empty()
    do i = size(items), 1, -1
       l = cons(items(i), l)
    end do
  end function list_of

  ! ---- cons_value-level accessors --------------------------------
  ! Same arrangement as PersistentVector's: these live here rather than
  ! in Values.f90 because Values cannot use this module -- the
  ! dependency runs one way. Each absorbs the allocated() guard its
  ! callers repeated, so an absent list is simply empty.

  function has_list(v) result(yes)
    type(cons_value), intent(in) :: v
    logical :: yes
    yes = allocated(v%list_val)
  end function has_list

  function val_lst_first(v) result(x)
    type(cons_value), intent(in) :: v
    type(cons_value) :: x
    if (allocated(v%list_val)) x = first(v%list_val)
  end function val_lst_first

  function val_lst_rest(v) result(l)
    type(cons_value), intent(in) :: v
    type(cons_ref) :: l
    l = list_empty()
    if (allocated(v%list_val)) l = rest(v%list_val)
  end function val_lst_rest

  ! The backing ref itself, for callers that walk the cells directly.
  ! Copies a cons_ref exactly as `l = v%list_val` always did -- the
  ! defined assignment bumps the refcount either way.
  function val_lst(v) result(l)
    type(cons_value), intent(in) :: v
    type(cons_ref) :: l
    l = list_empty()
    if (allocated(v%list_val)) l = v%list_val
  end function val_lst

  function val_lst_count(v) result(n)
    type(cons_value), intent(in) :: v
    integer :: n
    n = 0
    if (allocated(v%list_val)) n = list_count(v%list_val)
  end function val_lst_count

  subroutine set_list(v, l)
    type(cons_value), intent(inout) :: v
    type(cons_ref), intent(in) :: l
    v%tag = TAG_LIST
    if (.not. allocated(v%list_val)) allocate(v%list_val)
    v%list_val = l
  end subroutine set_list

end module PersistentList
