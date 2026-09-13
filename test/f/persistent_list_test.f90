! Validates PersistentList: cons/first/rest/count correctness, shared
! tails across versions, and that every cell allocated is eventually
! freed. Mirrors persistent_vector_test.f90's discipline.
program persistent_list_test
  use values
  use PersistentList
  implicit none

  logical :: all_ok
  type(cons_ref) :: l0, l1, l2, l3
  integer :: freed_before

  all_ok = .true.

  l0 = list_empty()
  call expect_eq("1. empty list has count 0: ", list_count(l0), 0, all_ok)
  ! rest of an empty list used to segfault: Fortran doesn't guarantee
  ! short-circuit evaluation, so `associated(l%ptr) .and.
  ! allocated(l%ptr%cdr)` dereferenced the null l%ptr anyway.
  call expect_eq("1b. rest of an empty list is empty, not a crash: ", list_count(rest(l0)), 0, all_ok)

  l1 = cons(mkval(1), l0)
  l2 = cons(mkval(2), l1)
  l3 = cons(mkval(3), l2)
  call expect_eq("2a. count after three cons: ", list_count(l3), 3, all_ok)
  call expect_eq("2b. first is the most recent cons: ", as_int(first(l3)), 3, all_ok)
  call expect_eq("2c. rest drops it: ", as_int(first(rest(l3))), 2, all_ok)
  call expect_eq("2d. rest of rest: ", as_int(first(rest(rest(l3)))), 1, all_ok)

  ! 3. Shared tail: l2's cells are untouched by building l3 on top of them.
  call expect_eq("3a. l2 still has its own count: ", list_count(l2), 2, all_ok)
  call expect_eq("3b. l2's first is unchanged: ", as_int(first(l2)), 2, all_ok)

  ! 4. Two different lists consed onto the same tail share it independently.
  block
    type(cons_ref) :: branch_a, branch_b
    branch_a = cons(mkval(100), l1)
    branch_b = cons(mkval(200), l1)
    call expect_eq("4a. branch_a sees its own head: ", as_int(first(branch_a)), 100, all_ok)
    call expect_eq("4b. branch_b sees its own head: ", as_int(first(branch_b)), 200, all_ok)
    call expect_eq("4c. both share the same tail: ", as_int(first(rest(branch_a))), as_int(first(rest(branch_b))), all_ok)
  end block

  ! 5. list_of builds items(1) as the head.
  block
    type(cons_value) :: items(3)
    type(cons_ref) :: l
    items(1) = mkval(10)
    items(2) = mkval(20)
    items(3) = mkval(30)
    l = list_of(items)
    call expect_eq("5a. list_of count: ", list_count(l), 3, all_ok)
    call expect_eq("5b. list_of head is items(1): ", as_int(first(l)), 10, all_ok)
    call expect_eq("5c. list_of last is items(3): ", as_int(first(rest(rest(l)))), 30, all_ok)
  end block

  ! 6. The point of the rework: a cons_value holding a list, copied by
  !    plain assignment, correctly shares it -- not the class(*) bug.
  block
    type(cons_value) :: boxed, copy
    integer :: freed_here

    boxed%tag = TAG_LIST
    allocate(boxed%list_val)
    boxed%list_val = cons(mkval(1), cons(mkval(2), list_empty()))

    copy = boxed
    call expect_eq("6a. copying a boxed list shares its head cell (refcount 2): ", &
         boxed%list_val%ptr%refcount, 2, all_ok)

    freed_here = cons_cell_total_freed
    call cons_value_release(boxed)
    call expect_eq("6b. releasing one copy frees nothing (copy still holds it): ", &
         cons_cell_total_freed - freed_here, 0, all_ok)
    call expect_eq("6c. ...and the copy still reads correctly: ", &
         as_int(first(copy%list_val)), 1, all_ok)
    call cons_value_release(copy)
  end block

  ! 7. Everything should be freed once nothing references it.
  freed_before = cons_cell_total_freed
  l0 = list_empty()
  l1 = list_empty()
  l2 = list_empty()
  l3 = list_empty()
  call expect_eq("7. dropping every list frees all remaining cells: ", &
       cons_cell_total_freed, cons_cell_total_allocated, all_ok)

  if (all_ok) then
     print *, ""
     print *, "ALL PERSISTENTLIST CHECKS PASSED (", cons_cell_total_allocated, " cells)"
  else
     print *, ""
     print *, "PERSISTENTLIST CHECKS FAILED"
     stop 1
  end if

contains

  function mkval(i) result(v)
    integer, intent(in) :: i
    type(cons_value) :: v
    v%tag = TAG_INT
    v%int_val = i
  end function mkval

  function as_int(v) result(i)
    type(cons_value), intent(in) :: v
    integer :: i
    i = v%int_val
  end function as_int

  subroutine expect_eq(label, actual, expected, ok)
    character(len=*), intent(in) :: label
    integer, intent(in) :: actual, expected
    logical, intent(inout) :: ok
    if (actual == expected) then
       print '(A,A,I0)', "ok   - ", label, actual
    else
       print '(A,A,I0,A,I0,A)', "FAIL - ", label, actual, "  (expected ", expected, ")"
       ok = .false.
    end if
    flush(6)
  end subroutine expect_eq

end program persistent_list_test
