! Validates RT: same generic operations behave correctly whether handed
! a list or a vector -- the actual point of the seq abstraction (this is
! what makes (apply + [1 2 3 4]) and (apply + '(1 2 3 4)) both just work).
program rt_test
  use values
  use PersistentList, only: list_empty, list_cons => cons
  use PersistentVector, only: vector_empty, vector_conj
  use RT
  implicit none

  logical :: all_ok
  type(cons_value) :: lst, vec

  all_ok = .true.

  lst = mklist([1, 2, 3, 4])
  vec = mkvector([1, 2, 3, 4])

  ! 1. Generic sum works identically over a list and a vector -- the
  !    actual (apply + coll) scenario, with no type-specific code.
  call expect_eq("1a. sum over a list: ", sum_via_seq(lst), 10, all_ok)
  call expect_eq("1b. sum over a vector: ", sum_via_seq(vec), 10, all_ok)

  ! 2. first/count/nth agree across both.
  call expect_eq("2a. first of list: ", as_int(first(lst)), 1, all_ok)
  call expect_eq("2b. first of vector: ", as_int(first(vec)), 1, all_ok)
  call expect_eq("2c. count of list: ", count(lst), 4, all_ok)
  call expect_eq("2d. count of vector: ", count(vec), 4, all_ok)
  call expect_eq("2e. nth(list, 2): ", as_int(nth(lst, 2)), 3, all_ok)
  call expect_eq("2f. nth(vector, 2): ", as_int(nth(vec, 2)), 3, all_ok)

  ! 3. rest is always a list, never nil; next is nil once exhausted.
  block
    type(cons_value) :: r, nx
    r = rest(mklist([9]))
    nx = next(mklist([9]))
    call expect_eq("3a. rest of a single-element list has count 0: ", count(r), 0, all_ok)
    call expect_eq("3b. rest's tag is still TAG_LIST (not nil): ", r%tag, TAG_LIST, all_ok)
    call expect_eq("3c. next of a single-element list is nil: ", nx%tag, TAG_NIL, all_ok)
  end block

  ! 4. seq: a vector isn't itself a seq -- (seq vec) builds a list view;
  !    an empty collection seqs to nil.
  block
    type(cons_value) :: s, empty_vec_seq, empty_list_seq
    s = seq(vec)
    empty_vec_seq = seq(vector_to_value(vector_empty()))
    empty_list_seq = seq(mklist_empty())
    call expect_eq("4a. seq(vector) produces a TAG_LIST: ", s%tag, TAG_LIST, all_ok)
    call expect_eq("4b. ...with the same first element: ", as_int(first(s)), 1, all_ok)
    call expect_eq("4c. seq of an empty vector is nil: ", empty_vec_seq%tag, TAG_NIL, all_ok)
    call expect_eq("4d. seq of an empty list is nil: ", empty_list_seq%tag, TAG_NIL, all_ok)
  end block

  ! 5. cons always returns a list, even onto a vector.
  block
    type(cons_value) :: c
    c = cons(mkint(0), vec)
    call expect_eq("5a. cons onto a vector yields a TAG_LIST: ", c%tag, TAG_LIST, all_ok)
    call expect_eq("5b. ...with the consed value first: ", as_int(first(c)), 0, all_ok)
    call expect_eq("5c. ...and count one more: ", count(c), 5, all_ok)
  end block

  ! 6. conj is type-preserving: prepend for list, append for vector.
  block
    type(cons_value) :: cl, cv
    cl = conj(lst, mkint(0))
    cv = conj(vec, mkint(0))
    call expect_eq("6a. conj onto a list prepends: ", as_int(first(cl)), 0, all_ok)
    call expect_eq("6b. conj onto a vector appends (still tag vector): ", cv%tag, TAG_VECTOR, all_ok)
    call expect_eq("6c. ...at the end: ", as_int(nth(cv, 4)), 0, all_ok)
  end block

  if (all_ok) then
     print *, ""
     print *, "ALL RT CHECKS PASSED"
  else
     print *, ""
     print *, "RT CHECKS FAILED"
     stop 1
  end if

contains

  function mkint(i) result(v)
    integer, intent(in) :: i
    type(cons_value) :: v
    v%tag = TAG_INT
    v%int_val = i
  end function mkint

  function as_int(v) result(i)
    type(cons_value), intent(in) :: v
    integer :: i
    i = v%int_val
  end function as_int

  function mklist(xs) result(v)
    integer, intent(in) :: xs(:)
    type(cons_value) :: v
    type(cons_ref) :: l
    integer :: i
    l = list_empty()
    do i = size(xs), 1, -1
       l = list_cons(mkint(xs(i)), l)
    end do
    v%tag = TAG_LIST
    allocate(v%list_val)
    v%list_val = l
  end function mklist

  function mklist_empty() result(v)
    type(cons_value) :: v
    v%tag = TAG_LIST
    allocate(v%list_val)
    v%list_val = list_empty()
  end function mklist_empty

  function mkvector(xs) result(v)
    integer, intent(in) :: xs(:)
    type(cons_value) :: v
    integer :: i
    v = vector_to_value(vector_empty())
    do i = 1, size(xs)
       v = conj(v, mkint(xs(i)))
    end do
  end function mkvector

  function vector_to_value(vec) result(v)
    type(vec_t), intent(in) :: vec
    type(cons_value) :: v
    v%tag = TAG_VECTOR
    allocate(v%vector_val)
    v%vector_val = vec
  end function vector_to_value

  function sum_via_seq(coll) result(total)
    type(cons_value), intent(in) :: coll
    integer :: total
    type(cons_value) :: s
    total = 0
    s = seq(coll)
    do while (s%tag == TAG_LIST .and. count(s) > 0)
       total = total + as_int(first(s))
       s = next(s)
    end do
  end function sum_via_seq

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

end program rt_test
