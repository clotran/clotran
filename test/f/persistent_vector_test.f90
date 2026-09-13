! Validates PersistentVector: nth/conj correctness, structural sharing
! across versions, tree growth past one and two levels, and that every
! node allocated is eventually freed.
program persistent_vector_test
  use values
  use PersistentVector
  implicit none

  logical :: all_ok
  type(vec_t) :: v0, v1, v40, v_big
  integer :: i, freed_before

  all_ok = .true.

  v0 = vector_empty()
  call expect_eq("1. empty vector has count 0: ", vector_count(v0), 0, all_ok)

  v1 = vector_conj(v0, mkval(42))
  call expect_eq("2a. count after one conj: ", vector_count(v1), 1, all_ok)
  call expect_eq("2b. nth(0) reads it back: ", as_int(vector_nth(v1, 0)), 42, all_ok)

  block
    type(vec_t) :: v
    logical :: ok40
    v = vector_empty()
    do i = 0, 39
       v = vector_conj(v, mkval(i * 10))
    end do
    ok40 = .true.
    do i = 0, 39
       if (as_int(vector_nth(v, i)) /= i * 10) ok40 = .false.
    end do
    call expect_eq("3. 40 elements (one level of growth) all read back: ", merge(1, 0, ok40), 1, all_ok)
    v40 = v
  end block

  block
    type(vec_t) :: v41
    v41 = vector_conj(v40, mkval(9999))
    call expect_eq("4a. old vector's count is unchanged: ", vector_count(v40), 40, all_ok)
    call expect_eq("4b. old vector's last element is unchanged: ", as_int(vector_nth(v40, 39)), 390, all_ok)
    call expect_eq("4c. new vector sees the appended element: ", as_int(vector_nth(v41, 40)), 9999, all_ok)
  end block

  block
    type(vec_t) :: v
    logical :: ok_big
    v = vector_empty()
    do i = 0, 1999
       v = vector_conj(v, mkval(i))
    end do
    ok_big = (as_int(vector_nth(v, 0)) == 0) .and. (as_int(vector_nth(v, 1000)) == 1000) &
         .and. (as_int(vector_nth(v, 1999)) == 1999)
    call expect_eq("5. 2000 elements (two levels of growth) sampled correctly: ", merge(1, 0, ok_big), 1, all_ok)
    v_big = v
  end block

  ! 6. The actual point of this rework: a cons_value holding a vector,
  !    copied (as it will be constantly, e.g. into a cons_cell%car), must
  !    correctly share the underlying trie -- not silently alias it the
  !    way class(*) did.
  block
    type(cons_value) :: boxed, copy
    integer :: freed_here

    boxed%tag = TAG_VECTOR
    allocate(boxed%vector_val)
    boxed%vector_val = vector_conj(vector_conj(vector_empty(), mkval(1)), mkval(2))

    copy = boxed ! plain assignment of a cons_value

    call expect_eq("6a. copying a boxed vector shares its root (refcount 2): ", &
         boxed%vector_val%root%ptr%refcount, 2, all_ok)

    freed_here = vec_node_total_freed
    call cons_value_release(boxed)
    call expect_eq("6b. releasing one copy frees nothing (copy still holds it): ", &
         vec_node_total_freed - freed_here, 0, all_ok)
    call expect_eq("6c. ...and the copy still reads correctly: ", &
         as_int(vector_nth(copy%vector_val, 1)), 2, all_ok)
    call cons_value_release(copy)
  end block

  freed_before = vec_node_total_freed
  v0 = vector_empty()
  v1 = vector_empty()
  v40 = vector_empty()
  v_big = vector_empty()
  call expect_eq("7. dropping every vector frees all remaining nodes: ", &
       vec_node_total_freed, vec_node_total_allocated, all_ok)

  if (all_ok) then
     print *, ""
     print *, "ALL PERSISTENTVECTOR CHECKS PASSED (", vec_node_total_allocated, " nodes)"
  else
     print *, ""
     print *, "PERSISTENTVECTOR CHECKS FAILED"
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

end program persistent_vector_test
