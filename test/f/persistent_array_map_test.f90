! Exercises the GC-backed array map on its own. The cases that matter
! are persistence (assoc must not disturb the original), dissoc's
! swap-with-last, key equality by CONTENT for text, and a map that
! stays correct while every allocation collects.
program persistent_array_map_test
  use GC
  use PersistentArrayMap
  implicit none

  logical :: all_ok
  type(gc_value) :: no_roots(0)

  all_ok = .true.

  call check_empty()
  call check_assoc_get()
  call check_replace_vs_append()
  call check_text_keys_by_content()
  call check_dissoc()
  call check_persistence()
  call check_torture()

  if (all_ok) then
     print *, ""
     print *, "ALL GCMAP CHECKS PASSED"
  else
     print *, ""
     print *, "GCMAP CHECKS FAILED"
     stop 1
  end if

contains

  subroutine ok(label, condition)
    character(len=*), intent(in) :: label
    logical, intent(in) :: condition
    if (condition) then
       print '(A,A)', "ok   - ", label
    else
       print '(A,A)', "FAIL - ", label
       all_ok = .false.
    end if
    flush(6)
  end subroutine ok

  subroutine ok_int(label, got, expected)
    character(len=*), intent(in) :: label
    integer, intent(in) :: got, expected
    if (got == expected) then
       print '(A,A,I0)', "ok   - ", label, got
    else
       print '(A,A,I0,A,I0,A)', "FAIL - ", label, got, "  (expected ", expected, ")"
       all_ok = .false.
    end if
    flush(6)
  end subroutine ok_int

  subroutine check_empty()
    type(gc_value) :: m
    call gc_init(64)
    m = gcm_empty(no_roots)
    call ok("1a. an empty map is a map: ", gcm_is(m))
    call ok_int("1b. ...with count 0: ", gcm_count(m), 0)
    call ok("1c. ...containing nothing: ", .not. gcm_contains(m, gc_int(1)))
    call ok_int("1d. get on a missing key is nil: ", get_tag(m, gc_int(1)), GCT_NIL)
  end subroutine check_empty

  subroutine check_assoc_get()
    type(gc_value) :: m, roots(1)
    integer :: i, bad
    call gc_init(64)
    m = gcm_empty(no_roots)
    do i = 1, 20
       roots(1) = m
       m = gcm_assoc(m, gc_int(i), gc_int(i * 100), roots)
    end do
    call ok_int("2a. assoc counts up: ", gcm_count(m), 20)
    bad = 0
    do i = 1, 20
       if (get_int(m, gc_int(i)) /= i * 100) bad = bad + 1
    end do
    call ok_int("2b. every key reads back: ", bad, 0)
    call ok("2c. a missing key is absent: ", .not. gcm_contains(m, gc_int(21)))
  end subroutine check_assoc_get

  ! Re-assoc must REPLACE, not append -- the bug that turns a map into
  ! a multimap and makes count drift.
  subroutine check_replace_vs_append()
    type(gc_value) :: m, roots(1)
    call gc_init(64)
    m = gcm_empty(no_roots)
    roots(1) = m
    m = gcm_assoc(m, gc_int(7), gc_int(1), roots)
    roots(1) = m
    m = gcm_assoc(m, gc_int(7), gc_int(2), roots)
    roots(1) = m
    m = gcm_assoc(m, gc_int(7), gc_int(3), roots)
    call ok_int("3a. re-assoc replaces rather than appends: ", gcm_count(m), 1)
    call ok_int("3b. ...with the newest value: ", get_int(m, gc_int(7)), 3)
  end subroutine check_replace_vs_append

  ! Text keys compare by CONTENT, not by pool slot. The same string
  ! allocated twice is two slots but one key, and a map that got this
  ! wrong would silently hold duplicates.
  subroutine check_text_keys_by_content()
    type(gc_value) :: m, k1, k2, roots(3)
    call gc_init(64)
    m = gcm_empty(no_roots)
    roots(1) = m
    k1 = gc_key("alpha", roots)
    roots(2) = k1
    k2 = gc_key("alpha", roots)
    roots(3) = k2
    call ok("4a. the same text twice is two pool slots: ", k1%ref /= k2%ref)
    m = gcm_assoc(m, k1, gc_int(1), roots)
    roots(1) = m
    m = gcm_assoc(m, k2, gc_int(2), roots)
    call ok_int("4b. ...but one key: ", gcm_count(m), 1)
    call ok_int("4c. ...with the newest value: ", get_int(m, k1), 2)
    call ok("4d. lookup works through either handle: ", gcm_contains(m, k2))
  end subroutine check_text_keys_by_content

  subroutine check_dissoc()
    type(gc_value) :: m, roots(1)
    integer :: i, bad
    call gc_init(64)
    m = gcm_empty(no_roots)
    do i = 1, 10
       roots(1) = m
       m = gcm_assoc(m, gc_int(i), gc_int(i), roots)
    end do
    roots(1) = m
    ! Remove from the middle: the last entry moves into the hole, so
    ! every OTHER key must still be findable afterwards.
    m = gcm_dissoc(m, gc_int(4), roots)
    call ok_int("5a. dissoc drops the count: ", gcm_count(m), 9)
    call ok("5b. ...removes that key: ", .not. gcm_contains(m, gc_int(4)))
    bad = 0
    do i = 1, 10
       if (i == 4) cycle
       if (get_int(m, gc_int(i)) /= i) bad = bad + 1
    end do
    call ok_int("5c. ...and keeps every other, incl. the moved last: ", bad, 0)
    roots(1) = m
    call ok_int("5d. dissoc of a missing key is a no-op: ", &
         gcm_count(gcm_dissoc(m, gc_int(99), roots)), 9)
  end subroutine check_dissoc

  ! Persistence: the original must be untouched by assoc and dissoc,
  ! and both must survive a collection.
  subroutine check_persistence()
    type(gc_value) :: a, b, c, roots(3)
    integer :: i
    call gc_init(64)
    a = gcm_empty(no_roots)
    do i = 1, 8
       roots(1) = a
       a = gcm_assoc(a, gc_int(i), gc_int(i), roots)
    end do
    roots(1) = a
    b = gcm_assoc(a, gc_int(3), gc_int(333), roots)
    roots(2) = b
    c = gcm_dissoc(a, gc_int(5), roots)
    roots(3) = c
    call ok_int("6a. assoc leaves the original alone: ", get_int(a, gc_int(3)), 3)
    call ok_int("6b. ...and the copy has the change: ", get_int(b, gc_int(3)), 333)
    call ok("6c. dissoc leaves the original alone: ", gcm_contains(a, gc_int(5)))
    call ok("6d. ...and the copy lost the key: ", .not. gcm_contains(c, gc_int(5)))
    call gc_collect(roots)
    call ok_int("6e. all three survive collection: ", &
         gcm_count(a) + gcm_count(b) + gcm_count(c), 8 + 8 + 7)
  end subroutine check_persistence

  subroutine check_torture()
    type(gc_value) :: m, roots(1)
    integer :: i, bad
    call gc_init(8)
    gc_torture = .true.
    m = gcm_empty(no_roots)
    do i = 1, 40
       roots(1) = m
       m = gcm_assoc(m, gc_int(i), gc_int(i * 3), roots)
    end do
    roots(1) = m
    block
       character(len=:), allocatable :: dlr_1
       call gc_check_heap(problem=dlr_1)
       call ok("7a. the heap audits clean under torture: ", dlr_1 == "")
    end block
    call ok_int("7b. ...with the count right: ", gcm_count(m), 40)
    bad = 0
    do i = 1, 40
       if (get_int(m, gc_int(i)) /= i * 3) bad = bad + 1
    end do
    call ok_int("7c. ...and every entry intact: ", bad, 0)
    gc_torture = .false.
  end subroutine check_torture

  ! --- helpers (flang cannot take a component off a function result) ---

  function get_int(m, k) result(n)
    type(gc_value), intent(in) :: m, k
    type(gc_value) :: x
    integer :: n
    x = gcm_get(m, k)
    n = x%ival
  end function get_int

  function get_tag(m, k) result(t)
    type(gc_value), intent(in) :: m, k
    type(gc_value) :: x
    integer :: t
    x = gcm_get(m, k)
    t = x%tag
  end function get_tag

end program persistent_array_map_test
