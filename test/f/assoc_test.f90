! Exercises the promotion rule: array map up to 8 entries, hash trie
! beyond, one-way. The cases that matter are the boundary itself and
! what survives crossing it -- a promotion that loses an entry, or
! loses a key bound to nil, is the kind of bug that shows up much
! later and nowhere near its cause.
program assoc_test
  use GC
  use Assoc
  implicit none

  logical :: all_ok
  type(gc_value) :: no_roots(0)

  all_ok = .true.

  call check_small_stays_array()
  call check_promotes_at_the_boundary()
  call check_everything_survives_promotion()
  call check_nil_value_survives()
  call check_replace_does_not_promote()
  call check_one_way()
  call check_torture()

  if (all_ok) then
     print *, ""
     print *, "ALL GCASSOC CHECKS PASSED"
  else
     print *, ""
     print *, "GCASSOC CHECKS FAILED"
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

  ! Builds a map of n integer keys, 1..n, each mapped to key*10.
  function build(n, roots) result(m)
    integer, intent(in) :: n
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m
    type(gc_value) :: r(size(roots) + 1)
    integer :: i
    m = gca_empty(roots)
    do i = 1, n
       r(1:size(roots)) = roots
       r(size(roots) + 1) = m
       m = gca_assoc(m, gc_int(i), gc_int(i * 10), r)
    end do
  end function build

  subroutine check_small_stays_array()
    type(gc_value) :: m
    call gc_init(256)
    m = build(GCA_ARRAY_MAX, no_roots)
    call ok_int("1a. eight entries: ", gca_count(m), GCA_ARRAY_MAX)
    call ok("1b. ...is still an array map: ", gca_is_array_map(m))
    call ok("1c. ...and is a map: ", gca_is(m))
  end subroutine check_small_stays_array

  ! The boundary itself: 8 stays, 9 promotes. Real Clojure does exactly
  ! this, verified against the clojure CLI.
  subroutine check_promotes_at_the_boundary()
    type(gc_value) :: m
    call gc_init(256)
    m = build(GCA_ARRAY_MAX + 1, no_roots)
    call ok_int("2a. nine entries: ", gca_count(m), GCA_ARRAY_MAX + 1)
    call ok("2b. ...has promoted to a trie: ", .not. gca_is_array_map(m))
    call ok("2c. ...and is still a map: ", gca_is(m))
  end subroutine check_promotes_at_the_boundary

  subroutine check_everything_survives_promotion()
    type(gc_value) :: m, roots(1)
    integer :: i, bad, n
    n = 40
    call gc_init(256)
    m = build(n, no_roots)
    roots(1) = m
    call ok_int("3a. every entry is still counted: ", gca_count(m), n)
    bad = 0
    do i = 1, n
       if (get_int(m, gc_int(i)) /= i * 10) bad = bad + 1
    end do
    call ok_int("3b. ...and every one reads back: ", bad, 0)
    call ok("3c. a key that was never added is absent: ", &
         .not. gca_contains(m, gc_int(n + 1)))
    call gc_collect(roots)
    call ok_int("3d. ...and all of it survives collection: ", gca_count(m), n)
  end subroutine check_everything_survives_promotion

  ! A key bound to nil must survive promotion. Copying entries by
  ! reading them back with `get` cannot tell "absent" from "present and
  ! nil", so it would silently drop this one -- which is why promote
  ! walks the entries positionally instead.
  subroutine check_nil_value_survives()
    type(gc_value) :: m, roots(1)
    integer :: i
    call gc_init(256)
    m = gca_empty(no_roots)
    roots(1) = m
    m = gca_assoc(m, gc_int(99), gc_nil(), roots)
    do i = 1, GCA_ARRAY_MAX
       roots(1) = m
       m = gca_assoc(m, gc_int(i), gc_int(i), roots)
    end do
    call ok("4a. the map promoted: ", .not. gca_is_array_map(m))
    call ok("4b. a nil-valued key survives promotion: ", gca_contains(m, gc_int(99)))
    call ok_int("4c. ...still bound to nil: ", get_tag(m, gc_int(99)), GCT_NIL)
    call ok_int("4d. ...and is counted: ", gca_count(m), GCA_ARRAY_MAX + 1)
  end subroutine check_nil_value_survives

  ! Overwriting a key in a FULL array map must not promote: the count
  ! does not change, so the representation should not either.
  subroutine check_replace_does_not_promote()
    type(gc_value) :: m, roots(1)
    call gc_init(256)
    m = build(GCA_ARRAY_MAX, no_roots)
    roots(1) = m
    m = gca_assoc(m, gc_int(3), gc_int(777), roots)
    call ok("5a. replacing in a full array map does not promote: ", &
         gca_is_array_map(m))
    call ok_int("5b. ...the count is unchanged: ", gca_count(m), GCA_ARRAY_MAX)
    call ok_int("5c. ...and the value is new: ", get_int(m, gc_int(3)), 777)
  end subroutine check_replace_does_not_promote

  ! Promotion is one-way, matching Clojure: a trie never demotes, so
  ! nothing may assume "small means array map".
  subroutine check_one_way()
    type(gc_value) :: m, roots(1)
    integer :: i
    call gc_init(256)
    m = build(GCA_ARRAY_MAX + 1, no_roots)
    call ok("6a. promoted: ", .not. gca_is_array_map(m))
    do i = 1, GCA_ARRAY_MAX
       roots(1) = m
       m = gca_dissoc(m, gc_int(i), roots)
    end do
    ! Assert the count actually dropped: without this, a dissoc that
    ! silently did nothing would still "pass" 6b by never shrinking
    ! the map at all. It did exactly that until gch_dissoc existed.
    call ok_int("6b. dissoc really removes from a trie: ", gca_count(m), 1)
    call ok("6c. ...and it stays a trie however small it gets: ", &
         .not. gca_is_array_map(m))
    call ok("6d. ...with the surviving key still findable: ", &
         gca_contains(m, gc_int(GCA_ARRAY_MAX + 1)))
  end subroutine check_one_way

  subroutine check_torture()
    type(gc_value) :: m, roots(1)
    integer :: i, bad
    call gc_init(8)
    gc_torture = .true.
    m = build(30, no_roots)
    roots(1) = m
    block
       character(len=:), allocatable :: dlr_1
       call gc_check_heap(problem=dlr_1)
       call ok("7a. the heap audits clean across promotion: ", dlr_1 == "")
    end block
    call ok_int("7b. ...with the count right: ", gca_count(m), 30)
    bad = 0
    do i = 1, 30
       if (get_int(m, gc_int(i)) /= i * 10) bad = bad + 1
    end do
    call ok_int("7c. ...and every entry intact: ", bad, 0)
    gc_torture = .false.
  end subroutine check_torture

  ! --- helpers (flang cannot take a component off a function result) ---

  function get_int(m, k) result(n)
    type(gc_value), intent(in) :: m, k
    type(gc_value) :: x
    integer :: n
    x = gca_get(m, k)
    n = x%ival
  end function get_int

  function get_tag(m, k) result(t)
    type(gc_value), intent(in) :: m, k
    type(gc_value) :: x
    integer :: t
    x = gca_get(m, k)
    t = x%tag
  end function get_tag

end program assoc_test
