! Exercises the GC-backed hash trie on its own. The cases that matter
! are the ones a trie gets wrong: replacing versus adding (count
! drift), splitting a leaf when two keys want the same slot, and true
! hash collisions, which are forced here with a real colliding pair
! rather than hoped for.
program persistent_hash_map_test
  use GC
  use PersistentHashMap
  implicit none

  logical :: all_ok
  type(gc_value) :: no_roots(0)

  all_ok = .true.

  call check_empty()
  call check_assoc_get()
  call check_replace_vs_add()
  call check_real_collisions()
  call check_many_keys()
  call check_dissoc()
  call check_torture()

  if (all_ok) then
     print *, ""
     print *, "ALL GCHAMT CHECKS PASSED"
  else
     print *, ""
     print *, "GCHAMT CHECKS FAILED"
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
    type(gc_value) :: t
    call gc_init(256)
    t = gch_empty(no_roots)
    call ok("1a. an empty trie is a trie: ", gch_is(t))
    call ok_int("1b. ...with count 0: ", gch_count(t), 0)
    call ok("1c. ...containing nothing: ", .not. gch_contains(t, gc_int(1)))
  end subroutine check_empty

  subroutine check_assoc_get()
    type(gc_value) :: t, roots(1)
    integer :: i, bad
    call gc_init(256)
    t = gch_empty(no_roots)
    do i = 1, 100
       roots(1) = t
       t = gch_assoc(t, gc_int(i), gc_int(i * 7), roots)
    end do
    call ok_int("2a. assoc counts up: ", gch_count(t), 100)
    bad = 0
    do i = 1, 100
       if (get_int(t, gc_int(i)) /= i * 7) bad = bad + 1
    end do
    call ok_int("2b. every key reads back: ", bad, 0)
    call ok("2c. a missing key is absent: ", .not. gch_contains(t, gc_int(101)))
  end subroutine check_assoc_get

  ! Count drift is the classic trie bug: a replace that counts as an
  ! add, or a split that counts twice.
  subroutine check_replace_vs_add()
    type(gc_value) :: t, roots(1)
    integer :: i
    call gc_init(256)
    t = gch_empty(no_roots)
    do i = 1, 5
       roots(1) = t
       t = gch_assoc(t, gc_int(42), gc_int(i), roots)
    end do
    call ok_int("3a. re-assoc replaces rather than adds: ", gch_count(t), 1)
    call ok_int("3b. ...with the newest value: ", get_int(t, gc_int(42)), 5)
  end subroutine check_replace_vs_add

  ! A genuine 32-bit hash collision, found rather than assumed. Two
  ! DIFFERENT keys with the SAME hash must both be findable -- that is
  ! the bucket path, and a trie that drops one here looks perfectly
  ! healthy until the day it does not.
  subroutine check_real_collisions()
    type(gc_value) :: t, ka, kb, roots(3)
    character(len=:), allocatable :: sa, sb
    logical :: found
    call gc_init(256)
    call find_collision(sa, sb, found)
    call ok("4a. found a real FNV-1a collision to test with: ", found)
    if (.not. found) return

    t = gch_empty(no_roots)
    roots(1) = t
    ka = gc_key(sa, roots)
    roots(2) = ka
    kb = gc_key(sb, roots)
    roots(3) = kb
    call ok("4b. the two keys really do collide: ", gc_hash(ka) == gc_hash(kb))
    call ok("4c. ...and really are different keys: ", .not. gc_equal(ka, kb))

    t = gch_assoc(t, ka, gc_int(111), roots)
    roots(1) = t
    t = gch_assoc(t, kb, gc_int(222), roots)
    roots(1) = t
    call ok_int("4d. both colliding keys are stored: ", gch_count(t), 2)
    call ok_int("4e. ...the first reads back: ", get_int(t, ka), 111)
    call ok_int("4f. ...and so does the second: ", get_int(t, kb), 222)
    ! Replacing inside a bucket must not grow the count either.
    t = gch_assoc(t, ka, gc_int(999), roots)
    call ok_int("4g. replacing within a bucket keeps the count: ", gch_count(t), 2)
    call ok_int("4h. ...with the new value: ", get_int(t, ka), 999)
  end subroutine check_real_collisions

  ! Enough keys to force several levels of splitting.
  subroutine check_many_keys()
    type(gc_value) :: t, roots(1)
    integer :: i, bad, n
    n = 3000
    call gc_init(64)
    t = gch_empty(no_roots)
    do i = 1, n
       roots(1) = t
       t = gch_assoc(t, gc_int(i), gc_int(i), roots)
    end do
    roots(1) = t
    call ok_int("5a. 3000 keys, count exact: ", gch_count(t), n)
    bad = 0
    do i = 1, n
       if (get_int(t, gc_int(i)) /= i) bad = bad + 1
    end do
    call ok_int("5b. ...every one findable across levels: ", bad, 0)
    call gc_collect(roots)
    call ok_int("5c. ...and all of it survives collection: ", gch_count(t), n)
  end subroutine check_many_keys

  subroutine check_dissoc()
    type(gc_value) :: t, roots(1)
    integer :: i, bad
    call gc_init(256)
    t = gch_empty(no_roots)
    do i = 1, 200
       roots(1) = t
       t = gch_assoc(t, gc_int(i), gc_int(i), roots)
    end do
    roots(1) = t
    t = gch_dissoc(t, gc_int(77), roots)
    roots(1) = t
    call ok_int("7a. dissoc drops the count: ", gch_count(t), 199)
    call ok("7b. ...removes that key: ", .not. gch_contains(t, gc_int(77)))
    bad = 0
    do i = 1, 200
       if (i == 77) cycle
       if (get_int(t, gc_int(i)) /= i) bad = bad + 1
    end do
    call ok_int("7c. ...and leaves every other key findable: ", bad, 0)
    call ok_int("7d. dissoc of a missing key is a no-op: ", &
         gch_count(gch_dissoc(t, gc_int(77), roots)), 199)
  end subroutine check_dissoc

  subroutine check_torture()
    type(gc_value) :: t, roots(1)
    integer :: i, bad
    call gc_init(8)
    gc_torture = .true.
    t = gch_empty(no_roots)
    do i = 1, 60
       roots(1) = t
       t = gch_assoc(t, gc_int(i), gc_int(i * 5), roots)
    end do
    roots(1) = t
    call ok("6a. the heap audits clean under torture: ", gc_check_heap() == "")
    call ok_int("6b. ...with the count right: ", gch_count(t), 60)
    bad = 0
    do i = 1, 60
       if (get_int(t, gc_int(i)) /= i * 5) bad = bad + 1
    end do
    call ok_int("6c. ...and every entry intact: ", bad, 0)
    gc_torture = .false.
  end subroutine check_torture

  ! --- helpers ---

  ! Searches short strings for two with the same 32-bit hash. Integers
  ! cannot be used: mix32 is the Murmur finaliser, which is bijective,
  ! so distinct integers never collide. Open addressing over a power-
  ! of-two table, first-index-wins, so a hit is a real pair.
  subroutine find_collision(sa, sb, found)
    character(len=:), allocatable, intent(out) :: sa, sb
    logical, intent(out) :: found
    integer, parameter :: TBITS = 21
    integer, parameter :: TSIZE = 2**TBITS
    integer, allocatable :: seen(:)
    character(len=16) :: buf
    type(gc_value) :: v
    integer :: i, h, slot, base
    found = .false.
    sa = ""
    sb = ""
    allocate(seen(0:TSIZE - 1))
    seen = 0
    base = vs_enter(1)
    do i = 1, 400000
       write(buf, '(A,I0)') "k", i
       v = gc_key(trim(buf), no_roots)
       call vs_set(base + 1, v)
       h = gc_hash(v)
       slot = iand(ieor(h, ishft(h, -TBITS)), TSIZE - 1)
       if (seen(slot) == 0) then
          seen(slot) = i
       else
          block
            character(len=16) :: other
            type(gc_value) :: ov
            write(other, '(A,I0)') "k", seen(slot)
            ov = gc_key(trim(other), no_roots)
            if (gc_hash(ov) == h .and. trim(other) /= trim(buf)) then
               sa = trim(other)
               sb = trim(buf)
               found = .true.
               exit
            end if
          end block
       end if
    end do
    call vs_leave(base)
  end subroutine find_collision

  function get_int(t, k) result(n)
    type(gc_value), intent(in) :: t, k
    type(gc_value) :: x
    integer :: n
    x = gch_get(t, k)
    n = x%ival
  end function get_int

end program persistent_hash_map_test
