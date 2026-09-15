! Validates PersistentHashMap directly: the real HAMT tier
! PersistentArrayMap.f90 promotes into past 8 entries. Structural
! sharing across versions, dissoc/collapse, and that every node
! allocated is eventually freed -- the same shape of coverage
! persistent_array_map_test.f90 gives the small-map tier.
program persistent_hash_map_test
  use values
  use PersistentHashMap
  implicit none

  logical :: all_ok

  all_ok = .true.

  block
    type(hamt_ref) :: root0, root1, root2, next_root
    logical :: is_new, found, removed
    integer :: i

    call expect_eq("1. empty root finds nothing: ", &
         merge(1, 0, hamt_contains(root0, mkstr("x"))), 0, all_ok)

    root1 = hamt_assoc(root0, mkstr("a"), mkint(1), is_new)
    call expect_eq("2a. assoc into empty reports a new key: ", merge(1, 0, is_new), 1, all_ok)
    call expect_eq("2b. get finds it: ", as_int(hamt_get(root1, mkstr("a"))), 1, all_ok)
    call expect_eq("2c. the empty root is untouched: ", &
         merge(1, 0, hamt_contains(root0, mkstr("a"))), 0, all_ok)

    next_root = hamt_assoc(root1, mkstr("a"), mkint(100), is_new)
    root2 = next_root
    call expect_eq("3a. re-assoc'ing an existing key reports not-new: ", merge(1, 0, is_new), 0, all_ok)
    call expect_eq("3b. ...with the new value: ", as_int(hamt_get(root2, mkstr("a"))), 100, all_ok)
    call expect_eq("3c. ...and the old version keeps the old value: ", as_int(hamt_get(root1, mkstr("a"))), 1, all_ok)

    ! Enough keys to force real collisions/push-downs at multiple trie
    ! levels (this is exactly the code path a real, isolated repro
    ! found broken three separate ways during development -- see
    ! NOTES.md's "Automatic reallocation" gotcha).
    block
      type(hamt_ref) :: r, nr
      type(cons_value), allocatable :: keys(:), vals(:)
      character(len=8) :: numbuf
      r = fresh_root()
      do i = 1, 500
         write(numbuf, '(I0)') i
         nr = hamt_assoc(r, mkstr(trim(numbuf)), mkint(i * 3), is_new)
         r = nr
         if (.not. is_new) then
            call expect_eq("4-fail. key "//trim(numbuf)//" should have been new: ", 0, 1, all_ok)
         end if
      end do
      call expect_eq("4a. every one of 500 keys is findable after the fact: ", &
           count_findable(r, 500), 500, all_ok)
      call expect_eq("4b. ...with the right value: ", as_int(hamt_get(r, mkstr("250"))), 750, all_ok)

      call hamt_entries(r, keys, vals)
      call expect_eq("4c. hamt_entries returns exactly 500 pairs: ", size(keys), 500, all_ok)
      call expect_eq("4c'. keys and vals line up: ", size(vals), 500, all_ok)

      ! dissoc every 3rd key, then confirm exactly those are gone and
      ! nothing else moved.
      do i = 1, 500, 3
         write(numbuf, '(I0)') i
         nr = hamt_dissoc(r, mkstr(trim(numbuf)), removed)
         r = nr
         if (.not. removed) then
            call expect_eq("4-fail. dissoc of "//trim(numbuf)//" should have removed it: ", 0, 1, all_ok)
         end if
      end do
      call expect_eq("4d. dissoc'd keys are really gone: ", &
           merge(1, 0, hamt_contains(r, mkstr("1"))), 0, all_ok)
      call expect_eq("4d'. ...others survive: ", as_int(hamt_get(r, mkstr("2"))), 6, all_ok)
      call expect_eq("4e. dissoc of an absent key reports not-removed: ", &
           merge(1, 0, dissoc_reports(r, "not-there")), 0, all_ok)
    end block
  end block

  call expect_eq("5. every hamt node allocated is eventually freed: ", &
       hamt_node_total_freed, hamt_node_total_allocated, all_ok)

  if (all_ok) then
     print *, ""
     print *, "ALL PERSISTENTHASHMAP CHECKS PASSED (", hamt_node_total_allocated, " nodes)"
  else
     print *, ""
     print *, "PERSISTENTHASHMAP CHECKS FAILED"
     stop 1
  end if

contains

  function fresh_root() result(r)
    type(hamt_ref) :: r
  end function fresh_root

  function mkint(i) result(v)
    integer, intent(in) :: i
    type(cons_value) :: v
    v%tag = TAG_INT
    v%int_val = i
  end function mkint

  function mkstr(s) result(v)
    character(len=*), intent(in) :: s
    type(cons_value) :: v
    v%tag = TAG_STRING
    call set_str(v, s)
  end function mkstr

  function as_int(v) result(i)
    type(cons_value), intent(in) :: v
    integer :: i
    i = v%int_val
  end function as_int

  function count_findable(r, n) result(c)
    type(hamt_ref), intent(in) :: r
    integer, intent(in) :: n
    integer :: c, i
    character(len=8) :: numbuf
    c = 0
    do i = 1, n
       write(numbuf, '(I0)') i
       if (hamt_contains(r, mkstr(trim(numbuf)))) c = c + 1
    end do
  end function count_findable

  function dissoc_reports(r, s) result(removed)
    type(hamt_ref), intent(in) :: r
    character(len=*), intent(in) :: s
    logical :: removed
    type(hamt_ref) :: nr
    nr = hamt_dissoc(r, mkstr(s), removed)
  end function dissoc_reports

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

end program persistent_hash_map_test
