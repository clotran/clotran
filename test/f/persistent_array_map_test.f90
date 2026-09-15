! Validates PersistentArrayMap: get/assoc correctness, structural sharing
! across versions, and that every node allocated is eventually freed.
program persistent_array_map_test
  use values
  use PersistentArrayMap
  implicit none

  logical :: all_ok
  type(array_map_t) :: m0, m1, m2
  integer :: freed_before

  all_ok = .true.

  m0 = array_map_empty()
  call expect_eq("1. empty map has count 0: ", array_map_count(m0), 0, all_ok)

  m1 = array_map_assoc(m0, mkstr("a"), mkint(1))
  m2 = array_map_assoc(m1, mkstr("b"), mkint(2))
  call expect_eq("2a. count after two assoc: ", array_map_count(m2), 2, all_ok)
  call expect_eq("2b. get finds the first key: ", as_int(array_map_get(m2, mkstr("a"))), 1, all_ok)
  call expect_eq("2c. get finds the second key: ", as_int(array_map_get(m2, mkstr("b"))), 2, all_ok)
  block
    type(cons_value) :: missing
    missing = array_map_get(m2, mkstr("z"))
    call expect_eq("2d. get on a missing key is nil: ", missing%tag, TAG_NIL, all_ok)
  end block

  ! 3. Old map is unchanged by building a new one on top of it.
  call expect_eq("3a. m1 still has count 1: ", array_map_count(m1), 1, all_ok)
  block
    type(cons_value) :: missing
    missing = array_map_get(m1, mkstr("b"))
    call expect_eq("3b. m1 doesn't see 'b': ", missing%tag, TAG_NIL, all_ok)
  end block

  ! 4. assoc onto an existing key replaces its value, not appends.
  block
    type(array_map_t) :: m3
    m3 = array_map_assoc(m2, mkstr("a"), mkint(100))
    call expect_eq("4a. replacing a key keeps count the same: ", array_map_count(m3), 2, all_ok)
    call expect_eq("4b. ...with the new value: ", as_int(array_map_get(m3, mkstr("a"))), 100, all_ok)
    call expect_eq("4c. ...and the old map is untouched: ", as_int(array_map_get(m2, mkstr("a"))), 1, all_ok)
  end block

  ! 4d. dissoc removes a key, persistently (the old map is untouched).
  block
    type(array_map_t) :: m4
    type(cons_value) :: missing
    m4 = array_map_dissoc(m2, mkstr("a"))
    call expect_eq("4d. dissoc drops the count by one: ", array_map_count(m4), 1, all_ok)
    missing = array_map_get(m4, mkstr("a"))
    call expect_eq("4e. ...and the key is really gone: ", missing%tag, TAG_NIL, all_ok)
    call expect_eq("4f. ...but the old map still has it: ", as_int(array_map_get(m2, mkstr("a"))), 1, all_ok)
    m4 = array_map_dissoc(m2, mkstr("nope"))
    call expect_eq("4g. dissoc of a missing key changes nothing: ", array_map_count(m4), 2, all_ok)
  end block

  ! 5. The point of the rework: a cons_value holding a map, copied by
  !    plain assignment, correctly shares it.
  block
    type(cons_value) :: boxed, copy
    integer :: freed_here

    boxed%tag = TAG_HASHMAP
    allocate(boxed%map_val)
    boxed%map_val = array_map_assoc(array_map_empty(), mkstr("k"), mkint(42))

    copy = boxed
    call expect_eq("5a. copying a boxed map shares its root (refcount 2): ", &
         boxed%map_val%root%ptr%refcount, 2, all_ok)

    freed_here = array_map_node_total_freed
    call cons_value_release(boxed)
    call expect_eq("5b. releasing one copy frees nothing (copy still holds it): ", &
         array_map_node_total_freed - freed_here, 0, all_ok)
    call expect_eq("5c. ...and the copy still reads correctly: ", &
         as_int(array_map_get(copy%map_val, mkstr("k"))), 42, all_ok)
    call cons_value_release(copy)
  end block

  ! 7. Promotion: the 9th distinct key (real Clojure's own threshold,
  ! confirmed against the `clojure` CLI) switches to the HAMT tier --
  ! transparent to every caller, but exercise it directly here.
  block
    type(array_map_t) :: p, next_p
    type(cons_value), allocatable :: ekeys(:), evals(:)
    integer :: i
    character(len=8) :: numbuf

    p = array_map_empty()
    do i = 1, 8
       write(numbuf, '(I0)') i
       next_p = array_map_assoc(p, mkstr(trim(numbuf)), mkint(i * 10))
       p = next_p
    end do
    call expect_eq("7a. still an array map at exactly 8 entries: ", array_map_count(p), 8, all_ok)
    call expect_eq("7a'. ...not yet promoted: ", merge(1, 0, .not. allocated(p%big)), 1, all_ok)

    next_p = array_map_assoc(p, mkstr("9"), mkint(90))
    p = next_p
    call expect_eq("7b. the 9th key promotes to a hash trie: ", array_map_count(p), 9, all_ok)
    call expect_eq("7b'. ...big is now allocated: ", merge(1, 0, allocated(p%big)), 1, all_ok)
    call expect_eq("7c. every key survives promotion, found by value: ", &
         as_int(array_map_get(p, mkstr("1"))), 10, all_ok)
    call expect_eq("7c'. ...including the one that triggered it: ", &
         as_int(array_map_get(p, mkstr("9"))), 90, all_ok)

    ! Growing further stays promoted (no demotion, matching real Clojure).
    do i = 10, 20
       write(numbuf, '(I0)') i
       next_p = array_map_assoc(p, mkstr(trim(numbuf)), mkint(i * 10))
       p = next_p
    end do
    call expect_eq("7d. keeps growing correctly once promoted: ", array_map_count(p), 20, all_ok)
    call expect_eq("7d'. ...a key added post-promotion is findable: ", &
         as_int(array_map_get(p, mkstr("20"))), 200, all_ok)

    call array_map_entries(p, ekeys, evals)
    call expect_eq("7e. array_map_entries returns every entry: ", size(ekeys), 20, all_ok)
    call expect_eq("7e'. ...keys and vals line up: ", size(evals), 20, all_ok)

    ! Dissoc after promotion: real removal, and no demotion even though
    ! this drops back below the array-map threshold.
    next_p = array_map_dissoc(p, mkstr("1"))
    p = next_p
    call expect_eq("7f. dissoc after promotion drops the count: ", array_map_count(p), 19, all_ok)
    call expect_eq("7f'. ...the key is really gone: ", merge(1, 0, array_map_contains(p, mkstr("1"))), 0, all_ok)
    call expect_eq("7f''. ...still promoted, no demotion: ", merge(1, 0, allocated(p%big)), 1, all_ok)
    next_p = array_map_dissoc(p, mkstr("not-there"))
    p = next_p
    call expect_eq("7g. dissoc of a missing key on a promoted map changes nothing: ", &
         array_map_count(p), 19, all_ok)
  end block
  call expect_eq("7h. every hamt node from the promoted map is freed once it's gone: ", &
       hamt_node_total_freed, hamt_node_total_allocated, all_ok)

  freed_before = array_map_node_total_freed
  m0 = array_map_empty()
  m1 = array_map_empty()
  m2 = array_map_empty()
  call expect_eq("6. dropping every map frees all remaining nodes: ", &
       array_map_node_total_freed, array_map_node_total_allocated, all_ok)

  if (all_ok) then
     print *, ""
     print *, "ALL PERSISTENTARRAYMAP CHECKS PASSED (", array_map_node_total_allocated, " nodes)"
  else
     print *, ""
     print *, "PERSISTENTARRAYMAP CHECKS FAILED"
     stop 1
  end if

contains

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

end program persistent_array_map_test
