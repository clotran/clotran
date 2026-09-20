  ! ---- sorted maps and sets ---------------------------------------------
  !
  ! A sorted map is the array map with its keys kept in comparator
  ! order (Assoc.f90: a flag, a comparator slot, binary search, and no
  ! promotion), and a sorted set is a set over one. core.clj's subseq
  ! and rsubseq ask a Sorted for seqFrom, entryKey, comparator and a
  ! seq with a direction; those are here, with rseq, and the ordering
  ! hook Assoc calls.

  ! Ordering, for Assoc: the map's comparator applied, or Clojure's
  ! compare when it has none. Keys compare cannot order throw
  ! ClassCastException, as on the JVM, and the search stops on huge(0).
  recursive function compare_via(cmp, a, b) result(c)
    type(gc_value), intent(in) :: cmp, a, b
    integer :: c
    logical :: ok
    c = 0
    if (cmp%tag == GCT_NIL) then
       c = compare_values(a, b, ok)
       if (.not. ok) then
          call raise_class("ClassCastException", &
               "cannot compare " // class_name_of(a) // " with " // class_name_of(b), [a, b])
          c = huge(0)
       end if
    else
       c = comparator_call(cmp, a, b)
       if (has_error) c = huge(0)
    end if
  end function compare_via

  ! (reduced x) is {:clotran/reduced x}, an array map of one entry; the
  ! probe for it must not reach a sorted map's comparator, which would
  ! compare the marker key against whatever keys it holds.
  function is_reduced(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    type(gc_value) :: m
    yes = .false.
    m = strip_meta(v)
    if (.not. gca_is(m)) return
    if (gca_is_sorted(m)) return
    yes = gca_contains(m, gc_key("clotran/reduced", [m]))
  end function is_reduced

  ! The sorted map behind a sorted map or set, or nil.
  function sorted_backing(v) result(m)
    type(gc_value), intent(in) :: v
    type(gc_value) :: m
    m = strip_meta(v)
    if (gc_kind(m) == OBJ_SET) m = gc_slot(m, 1)
    if (.not. gca_is_sorted(m)) m = gc_nil()
  end function sorted_backing

  function is_sorted_coll(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    type(gc_value) :: m
    m = sorted_backing(v)
    yes = m%tag /= GCT_NIL
  end function is_sorted_coll

  ! PersistentTreeMap/create keyvals | comparator keyvals, and the set's
  ! create over keys: an empty sorted map, then assoc in turn.
  recursive function sorted_create(args, n, as_set, roots) result(out)
    type(gc_value), intent(in) :: args
    integer, intent(in) :: n
    logical, intent(in) :: as_set
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, items, mp
    integer :: base, i, step
    out = gc_nil()
    base = vs_enter(3)
    if (n >= 2) call vs_set(base + 1, gcv_nth(args, 0))   ! the comparator; nil otherwise
    items = coll_to_vector(gcv_nth(args, n - 1), [roots, vs_get(base + 1)])
    call vs_set(base + 2, items)
    mp = gca_sorted_empty(vs_get(base + 1), [roots, vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, mp)
    step = 2
    if (as_set) step = 1
    do i = 0, gcv_count(vs_get(base + 2)) - step, step
       if (as_set) then
          mp = gca_assoc(vs_get(base + 3), gcv_nth(vs_get(base + 2), i), gcv_nth(vs_get(base + 2), i), &
               [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
       else
          mp = gca_assoc(vs_get(base + 3), gcv_nth(vs_get(base + 2), i), gcv_nth(vs_get(base + 2), i + 1), &
               [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
       end if
       if (has_error) exit
       call vs_set(base + 3, mp)
    end do
    if (.not. has_error) then
       if (as_set) then
          out = gc_obj(OBJ_SET, [vs_get(base + 3)], [roots, vs_get(base + 3)])
       else
          out = vs_get(base + 3)
       end if
    end if
    call vs_leave(base)
  end function sorted_create

  ! The entries of `coll` -- [k v] for a map, the key for a set -- from
  ! position `from` (1-based) forward or backward, as a seq; nil when
  ! there are none.
  function sorted_entries(coll, from, ascending, roots) result(out)
    type(gc_value), intent(in) :: coll
    integer, intent(in) :: from
    logical, intent(in) :: ascending
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, m, acc, e
    integer :: base, i, n, step, last
    logical :: is_set
    out = gc_nil()
    is_set = (gc_kind(strip_meta(coll)) == OBJ_SET)
    m = sorted_backing(coll)
    if (m%tag == GCT_NIL) return
    n = gca_count(m)
    if (from < 1 .or. from > n) return
    if (ascending) then
       step = 1
       last = n
    else
       step = -1
       last = 1
    end if
    base = vs_enter(3)
    call vs_set(base + 1, m)
    acc = gcv_empty([roots, vs_get(base + 1)])
    call vs_set(base + 2, acc)
    do i = from, last, step
       if (is_set) then
          e = gca_key_at(vs_get(base + 1), i)
       else
          e = gcv_build(2, [roots, vs_get(base + 1), vs_get(base + 2)])
          call vs_set(base + 3, e)
          e = gcv_put(vs_get(base + 3), 0, gca_key_at(vs_get(base + 1), i), &
               [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
          e = gcv_put(vs_get(base + 3), 1, gca_val_at(vs_get(base + 1), i), &
               [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
       end if
       call vs_set(base + 3, e)
       acc = gcv_conj(vs_get(base + 2), vs_get(base + 3), &
            [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
       call vs_set(base + 2, acc)
    end do
    out = to_seq(vs_get(base + 2), [roots, vs_get(base + 2)])
    call vs_leave(base)
  end function sorted_entries

  ! (rseq coll): a vector or a sorted collection, last first.
  function reverse_seq(a, roots) result(out)
    type(gc_value), intent(in) :: a
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, acc, m
    integer :: base, i
    out = gc_nil()
    if (gcv_is(a)) then
       if (gcv_count(a) == 0) return
       base = vs_enter(2)
       call vs_set(base + 1, a)
       acc = gcv_empty([roots, vs_get(base + 1)])
       call vs_set(base + 2, acc)
       do i = gcv_count(vs_get(base + 1)) - 1, 0, -1
          acc = gcv_conj(vs_get(base + 2), gcv_nth(vs_get(base + 1), i), [roots, vs_get(base + 1), vs_get(base + 2)])
          call vs_set(base + 2, acc)
       end do
       out = to_seq(vs_get(base + 2), [roots, vs_get(base + 2)])
       call vs_leave(base)
       return
    end if
    m = sorted_backing(a)
    if (m%tag == GCT_NIL) then
       call fail("rseq: not reversible: " // class_name_of(a))
       return
    end if
    out = sorted_entries(a, gca_count(m), .false., roots)
  end function reverse_seq
