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
  ! ClassCastException, as in clj, and the search stops on huge(0).
  recursive function compare_via(cmp, a, b) result(c)
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: cmp, a, b
    integer :: c
    logical :: ok
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    tctx => ctx_self()
    c = 0
    if (cmp%tag == GCT_NIL) then
       ! A key ADMITTED to a sorted collection is compared with itself
       ! first (Assoc's empty-map case), which is where PersistentTreeMap
       ! refuses a key that is not nil, a Number or Comparable
       if (same_object(a, b) .and. .not. comparable_kind(a)) then
          block
             call gcp_str(a, .true., s=dlt_1)
             call raise_class("clotran.host.class_cast_exception",  "Default comparator requires nil, Number, or Comparable: " // dlt_1, [a])
          end block
          c = huge(0)
          return
       end if
       c = compare_values(a, b, ok)
       if (.not. ok) then
          block
             call class_name_of(a, s=dlt_1)
             call class_name_of(b, s=dlt_2)
             call raise_class("clotran.host.class_cast_exception",  "cannot compare " // dlt_1 // " with " // dlt_2, [a, b])
          end block
          c = huge(0)
       end if
    else
       c = comparator_call(cmp, a, b)
       if (tctx%has_error) c = huge(0)
    end if
  end function compare_via

  ! Whether `seq` can be asked of v: nil, a string, or a heap object
  ! that is not a fn, a reference or a task. RT.seq throws
  ! IllegalArgumentException for the rest, and so does this, which is
  ! how (first 1) and (get-in m 5) fail rather than answer nil.
  function seqable(v0) result(yes)
    type(gc_value), intent(in) :: v0
    logical :: yes
    type(gc_value) :: v
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    v = strip_meta(v0)
    yes = .true.
    select case (v%tag)
    case (GCT_NIL, GCT_STR)
       return
    case (GCT_OBJ)
       select case (gc_kind(v))
       case (OBJ_CLOSURE, OBJ_BUILTIN, OBJ_COMPILED, OBJ_MULTIFN, OBJ_ATOM, OBJ_VAR, OBJ_NS, OBJ_TASK, OBJ_VOLATILE, &
            OBJ_DELAY, OBJ_REGEX, OBJ_MATCHER, OBJ_WRITER, OBJ_ERR, OBJ_TYPE)
          yes = .false.
       end select
    case default
       yes = .false.
    end select
    if (.not. yes) then
       block
          call class_name_of(v, s=dlt_1)
          call raise_class("clotran.host.illegal_argument_exception",  "Don't know how to create ISeq from: " // dlt_1, [v])
       end block
    end if
  end function seqable

  ! A TAGGED LITERAL -- #inst "..." as data -- is a map of :tag and
  ! :form under a marker key (the probe must not reach a sorted map's
  ! comparator, which would compare the marker against its keys), so that
  ! (:tag x) and (:form x) are ordinary lookups and equality is the
  ! map's. class_name_of answers clotran.host.tagged_literal for it,
  ! which is what instance? and print-method dispatch on.
  ! Whether a STRING has the shape of a UUID: 8-4-4-4-12 hex
  ! digits. A UUID is text here, so this is what uuid? can ask.
  function is_uuid_text(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    type(gc_value) :: s
    character(len=:), allocatable :: u
    integer :: i
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    yes = .false.
    s = strip_meta(v)
    if (s%tag /= GCT_STR) return
    block
       call gc_ref_text(s%ref, s=dlt_1)
       u = dlt_1
    end block
    if (len(u) /= 36) return
    do i = 1, 36
       if (i == 9 .or. i == 14 .or. i == 19 .or. i == 24) then
          if (u(i:i) /= "-") return
       else if (.not. ((u(i:i) >= "0" .and. u(i:i) <= "9") .or. &
            (u(i:i) >= "a" .and. u(i:i) <= "f") .or. &
            (u(i:i) >= "A" .and. u(i:i) <= "F"))) then
          return
       end if
    end do
    yes = .true.
  end function is_uuid_text

  function is_tagged_literal(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    type(gc_value) :: m
    yes = .false.
    m = strip_meta(v)
    if (.not. gca_is(m)) return
    if (gca_is_sorted(m)) return
    yes = gca_contains(m, gc_key("clotran/tagged-literal", [m]))
  end function is_tagged_literal

  ! (reduced x): an atom-shaped box marked i1 = 3 (Eval, clotran.host.reduced)
  function is_reduced(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    type(gc_value) :: m
    m = strip_meta(v)
    yes = gc_kind(m) == OBJ_ATOM
    if (yes) yes = gc_i1(m) == 3
  end function is_reduced

  ! A collection operation answers with the metadata its argument had:
  ! (assoc (with-meta {} m) k v) keeps m, as every persistent
  ! collection's does in clj. Metadata is a wrapper here
  ! (DEVIATIONS 5), so the result is wrapped again.
  function keep_meta(orig, v, roots) result(out)
    type(gc_value), intent(in) :: orig, v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    out = v
    if (gc_kind(orig) /= OBJ_META) return
    if (v%tag /= GCT_OBJ) return
    if (gc_kind(v) == OBJ_META) return
    out = gc_obj(OBJ_META, [v, gc_slot(orig, 2)], [roots, orig, v])
  end function keep_meta

  ! Every argument a number, or ClassCastException for the first that
  ! is not: what Numbers.add, lt and the rest throw, where reading a
  ! string's %ival answered 0 without a word.
  function numbers_ok(args, n, roots) result(ok)
    type(gc_value), intent(in) :: args
    integer, intent(in) :: n
    type(gc_value), intent(in) :: roots(:)
    logical :: ok
    type(gc_value) :: x
    integer :: i
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    ok = .true.
    do i = 0, n - 1
       x = strip_meta(gcv_nth(args, i))
       if (x%tag == GCT_NIL) then
          ! unboxing nil, as clj does it
          ok = .false.
          call raise_class("clotran.host.null_pointer_exception", "", roots)
          return
       else if (.not. is_number(x)) then
          ok = .false.
          block
             call class_name_of(x, s=dlt_1)
             call raise_class("clotran.host.class_cast_exception", "class " // dlt_1 //  " cannot be cast to class clotran.host.number", roots)
          end block
          return
       end if
    end do
  end function numbers_ok

  ! What the default comparator can order: nil, a number, a string, a
  ! keyword, a symbol, a character, a boolean, or a vector.
  function comparable_kind(v0) result(yes)
    type(gc_value), intent(in) :: v0
    logical :: yes
    type(gc_value) :: v
    v = strip_meta(v0)
    select case (v%tag)
    case (GCT_NIL, GCT_INT, GCT_REAL, GCT_RATIO, GCT_STR, GCT_KEY, GCT_SYM, GCT_CHAR, GCT_BOOL, &
          GCT_BIG, GCT_DEC, GCT_BIGRATIO)
       yes = .true.
    case default
       yes = gcv_is(v)
    end select
  end function comparable_kind

  ! seqable, without the error: for the callers that answer their own.
  function seqable_quiet(v0) result(yes)
    type(gc_value), intent(in) :: v0
    logical :: yes
    type(gc_value) :: v
    v = strip_meta(v0)
    yes = .true.
    select case (v%tag)
    case (GCT_NIL, GCT_STR)
       return
    case (GCT_OBJ)
       select case (gc_kind(v))
       case (OBJ_CLOSURE, OBJ_BUILTIN, OBJ_COMPILED, OBJ_MULTIFN, OBJ_ATOM, OBJ_VAR, OBJ_NS, OBJ_TASK, OBJ_VOLATILE, &
            OBJ_DELAY, OBJ_REGEX, OBJ_MATCHER, OBJ_WRITER, OBJ_ERR, OBJ_TYPE)
          yes = .false.
       end select
    case default
       yes = .false.
    end select
  end function seqable_quiet

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
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: args
    integer, intent(in) :: n
    logical, intent(in) :: as_set
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, items, mp
    integer :: base, i, step
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    base = vs_enter(vst, 3)
    if (n >= 2) call vs_set(vst, base + 1, gcv_nth(args, 0))   ! the comparator; nil otherwise
    items = coll_to_vector(gcv_nth(args, n - 1), [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, items)
    if (.not. as_set .and. mod(gcv_count(items), 2) /= 0) then
       call no_value_for_key(items, [roots, vs_get(vst, base + 2)])
       call vs_leave(vst, base)
       return
    end if
    mp = gca_sorted_empty(vs_get(vst, base + 1), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, mp)
    step = 2
    if (as_set) step = 1
    do i = 0, gcv_count(vs_get(vst, base + 2)) - step, step
       if (as_set) then
          mp = gca_assoc(vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 2), i), gcv_nth(vs_get(vst, base + 2), i), &
               [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
       else
          mp = gca_assoc(vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 2), i), gcv_nth(vs_get(vst, base + 2), i + 1), &
               [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
       end if
       if (tctx%has_error) exit
       call vs_set(vst, base + 3, mp)
    end do
    if (.not. tctx%has_error) then
       if (as_set) then
          out = gc_obj(OBJ_SET, [vs_get(vst, base + 3)], [roots, vs_get(vst, base + 3)])
       else
          out = vs_get(vst, base + 3)
       end if
    end if
    call vs_leave(vst, base)
  end function sorted_create

  ! The entries of `coll` -- [k v] for a map, the key for a set -- from
  ! position `from` (1-based) forward or backward, as a seq; nil when
  ! there are none.
  function sorted_entries(coll, from, ascending, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: coll
    integer, intent(in) :: from
    logical, intent(in) :: ascending
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, m, acc, e
    integer :: base, i, n, step, last
    logical :: is_set
    vst => gc_my_stack()
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
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, m)
    acc = gcv_empty([roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, acc)
    do i = from, last, step
       if (is_set) then
          e = gca_key_at(vs_get(vst, base + 1), i)
       else
          e = gcv_build(2, [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call vs_set(vst, base + 3, e)
          e = gcv_put(vs_get(vst, base + 3), 0, gca_key_at(vs_get(vst, base + 1), i), &
               [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
          e = gcv_put(vs_get(vst, base + 3), 1, gca_val_at(vs_get(vst, base + 1), i), &
               [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
          call mark_entry(e)
       end if
       call vs_set(vst, base + 3, e)
       acc = gcv_conj(vs_get(vst, base + 2), vs_get(vst, base + 3), &
            [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
       call vs_set(vst, base + 2, acc)
    end do
    out = to_seq(vs_get(vst, base + 2), [roots, vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function sorted_entries

  ! (rseq coll): a vector or a sorted collection, last first.
  function reverse_seq(a, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: a
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, acc, m
    integer :: base, i
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    out = gc_nil()
    if (gcv_is(a)) then
       if (gcv_count(a) == 0) return
       base = vs_enter(vst, 2)
       call vs_set(vst, base + 1, a)
       acc = gcv_empty([roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 2, acc)
       do i = gcv_count(vs_get(vst, base + 1)) - 1, 0, -1
          acc = gcv_conj(vs_get(vst, base + 2), gcv_nth(vs_get(vst, base + 1), i), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call vs_set(vst, base + 2, acc)
       end do
       out = to_seq(vs_get(vst, base + 2), [roots, vs_get(vst, base + 2)])
       call vs_leave(vst, base)
       return
    end if
    m = sorted_backing(a)
    if (m%tag == GCT_NIL) then
       block
          call class_name_of(a, s=dlt_1)
          call fail("rseq: not reversible: " // dlt_1)
       end block
       return
    end if
    out = sorted_entries(a, gca_count(m), .false., roots)
  end function reverse_seq
