  ! ===================================================================
  ! exec.inc -- the executor. Included into Eval.f90.
  !
  ! Walks the nodes analyze.inc builds. Locals live in `frame`, a raw
  ! vector of slots owned by the current fn invocation; nothing is
  ! looked up by name at run time. Intermediates that must survive an
  ! allocation still go on the value stack (vs_*), exactly as before:
  ! this stage changes what is executed, not yet how it is rooted.
  ! ===================================================================

  ! Three accessors, because Fortran will not select a component off a
  ! function result (NOTES.md gotchas): the value goes through a
  ! variable first.
  integer function int_of(v)
    type(gc_value), intent(in) :: v
    type(gc_value) :: t
    t = strip_meta(v)
    int_of = int(t%ival, kind=4)
  end function int_of

  integer function tag_of(v)
    type(gc_value), intent(in) :: v
    tag_of = v%tag
  end function tag_of

  function sym_text(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    type(gc_value) :: t
    t = strip_meta(v)
    s = gc_ref_text(t%ref)
  end function sym_text

  ! A frame of n nil slots.
  function new_frame(n, roots) result(fr)
    integer, intent(in) :: n
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: fr
    fr = gc_vec(max(n, 0), roots)
  end function new_frame

  function frame_get(fr, slot) result(v)
    type(gc_value), intent(in) :: fr
    integer, intent(in) :: slot
    type(gc_value) :: v
    v = gc_vec_get(fr, slot + 1)
  end function frame_get

  subroutine frame_set(fr, slot, v)
    type(gc_value), intent(in) :: fr, v
    integer, intent(in) :: slot
    call gc_vec_set(fr, slot + 1, v)
  end subroutine frame_set

  ! Evaluates every child into a persistent vector of values.
  recursive function exec_args(kids, from, frame) result(argv)
    type(gc_value), intent(in) :: kids, frame
    integer, intent(in) :: from
    type(gc_value) :: argv, v
    integer :: base, i
    base = vs_enter(3)
    call vs_set(base + 1, kids)
    call vs_set(base + 2, frame)
    argv = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, argv)
    do i = from, gcv_count(vs_get(base + 1)) - 1
       v = exec(gcv_nth(vs_get(base + 1), i), vs_get(base + 2))
       if (has_error) exit
       argv = gcv_conj(vs_get(base + 3), v, [vs_get(base + 1), vs_get(base + 2), v])
       call vs_set(base + 3, argv)
    end do
    argv = vs_get(base + 3)
    call vs_leave(base)
  end function exec_args

  ! (quote v) -- a value as a form the old walker evaluates to itself.
  ! The bridge to eval_dot and eval_new, which still take forms.
  function quoted(v, roots) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, q
    integer :: base
    base = vs_enter(3)
    call vs_set(base + 1, v)
    q = gcl_cons(vs_get(base + 1), gcl_empty([roots, vs_get(base + 1)]), [roots, vs_get(base + 1)])
    call vs_set(base + 2, q)
    q = gc_sym("quote", [roots, vs_get(base + 2)])
    call vs_set(base + 3, q)
    out = gcl_cons(vs_get(base + 3), vs_get(base + 2), [roots, vs_get(base + 2), vs_get(base + 3)])
    call vs_leave(base)
  end function quoted

  ! A list of quoted values from a vector of values.
  function quoted_list(argv, roots) result(out)
    type(gc_value), intent(in) :: argv
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, q
    integer :: base, i
    base = vs_enter(3)
    call vs_set(base + 1, argv)
    out = gcl_empty([roots, vs_get(base + 1)])
    call vs_set(base + 2, out)
    do i = gcv_count(argv) - 1, 0, -1
       q = quoted(gcv_nth(vs_get(base + 1), i), [roots, vs_get(base + 2)])
       call vs_set(base + 3, q)
       out = gcl_cons(vs_get(base + 3), vs_get(base + 2), [roots, vs_get(base + 2), vs_get(base + 3)])
       call vs_set(base + 2, out)
    end do
    out = vs_get(base + 2)
    call vs_leave(base)
  end function quoted_list

  ! --- closures ------------------------------------------------------

  ! A closure over `frame` from a template: the captured slots are
  ! COPIED now. Slot 1 = template, 2 = captures, 5 = name (set by def).
  function make_closure_from(tmpl, frame, roots) result(fn)
    type(gc_value), intent(in) :: tmpl, frame
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: fn, caps, capv
    integer :: base, ncap, i
    base = vs_enter(3)
    call vs_set(base + 1, tmpl)
    call vs_set(base + 2, frame)
    capv = gcv_nth(tmpl, 2)
    ncap = gcv_count(capv) / 2
    caps = gc_vec(ncap, [roots, vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, caps)
    do i = 0, ncap - 1
       call gc_vec_set(vs_get(base + 3), i + 1, &
            frame_get(vs_get(base + 2), int_of(gcv_nth(gcv_nth(vs_get(base + 1), 2), 2 * i))))
    end do
    fn = gc_obj(OBJ_CLOSURE, [vs_get(base + 1), vs_get(base + 3), gc_nil(), gc_nil(), gc_nil()], &
         [roots, vs_get(base + 1), vs_get(base + 3)])
    call vs_leave(base)
  end function make_closure_from

  ! Re-copies a closure's captures from `frame`: letfn's second pass,
  ! after every function of the group exists.
  subroutine refresh_captures(fn, frame)
    type(gc_value), intent(in) :: fn, frame
    type(gc_value) :: tmpl, caps, capv
    integer :: i, ncap
    tmpl = gc_slot(fn, 1)
    caps = gc_slot(fn, 2)
    capv = gcv_nth(tmpl, 2)
    ncap = gcv_count(capv) / 2
    do i = 0, ncap - 1
       call gc_vec_set(caps, i + 1, frame_get(frame, int_of(gcv_nth(capv, 2 * i))))
    end do
  end subroutine refresh_captures

  logical function is_node_closure(fn)
    type(gc_value), intent(in) :: fn
    is_node_closure = .false.
    if (gc_kind(fn) /= OBJ_CLOSURE) return
    is_node_closure = gcv_is(gc_slot(fn, 1)) .and. (gc_kind(gc_slot(fn, 3)) /= OBJ_ENV)
    if (is_node_closure) is_node_closure = (gcv_count(gc_slot(fn, 1)) == 5)
  end function is_node_closure

  ! Calls a closure: pick the arity, build the frame, bind, run.
  recursive function invoke_closure(fn, argv) result(out)
    type(gc_value), intent(in) :: fn, argv
    type(gc_value) :: out, tmpl, arities, ar, frame, caps, capv, rest
    integer :: base, argc, i, n, nfixed, start, nslots, ncap, self
    logical :: variadic, found

    out = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, fn)
    call vs_set(base + 2, argv)
    call push_frame(fn, pending_site)
    pending_site = 0
    tmpl = gc_slot(fn, 1)
    call vs_set(base + 3, tmpl)
    arities = gcv_nth(tmpl, 1)
    argc = gcv_count(argv)

    ! An exact fixed arity wins; otherwise the variadic one that fits.
    found = .false.
    n = gcv_count(arities)
    do i = 0, n - 1
       ar = gcv_nth(arities, i)
       nfixed = int_of(gcv_nth(ar, 0))
       variadic = truthy(gcv_nth(ar, 1))
       if (.not. variadic .and. nfixed == argc) then
          found = .true.
          exit
       end if
    end do
    if (.not. found) then
       do i = 0, n - 1
          ar = gcv_nth(arities, i)
          nfixed = int_of(gcv_nth(ar, 0))
          variadic = truthy(gcv_nth(ar, 1))
          if (variadic .and. argc >= nfixed) then
             found = .true.
             exit
          end if
       end do
    end if
    if (.not. found) then
       call raise_arity(argc, vs_get(base + 1), [vs_get(base + 1), vs_get(base + 2)])
       call pop_frame()
       call vs_leave(base)
       return
    end if
    call vs_set(base + 4, ar)
    start = int_of(gcv_nth(ar, 2))
    nslots = int_of(gcv_nth(vs_get(base + 3), 3))
    self = int_of(gcv_nth(vs_get(base + 3), 4))

    frame = new_frame(nslots, [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3), vs_get(base + 4)])
    call vs_set(base + 5, frame)
    do i = 0, nfixed - 1
       call frame_set(vs_get(base + 5), start + i, gcv_nth(vs_get(base + 2), i))
    end do
    if (variadic) then
       ! nil when nothing is left, not the empty list (if-let asserts it)
       if (argc <= nfixed) then
          call frame_set(vs_get(base + 5), start + nfixed, gc_nil())
       else
          rest = gcl_empty([vs_get(base + 1), vs_get(base + 2), vs_get(base + 5)])
          call frame_set(vs_get(base + 5), start + nfixed, rest)
          do i = argc - 1, nfixed, -1
             rest = gcl_cons(gcv_nth(vs_get(base + 2), i), frame_get(vs_get(base + 5), start + nfixed), &
                  [vs_get(base + 1), vs_get(base + 2), vs_get(base + 5)])
             call frame_set(vs_get(base + 5), start + nfixed, rest)
          end do
       end if
    end if
    ! captures, then the fn's own name
    caps = gc_slot(vs_get(base + 1), 2)
    capv = gcv_nth(vs_get(base + 3), 2)
    ncap = gcv_count(capv) / 2
    do i = 0, ncap - 1
       call frame_set(vs_get(base + 5), int_of(gcv_nth(capv, 2 * i + 1)), gc_vec_get(caps, i + 1))
    end do
    if (self >= 0) call frame_set(vs_get(base + 5), self, vs_get(base + 1))

    ! The body is a recur point: recur has already rewritten the
    ! parameter slots, so running the body again is the loop.
    do
       out = exec(gcv_nth(vs_get(base + 4), 3), vs_get(base + 5))
       if (has_error) exit
       if (gc_kind(out) /= OBJ_RECUR) exit
    end do
    call pop_frame()
    call vs_leave(base)
  end function invoke_closure

  ! --- the executor --------------------------------------------------

  recursive function exec(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, kids, v, fnv
    integer :: base, kind, i, n

    out = gc_nil()
    if (has_error) return
    if (ev_limit == 0) call read_depth_limit()
    ev_depth = ev_depth + 1
    gce_evals = gce_evals + 1
    if (ev_depth > ev_limit) then
       call fail("stack overflow")
       ev_depth = ev_depth - 1
       return
    end if
    base = vs_enter(4)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, frame)
    kind = gc_i1(nd)
    kids = gc_slot(nd, 1)

    select case (kind)
    case (N_CONST)
       out = gc_slot(nd, 2)
    case (N_LOCAL)
       out = frame_get(frame, gc_i2(nd))
    case (N_VAR)
       out = gcn_var_value(gc_slot(nd, 2))
    case (N_IF)
       v = exec(gcv_nth(kids, 0), frame)
       if (.not. has_error) then
          if (truthy(v)) then
             out = exec(gcv_nth(gc_slot(vs_get(base + 1), 1), 1), vs_get(base + 2))
          else if (gcv_count(gc_slot(vs_get(base + 1), 1)) > 2) then
             out = exec(gcv_nth(gc_slot(vs_get(base + 1), 1), 2), vs_get(base + 2))
          end if
       end if
    case (N_DO)
       n = gcv_count(kids)
       do i = 0, n - 1
          out = exec(gcv_nth(gc_slot(vs_get(base + 1), 1), i), vs_get(base + 2))
          if (has_error) exit
       end do
    case (N_CALL)
       fnv = exec(gcv_nth(kids, 0), frame)
       if (.not. has_error) then
          call vs_set(base + 3, fnv)
          v = exec_args(gc_slot(vs_get(base + 1), 1), 1, vs_get(base + 2))
          if (.not. has_error) then
             call vs_set(base + 4, v)
             ! where this call is, for the frame invoke_closure pushes
             v = gc_slot(vs_get(base + 1), 4)
             pending_site = 0
             if (v%tag == GCT_INT) pending_site = int(v%ival, kind=4)
             out = apply(vs_get(base + 3), vs_get(base + 4))
          end if
       end if
    case (N_VECTOR)
       out = exec_args(kids, 0, frame)
    case (N_MAP)
       out = exec_map(kids, frame)
    case (N_SET)
       v = exec_args(kids, 0, frame)
       if (.not. has_error) then
          call vs_set(base + 3, v)
          out = vec_to_set(vs_get(base + 3), [vs_get(base + 1)])
       end if
    case (N_DEF)
       out = exec_def(nd, frame)
    case (N_LET)
       out = exec_let(nd, frame, .false.)
    case (N_LOOP)
       out = exec_let(nd, frame, .true.)
    case (N_LETFN)
       out = exec_letfn(nd, frame)
    case (N_FN)
       out = make_closure_from(gc_slot(nd, 2), frame, [vs_get(base + 1), vs_get(base + 2)])
    case (N_LAZY)
       v = make_closure_from(gc_slot(nd, 2), frame, [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 3, v)
       out = gc_obj(OBJ_LAZY, [vs_get(base + 3), gc_nil(), gc_nil()], [vs_get(base + 3)])
       call gc_set_i1(out, LAZY_PENDING)
    case (N_RECUR)
       out = exec_recur(nd, frame)
    case (N_THROW)
       v = exec(gcv_nth(kids, 0), frame)
       if (.not. has_error) then
          call set_thrown(v)
          has_error = .true.
          last_error = gcp_str(v, .true.)
          call capture_trace()
       end if
    case (N_TRY)
       out = exec_try(nd, frame)
    case (N_CASE)
       out = exec_case(nd, frame)
    case (N_DEFTYPE)
       out = exec_deftype(nd, frame)
    case (N_DOT)
       out = exec_dot(nd, frame)
    case (N_NEW)
       v = exec_args(kids, 0, frame)
       if (.not. has_error) then
          call vs_set(base + 3, v)
          v = quoted_list(vs_get(base + 3), [vs_get(base + 1)])
          call vs_set(base + 4, v)
          v = gcl_cons(gc_slot(vs_get(base + 1), 2), vs_get(base + 4), [vs_get(base + 1), vs_get(base + 4)])
          call vs_set(base + 4, v)
          out = eval_new(vs_get(base + 4), gc_nil())
       end if
    case (N_NEWTYPE)
       v = exec_args(kids, 0, frame)
       if (.not. has_error) then
          call vs_set(base + 3, v)
          fnv = find_type(sym_text(gc_slot(vs_get(base + 1), 2)))
          if (gc_kind(fnv) /= OBJ_TYPE) then
             call fail("no such class: " // sym_text(gc_slot(vs_get(base + 1), 2)))
          else
             call vs_set(base + 4, fnv)
             out = construct_type_vals(vs_get(base + 4), vs_get(base + 3))
          end if
       end if
    case (N_SETBANG)
       out = exec_setbang(nd, frame)
    case (N_LATEVAR)
       v = resolve_var(gc_slot(nd, 2), gc_nil())
       if (gcn_is_var(v)) then
          out = gcn_var_value(v)
       else
          call fail("Unable to resolve symbol: " // sym_text(gc_slot(vs_get(base + 1), 2)))
       end if
    case (N_FAIL)
       call fail(sym_text(gc_slot(nd, 2)))
    case (N_TOP)
       v = new_frame(gc_i2(nd), [vs_get(base + 1)])
       call vs_set(base + 3, v)
       out = exec(gc_slot(vs_get(base + 1), 2), vs_get(base + 3))
    case (N_TOPDO)
       ! Each subform analysed after the previous one has run.
       call vs_set(base + 3, gc_slot(nd, 2))
       do while (gcl_count(vs_get(base + 3)) > 0)
          v = analyze_top(gcl_first(vs_get(base + 3)))
          if (has_error) exit
          call vs_set(base + 4, v)
          out = exec(vs_get(base + 4), gc_nil())
          if (has_error) exit
          call vs_set(base + 3, gcl_rest(vs_get(base + 3), [vs_get(base + 1)]))
       end do
    case default
       call fail("exec: unknown node kind")
    end select

    if (has_error) call note_position(vs_get(base + 1))
    call vs_leave(base)
    ev_depth = ev_depth - 1
  end function exec

  ! Appends "  at file:line:col" to the error once, from the innermost
  ! node that has a position -- the error propagates outward through
  ! every enclosing node, and only the first appends.
  subroutine note_position(nd)
    type(gc_value), intent(in) :: nd
    type(gc_value) :: p
    p = gc_slot(nd, 4)
    if (p%tag /= GCT_INT) return
    if (index(last_error, "  at ") > 0) return
    last_error = last_error // "  at " // gcr_position(int(p%ival, kind=4))
  end subroutine note_position

  recursive function exec_map(kids, frame) result(out)
    type(gc_value), intent(in) :: kids, frame
    type(gc_value) :: out, k, v
    integer :: base, i
    base = vs_enter(4)
    call vs_set(base + 1, kids)
    call vs_set(base + 2, frame)
    out = gca_empty([vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, out)
    do i = 0, gcv_count(kids) - 1, 2
       k = exec(gcv_nth(vs_get(base + 1), i), vs_get(base + 2))
       if (has_error) exit
       call vs_set(base + 4, k)
       v = exec(gcv_nth(vs_get(base + 1), i + 1), vs_get(base + 2))
       if (has_error) exit
       out = gca_assoc(vs_get(base + 3), vs_get(base + 4), v, [vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
       call vs_set(base + 3, out)
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function exec_map

  function vec_to_set(vals, roots) result(out)
    type(gc_value), intent(in) :: vals
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, mp
    integer :: base, i
    base = vs_enter(2)
    call vs_set(base + 1, vals)
    mp = gca_empty([roots, vs_get(base + 1)])
    call vs_set(base + 2, mp)
    do i = 0, gcv_count(vals) - 1
       mp = gca_assoc(vs_get(base + 2), gcv_nth(vs_get(base + 1), i), gcv_nth(vs_get(base + 1), i), &
            [roots, vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 2, mp)
    end do
    out = gc_obj(OBJ_SET, [vs_get(base + 2)], [roots, vs_get(base + 2)])
    call vs_leave(base)
  end function vec_to_set

  ! def: the Var was interned at analysis; here it gets its value, its
  ! evaluated metadata, and -- if the value is a closure with no name
  ! yet -- the qualified name an arity error will report.
  recursive function exec_def(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, var, v, md, fnv, nmsym
    character(len=:), allocatable :: qual
    integer :: base, flags

    out = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, frame)
    var = gc_slot(nd, 2)
    call vs_set(base + 3, var)
    flags = gc_i2(nd)
    if (iand(flags, 1) /= 0) then
       v = exec(gcv_nth(gc_slot(vs_get(base + 1), 1), 0), vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       call vs_set(base + 4, v)
       call gc_set_slot(vs_get(base + 3), 1, vs_get(base + 4))
       call gc_set_i1(vs_get(base + 3), 1)
    end if
    md = gc_slot(vs_get(base + 1), 3)
    if (gc_kind(md) == OBJ_AST) then
       md = exec(md, vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       call vs_set(base + 5, md)
       call gc_set_slot(vs_get(base + 3), 2, vs_get(base + 5))
    end if
    fnv = strip_meta(gcn_var_value(vs_get(base + 3)))
    if (gc_kind(fnv) == OBJ_CLOSURE) then
       if (tag_of(gc_slot(fnv, 5)) == GCT_NIL) then
          call vs_set(base + 4, fnv)
          nmsym = gc_slot(vs_get(base + 3), 4)
          qual = gcn_name(gc_slot(vs_get(base + 3), 3)) // "/" // gc_ref_text(nmsym%ref)
          call gc_set_slot(vs_get(base + 4), 5, gc_sym(qual, [vs_get(base + 3), vs_get(base + 4)]))
       end if
    end if
    if (iand(flags, 2) /= 0) call var_set_macro(vs_get(base + 3), gc_nil())
    out = vs_get(base + 3)
    call vs_leave(base)
  end function exec_def

  ! let* and loop*: inits into consecutive slots, then the body; a loop
  ! runs its body again for as long as it recurs.
  recursive function exec_let(nd, frame, is_loop) result(out)
    type(gc_value), intent(in) :: nd, frame
    logical, intent(in) :: is_loop
    type(gc_value) :: out, v
    integer :: base, i, n, start

    out = gc_nil()
    base = vs_enter(2)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, frame)
    n = gc_i2(nd)
    start = int_of(gc_slot(nd, 2))
    do i = 0, n - 1
       v = exec(gcv_nth(gc_slot(vs_get(base + 1), 1), i), vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       call frame_set(vs_get(base + 2), start + i, v)
    end do
    do
       out = exec(gcv_nth(gc_slot(vs_get(base + 1), 1), n), vs_get(base + 2))
       if (has_error) exit
       if (.not. is_loop) exit
       if (gc_kind(out) /= OBJ_RECUR) exit
    end do
    call vs_leave(base)
  end function exec_let

  ! letfn*: every closure is made, stored, and then has its captures
  ! copied AGAIN, so each one sees the others.
  recursive function exec_letfn(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, v
    integer :: base, i, n, start
    out = gc_nil()
    base = vs_enter(2)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, frame)
    n = gc_i2(nd)
    start = int_of(gc_slot(nd, 2))
    do i = 0, n - 1
       v = exec(gcv_nth(gc_slot(vs_get(base + 1), 1), i), vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       call frame_set(vs_get(base + 2), start + i, v)
    end do
    do i = 0, n - 1
       v = frame_get(vs_get(base + 2), start + i)
       if (is_node_closure(v)) call refresh_captures(v, vs_get(base + 2))
    end do
    out = exec(gcv_nth(gc_slot(vs_get(base + 1), 1), n), vs_get(base + 2))
    call vs_leave(base)
  end function exec_letfn

  ! recur: arguments evaluated, THEN written to the target's slots (an
  ! argument may read a slot another argument replaces), then a marker
  ! the enclosing loop or fn body reads. Into a variadic fn the last
  ! argument is the rest parameter itself, as Clojure's recur binds it.
  recursive function exec_recur(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, argv, rinfo
    integer :: base, i, n, start
    out = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, frame)
    argv = exec_args(gc_slot(nd, 1), 0, frame)
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, argv)
    rinfo = gc_slot(vs_get(base + 1), 2)
    start = int_of(gcv_nth(rinfo, 1))
    n = int_of(gcv_nth(rinfo, 2))
    do i = 0, n - 1
       call frame_set(vs_get(base + 2), start + i, gcv_nth(vs_get(base + 3), i))
    end do
    out = gc_obj(OBJ_RECUR, [gc_nil()], [vs_get(base + 1)])
    call vs_leave(base)
  end function exec_recur

  recursive function exec_try(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, exc, catches, cl, fin
    integer :: base, i, n
    logical :: caught

    out = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, frame)
    out = exec(gcv_nth(gc_slot(nd, 1), 0), frame)
    if (has_error) then
       exc = thrown_value()
       if (exc%tag == GCT_NIL) exc = error_value(gce_error(), [vs_get(base + 1)])
       call vs_set(base + 3, exc)
       catches = gc_slot(vs_get(base + 1), 2)
       n = gcv_count(catches)
       caught = .false.
       do i = 0, n - 1
          cl = gcv_nth(catches, i)
          call vs_set(base + 4, cl)
          if (.not. catch_matches(gcv_nth(vs_get(base + 4), 0), vs_get(base + 3), gc_nil())) cycle
          call gce_clear_error()
          call frame_set(vs_get(base + 2), int_of(gcv_nth(vs_get(base + 4), 1)), vs_get(base + 3))
          out = exec(gcv_nth(vs_get(base + 4), 2), vs_get(base + 2))
          caught = .true.
          exit
       end do
    end if
    fin = gcv_nth(gc_slot(vs_get(base + 1), 1), 1)
    if (gc_kind(fin) == OBJ_AST) then
       block
         logical :: had
         type(gc_value) :: saved_exc, fv
         character(len=:), allocatable :: saved_msg
         had = has_error
         saved_msg = last_error
         saved_exc = thrown_value()
         call vs_set(base + 5, saved_exc)
         call gce_clear_error()
         fv = exec(fin, vs_get(base + 2))
         if (.not. has_error .and. had) then
            has_error = .true.
            last_error = saved_msg
            call set_thrown(vs_get(base + 5))
         end if
       end block
    end if
    call vs_leave(base)
  end function exec_try

  ! case*: the same table walk eval_case does, over nodes.
  recursive function exec_case(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, val, info, tt, entry
    integer :: base, shift, mask, h
    logical :: hit

    out = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, frame)
    val = exec(gcv_nth(gc_slot(nd, 1), 0), frame)
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, val)
    info = gc_slot(vs_get(base + 1), 3)
    shift = int_of(gcv_nth(info, 0))
    mask = int_of(gcv_nth(info, 1))
    tt = gcv_nth(info, 2)
    if (tt%tag == GCT_KEY .and. gc_ref_is(tt%ref, "int")) then
       h = ival_of(vs_get(base + 3))
    else
       h = gc_hash(vs_get(base + 3))
    end if
    if (mask /= 0) h = iand(shifta(h, shift), mask)
    entry = strip_meta(gca_get(gc_slot(vs_get(base + 1), 2), gc_int(h)))
    call vs_set(base + 4, entry)
    hit = .false.
    if (gcv_is(vs_get(base + 4))) then
       if (gcv_count(vs_get(base + 4)) == 2) then
          if (in_skip(gcv_nth(info, 3), h)) then
             hit = .true.
          else
             hit = deep_equal(vs_get(base + 3), gcv_nth(vs_get(base + 4), 0), [vs_get(base + 3), vs_get(base + 4)])
          end if
       end if
    end if
    if (hit) then
       out = exec(gcv_nth(vs_get(base + 4), 1), vs_get(base + 2))
    else
       out = exec(gcv_nth(gc_slot(vs_get(base + 1), 1), 1), vs_get(base + 2))
    end if
    call vs_leave(base)
  end function exec_case

  ! deftype*/reify*/proxy: the type from its spec, each method a closure
  ! over the current frame. i2 = 0 registers the type and answers it;
  ! 1 answers a fresh instance and registers nothing.
  recursive function exec_deftype(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, spec, methods, names, fns, fnv, ty
    integer :: base, i, n

    out = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, frame)
    spec = gc_slot(nd, 2)
    call vs_set(base + 3, spec)
    methods = gca_empty([vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_set(base + 4, methods)
    names = gcv_nth(spec, 3)
    fns = gcv_nth(spec, 4)
    n = gcv_count(names)
    do i = 0, n - 1
       fnv = exec(gcv_nth(gcv_nth(vs_get(base + 3), 4), i), vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       call vs_set(base + 5, fnv)
       methods = gca_assoc(vs_get(base + 4), gcv_nth(gcv_nth(vs_get(base + 3), 3), i), vs_get(base + 5), &
            [vs_get(base + 3), vs_get(base + 4), vs_get(base + 5)])
       call vs_set(base + 4, methods)
    end do
    ty = gc_obj(OBJ_TYPE, [gcv_nth(vs_get(base + 3), 0), gcv_nth(vs_get(base + 3), 1), &
         vs_get(base + 4), gcv_nth(vs_get(base + 3), 2)], [vs_get(base + 3), vs_get(base + 4)])
    call vs_set(base + 5, ty)
    if (gc_i2(nd) == 0) then
       call register_type(vs_get(base + 5))
       out = vs_get(base + 5)
    else
       out = gc_obj(OBJ_INST, [vs_get(base + 5), gcv_empty([vs_get(base + 5)]), gc_nil()], [vs_get(base + 5)])
    end if
    call vs_leave(base)
  end function exec_deftype

  ! (. target member args): a native instance member on anything but a
  ! deftype instance is called directly; everything else is handed to
  ! eval_dot with its parts evaluated and quoted.
  recursive function exec_dot(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, kids, tv, argv, native, form, m, q
    integer :: base, from
    logical :: is_call

    out = gc_nil()
    base = vs_enter(6)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, frame)
    kids = gc_slot(nd, 1)
    is_call = (gc_i2(nd) == 1)
    if (tag_of(gc_slot(nd, 3)) == GCT_SYM) then
       ! class target: unevaluated symbol, children are all arguments
       tv = gc_slot(nd, 3)
       from = 0
    else
       tv = exec(gcv_nth(kids, 0), frame)
       if (has_error) then
          call vs_leave(base)
          return
       end if
       from = 1
    end if
    call vs_set(base + 3, tv)
    argv = exec_args(gc_slot(vs_get(base + 1), 1), from, vs_get(base + 2))
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 4, argv)

    native = gc_slot(vs_get(base + 1), 3)
    if (from == 1 .and. gc_kind(native) == OBJ_BUILTIN .and. &
         gc_kind(strip_meta(vs_get(base + 3))) /= OBJ_INST .and. &
         .not. gcn_is_var(strip_meta(vs_get(base + 3)))) then
       ! (target args...) through the native
       q = gcv_empty([vs_get(base + 3), vs_get(base + 4)])
       call vs_set(base + 5, q)
       q = gcv_conj(vs_get(base + 5), vs_get(base + 3), [vs_get(base + 4)])
       call vs_set(base + 5, q)
       q = concat_vecs(vs_get(base + 5), vs_get(base + 4), [vs_get(base + 3)])
       call vs_set(base + 5, q)
       out = apply(native, vs_get(base + 5))
       call vs_leave(base)
       return
    end if

    ! the bridge: (target' member) or (target' (member args'...))
    if (is_call) then
       m = quoted_list(vs_get(base + 4), [vs_get(base + 3)])
       call vs_set(base + 5, m)
       m = gcl_cons(gc_slot(vs_get(base + 1), 2), vs_get(base + 5), [vs_get(base + 3), vs_get(base + 5)])
       call vs_set(base + 5, m)
       form = gcl_cons(vs_get(base + 5), gcl_empty([vs_get(base + 3), vs_get(base + 5)]), [vs_get(base + 3), vs_get(base + 5)])
    else
       form = gcl_cons(gc_slot(vs_get(base + 1), 2), gcl_empty([vs_get(base + 3)]), [vs_get(base + 3)])
    end if
    call vs_set(base + 5, form)
    if (from == 1) then
       q = quoted(vs_get(base + 3), [vs_get(base + 5)])
    else
       q = vs_get(base + 3)
    end if
    call vs_set(base + 6, q)
    form = gcl_cons(vs_get(base + 6), vs_get(base + 5), [vs_get(base + 5), vs_get(base + 6)])
    call vs_set(base + 5, form)
    out = eval_dot(vs_get(base + 5), gc_nil())
    call vs_leave(base)
  end function exec_dot

  recursive function exec_setbang(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, tgt, val
    integer :: base
    out = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, frame)
    select case (gc_i2(nd))
    case (0)
       val = exec(gcv_nth(gc_slot(nd, 1), 0), frame)
       if (.not. has_error) then
          call gc_set_slot(gc_slot(vs_get(base + 1), 2), 1, val)
          out = val
       end if
    case (2)
       ! (set! (.__methodImplCache f) cache) -- the one host field with
       ! storage, in the closure slot a fn does not otherwise use.
       tgt = strip_meta(exec(gcv_nth(gc_slot(nd, 1), 0), frame))
       if (.not. has_error) then
          call vs_set(base + 3, tgt)
          val = exec(gcv_nth(gc_slot(vs_get(base + 1), 1), 1), vs_get(base + 2))
          if (.not. has_error) then
             if (gc_kind(vs_get(base + 3)) == OBJ_CLOSURE) call gc_set_slot(vs_get(base + 3), 5, val)
             out = val
          end if
       end if
    case (3)
       ! Class/field: the value, discarded
       val = exec(gcv_nth(gc_slot(nd, 1), 0), frame)
       if (.not. has_error) out = val
    case default
       ! any other host field: the write is discarded, the value returned
       tgt = exec(gcv_nth(gc_slot(nd, 1), 0), frame)
       if (.not. has_error) then
          val = exec(gcv_nth(gc_slot(vs_get(base + 1), 1), 1), vs_get(base + 2))
          if (.not. has_error) out = val
       end if
    end select
    call vs_leave(base)
  end function exec_setbang

  ! (new user.Name f1 f2) with the arguments already evaluated: the
  ! tail of construct_type, including defrecord's short constructors.
  function construct_type_vals(ty, argv) result(out)
    type(gc_value), intent(in) :: ty, argv
    type(gc_value) :: out, tmp
    character(len=24) :: want, got
    integer :: base, nf, na, drops

    out = gc_nil()
    base = vs_enter(2)
    call vs_set(base + 1, ty)
    call vs_set(base + 2, argv)
    nf = gcv_count(gc_slot(vs_get(base + 1), 2))
    na = gcv_count(vs_get(base + 2))
    drops = alt_ctor_drops(gc_slot(vs_get(base + 1), 2))
    if (na /= nf) then
       if (drops > 0 .and. (na == nf - drops .or. na == nf - 2)) then
          tmp = pad_record_fields(vs_get(base + 2), gc_slot(vs_get(base + 1), 2))
          call vs_set(base + 2, tmp)
       else
          write(want, '(I0)') nf
          write(got, '(I0)') na
          call fail(class_text(vs_get(base + 1)) // " takes " // trim(want) // " fields, given " // trim(got))
          call vs_leave(base)
          return
       end if
    end if
    out = gc_obj(OBJ_INST, [vs_get(base + 1), vs_get(base + 2), gc_nil()], [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function construct_type_vals
