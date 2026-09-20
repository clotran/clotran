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
    argv = gcv_build(gcv_count(kids) - from, [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, argv)
    do i = from, gcv_count(vs_get(base + 1)) - 1
       v = exec(gcv_nth(vs_get(base + 1), i), vs_get(base + 2))
       if (has_error) exit
       argv = gcv_put(vs_get(base + 3), i - from, v, [vs_get(base + 1), vs_get(base + 2), v])
       call vs_set(base + 3, argv)
    end do
    argv = vs_get(base + 3)
    call vs_leave(base)
  end function exec_args

  ! --- closures ------------------------------------------------------

  ! A closure over `frame` from a template: the captured slots are
  ! COPIED now. Slot 1 = template, 2 = captures, 5 = name (set by def).
  function make_closure_from(tmpl, frame, roots) result(fn)
    type(gc_value), intent(in) :: tmpl, frame
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: fn, caps, capv
    integer :: base, ncap, i
    if (trace_macros == 1 .and. int_of(gcv_nth(tmpl, 3)) > 64) &
         write(0, '(A,I0,A,A)') "wide frame: ", int_of(gcv_nth(tmpl, 3)), " slots for ", gcp_str(gcv_nth(tmpl, 0), .false.)
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

  ! Calls a closure from outside the loop -- a native, a multimethod.
  ! The body runs in a nested run; a call the loop itself makes does
  ! not come here (see run, N_CALL).
  recursive function invoke_closure(fn, argv) result(out)
    type(gc_value), intent(in) :: fn, argv
    type(gc_value) :: out, frame, body
    integer :: base
    logical :: ok
    out = gc_nil()
    base = vs_enter(1)
    call vs_set(base + 1, fn)
    call push_frame(fn, pending_site)
    pending_site = 0
    ok = bind_closure(vs_get(base + 1), argv, frame, body)
    if (ok) then
       out = run(body, frame, ior(KF_FNBODY, KF_RESTART), body)
    else
       call pop_frame()
    end if
    call vs_leave(base)
  end function invoke_closure

  ! The captured values and the fn's own name into a frame that already
  ! holds the arguments. No allocation.
  subroutine bind_captures(fn, frame)
    type(gc_value), intent(in) :: fn, frame
    type(gc_value) :: tmpl, caps, capv
    integer :: i, ncap, self
    tmpl = gc_slot(fn, 1)
    caps = gc_slot(fn, 2)
    capv = gcv_nth(tmpl, 2)
    ncap = gcv_count(capv) / 2
    do i = 0, ncap - 1
       call frame_set(frame, int_of(gcv_nth(capv, 2 * i + 1)), gc_vec_get(caps, i + 1))
    end do
    self = int_of(gcv_nth(tmpl, 4))
    if (self >= 0) call frame_set(frame, self, fn)
  end subroutine bind_captures

  ! The index of the fixed arity taking exactly argc arguments, or -1.
  integer function fixed_arity(fn, argc)
    type(gc_value), intent(in) :: fn
    integer, intent(in) :: argc
    type(gc_value) :: arities, ar
    integer :: i
    fixed_arity = -1
    arities = gcv_nth(gc_slot(fn, 1), 1)
    do i = 0, gcv_count(arities) - 1
       ar = gcv_nth(arities, i)
       if (.not. truthy(gcv_nth(ar, 1)) .and. int_of(gcv_nth(ar, 0)) == argc) then
          fixed_arity = i
          return
       end if
    end do
  end function fixed_arity

  ! Picks the arity, builds the frame and binds the arguments, the
  ! captures and the fn's own name. Answers the frame and the body to
  ! run; false with an error set when no arity fits. `argv` is taken
  ! over: it is rooted here at once and dropped once the frame has it.
  function bind_closure(fn, argv, frame, body) result(ok)
    type(gc_value), intent(in) :: fn, argv
    type(gc_value), intent(out) :: frame, body
    logical :: ok
    type(gc_value) :: tmpl, arities, ar, caps, capv, rest
    integer :: base, argc, i, n, nfixed, start, nslots, ncap, self
    logical :: variadic, found

    ok = .false.
    frame = gc_nil()
    body = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, fn)
    call vs_set(base + 2, argv)
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
    call bind_captures(vs_get(base + 1), vs_get(base + 5))
    frame = vs_get(base + 5)
    body = gcv_nth(vs_get(base + 4), 3)
    ok = .true.
    call vs_leave(base)
  end function bind_closure

  ! --- the executor --------------------------------------------------
  !
  ! `run` is a loop over an explicit continuation stack, not a recursive
  ! walk: one kframe per node being evaluated, its values in a region of
  ! the value stack (so the collector sees them), its progress in `pc`.
  ! A child is evaluated by pushing a frame for it; when that frame
  ! finishes it delivers its value in `val` and the parent's pc says
  ! what to do with it. A node in TAIL position replaces its parent's
  ! frame instead of stacking on it, so a call in tail position does not
  ! grow the stack -- the Fortran stack no longer bounds recursion
  ! (DEVIATIONS 7), and a suspended context is data (PLAN stage 2).
  !
  ! What the loop handles itself: constants, locals, Vars, if, do, let*
  ! and loop*, case*, calls, recur, try/catch/finally, fn and lazy-seq.
  ! Everything else still goes through the helpers below, which call
  ! exec and therefore nest a run on the Fortran stack; that nesting is
  ! shallow (a def's value, a throw's argument, a deftype's methods) and
  ! bounded by ev_limit as before. A native that calls back into
  ! Clojure -- forcing a lazy seq, a multimethod's dispatch -- nests the
  ! same way. Those are the pinned frames Loom has too.

  subroutine k_push(nd, frame, flags, restart)
    type(gc_value), intent(in) :: nd, frame, restart
    integer, intent(in) :: flags
    type(kframe), allocatable :: bigger(:)
    integer :: n, b
    if (.not. allocated(kst)) allocate(kst(1024))
    if (ksp >= size(kst)) then
       n = size(kst)
       allocate(bigger(2 * n))
       bigger(1:n) = kst(1:n)
       call move_alloc(bigger, kst)
    end if
    if (k_limit == 0) call read_frame_limit()
    if (ksp >= k_limit) then
       call fail("stack overflow")
       return
    end if
    b = vs_enter(K_SLOTS)
    ksp = ksp + 1
    kst(ksp)%base = b
    kst(ksp)%pc = 0
    kst(ksp)%i = 0
    kst(ksp)%flags = flags
    kst(ksp)%nfr = 0
    kst(ksp)%mode = 0
    if (iand(flags, KF_FNBODY) /= 0) kst(ksp)%nfr = 1
    call vs_set(b + 1, nd)
    call vs_set(b + 2, frame)
    call vs_set(b + 5, restart)
    gce_evals = gce_evals + 1
  end subroutine k_push

  ! The top frame becomes `nd`, keeping its locals, flags and restart
  ! point: a child in tail position.
  subroutine k_tail(nd)
    type(gc_value), intent(in) :: nd
    integer :: b
    b = kst(ksp)%base
    call vs_set(b + 1, nd)
    call vs_set(b + 3, gc_nil())
    call vs_set(b + 4, gc_nil())
    kst(ksp)%pc = 0
    kst(ksp)%i = 0
    kst(ksp)%mode = 0
    gce_evals = gce_evals + 1
  end subroutine k_tail

  ! Pops the top frame, delivering `val` to the one below. A restart
  ! point that received the recur marker runs its body again instead;
  ! a fn body's frame leaves the call stack on the way out.
  subroutine k_finish(val)
    type(gc_value), intent(inout) :: val
    integer :: b
    b = kst(ksp)%base
    if (iand(kst(ksp)%flags, KF_RESTART) /= 0 .and. gc_kind(val) == OBJ_RECUR) then
       call vs_set(b + 1, vs_get(b + 5))
       call vs_set(b + 3, gc_nil())
       call vs_set(b + 4, gc_nil())
       kst(ksp)%pc = 0
       kst(ksp)%i = 0
       val = gc_nil()
       return
    end if
    do while (kst(ksp)%nfr > 0)
       call pop_frame()
       kst(ksp)%nfr = kst(ksp)%nfr - 1
    end do
    call vs_leave(b)
    ksp = ksp - 1
  end subroutine k_finish

  ! An error is set: pop frames down to `kbot`, giving each try its
  ! chance. Returns with has_error false and a catch or finally body
  ! pushed, or with has_error true and the stack at kbot.
  subroutine k_unwind(kbot)
    integer, intent(in) :: kbot
    type(gc_value) :: nd, exc, catches, cl, fin
    integer :: b, i, n
    do while (ksp > kbot)
       b = kst(ksp)%base
       nd = vs_get(b + 1)
       call note_position(nd)
       if (gc_i1(nd) == N_TRY .and. (kst(ksp)%pc == 1 .or. kst(ksp)%pc == 3)) then
          exc = thrown_value()
          if (exc%tag == GCT_NIL) exc = error_value(gce_error(), [nd])
          call vs_set(b + 3, exc)
          if (kst(ksp)%pc == 1) then
             catches = gc_slot(nd, 2)
             n = gcv_count(catches)
             do i = 0, n - 1
                cl = gcv_nth(catches, i)
                call vs_set(b + 4, cl)
                if (.not. catch_matches(gcv_nth(vs_get(b + 4), 0), vs_get(b + 3), gc_nil())) cycle
                call gce_clear_error()
                call frame_set(vs_get(b + 2), int_of(gcv_nth(vs_get(b + 4), 1)), vs_get(b + 3))
                kst(ksp)%pc = 3
                call k_push(gcv_nth(vs_get(b + 4), 2), vs_get(b + 2), 0, gc_nil())
                return
             end do
          end if
          ! not caught here: a finally still runs, then the error goes on
          fin = gcv_nth(gc_slot(vs_get(b + 1), 1), 1)
          if (gc_kind(fin) == OBJ_AST) then
             kst(ksp)%msg = last_error
             call gce_clear_error()
             kst(ksp)%pc = 4
             call k_push(fin, vs_get(b + 2), 0, gc_nil())
             return
          end if
       end if
       do while (kst(ksp)%nfr > 0)
          call pop_frame()
          kst(ksp)%nfr = kst(ksp)%nfr - 1
       end do
       call vs_leave(b)
       ksp = ksp - 1
    end do
  end subroutine k_unwind

  ! The frame limit: how many nodes may be pending at once. Not the
  ! Fortran stack -- that is ev_limit, for the nesting natives cause.
  subroutine read_frame_limit()
    character(len=16) :: buf
    integer :: st, n
    k_limit = 200000
    call get_environment_variable("CLOTRAN_MAX_FRAMES", buf)
    if (len_trim(buf) > 0) then
       read(buf, *, iostat=st) n
       if (st == 0 .and. n > 0) k_limit = n
    end if
  end subroutine read_frame_limit

  recursive function exec(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out
    out = run(nd, frame, 0, gc_nil())
  end function exec

  recursive function run(nd0, frame0, flags0, restart0) result(out)
    type(gc_value), intent(in) :: nd0, frame0, restart0
    integer, intent(in) :: flags0
    type(gc_value) :: out, nd, kids, val, v, fnv, newframe, body
    integer :: kbot, vbase, kind, n, b, site
    logical :: ok

    out = gc_nil()
    if (has_error) return
    if (ev_limit == 0) call read_depth_limit()
    ev_depth = ev_depth + 1
    if (ev_depth > ev_limit) then
       call fail("stack overflow")
       ev_depth = ev_depth - 1
       return
    end if
    vbase = vs_enter(1)
    kbot = ksp
    val = gc_nil()
    call k_push(nd0, frame0, flags0, restart0)

    do
       if (has_error) then
          call k_unwind(kbot)
          if (has_error) exit
          val = gc_nil()
          call vs_set(vbase + 1, val)
       end if
       if (ksp == kbot) exit
       b = kst(ksp)%base
       nd = vs_get(b + 1)
       kind = gc_i1(nd)
       kids = gc_slot(nd, 1)

       select case (kind)
       case (N_CONST)
          val = gc_slot(nd, 2)
          call k_finish(val)
       case (N_LOCAL)
          val = frame_get(vs_get(b + 2), gc_i2(nd))
          if (tag_of(gc_slot(nd, 3)) == GCT_BOOL) call frame_set(vs_get(b + 2), gc_i2(nd), gc_nil())
          call k_finish(val)
       case (N_VAR)
          val = gcn_var_value(gc_slot(nd, 2))
          call k_finish(val)
       case (N_IF)
          if (kst(ksp)%pc == 0) then
             kst(ksp)%pc = 1
             call k_push(gcv_nth(kids, 0), vs_get(b + 2), 0, gc_nil())
          else if (truthy(val)) then
             call k_tail(gcv_nth(kids, 1))
          else if (gcv_count(kids) > 2) then
             call k_tail(gcv_nth(kids, 2))
          else
             val = gc_nil()
             call k_finish(val)
          end if
       case (N_DO)
          n = gcv_count(kids)
          if (n == 0) then
             val = gc_nil()
             call k_finish(val)
          else if (kst(ksp)%i < n - 1) then
             kst(ksp)%i = kst(ksp)%i + 1
             call k_push(gcv_nth(kids, kst(ksp)%i - 1), vs_get(b + 2), 0, gc_nil())
          else
             call k_tail(gcv_nth(kids, n - 1))
          end if
       case (N_CALL)
          select case (kst(ksp)%pc)
          case (0)
             kst(ksp)%pc = 1
             call k_push(gcv_nth(kids, 0), vs_get(b + 2), 0, gc_nil())
          case (1)
             ! The callee is known before its arguments are: a closure
             ! with a fixed arity of the right count gets its FRAME now
             ! and the arguments land in it (mode 2); anything else gets
             ! a one-node argument vector (mode 1). No vector is copied
             ! per argument either way.
             fnv = strip_meta(val)
             if (gcn_is_var(fnv)) fnv = gcn_var_value(fnv)
             call vs_set(b + 3, fnv)
             n = gcv_count(kids) - 1
             kst(ksp)%mode = 1
             if (is_node_closure(vs_get(b + 3))) then
                kst(ksp)%aux2 = fixed_arity(vs_get(b + 3), n)
                if (kst(ksp)%aux2 >= 0) then
                   kst(ksp)%mode = 2
                   kst(ksp)%aux = int_of(gcv_nth(gcv_nth(gcv_nth(gc_slot(vs_get(b + 3), 1), 1), kst(ksp)%aux2), 2))
                   call vs_set(b + 4, new_frame(int_of(gcv_nth(gc_slot(vs_get(b + 3), 1), 3)), [vs_get(b + 1)]))
                end if
             end if
             if (kst(ksp)%mode == 1) call vs_set(b + 4, gcv_build(n, [vs_get(b + 1)]))
             kst(ksp)%i = 1
             kst(ksp)%pc = 2
          case (2)
             if (kst(ksp)%i < gcv_count(kids)) then
                kst(ksp)%pc = 3
                call k_push(gcv_nth(kids, kst(ksp)%i), vs_get(b + 2), 0, gc_nil())
             else
                kst(ksp)%pc = 4
             end if
          case (3)
             if (kst(ksp)%mode == 2) then
                call frame_set(vs_get(b + 4), kst(ksp)%aux + kst(ksp)%i - 1, val)
             else
                call vs_set(b + 4, gcv_put(vs_get(b + 4), kst(ksp)%i - 1, val, [vs_get(b + 1)]))
             end if
             kst(ksp)%i = kst(ksp)%i + 1
             kst(ksp)%pc = 2
          case (4)
             ! where this call is, for the call stack
             v = gc_slot(nd, 4)
             site = 0
             if (v%tag == GCT_INT) site = int(v%ival, kind=4)
             fnv = vs_get(b + 3)
             if (kst(ksp)%mode == 2) then
                ! the frame holds the arguments; captures and the name
                ! complete it, and this frame becomes the body's
                call push_frame(fnv, site)
                if (has_error) cycle
                kst(ksp)%nfr = kst(ksp)%nfr + 1
                call bind_captures(vs_get(b + 3), vs_get(b + 4))
                body = gcv_nth(gcv_nth(gcv_nth(gc_slot(vs_get(b + 3), 1), 1), kst(ksp)%aux2), 3)
                call vs_set(b + 2, vs_get(b + 4))
                call vs_set(b + 5, body)
                kst(ksp)%flags = ior(kst(ksp)%flags, KF_RESTART)
                call k_tail(body)
                cycle
             end if
             ! The argument vector is handed over, not kept (see
             ! bind_closure / apply): nothing allocates between this nil
             ! and the callee rooting it.
             v = vs_get(b + 4)
             call vs_set(b + 4, gc_nil())
             if (is_node_closure(fnv)) then
                ! A tail call: this frame becomes the callee's body. The
                ! caller stays on the call stack, as it would on the JVM,
                ! so a trace names every call and a runaway tail recursion
                ! overflows at k_limit rather than running forever.
                call push_frame(fnv, site)
                if (has_error) cycle
                kst(ksp)%nfr = kst(ksp)%nfr + 1
                call vs_set(b + 3, fnv)
                ok = bind_closure(vs_get(b + 3), v, newframe, body)
                if (ok) then
                   call vs_set(b + 2, newframe)
                   call vs_set(b + 5, body)
                   kst(ksp)%flags = ior(kst(ksp)%flags, KF_RESTART)
                   call k_tail(body)
                end if
             else
                pending_site = site
                val = apply(vs_get(b + 3), v)
                call k_finish(val)
             end if
          end select
       case (N_LET, N_LOOP)
          n = gc_i2(nd)
          if (kst(ksp)%pc == 1) then
             call frame_set(vs_get(b + 2), int_of(gc_slot(nd, 2)) + kst(ksp)%i, val)
             kst(ksp)%i = kst(ksp)%i + 1
             kst(ksp)%pc = 0
          else if (kst(ksp)%i < n) then
             kst(ksp)%pc = 1
             call k_push(gcv_nth(kids, kst(ksp)%i), vs_get(b + 2), 0, gc_nil())
          else
             if (kind == N_LOOP) then
                call vs_set(b + 5, gcv_nth(kids, n))
                kst(ksp)%flags = ior(kst(ksp)%flags, KF_RESTART)
             end if
             call k_tail(gcv_nth(kids, n))
          end if
       case (N_CASE)
          if (kst(ksp)%pc == 0) then
             kst(ksp)%pc = 1
             call k_push(gcv_nth(kids, 0), vs_get(b + 2), 0, gc_nil())
          else
             call vs_set(b + 3, val)
             v = case_branch(vs_get(b + 1), vs_get(b + 3))
             call k_tail(v)
          end if
       case (N_TRY)
          select case (kst(ksp)%pc)
          case (0)
             kst(ksp)%pc = 1
             call k_push(gcv_nth(kids, 0), vs_get(b + 2), 0, gc_nil())
          case (1, 3)
             ! the body, or a catch, finished normally
             call vs_set(b + 3, val)
             v = gcv_nth(kids, 1)
             if (gc_kind(v) == OBJ_AST) then
                kst(ksp)%pc = 2
                call k_push(v, vs_get(b + 2), 0, gc_nil())
             else
                call k_finish(val)
             end if
          case (2)
             val = vs_get(b + 3)
             call k_finish(val)
          case (4)
             ! the finally ran after an uncaught error: the error goes on
             has_error = .true.
             last_error = kst(ksp)%msg
             call set_thrown(vs_get(b + 3))
             kst(ksp)%pc = 5
          case default
             call k_finish(val)
          end select
       case (N_VECTOR, N_MAP, N_SET)
          ! children collected into slot 4, one frame each, then built
          select case (kst(ksp)%pc)
          case (0)
             call vs_set(b + 4, gcv_build(gcv_count(kids), [vs_get(b + 1)]))
             kst(ksp)%i = 0
             kst(ksp)%pc = 2
          case (2)
             if (kst(ksp)%i < gcv_count(kids)) then
                kst(ksp)%pc = 3
                call k_push(gcv_nth(kids, kst(ksp)%i), vs_get(b + 2), 0, gc_nil())
             else
                select case (kind)
                case (N_VECTOR); val = vs_get(b + 4)
                case (N_SET);    val = vec_to_set(vs_get(b + 4), [vs_get(b + 1)])
                case default;    val = vec_to_map(vs_get(b + 4), [vs_get(b + 1)])
                end select
                call k_finish(val)
             end if
          case (3)
             call vs_set(b + 4, gcv_put(vs_get(b + 4), kst(ksp)%i, val, [vs_get(b + 1)]))
             kst(ksp)%i = kst(ksp)%i + 1
             kst(ksp)%pc = 2
          end select
       case (N_RECUR)
          val = exec_recur(nd, vs_get(b + 2))
          if (.not. has_error) call k_finish(val)
       case (N_THROW)
          v = exec(gcv_nth(kids, 0), vs_get(b + 2))
          if (.not. has_error) then
             call set_thrown(v)
             has_error = .true.
             last_error = gcp_str(v, .true.)
             call capture_trace()
          end if
       case (N_FN)
          val = make_closure_from(gc_slot(nd, 2), vs_get(b + 2), [vs_get(b + 1)])
          call k_finish(val)
       case (N_LAZY)
          v = make_closure_from(gc_slot(nd, 2), vs_get(b + 2), [vs_get(b + 1)])
          call vs_set(b + 3, v)
          val = gc_obj(OBJ_LAZY, [vs_get(b + 3), gc_nil(), gc_nil()], [vs_get(b + 3)])
          call gc_set_i1(val, LAZY_PENDING)
          call k_finish(val)
       case (N_TOP)
          v = new_frame(gc_i2(nd), [vs_get(b + 1)])
          call vs_set(b + 2, v)
          call k_tail(gc_slot(vs_get(b + 1), 2))
       case default
          val = exec_other(nd, vs_get(b + 2))
          if (.not. has_error) call k_finish(val)
       end select
       call vs_set(vbase + 1, val)
    end do

    out = val
    if (has_error) out = gc_nil()
    call vs_leave(vbase)
    ev_depth = ev_depth - 1
  end function run

  ! The node kinds the loop leaves to a helper. Each helper evaluates
  ! its children through exec, nesting a run.
  recursive function exec_other(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, kids, v, fnv
    integer :: base, kind

    out = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, frame)
    kind = gc_i1(nd)
    kids = gc_slot(nd, 1)
    select case (kind)
    case (N_DEF)
       out = exec_def(nd, frame)
    case (N_LETFN)
       out = exec_letfn(nd, frame)
    case (N_DEFTYPE)
       out = exec_deftype(nd, frame)
    case (N_DOT)
       out = exec_dot(nd, frame)
    case (N_NEW)
       v = exec_args(kids, 0, frame)
       if (.not. has_error) then
          call vs_set(base + 3, v)
          out = eval_new(sym_text(gc_slot(vs_get(base + 1), 2)), vs_get(base + 3))
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
  end function exec_other

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

  ! Alternating keys and values, as a map literal's children come.
  function vec_to_map(vals, roots) result(out)
    type(gc_value), intent(in) :: vals
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, mp
    integer :: base, i
    base = vs_enter(2)
    call vs_set(base + 1, vals)
    mp = gca_empty([roots, vs_get(base + 1)])
    call vs_set(base + 2, mp)
    do i = 0, gcv_count(vals) - 1, 2
       mp = gca_assoc(vs_get(base + 2), gcv_nth(vs_get(base + 1), i), gcv_nth(vs_get(base + 1), i + 1), &
            [roots, vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 2, mp)
    end do
    out = vs_get(base + 2)
    call vs_leave(base)
  end function vec_to_map

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
    if (iand(flags, 2) /= 0) call var_set_macro(vs_get(base + 3))
    out = vs_get(base + 3)
    call vs_leave(base)
  end function exec_def


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

  ! case*: the table walk, answering the branch node to run.
  function case_branch(nd, val) result(branch)
    type(gc_value), intent(in) :: nd, val
    type(gc_value) :: branch, info, tt, entry
    integer :: base, shift, mask, h
    logical :: hit

    base = vs_enter(3)
    call vs_set(base + 1, nd)
    call vs_set(base + 2, val)
    info = gc_slot(nd, 3)
    shift = int_of(gcv_nth(info, 0))
    mask = int_of(gcv_nth(info, 1))
    tt = gcv_nth(info, 2)
    if (tt%tag == GCT_KEY .and. gc_ref_is(tt%ref, "int")) then
       h = ival_of(vs_get(base + 2))
    else
       h = gc_hash(vs_get(base + 2))
    end if
    if (mask /= 0) h = iand(shifta(h, shift), mask)
    entry = strip_meta(gca_get(gc_slot(vs_get(base + 1), 2), gc_int(h)))
    call vs_set(base + 3, entry)
    hit = .false.
    if (gcv_is(vs_get(base + 3))) then
       if (gcv_count(vs_get(base + 3)) == 2) then
          if (in_skip(gcv_nth(info, 3), h)) then
             hit = .true.
          else
             hit = deep_equal(vs_get(base + 2), gcv_nth(vs_get(base + 3), 0), [vs_get(base + 2), vs_get(base + 3)])
          end if
       end if
    end if
    if (hit) then
       branch = gcv_nth(vs_get(base + 3), 1)
    else
       branch = gcv_nth(gc_slot(vs_get(base + 1), 1), 1)
    end if
    call vs_leave(base)
  end function case_branch

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
  ! eval_dot with its parts evaluated.
  recursive function exec_dot(nd, frame) result(out)
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, kids, tv, argv, native
    integer :: base, from
    logical :: is_call

    out = gc_nil()
    base = vs_enter(4)
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
       call vs_set(base + 4, cons_vec(vs_get(base + 3), vs_get(base + 4), [vs_get(base + 1)]))
       out = apply(native, vs_get(base + 4))
       call vs_leave(base)
       return
    end if

    out = eval_dot(vs_get(base + 3), sym_text(gc_slot(vs_get(base + 1), 2)), is_call, &
         vs_get(base + 4), from == 0)
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
