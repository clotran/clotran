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

  subroutine sym_text(v, s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable, intent(out) :: s
    type(gc_value) :: t
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    t = strip_meta(v)
    block
       call gc_ref_text(t%ref, s=dlt_1)
       s = dlt_1
    end block
  end subroutine sym_text

  ! A frame of n nil slots: one this thread gave back (give_frame), or a
  ! new one. The calling convention's step 2 (PLAN.md): a frame was
  ! allocated per interpreted call and dropped after it.
  function new_frame(n, roots) result(fr)
    type(gc_stack), pointer :: vst
    integer, intent(in) :: n
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: fr
    vst => gc_my_stack()
    fr = gc_frame_take(vst, n)
    if (fr%tag /= GCT_VEC) fr = gc_vec(max(n, 0), roots)
  end function new_frame

  ! A frame whose call has returned, back for the next call of its size.
  ! Nothing keeps a frame after its call: a closure COPIES what it
  ! captures (make_closure_from), letfn copies again (refresh_captures),
  ! and a break copies each local into a map (take_break).
  subroutine give_frame(fr)
    type(gc_value), intent(in) :: fr
    type(gc_stack), pointer :: vst
    if (fr%tag /= GCT_VEC) return
    vst => gc_my_stack()
    call gc_frame_give(vst, fr)
  end subroutine give_frame

  function frame_get(fr, slot) result(v)
    type(gc_value), intent(in) :: fr
    integer, intent(in) :: slot
    type(gc_value) :: v
    type(gc_stack), pointer :: vst
    if (fr%tag == GCT_SFRAME) then
       ! the stack of the context running the body (flat_run's tctx%stk)
       vst => ctx_self_stack()
       v = vst%vstack(fr%ref + slot + 1)
       return
    end if
    v = gc_vec_get(fr, slot + 1)
  end function frame_get

  ! How many slots a frame has, on the heap or on the stack
  integer function frame_len(fr)
    type(gc_value), intent(in) :: fr
    if (fr%tag == GCT_SFRAME) then
       frame_len = int(fr%ival)
    else
       frame_len = gc_vec_len(fr)
    end if
  end function frame_len

  subroutine frame_set(fr, slot, v)
    type(gc_value), intent(in) :: fr, v
    integer, intent(in) :: slot
    type(gc_stack), pointer :: vst
    if (fr%tag == GCT_SFRAME) then
       ! the stack of the context running the body (flat_run's tctx%stk)
       vst => ctx_self_stack()
       vst%vstack(fr%ref + slot + 1) = v
       return
    end if
    call gc_vec_set(fr, slot + 1, v)
  end subroutine frame_set

  ! Evaluates every child into a persistent vector of values.
  recursive function exec_args(kids, from, frame) result(argv)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: kids, frame
    integer, intent(in) :: from
    type(gc_value) :: argv, v
    integer :: base, i
    tctx => ctx_self()
    vst => tctx%stk
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, kids)
    call vs_set(vst, base + 2, frame)
    argv = gcv_build(gcv_count(kids) - from, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, argv)
    do i = from, gcv_count(vs_get(vst, base + 1)) - 1
       v = exec(gcv_nth(vs_get(vst, base + 1), i), vs_get(vst, base + 2))
       if (tctx%has_error) exit
       argv = gcv_put(vs_get(vst, base + 3), i - from, v, [vs_get(vst, base + 1), vs_get(vst, base + 2), v])
       call vs_set(vst, base + 3, argv)
    end do
    argv = vs_get(vst, base + 3)
    call vs_leave(vst, base)
  end function exec_args

  ! --- closures ------------------------------------------------------

  ! A closure over `frame` from a template: the captured slots are
  ! COPIED now. Slot 1 = template, 2 = captures, 5 = name (set by def).
  function make_closure_from(tmpl, frame, roots) result(fn)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: tmpl, frame
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: fn, caps, capv
    integer :: base, ncap, i
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    if (trace_macros == 1 .and. int_of(gcv_nth(tmpl, 3)) > 64) then
       block
          call gcp_str(gcv_nth(tmpl, 0), .false., s=dlt_1)
          write(0, '(A,I0,A,A)') "wide frame: ", int_of(gcv_nth(tmpl, 3)), " slots for ", dlt_1
       end block
    end if
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, tmpl)
    call vs_set(vst, base + 2, frame)
    capv = gcv_nth(tmpl, 2)
    ncap = gcv_count(capv) / 2
    if (ncap <= 2) then
       ! ONE OBJECT (PLAN 26.6): up to two captures in the closure's own
       ! slots 2 and 4 (cap_of); the values are the frame's, rooted there
       block
         type(gc_value) :: c0, c1
         c0 = gc_nil(); c1 = gc_nil()
         if (ncap >= 1) c0 = frame_get(vs_get(vst, base + 2), int_of(gcv_nth(capv, 0)))
         if (ncap >= 2) c1 = frame_get(vs_get(vst, base + 2), int_of(gcv_nth(capv, 2)))
         fn = gc_obj(OBJ_CLOSURE, [vs_get(vst, base + 1), c0, gc_nil(), c1, gc_nil()], roots)
       end block
       call vs_leave(vst, base)
       return
    end if
    ! roots as they are: tmpl and frame are on the stack, and a
    ! [roots, ...] list is a heap temporary on every closure made
    caps = gc_vec(ncap, roots)
    call vs_set(vst, base + 3, caps)
    do i = 0, ncap - 1
       call gc_vec_set(vs_get(vst, base + 3), i + 1, &
            frame_get(vs_get(vst, base + 2), int_of(gcv_nth(gcv_nth(vs_get(vst, base + 1), 2), 2 * i))))
    end do
    fn = gc_obj(OBJ_CLOSURE, [vs_get(vst, base + 1), vs_get(vst, base + 3), gc_nil(), gc_nil(), gc_nil()], roots)
    call vs_leave(vst, base)
  end function make_closure_from

  ! Re-copies a closure's captures from `frame`: letfn's second pass,
  ! after every function of the group exists.
  subroutine refresh_captures(fn, frame)
    type(gc_value), intent(in) :: fn, frame
    type(gc_value) :: tmpl, caps, capv
    integer :: i, ncap
    tmpl = gc_slot(fn, 1)
    capv = gcv_nth(tmpl, 2)
    ncap = gcv_count(capv) / 2
    do i = 0, ncap - 1
       call cap_put(fn, i, ncap, frame_get(frame, int_of(gcv_nth(capv, 2 * i))))
    end do
  end subroutine refresh_captures

  ! Capture i (0-based) of a template closure that has ncap of them:
  ! one or two live in the closure's slots 2 and 4, more in a vector
  ! in slot 2 (make_closure_from)
  function cap_of(fn, i, ncap) result(v)
    type(gc_value), intent(in) :: fn
    integer, intent(in) :: i, ncap
    type(gc_value) :: v
    if (ncap > 2) then
       v = gc_vec_get(gc_slot(fn, 2), i + 1)
    else if (i == 0) then
       v = gc_slot(fn, 2)
    else
       v = gc_slot(fn, 4)
    end if
  end function cap_of

  subroutine cap_put(fn, i, ncap, v)
    type(gc_value), intent(in) :: fn, v
    integer, intent(in) :: i, ncap
    if (ncap > 2) then
       call gc_vec_set(gc_slot(fn, 2), i + 1, v)
    else if (i == 0) then
       call gc_set_slot(fn, 2, v)
    else
       call gc_set_slot(fn, 4, v)
    end if
  end subroutine cap_put

  logical function is_node_closure(fn)
    type(gc_value), intent(in) :: fn
    is_node_closure = .false.
    if (gc_kind(fn) /= OBJ_CLOSURE) return
    is_node_closure = gcv_is(gc_slot(fn, 1)) .and. (gc_kind(gc_slot(fn, 3)) /= OBJ_ENV)
    if (is_node_closure) is_node_closure = (gcv_count(gc_slot(fn, 1)) >= 5)
  end function is_node_closure

  ! The builtin a wrapper fn stands for (analyze.inc wrapper_builtin),
  ! when fn is one and n is its arity; nil otherwise
  function wrapper_of(fn, n) result(wb)
    type(gc_value), intent(in) :: fn
    integer, intent(in) :: n
    type(gc_value) :: wb, tmpl, bs, arities
    integer :: i
    wb = gc_nil()
    ! a pending step stops at every call, core's wrappers included
    if (step_at /= 0) return
    if (gc_kind(fn) /= OBJ_CLOSURE) return
    ! the call table has it, one raw read: the template walk below was
    ! eight gcv_nth a call, on every first/next/seq compiled code made
    block
      type(gc_value) :: ct
      ct = call_table_of(fn)
      if (ct%tag == GCT_VEC) then
         if (n <= ct_int(ct, 4)) then
            if (ct_int(ct, 5 + 4 * n) >= 0) wb = gc_vec_get(ct, 5 + 4 * n + 3)
         end if
         return
      end if
    end block
    if (.not. is_node_closure(fn)) return
    tmpl = gc_slot(fn, 1)
    if (gcv_count(tmpl) < 7) return
    bs = gcv_nth(tmpl, 6)
    if (bs%tag == GCT_NIL) return
    ! the arity with exactly n fixed parameters, if it is a wrapper
    arities = gcv_nth(tmpl, 1)
    do i = 0, gcv_count(arities) - 1
       if (int_of(gcv_nth(gcv_nth(arities, i), 0)) == n .and. .not. truthy(gcv_nth(gcv_nth(arities, i), 1))) then
          wb = gcv_nth(bs, i)
          return
       end if
    end do
  end function wrapper_of

  ! Calls a closure from outside the loop -- a native, a multimethod.
  ! The body runs in a nested run; a call the loop itself makes does
  ! not come here (see run, N_CALL).
  ! restseq, when given, is the REST argument as it is -- a seq apply
  ! did not realise -- with argv holding only the fixed arguments.
  recursive function invoke_closure(fn, argv, restseq) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: fn, argv
    type(gc_value), intent(in), optional :: restseq
    type(gc_value) :: out, frame, body
    integer :: base
    logical :: ok
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, fn)
    call push_frame(tctx, fn, tctx%pending_site)
    tctx%pending_site = 0
    if (present(restseq)) then
       ok = bind_closure(vs_get(vst, base + 1), argv, frame, body, restseq)
    else
       ok = bind_closure(vs_get(vst, base + 1), argv, frame, body)
    end if
    if (ok) then
       ! rooted here: the body runs on a copy of it on the stack (k_push),
       ! and an unrooted frame collected under the call would go back to
       ! the pool still in use by whatever reused it
       call vs_set(vst, base + 2, frame)
       out = run(body, frame, ior(KF_FNBODY, KF_RESTART), body, vs_get(vst, base + 1))
       call give_frame(vs_get(vst, base + 2))
    else
       call pop_frame(tctx)
    end if
    call vs_leave(vst, base)
  end function invoke_closure

  ! The captured values and the fn's own name into a frame that already
  ! holds the arguments. No allocation.
  subroutine bind_captures(fn, frame)
    type(gc_value), intent(in) :: fn, frame
    type(gc_value) :: tmpl, caps, capv
    integer :: i, ncap, self
    tmpl = gc_slot(fn, 1)
    capv = gcv_nth(tmpl, 2)
    ncap = gcv_count(capv) / 2
    do i = 0, ncap - 1
       call frame_set(frame, int_of(gcv_nth(capv, 2 * i + 1)), cap_of(fn, i, ncap))
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
  ! With restseq, argv is exactly the variadic arity's fixed arguments
  ! and restseq is its rest as it is (RestFn.doInvoke's last argument),
  ! so only the variadic arity can match.
  function bind_closure(fn, argv, frame, body, restseq) result(ok)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: fn, argv
    type(gc_value), intent(out) :: frame, body
    type(gc_value), intent(in), optional :: restseq
    logical :: ok
    type(gc_value) :: tmpl, arities, ar, caps, capv, rest
    integer :: base, argc, i, n, nfixed, start, nslots, ncap, self
    logical :: variadic, found

    vst => gc_my_stack()
    ok = .false.
    frame = gc_nil()
    body = gc_nil()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, fn)
    call vs_set(vst, base + 2, argv)
    ! a fixed arity through the fn's call table (flat.inc): what a
    ! lazy seq's thunk, forced from Fortran, is called by
    if (.not. present(restseq)) then
       call vs_set(vst, base + 3, call_table_of(fn))
       if (tag_of(vs_get(vst, base + 3)) == GCT_VEC) then
          argc = gcv_count(argv)
          if (argc <= ct_int(vs_get(vst, base + 3), 4)) then
             i = 5 + 4 * argc
             start = ct_int(vs_get(vst, base + 3), i)
             if (start >= 0) then
                frame = ct_frame(vs_get(vst, base + 1), vs_get(vst, base + 3), [vs_get(vst, base + 2)])
                call vs_set(vst, base + 5, frame)
                do n = 0, argc - 1
                   call reg_set(vs_get(vst, base + 5), start + n, gcv_nth(vs_get(vst, base + 2), n))
                end do
                body = ct_body(vs_get(vst, base + 3), i)
                frame = vs_get(vst, base + 5)
                ok = .true.
                call vs_leave(vst, base)
                return
             end if
          end if
       end if
    end if
    tmpl = gc_slot(fn, 1)
    call vs_set(vst, base + 3, tmpl)
    arities = gcv_nth(tmpl, 1)
    argc = gcv_count(argv)

    ! An exact fixed arity wins; otherwise the variadic one that fits.
    found = .false.
    n = gcv_count(arities)
    do i = 0, n - 1
       ar = gcv_nth(arities, i)
       nfixed = int_of(gcv_nth(ar, 0))
       variadic = truthy(gcv_nth(ar, 1))
       if (.not. variadic .and. nfixed == argc .and. .not. present(restseq)) then
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
       call raise_arity(argc, vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 4, ar)
    start = int_of(gcv_nth(ar, 2))
    nslots = int_of(gcv_nth(vs_get(vst, base + 3), 3))
    self = int_of(gcv_nth(vs_get(vst, base + 3), 4))

    frame = new_frame(nslots, [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
    call vs_set(vst, base + 5, frame)
    do i = 0, nfixed - 1
       call frame_set(vs_get(vst, base + 5), start + i, gcv_nth(vs_get(vst, base + 2), i))
    end do
    if (variadic .and. present(restseq)) then
       call frame_set(vs_get(vst, base + 5), start + nfixed, restseq)
    else if (variadic) then
       ! nil when nothing is left, not the empty list (if-let asserts it)
       if (argc <= nfixed) then
          call frame_set(vs_get(vst, base + 5), start + nfixed, gc_nil())
       else
          rest = gcl_empty([vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 5)])
          call frame_set(vs_get(vst, base + 5), start + nfixed, rest)
          do i = argc - 1, nfixed, -1
             rest = gcl_cons(gcv_nth(vs_get(vst, base + 2), i), frame_get(vs_get(vst, base + 5), start + nfixed), &
                  [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 5)])
             call frame_set(vs_get(vst, base + 5), start + nfixed, rest)
          end do
       end if
    end if
    call bind_captures(vs_get(vst, base + 1), vs_get(vst, base + 5))
    frame = vs_get(vst, base + 5)
    body = arity_body(vs_get(vst, base + 4))
    ok = .true.
    call vs_leave(vst, base)
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

  ! --- the break protocol --------------------------------------------
  !
  ! A break is the paused state as DATA: why, where, and one entry per
  ! call still on the continuation stack with that call's locals by
  ! name. Nothing here knows about a terminal. `(clotran-break)` takes
  ! one and answers it; an error takes one when CLOTRAN_BREAK=1 or
  ! CLOTRAN_BREAK_FILE is set, and `(clotran-last-break)` reads it back
  ! afterwards, the way *e holds the last exception.
  !
  ! It is taken BEFORE unwinding -- capture_trace runs at the throw,
  ! where every frame is still pending -- because after the unwind the
  ! locals are gone. PLAN.md's debugger protocol is this data plus a
  ! handler that can answer :continue or :eval; the handler is not
  ! here yet, and the shape of the data is meant to not change when it
  ! arrives.

  ! A value as a short string, WITHOUT forcing anything: a break may
  ! be taken while an infinite seq is half built, and printing it is
  ! not worth hanging the process that was already in trouble.
  subroutine safe_str(v, s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable, intent(out) :: s
    character(len=16) :: nbuf
    integer :: k, n
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    k = gc_kind(strip_meta(v))
    n = -1
    select case (k)
    case (OBJ_LAZY, OBJ_CHUNKSEQ)
       if (.not. seq_realised_p(strip_meta(v))) then
          s = "#<unrealised seq>"
          return
       end if
    case (OBJ_VECTOR)
       if (gcv_count(strip_meta(v)) > 32) then
          n = gcv_count(strip_meta(v))
          s = "#<vector "
       end if
    case (OBJ_MAP, OBJ_HAMT)
       if (gca_count(strip_meta(v)) > 32) then
          n = gca_count(strip_meta(v))
          s = "#<map "
       end if
    case (OBJ_SET)
       if (gca_count(gc_slot(strip_meta(v), 1)) > 32) then
          n = gca_count(gc_slot(strip_meta(v), 1))
          s = "#<set "
       end if
    case (OBJ_CONS)
       if (gcl_count(strip_meta(v)) > 32) then
          n = gcl_count(strip_meta(v))
          s = "#<list "
       end if
    end select
    if (n >= 0) then
       write(nbuf, '(I0)') n
       block
          character(len=:), allocatable :: dlw
          dlw = s // trim(nbuf) // ">"
          call move_alloc(dlw, s)
       end block
       return
    end if
    block
       call gcp_str(v, .true., s=dlt_1)
       s = dlt_1
    end block
    if (len(s) > 120) then
       block
          character(len=:), allocatable :: dlw
          dlw = s(1:117) // "..."
          call move_alloc(dlw, s)
       end block
    end if
  end subroutine safe_str

  ! One map per call still pending, innermost first:
  !   {:fn "user/f" :file "x.clj" :line 12 :col 3 :env {x 3, coll [1 2]}}
  ! A frame that is not a fn body -- an `if` waiting on its test -- is
  ! not a call and is skipped. A local already cleared after its last
  ! read reads as nil, here as in clj. Only the slots this frame's
  ! ARITY binds are its locals (arity_slots): one frame serves every
  ! arity, and the others' slots read nil without ever having been
  ! bound, which is not the same thing.
  function break_frames(roots) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, m, fn, nd, env, names, tmpl, nm, pos
    type(gc_value), allocatable :: ks(:), vls(:)
    character(len=:), allocatable :: who, fname, pfname
    integer :: base, i, j, b, line, col, slot, lo, hi, pline, pcol
    logical :: have_pos

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    base = vs_enter(vst, 4)
    out = gcv_empty(roots)
    call vs_set(vst, base + 1, out)
    have_pos = .false.
    do i = tctx%ksp, 1, -1
       b = tctx%kst(i)%base
       nd = vs_get(vst, b + 1)
       ! Where a fn IS: its innermost pending node's position, the one
       ! a trace line shows -- the call it is waiting on, or the break
       ! itself -- rather than its body's, which a macro's expansion
       ! usually has not got. The first node with one, walking down
       ! from the top; reset at each fn frame.
       if (.not. have_pos) then
          pos = gc_slot(nd, 4)
          ! a flat body is where its current call is (flat_run keeps
          ! the site in aux2); just entered, where its tree begins
          if (gc_i1(nd) == N_FLAT) then
             if (tctx%kst(i)%pc /= 0 .and. tctx%kst(i)%aux2 > 0) then
                pos = gc_int(int(tctx%kst(i)%aux2, gc_ip))
             else
                nd = gc_slot(nd, 5)
                pos = gc_slot(nd, 4)
             end if
          end if
          ! a body just entered (a step stops there) is a `do` the
          ! analyser made, with no position of its own: it is where its
          ! first form is
          if (pos%tag /= GCT_INT .and. gc_i1(nd) == N_DO) then
             if (gcv_count(gc_slot(nd, 1)) > 0) pos = gc_slot(gcv_nth(gc_slot(nd, 1), 0), 4)
          end if
          if (pos%tag == GCT_INT) then
             if (pos%ival > 0) then
                call gcr_position_parts(int(pos%ival, kind=4), pfname, pline, pcol)
                have_pos = .true.
             end if
          end if
       end if
       fn = vs_get(vst, b + 7)
       if (gc_kind(fn) /= OBJ_CLOSURE) cycle
       call vs_set(vst, base + 2, fn)
       fname = ""
       line = 0
       col = 0
       if (have_pos) then
          fname = pfname
          line = pline
          col = pcol
       end if
       have_pos = .false.
       who = "fn"
       nm = gc_slot(vs_get(vst, base + 2), 5)
       if (nm%tag == GCT_SYM) then
          block
             call gc_ref_text(nm%ref, s=dlt_1)
             who = dlt_1
          end block
       end if

       env = gca_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 3, env)
       tmpl = gc_slot(vs_get(vst, base + 2), 1)
       if (gcv_count(tmpl) >= 6) then
          names = gcv_nth(tmpl, 5)
          call arity_slots(tmpl, vs_get(vst, b + 5), lo, hi)
          if (gca_is(names)) then
             call gca_entries(names, ks, vls)
             do j = 1, size(ks)
                slot = int_of(ks(j))
                if (slot < lo .or. slot >= hi) then
                   if (slot /= int_of(gcv_nth(tmpl, 4)) .and. .not. captured_slot(tmpl, slot)) cycle
                end if
                if (slot >= 0 .and. slot < frame_len(vs_get(vst, b + 2))) then
                   env = gca_assoc(vs_get(vst, base + 3), vls(j), frame_get(vs_get(vst, b + 2), slot), &
                        [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
                   call vs_set(vst, base + 3, env)
                end if
             end do
          end if
       end if

       m = gca_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
       call vs_set(vst, base + 4, m)
       call brk_put(base + 4, "fn", gc_str(who, [roots, vs_get(vst, base + 4)]), roots, base)
       call brk_put(base + 4, "file", gc_str(fname, [roots, vs_get(vst, base + 4)]), roots, base)
       call brk_put(base + 4, "line", gc_int(int(line, gc_ip)), roots, base)
       call brk_put(base + 4, "col", gc_int(int(col, gc_ip)), roots, base)
       call brk_put(base + 4, "env", vs_get(vst, base + 3), roots, base)
       out = gcv_conj(vs_get(vst, base + 1), vs_get(vst, base + 4), &
            [roots, vs_get(vst, base + 1), vs_get(vst, base + 4)])
       call vs_set(vst, base + 1, out)
    end do
    out = vs_get(vst, base + 1)
    call vs_leave(vst, base)
  end function break_frames

  ! The slot range a frame running `body` binds: parameters and lets
  ! take consecutive slots and the next arity's begin where they end
  ! (analyze_fn), so an arity owns [its first parameter slot, the next
  ! arity's). The fn's own name and its captures, bound for every
  ! arity, lie outside the range and are admitted by name.
  subroutine arity_slots(tmpl, body, lo, hi)
    type(gc_value), intent(in) :: tmpl, body
    integer, intent(out) :: lo, hi
    type(gc_value) :: ars, ar, bd, fl
    integer :: i, n
    ars = gcv_nth(tmpl, 1)
    n = gcv_count(ars)
    lo = 0
    hi = int_of(gcv_nth(tmpl, 3))
    do i = 0, n - 1
       ar = gcv_nth(ars, i)
       bd = gcv_nth(ar, 3)
       ! the body running may be the arity's flat form (flat.inc)
       if (gcv_count(ar) >= 5) then
          fl = gcv_nth(ar, 4)
          if (fl%tag == body%tag .and. fl%ref == body%ref) bd = body
       end if
       if (bd%tag == body%tag .and. bd%ref == body%ref) then
          lo = int_of(gcv_nth(ar, 2))
          if (i + 1 < n) hi = int_of(gcv_nth(gcv_nth(ars, i + 1), 2))
          return
       end if
    end do
  end subroutine arity_slots

  ! Captures are (outer, inner) slot pairs, flattened.
  logical function captured_slot(tmpl, slot)
    type(gc_value), intent(in) :: tmpl
    integer, intent(in) :: slot
    type(gc_value) :: caps
    integer :: k
    captured_slot = .false.
    caps = gcv_nth(tmpl, 2)
    do k = 1, gcv_count(caps) - 1, 2
       if (int_of(gcv_nth(caps, k)) == slot) captured_slot = .true.
    end do
  end function captured_slot

  ! (assoc m :k v) in place on a value-stack slot, so the callers above
  ! stay readable.
  subroutine brk_put(slot, k, v, roots, base)
    type(gc_stack), pointer :: vst
    integer, intent(in) :: slot, base
    character(len=*), intent(in) :: k
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m
    vst => gc_my_stack()
    m = gca_assoc(vs_get(vst, slot), gc_key(k, [roots, vs_get(vst, slot), v]), v, &
         [roots, vs_get(vst, slot), v])
    call vs_set(vst, slot, m)
  end subroutine brk_put

  ! The paused state, stored and answered. `reason` is :error or :break.
  function capture_break(reason) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    character(len=*), intent(in) :: reason
    type(gc_value) :: out, fr
    integer :: base
    tctx => ctx_self()
    vst => tctx%stk
    base = vs_enter(vst, 2)
    fr = break_frames([gc_nil()])
    call vs_set(vst, base + 1, fr)
    out = gca_empty([vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, out)
    call brk_put(base + 2, "reason", gc_key(reason, [vs_get(vst, base + 1), vs_get(vst, base + 2)]), &
         [vs_get(vst, base + 1)], base)
    if (allocated(tctx%last_error)) then
       call brk_put(base + 2, "message", gc_str(tctx%last_error, [vs_get(vst, base + 1), vs_get(vst, base + 2)]), &
            [vs_get(vst, base + 1)], base)
    end if
    call brk_put(base + 2, "frames", vs_get(vst, base + 1), [vs_get(vst, base + 1)], base)
    out = vs_get(vst, base + 2)
    call gc_global_keep(break_root, out)
    call vs_leave(vst, base)
  end function capture_break

  ! The protocol (PLAN.md): the paused state goes to the handler Var,
  ! *clotran-break-handler*, and a command comes back --
  !   :continue | {:continue v} | :step-in | :step-over | :step-out | :abort
  ! -- which decides what the break answers. The handler runs in a
  ! context of its own: the paused stacks, error and trace are parked
  ! untouched while it works, and its frames and errors are its own.
  ! That switch happens INSIDE a native call and is undone before the
  ! call returns, the one safe way to switch under a run in progress
  ! (see gce_ctx_switch).
  !
  ! No handler bound, or a break taken while the handler runs, and the
  ! state itself is the answer: the break is then only a snapshot, which
  ! is what a script and the tests want. One level: the debugger does
  ! not debug itself, and an error inside the handler is not a break.
  !
  ! `reason` is "break", "step" or "error". At an error the throw is
  ! already in progress: every command lets it go on, and a step asked
  ! for there is dropped rather than left to fire at the REPL's next
  ! call. A step counts CALLS, the events this executor has: in = the
  ! next call anywhere; over = the next call this frame's fn or its
  ! callers make, so it walks this body without descending; out = the
  ! next call made once this frame has returned.
  recursive function take_break(reason) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    character(len=*), intent(in) :: reason
    type(gc_value) :: out, h, cmd, argv, thrown
    type(gc_value) :: none(0)
    integer :: base, paused, depth
    logical :: failed
    character(len=:), allocatable :: msg, trc

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    if (in_handler .and. reason /= "break") return
    out = capture_break(reason)
    if (break_mode == 0) call read_break_mode()
    if (break_mode == 2) call dump_break(gc_root_get(break_root))
    h = gc_nil()
    if (gc_root_live(handler_var_root)) h = gcn_var_value(gc_root_get(handler_var_root))
    if (in_handler .or. h%tag == GCT_NIL) return
    ! read here, in the paused context, where a `binding` of it is in force
    call gc_global_keep(handler_fn_root, h)
    depth = tctx%fstack_top

    if (handler_ctx == 0) handler_ctx = gce_ctx_new()
    paused = gce_ctx_current()
    ctxs(handler_ctx)%c%ev_depth = tctx%ev_depth   ! one Fortran stack: the nesting limit counts on
    ! the handler is not a task, whatever it interrupted was
    in_handler = .true.
    call gce_ctx_switch(handler_ctx)
    tctx => ctx_self()   ! the handler's context now: re-read
    vst => tctx%stk
    tctx%cur_task = gc_nil()
    tctx%task_loop_depth = 0
    call gce_clear_error()
    base = vs_enter(vst, 1)
    argv = gcv_build(1, none)
    call vs_set(vst, base + 1, argv)
    argv = gcv_put(vs_get(vst, base + 1), 0, gc_root_get(break_root), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 1, argv)
    cmd = apply(gc_root_get(handler_fn_root), vs_get(vst, base + 1))
    call gc_global_keep(resume_root, cmd)
    failed = tctx%has_error
    thrown = gc_nil()
    if (failed) then
       msg = tctx%last_error
       trc = tctx%last_trace
       thrown = thrown_value()   ! stays rooted: the handler context keeps its slot
    end if
    call vs_leave(vst, base)
    call gce_ctx_switch(paused)
    tctx => ctx_self()   ! the paused context again
    vst => tctx%stk
    in_handler = .false.
    ! back where the break was taken; the error state is as it was

    out = gc_nil()
    if (failed .and. reason /= "error") then
       ! the handler threw: that is the break's answer, thrown here
       tctx%has_error = .true.
       tctx%last_error = msg
       tctx%last_trace = trc
       call set_thrown(thrown)
       return
    end if
    cmd = strip_meta(gc_root_get(resume_root))
    if (cmd%tag == GCT_KEY) then
       if (reason == "error") return
       block
          call gc_ref_text(cmd%ref, s=dlt_1)
       select case (dlt_1)
       case ("step-in")
          step_at = huge(step_at)
       case ("step-over")
          step_at = depth + 1
       case ("step-out")
          step_at = depth
       case ("abort")
          ! set directly, not through fail: an abort is not an error to
          ! take another break on
          tctx%has_error = .true.
          tctx%last_error = "aborted at break"
          tctx%last_trace = ""
       end select
       end block
    else if (gca_is(cmd)) then
       out = gca_get(cmd, gc_key("continue", [cmd]))
    end if
  end function take_break

  ! A step command pending from the last break: stop at the next call
  ! no deeper than step_at. Called once the callee's frame is in place,
  ! so the break shows it at the top with its arguments bound.
  recursive subroutine step_check()
    type(eval_ctx), pointer :: tctx
    type(gc_value) :: v
    tctx => ctx_self()
    if (tctx%fstack_top > step_at) return
    step_at = 0
    v = take_break("step")
  end subroutine step_check

  ! CLOTRAN_BREAK=1 writes each break to stderr; CLOTRAN_BREAK_FILE
  ! writes it to that file as well, appended, for a run that ends
  ! before anyone can ask. Either one turns capture on; without them an
  ! error costs nothing extra.
  subroutine read_break_mode()
    character(len=1024) :: b
    break_mode = 1
    break_stderr = .false.
    call get_environment_variable("CLOTRAN_BREAK", b)
    if (trim(b) == "1") then
       break_mode = 2
       break_stderr = .true.
    end if
    call get_environment_variable("CLOTRAN_BREAK_FILE", b)
    if (len_trim(b) > 0) then
       break_path = trim(b)
       break_mode = 2
    end if
  end subroutine read_break_mode

  subroutine dump_break(m)
    type(gc_value), intent(in) :: m
    integer :: u, st
    if (break_stderr) call write_break(m, 0)
    if (allocated(break_path)) then
       open(newunit=u, file=break_path, position="append", action="write", iostat=st)
       if (st == 0) then
          call write_break(m, u)
          close(u)
       end if
    end if
  end subroutine dump_break

  ! Rendered by hand rather than printed as a map: every value goes
  ! through safe_str, so a dump never forces a seq or writes a
  ! megabyte.
  subroutine write_break(m, u, limit)
    type(gc_value), intent(in) :: m
    integer, intent(in) :: u
    integer, intent(in), optional :: limit   ! frames to show; the rest are counted
    type(gc_value) :: frames, f, env
    type(gc_value), allocatable :: ks(:), vls(:)
    character(len=32) :: nbuf
    character(len=:), allocatable :: where
    integer :: i, j, top
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    block
       call gcp_str(gca_get(m, gc_key("reason", [m])), .true., s=dlt_1)
       call text_of(gca_get(m, gc_key("message", [m])), s=dlt_2)
       write(u, '(A)') "break: " // dlt_1 // " " //  dlt_2
    end block
    frames = gca_get(m, gc_key("frames", [m]))
    top = gcv_count(frames) - 1
    if (present(limit)) top = min(top, limit - 1)
    do i = 0, top
       f = gcv_nth(frames, i)
       write(nbuf, '(I0)') i
       block
          call text_of(gca_get(f, gc_key("file", [f])), s=dlt_1)
          where = dlt_1
       end block
       if (len(where) > 0) where = where // ":"
       block
          call int_text(gca_get(f, gc_key("line", [f])), s=dlt_1)
          call int_text(gca_get(f, gc_key("col", [f])), s=dlt_2)
          where = where // trim(dlt_1) // ":" //  trim(dlt_2)
       end block
       block
          call text_of(gca_get(f, gc_key("fn", [f])), s=dlt_1)
          write(u, '(A)') "  " // trim(nbuf) // " " // dlt_1 // " (" // where // ")"
       end block
       env = gca_get(f, gc_key("env", [f]))
       if (gca_is(env)) then
          call gca_entries(env, ks, vls)
          do j = 1, size(ks)
             block
                call gcp_str(ks(j), .false., s=dlt_1)
                call safe_str(vls(j), s=dlt_2)
                write(u, '(A)') "      " // dlt_1 // " = " // dlt_2
             end block
          end do
       end if
    end do
    if (top < gcv_count(frames) - 1) then
       write(nbuf, '(I0)') gcv_count(frames) - 1 - top
       write(u, '(A)') "  ... " // trim(nbuf) // " more"
    end if
    flush(u)
  end subroutine write_break

  subroutine int_text(v, s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable, intent(out) :: s
    call gc_int_text(int(int(v%ival, kind=4), gc_ip), s)
  end subroutine int_text

  ! The builtins a call may hand a REUSED argument vector: numeric, and
  ! none of them keeps its arguments or calls back into Clojure. That
  ! is the whole condition, and the reason `vector` or `list` can
  ! never be here.
  logical function scalar_builtin(id)
    integer, intent(in) :: id
    select case (id)
    case (B_ADD, B_SUB, B_MUL, B_DIV, B_LT, B_GT, B_LTE, B_GTE, B_NUMEQ, B_EQ, &
         B_INC, B_DEC, B_ZERO, B_POS, B_NEG, B_REM, B_QUOT, B_MAX, B_MIN, B_ABS, B_IDENTICAL)
       scalar_builtin = .true.
    case default
       scalar_builtin = .false.
    end select
  end function scalar_builtin

  ! The scratch vector of n slots (1 or 2), made once.
  function scratch_args(n) result(v)
    type(eval_ctx), pointer :: tctx
    integer, intent(in) :: n
    type(gc_value) :: v
    tctx => ctx_self()
    if (n == 1) then
       if (.not. gc_root_live(tctx%scratch1_root)) call gc_global_keep(tctx%scratch1_root, gcv_build(1, [gc_nil()]))
       v = gc_root_get(tctx%scratch1_root)
    else
       if (.not. gc_root_live(tctx%scratch2_root)) call gc_global_keep(tctx%scratch2_root, gcv_build(2, [gc_nil()]))
       v = gc_root_get(tctx%scratch2_root)
    end if
  end function scratch_args

  ! An empty argument vector, one per context: a thunk's call (a lazy
  ! seq forced) allocated one per cell. Nothing writes into it.
  function no_args() result(v)
    type(eval_ctx), pointer :: tctx
    type(gc_value) :: v
    tctx => ctx_self()
    if (.not. gc_root_live(tctx%noargs_root)) call gc_global_keep(tctx%noargs_root, gcv_build(0, [gc_nil()]))
    v = gc_root_get(tctx%noargs_root)
    if (.not. gcv_is(v)) then
       call gc_global_keep(tctx%noargs_root, gcv_empty([gc_nil()]))
       v = gc_root_get(tctx%noargs_root)
    end if
  end function no_args

  ! The recur marker, one for the whole process.
  function recur_marker() result(v)
    type(eval_ctx), pointer :: tctx
    type(gc_value) :: v
    tctx => ctx_self()
    if (.not. gc_root_live(tctx%recur_root)) call gc_global_keep(tctx%recur_root, gc_obj(OBJ_RECUR, [gc_nil()], [gc_nil()]))
    v = gc_root_get(tctx%recur_root)
  end function recur_marker

  ! `ctx`: the run loop passes its context; a thread-local lookup for
  ! it on every push, tail and finish was a tenth of a step
  subroutine k_push(nd, frame, flags, restart, ctx)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd, frame, restart
    integer, intent(in) :: flags
    type(eval_ctx), pointer, intent(in), optional :: ctx
    type(kframe), allocatable :: bigger(:)
    integer :: n, b, nr, j
    if (present(ctx)) then
       tctx => ctx
    else
       tctx => ctx_self()
    end if
    vst => tctx%stk
    if (.not. allocated(tctx%kst)) allocate(tctx%kst(1024))
    if (tctx%ksp >= size(tctx%kst)) then
       n = size(tctx%kst)
       allocate(bigger(2 * n))
       bigger(1:n) = tctx%kst(1:n)
       call move_alloc(bigger, tctx%kst)
    end if
    if (k_limit == 0) call read_frame_limit()
    if (tctx%ksp >= k_limit) then
       call raise_class("clotran.host.stack_overflow_error", "stack overflow", [gc_value ::])
       return
    end if
    ! A FLAT BODY's registers live on the stack right above its record
    ! (PLAN 26.2): a frame made on the heap is copied there now, and the
    ! record's frame slot names them; they leave with the record. A
    ! top-level form's too: its record is the first a run pushes, below
    ! the run loop's own slot, so its registers go here or nowhere.
    nr = -1
    if (gc_kind(nd) == OBJ_AST) then
       if (gc_i1(nd) == N_TOP) then
          ! a fresh frame of its own, whatever it was handed, as before
          nr = gc_i2(nd)
       else if (gc_i1(nd) == N_FLAT .and. frame%tag == GCT_VEC) then
          nr = gc_vec_len(frame)
       end if
    end if
    if (nr >= 0) then
       b = vs_enter(vst, K_SLOTS + nr)
       if (frame%tag == GCT_VEC .and. gc_i1(nd) == N_FLAT) then
          ! moved, not copied: the heap frame stays rooted by whoever
          ! made it until it goes back to the pool, and must not hold
          ! the arguments -- a seq's head -- while the body runs
          do j = 1, min(nr, gc_vec_len(frame))
             vst%vstack(b + K_SLOTS + j) = gc_vec_get(frame, j)
             vec_store(vec_pool(frame%ref)%off + j - 1) = gc_nil()
          end do
       end if
       tctx%ksp = tctx%ksp + 1
       tctx%kst(tctx%ksp)%base = b
       tctx%kst(tctx%ksp)%pc = 0
       tctx%kst(tctx%ksp)%i = 0
       tctx%kst(tctx%ksp)%flags = flags
       tctx%kst(tctx%ksp)%nfr = 0
       tctx%kst(tctx%ksp)%mode = 0
       if (iand(flags, KF_FNBODY) /= 0) tctx%kst(tctx%ksp)%nfr = 1
       call vs_set(vst, b + 1, nd)
       call vs_set(vst, b + 2, gc_value(GCT_SFRAME, b + K_SLOTS, int(nr, gc_ip)))
       call vs_set(vst, b + 5, restart)
       gce_evals = gce_evals + 1
       return
    end if
    b = vs_enter(vst, K_SLOTS)
    tctx%ksp = tctx%ksp + 1
    tctx%kst(tctx%ksp)%base = b
    tctx%kst(tctx%ksp)%pc = 0
    tctx%kst(tctx%ksp)%i = 0
    tctx%kst(tctx%ksp)%flags = flags
    tctx%kst(tctx%ksp)%nfr = 0
    tctx%kst(tctx%ksp)%mode = 0
    if (iand(flags, KF_FNBODY) /= 0) tctx%kst(tctx%ksp)%nfr = 1
    call vs_set(vst, b + 1, nd)
    call vs_set(vst, b + 2, frame)
    call vs_set(vst, b + 5, restart)
    gce_evals = gce_evals + 1
  end subroutine k_push

  ! The top frame becomes `nd`, keeping its locals, flags and restart
  ! point: a child in tail position.
  subroutine k_tail(nd, ctx)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd
    type(eval_ctx), pointer, intent(in), optional :: ctx
    integer :: b
    if (present(ctx)) then
       tctx => ctx
    else
       tctx => ctx_self()
    end if
    vst => tctx%stk
    b = tctx%kst(tctx%ksp)%base
    call vs_set(vst, b + 1, nd)
    call vs_set(vst, b + 3, gc_nil())
    call vs_set(vst, b + 4, gc_nil())
    call vs_set(vst, b + 6, gc_nil())
    tctx%kst(tctx%ksp)%pc = 0
    tctx%kst(tctx%ksp)%i = 0
    tctx%kst(tctx%ksp)%mode = 0
    gce_evals = gce_evals + 1
  end subroutine k_tail

  ! Pops the top frame, delivering `val` to the one below. A restart
  ! point that received the recur marker runs its body again instead;
  ! a fn body's frame leaves the call stack on the way out.
  subroutine k_finish(val, ctx)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(inout) :: val
    type(eval_ctx), pointer, intent(in), optional :: ctx
    integer :: b
    if (present(ctx)) then
       tctx => ctx
    else
       tctx => ctx_self()
    end if
    vst => tctx%stk
    b = tctx%kst(tctx%ksp)%base
    if (iand(tctx%kst(tctx%ksp)%flags, KF_RESTART) /= 0 .and. gc_kind(val) == OBJ_RECUR) then
       call vs_set(vst, b + 1, vs_get(vst, b + 5))
       call vs_set(vst, b + 3, gc_nil())
       call vs_set(vst, b + 4, gc_nil())
       tctx%kst(tctx%ksp)%pc = 0
       tctx%kst(tctx%ksp)%i = 0
       val = gc_nil()
       return
    end if
    do while (tctx%kst(tctx%ksp)%nfr > 0)
       call pop_frame(tctx)
       tctx%kst(tctx%ksp)%nfr = tctx%kst(tctx%ksp)%nfr - 1
    end do
    call vs_leave(vst, b)
    tctx%ksp = tctx%ksp - 1
  end subroutine k_finish

  ! An error is set: pop frames down to `kbot`, giving each try its
  ! chance. Returns with has_error false and a catch or finally body
  ! pushed, or with has_error true and the stack at kbot.
  subroutine k_unwind(kbot)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    integer, intent(in) :: kbot
    type(gc_value) :: nd, exc, catches, cl, fin
    integer :: b, i, n
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    do while (tctx%ksp > kbot)
       b = tctx%kst(tctx%ksp)%base
       nd = vs_get(vst, b + 1)
       call note_position(nd)
       ! a flat body inside a try of its own lands in its handler
       if (gc_i1(nd) == N_FLAT .and. tctx%kst(tctx%ksp)%mode > 0) then
          call flat_catch(tctx, b)
          return
       end if
       if (gc_i1(nd) == N_TRY .and. (tctx%kst(tctx%ksp)%pc == 1 .or. tctx%kst(tctx%ksp)%pc == 3)) then
          exc = thrown_value()
          if (exc%tag == GCT_NIL) then
             block
                call gce_error(s=dlt_1)
                exc = error_value(dlt_1, [nd])
             end block
          end if
          call vs_set(vst, b + 3, exc)
          if (tctx%kst(tctx%ksp)%pc == 1) then
             catches = gc_slot(nd, 2)
             n = gcv_count(catches)
             do i = 0, n - 1
                cl = gcv_nth(catches, i)
                call vs_set(vst, b + 4, cl)
                if (.not. catch_matches(gcv_nth(vs_get(vst, b + 4), 0), vs_get(vst, b + 3), gc_nil())) cycle
                call gce_clear_error()
                ! the calls the error unwound out of are gone: a call
                ! pushed by a native and never popped on the way out
                ! stayed on the stack and showed in every later trace
                tctx%fstack_top = min(tctx%fstack_top, tctx%kst(tctx%ksp)%ftop)
                call frame_set(vs_get(vst, b + 2), int_of(gcv_nth(vs_get(vst, b + 4), 1)), vs_get(vst, b + 3))
                tctx%kst(tctx%ksp)%pc = 3
                call k_push(gcv_nth(vs_get(vst, b + 4), 2), vs_get(vst, b + 2), 0, gc_nil())
                return
             end do
          end if
          ! not caught here: a finally still runs, then the error goes on
          fin = gcv_nth(gc_slot(vs_get(vst, b + 1), 1), 1)
          if (gc_kind(fin) == OBJ_AST) then
             tctx%kst(tctx%ksp)%msg = tctx%last_error
             call gce_clear_error()
             tctx%fstack_top = min(tctx%fstack_top, tctx%kst(tctx%ksp)%ftop)
             tctx%kst(tctx%ksp)%pc = 4
             call k_push(fin, vs_get(vst, b + 2), 0, gc_nil())
             return
          end if
       end if
       ! a flat body waiting on a thunk it forced in the loop: the thunk
       ! threw, so its cell is pending again (flat.inc flat_force)
       if (gc_i1(nd) == N_FLAT .and. tctx%kst(tctx%ksp)%aux == -1) then
          tctx%kst(tctx%ksp)%aux = 0
          call flat_release(vs_get(vst, b + 6))
       end if
       do while (tctx%kst(tctx%ksp)%nfr > 0)
          call pop_frame(tctx)
          tctx%kst(tctx%ksp)%nfr = tctx%kst(tctx%ksp)%nfr - 1
       end do
       call vs_leave(vst, b)
       tctx%ksp = tctx%ksp - 1
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
    out = run(nd, frame, 0, gc_nil(), gc_nil())
  end function exec

  ! `fn0` is the closure whose body this is, for the debugger: it rides
  ! in kframe slot 7 and is what break_frames reports a frame as.
  recursive function run(nd0, frame0, flags0, restart0, fn0) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd0, frame0, restart0, fn0
    integer, intent(in) :: flags0
    type(gc_value) :: out
    integer :: kbot, vbase

    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    if (tctx%has_error) return
    if (ev_limit == 0) call read_depth_limit()
    tctx%ev_depth = tctx%ev_depth + 1
    if (tctx%ev_depth > ev_limit) then
       call raise_class("clotran.host.stack_overflow_error", "stack overflow", [gc_value ::])
       tctx%ev_depth = tctx%ev_depth - 1
       return
    end if
    vbase = vs_enter(vst, 1)
    kbot = tctx%ksp
    call k_push(nd0, frame0, flags0, restart0)
    call vs_set(vst, tctx%kst(tctx%ksp)%base + 7, fn0)
    if (step_at /= 0 .and. gc_kind(fn0) == OBJ_CLOSURE) call step_check()
    out = run_loop(kbot, vbase)
    if (tctx%has_error) out = gc_nil()
    call vs_leave(vst, vbase)
    ! the top-level form is over: a step it did not reach does not wait
    ! for the next form's first call
    if (tctx%ev_depth == 1) step_at = 0
    tctx%ev_depth = tctx%ev_depth - 1
  end function run

  ! The loop itself, over the frames above `kbot`, with the value in
  ! flight rooted at vbase + 1. Returns when the stack is back at kbot
  ! -- the value, or nil with has_error set -- or when a blocking
  ! builtin has asked to YIELD (yield_flag, tasks.inc): then the frames
  ! stay as they are, the node that blocked is not finished, and the
  ! task scheduler resumes the loop later and re-executes that node.
  recursive function run_loop(kbot, vbase) result(val)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    integer, intent(in) :: kbot, vbase
    type(gc_value) :: val, nd, kids, v, fnv, newframe, body
    integer :: kind, n, b, site
    logical :: ok

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    val = gc_nil()
    do
       if (tctx%has_error) then
          call k_unwind(kbot)
          if (tctx%has_error) exit
          val = gc_nil()
          call vs_set(vst, vbase + 1, val)
       end if
       if (tctx%ksp == kbot) exit
       ! a SAFEPOINT each step (PLAN.md step 14f): a collection elsewhere
       ! stops this thread here even in a loop that allocates nothing.
       ! `val` -- what the last step handed on, a callee's answer on its
       ! way to the frame that asked -- is only a local here, so it goes
       ! into the loop's value slot while the world is stopped. It did
       ! not, and a value collected here was stored into its frame just
       ! after, freed under it (found by test/clj/threads_heap.clj).
       if (gc_stop_pending()) then
          call vs_set(vst, vbase + 1, val)
          call gc_poll()
          val = vs_get(vst, vbase + 1)
       end if
       b = tctx%kst(tctx%ksp)%base
       nd = vs_get(vst, b + 1)
       kind = gc_i1(nd)
       kids = gc_slot(nd, 1)

       select case (kind)
       case (N_FLAT)
          call flat_run(tctx, kbot, vbase, val)
          if (tctx%yield_flag) exit
       case (N_CONST)
          val = gc_slot(nd, 2)
          call k_finish(val, tctx)
       case (N_LOCAL)
          val = frame_get(vs_get(vst, b + 2), gc_i2(nd))
          if (tag_of(gc_slot(nd, 3)) == GCT_BOOL) call frame_set(vs_get(vst, b + 2), gc_i2(nd), gc_nil())
          call k_finish(val, tctx)
       case (N_VAR)
          val = var_deref(gc_slot(nd, 2), [gc_slot(nd, 2)])
          call k_finish(val, tctx)
       case (N_IF)
          if (tctx%kst(tctx%ksp)%pc == 0) then
             tctx%kst(tctx%ksp)%pc = 1
             call k_push(gcv_nth(kids, 0), vs_get(vst, b + 2), 0, gc_nil(), tctx)
          else if (truthy(val)) then
             call k_tail(gcv_nth(kids, 1), tctx)
          else if (gcv_count(kids) > 2) then
             call k_tail(gcv_nth(kids, 2), tctx)
          else
             val = gc_nil()
             call k_finish(val, tctx)
          end if
       case (N_DO)
          n = gcv_count(kids)
          if (n == 0) then
             val = gc_nil()
             call k_finish(val, tctx)
          else if (tctx%kst(tctx%ksp)%i < n - 1) then
             tctx%kst(tctx%ksp)%i = tctx%kst(tctx%ksp)%i + 1
             call k_push(gcv_nth(kids, tctx%kst(tctx%ksp)%i - 1), vs_get(vst, b + 2), 0, gc_nil(), tctx)
          else
             call k_tail(gcv_nth(kids, n - 1), tctx)
          end if
       case (N_CALL)
          select case (tctx%kst(tctx%ksp)%pc)
          case (0)
             tctx%kst(tctx%ksp)%pc = 1
             ! a direct-linked head (N_VAR, i2 = 1, DEVIATIONS 55): the fn
             ! bound at analysis is the callee, and the Var is not read.
             ! After an epoch change -- a compiled namespace installed,
             ! every Var re-rooted -- the Var is read ONCE more, and only
             ! a compiled fn found there replaces the binding: anything
             ! else (a with-redefs in force at this site's first call, say)
             ! is not what the install put there, and the binding stands.
             v = gcv_nth(kids, 0)
             if (gc_kind(v) == OBJ_AST) then
                if (gc_i1(v) == N_VAR .and. gc_i2(v) == 1) then
                   fnv = gc_slot(v, 5)   ! slot 4 is the node's source position
                   if (fnv%tag == GCT_INT) then
                      if (fnv%ival /= link_epoch) then
                         fnv = gcn_var_value(gc_slot(v, 2))
                         if (gc_kind(fnv) == OBJ_COMPILED) call gc_set_slot(v, 3, fnv)
                         call gc_set_slot(v, 5, gc_int(int(link_epoch, gc_ip)))
                      end if
                      val = gc_slot(v, 3)
                      cycle
                   end if
                end if
             end if
             call k_push(gcv_nth(kids, 0), vs_get(vst, b + 2), 0, gc_nil(), tctx)
          case (1)
             ! The callee is known before its arguments are: a closure
             ! with a fixed arity of the right count gets its FRAME now
             ! and the arguments land in it (mode 2); anything else gets
             ! a one-node argument vector (mode 1). No vector is copied
             ! per argument either way.
             fnv = strip_meta(val)
             if (gcn_is_var(fnv)) fnv = gcn_var_value(fnv)
             n = gcv_count(kids) - 1
             ! a fn that only wraps a builtin, called with its arity: the
             ! builtin is the callee (analyze.inc wrapper_builtin)
             ! b + 6 keeps the wrapper for the call stack (case 4)
             v = wrapper_of(fnv, n)
             call vs_set(vst, b + 6, gc_nil())
             if (v%tag /= GCT_NIL) then
                call vs_set(vst, b + 6, fnv)
                fnv = v
             end if
             call vs_set(vst, b + 3, fnv)
             tctx%kst(tctx%ksp)%mode = 1
             if (is_node_closure(vs_get(vst, b + 3))) then
                tctx%kst(tctx%ksp)%aux2 = fixed_arity(vs_get(vst, b + 3), n)
                if (tctx%kst(tctx%ksp)%aux2 >= 0) then
                   tctx%kst(tctx%ksp)%mode = 2
                   tctx%kst(tctx%ksp)%aux = int_of(gcv_nth(gcv_nth(gcv_nth(gc_slot(vs_get(vst, b + 3), 1), 1), tctx%kst(tctx%ksp)%aux2), 2))
                   call vs_set(vst, b + 4, new_frame(int_of(gcv_nth(gc_slot(vs_get(vst, b + 3), 1), 3)), [vs_get(vst, b + 1)]))
                end if
             end if
             if (tctx%kst(tctx%ksp)%mode == 1 .and. n >= 1 .and. n <= 2) then
                if (gc_kind(vs_get(vst, b + 3)) == OBJ_BUILTIN) then
                   if (scalar_builtin(gc_i1(vs_get(vst, b + 3)))) tctx%kst(tctx%ksp)%mode = 3
                end if
             end if
             ! a builtin that keeps no argument: a spare vector (mode 4)
             if (tctx%kst(tctx%ksp)%mode == 1 .and. n >= 1 .and. n <= ARG_SPARE_MAX) then
                if (gc_kind(vs_get(vst, b + 3)) == OBJ_BUILTIN) then
                   if (args_reusable(gc_i1(vs_get(vst, b + 3)))) then
                      tctx%kst(tctx%ksp)%mode = 4
                      call vs_set(vst, b + 4, args_take(n, [vs_get(vst, b + 1), vs_get(vst, b + 3)]))
                   end if
                end if
             end if
             if (tctx%kst(tctx%ksp)%mode == 1) call vs_set(vst, b + 4, gcv_build(n, [vs_get(vst, b + 1)]))
             tctx%kst(tctx%ksp)%i = 1
             tctx%kst(tctx%ksp)%pc = 2
          case (2)
             if (tctx%kst(tctx%ksp)%i < gcv_count(kids)) then
                tctx%kst(tctx%ksp)%pc = 3
                call k_push(gcv_nth(kids, tctx%kst(tctx%ksp)%i), vs_get(vst, b + 2), 0, gc_nil(), tctx)
             else
                tctx%kst(tctx%ksp)%pc = 4
             end if
          case (3)
             if (tctx%kst(tctx%ksp)%mode == 2) then
                call frame_set(vs_get(vst, b + 4), tctx%kst(tctx%ksp)%aux + tctx%kst(tctx%ksp)%i - 1, val)
             else if (tctx%kst(tctx%ksp)%mode == 3) then
                if (tctx%kst(tctx%ksp)%i == 1) call vs_set(vst, b + 4, val)
             else
                call vs_set(vst, b + 4, gcv_put(vs_get(vst, b + 4), tctx%kst(tctx%ksp)%i - 1, val, [vs_get(vst, b + 1)]))
             end if
             tctx%kst(tctx%ksp)%i = tctx%kst(tctx%ksp)%i + 1
             tctx%kst(tctx%ksp)%pc = 2
          case (5)
             ! the callee's body finished; its value is this call's, and
             ! its frame is free for the next call
             call give_frame(vs_get(vst, b + 4))
             call vs_set(vst, b + 4, gc_nil())
             call k_finish(val, tctx)
          case (4)
             ! where this call is, for the call stack
             v = gc_slot(nd, 4)
             site = 0
             if (v%tag == GCT_INT) site = int(v%ival, kind=4)
             fnv = vs_get(vst, b + 3)
             ! an elided wrapper (case 1) is on the call stack while its
             ! builtin runs, as in clj; nfr has k_finish, or an
             ! unwinding error, pop it
             if (tctx%kst(tctx%ksp)%mode /= 2 .and. tag_of(vs_get(vst, b + 6)) /= GCT_NIL) then
                call push_frame(tctx, vs_get(vst, b + 6), site)
                if (tctx%has_error) cycle
                tctx%kst(tctx%ksp)%nfr = tctx%kst(tctx%ksp)%nfr + 1
                call vs_set(vst, b + 6, gc_nil())
             end if
             if (tctx%kst(tctx%ksp)%mode == 4) then
                ! a builtin that keeps no argument, in a spare vector
                n = gcv_count(kids) - 1
                tctx%pending_site = site
                v = vs_get(vst, b + 4)
                ! the loop's last-value slot (vbase + 1) still holds the
                ! last ARGUMENT evaluated; a builtin that walks it (count
                ! over a seq) must not find the head rooted there for the
                ! whole call (PLAN.md step 16). Not before the arguments
                ! are in a vector: on the numeric path the last one is
                ! still only in `val`, and that slot was its root.
                call vs_set(vst, vbase + 1, gc_nil())
                val = call_builtin(gc_i1(fnv), v)
                call args_give(vs_get(vst, b + 4), n)
                call vs_set(vst, b + 4, gc_nil())
                call k_finish(val, tctx)
                cycle
             end if
             if (tctx%kst(tctx%ksp)%mode == 3) then
                ! the numeric fast path: no vector is allocated for the call
                n = gcv_count(kids) - 1
                v = scratch_args(n)
                if (n == 1) then
                   call gc_vec_set(gc_slot(v, 1), 1, val)
                else
                   call gc_vec_set(gc_slot(v, 1), 1, vs_get(vst, b + 4))
                   call vs_set(vst, b + 4, gc_nil())
                   call gc_vec_set(gc_slot(v, 1), 2, val)
                end if
                call vs_set(vst, vbase + 1, gc_nil())
                val = call_builtin(gc_i1(fnv), v)
                call k_finish(val, tctx)
                cycle
             end if
             if (tctx%kst(tctx%ksp)%mode == 2) then
                ! the frame already holds the arguments; captures and the
                ! fn's own name complete it, and the body runs in a frame
                ! OF ITS OWN. A call in tail position used to reuse this
                ! one, which cost nothing at the time -- the caller was
                ! finished with its locals -- but a caller's locals are
                ! exactly what a break has to show, and the call stack
                ! names the caller either way. Clojure eliminates no tail
                ! call, so keeping the frame is also what it does.
                call push_frame(tctx, fnv, site)
                if (tctx%has_error) cycle
                call bind_captures(vs_get(vst, b + 3), vs_get(vst, b + 4))
                body = arity_body(gcv_nth(gcv_nth(gc_slot(vs_get(vst, b + 3), 1), 1), tctx%kst(tctx%ksp)%aux2))
                call vs_set(vst, b + 5, body)
                tctx%kst(tctx%ksp)%pc = 5
                call k_push(vs_get(vst, b + 5), vs_get(vst, b + 4), ior(KF_FNBODY, KF_RESTART), vs_get(vst, b + 5), tctx)
                call vs_set(vst, tctx%kst(tctx%ksp)%base + 7, fnv)
                if (step_at /= 0) call step_check()
                cycle
             end if
             ! The argument vector is handed over, not kept (see
             ! bind_closure / apply): nothing allocates between this nil
             ! and the callee rooting it.
             v = vs_get(vst, b + 4)
             call vs_set(vst, b + 4, gc_nil())
             if (is_node_closure(fnv)) then
                ! The callee's body, in a frame of its own (see mode 2).
                call push_frame(tctx, fnv, site)
                if (tctx%has_error) cycle
                call vs_set(vst, b + 3, fnv)
                ok = bind_closure(vs_get(vst, b + 3), v, newframe, body)
                if (ok) then
                   call vs_set(vst, b + 4, newframe)
                   call vs_set(vst, b + 5, body)
                   tctx%kst(tctx%ksp)%pc = 5
                   call k_push(vs_get(vst, b + 5), vs_get(vst, b + 4), ior(KF_FNBODY, KF_RESTART), vs_get(vst, b + 5), tctx)
                   call vs_set(vst, tctx%kst(tctx%ksp)%base + 7, vs_get(vst, b + 3))
                   if (step_at /= 0) call step_check()
                else
                   ! no arity fits: the entry pushed above is ours to drop
                   call pop_frame(tctx)
                end if
             else
                tctx%pending_site = site
                call vs_set(vst, vbase + 1, gc_nil())
                val = apply(vs_get(vst, b + 3), v)
                if (tctx%yield_flag) then
                   ! parked here: the vector goes back for the re-dispatch
                   call vs_set(vst, b + 4, v)
                   exit
                end if
                call k_finish(val, tctx)
             end if
          end select
       case (N_LET, N_LOOP)
          n = gc_i2(nd)
          if (tctx%kst(tctx%ksp)%pc == 1) then
             call frame_set(vs_get(vst, b + 2), int_of(gc_slot(nd, 2)) + tctx%kst(tctx%ksp)%i, val)
             tctx%kst(tctx%ksp)%i = tctx%kst(tctx%ksp)%i + 1
             tctx%kst(tctx%ksp)%pc = 0
          else if (tctx%kst(tctx%ksp)%i < n) then
             tctx%kst(tctx%ksp)%pc = 1
             call k_push(gcv_nth(kids, tctx%kst(tctx%ksp)%i), vs_get(vst, b + 2), 0, gc_nil(), tctx)
          else
             if (kind == N_LOOP) then
                call vs_set(vst, b + 5, gcv_nth(kids, n))
                tctx%kst(tctx%ksp)%flags = ior(tctx%kst(tctx%ksp)%flags, KF_RESTART)
             end if
             call k_tail(gcv_nth(kids, n), tctx)
          end if
       case (N_CASE)
          if (tctx%kst(tctx%ksp)%pc == 0) then
             tctx%kst(tctx%ksp)%pc = 1
             call k_push(gcv_nth(kids, 0), vs_get(vst, b + 2), 0, gc_nil(), tctx)
          else
             call vs_set(vst, b + 3, val)
             v = case_branch(vs_get(vst, b + 1), vs_get(vst, b + 3))
             call k_tail(v, tctx)
          end if
       case (N_TRY)
          select case (tctx%kst(tctx%ksp)%pc)
          case (0)
             tctx%kst(tctx%ksp)%pc = 1
             tctx%kst(tctx%ksp)%ftop = tctx%fstack_top
             call k_push(gcv_nth(kids, 0), vs_get(vst, b + 2), 0, gc_nil(), tctx)
          case (1, 3)
             ! the body, or a catch, finished normally
             call vs_set(vst, b + 3, val)
             v = gcv_nth(kids, 1)
             if (gc_kind(v) == OBJ_AST) then
                tctx%kst(tctx%ksp)%pc = 2
                call k_push(v, vs_get(vst, b + 2), 0, gc_nil(), tctx)
             else
                call k_finish(val, tctx)
             end if
          case (2)
             val = vs_get(vst, b + 3)
             call k_finish(val, tctx)
          case (4)
             ! the finally ran after an uncaught error: the error goes on
             tctx%has_error = .true.
             tctx%last_error = tctx%kst(tctx%ksp)%msg
             call set_thrown(vs_get(vst, b + 3))
             tctx%kst(tctx%ksp)%pc = 5
          case default
             call k_finish(val, tctx)
          end select
       case (N_VECTOR, N_MAP, N_SET)
          ! children collected into slot 4, one frame each, then built
          select case (tctx%kst(tctx%ksp)%pc)
          case (0)
             call vs_set(vst, b + 4, gcv_build(gcv_count(kids), [vs_get(vst, b + 1)]))
             tctx%kst(tctx%ksp)%i = 0
             tctx%kst(tctx%ksp)%pc = 2
          case (2)
             if (tctx%kst(tctx%ksp)%i < gcv_count(kids)) then
                tctx%kst(tctx%ksp)%pc = 3
                call k_push(gcv_nth(kids, tctx%kst(tctx%ksp)%i), vs_get(vst, b + 2), 0, gc_nil(), tctx)
             else
                select case (kind)
                case (N_VECTOR); val = vs_get(vst, b + 4)
                case (N_SET);    val = vec_to_set(vs_get(vst, b + 4), [vs_get(vst, b + 1)])
                case default;    val = vec_to_map(vs_get(vst, b + 4), [vs_get(vst, b + 1)])
                end select
                call k_finish(val, tctx)
             end if
          case (3)
             call vs_set(vst, b + 4, gcv_put(vs_get(vst, b + 4), tctx%kst(tctx%ksp)%i, val, [vs_get(vst, b + 1)]))
             tctx%kst(tctx%ksp)%i = tctx%kst(tctx%ksp)%i + 1
             tctx%kst(tctx%ksp)%pc = 2
          end select
       case (N_RECUR)
          val = exec_recur(nd, vs_get(vst, b + 2))
          if (.not. tctx%has_error) call k_finish(val, tctx)
       case (N_THROW)
          v = exec(gcv_nth(kids, 0), vs_get(vst, b + 2))
          if (.not. tctx%has_error) then
             call set_thrown(v)
             tctx%has_error = .true.
             block
                call gcp_str(v, .true., s=dlt_1)
                tctx%last_error = dlt_1
             end block
             call capture_trace()
          end if
       case (N_FN)
          val = make_closure_from(gc_slot(nd, 2), vs_get(vst, b + 2), [vs_get(vst, b + 1)])
          call k_finish(val, tctx)
       case (N_LAZY)
          v = make_closure_from(gc_slot(nd, 2), vs_get(vst, b + 2), [vs_get(vst, b + 1)])
          call vs_set(vst, b + 3, v)
          val = gc_obj(OBJ_LAZY, [vs_get(vst, b + 3), gc_nil(), gc_nil()], [vs_get(vst, b + 3)])
          call gc_set_i1(val, LAZY_PENDING)
          call k_finish(val, tctx)
       case (N_TOP)
          ! its frame is on the stack, made when it was pushed (k_push)
          v = vs_get(vst, b + 2)
          if (v%tag /= GCT_SFRAME) then
             v = new_frame(gc_i2(nd), [vs_get(vst, b + 1)])
             call vs_set(vst, b + 2, v)
          end if
          ! its flat form when it has one (analyze_top)
          v = gc_slot(vs_get(vst, b + 1), 3)
          if (v%tag == GCT_NIL .or. .not. flat_enabled()) v = gc_slot(vs_get(vst, b + 1), 2)
          call k_tail(v, tctx)
       case (N_DOT)
          ! (. target member args...): the target, then the arguments,
          ! into this frame -- slot 3 and slot 4 -- and then the dispatch,
          ! which is re-executable as it stands: a block in it yields
          ! (tasks.inc) and resumes by dispatching again, reading no
          ! local a clearing pass may since have dropped. aux is where
          ! the arguments start among the children: 1 after an evaluated
          ! target, 0 when the target is a class.
          select case (tctx%kst(tctx%ksp)%pc)
          case (0)
             if (tag_of(gc_slot(nd, 3)) == GCT_SYM) then
                call vs_set(vst, b + 3, gc_slot(nd, 3))
                tctx%kst(tctx%ksp)%aux = 0
                tctx%kst(tctx%ksp)%i = 0
                tctx%kst(tctx%ksp)%pc = 2
             else
                tctx%kst(tctx%ksp)%pc = 1
                call k_push(gcv_nth(kids, 0), vs_get(vst, b + 2), 0, gc_nil(), tctx)
             end if
          case (1)
             call vs_set(vst, b + 3, val)
             tctx%kst(tctx%ksp)%aux = 1
             tctx%kst(tctx%ksp)%i = 1
             tctx%kst(tctx%ksp)%pc = 2
          case (2)
             if (tctx%kst(tctx%ksp)%i == tctx%kst(tctx%ksp)%aux) &
                  call vs_set(vst, b + 4, gcv_build(gcv_count(kids) - tctx%kst(tctx%ksp)%aux, [vs_get(vst, b + 1)]))
             if (tctx%kst(tctx%ksp)%i < gcv_count(kids)) then
                tctx%kst(tctx%ksp)%pc = 3
                call k_push(gcv_nth(kids, tctx%kst(tctx%ksp)%i), vs_get(vst, b + 2), 0, gc_nil(), tctx)
             else
                tctx%kst(tctx%ksp)%pc = 4
             end if
          case (3)
             call vs_set(vst, b + 4, gcv_put(vs_get(vst, b + 4), tctx%kst(tctx%ksp)%i - tctx%kst(tctx%ksp)%aux, val, [vs_get(vst, b + 1)]))
             tctx%kst(tctx%ksp)%i = tctx%kst(tctx%ksp)%i + 1
             tctx%kst(tctx%ksp)%pc = 2
          case (4)
             call vs_set(vst, vbase + 1, gc_nil())   ! see N_CALL's case (4)
             ! the argument vector is handed over, as N_CALL's is:
             ! dot_dispatch roots it first thing, and this frame kept
             ! (. f (applyTo s)) -- core's apply -- holding the head of s
             ! for the whole call, every cell of (apply + (take n (range)))
             v = vs_get(vst, b + 4)
             call vs_set(vst, b + 4, gc_nil())
             val = dot_dispatch(nd, vs_get(vst, b + 3), v, tctx%kst(tctx%ksp)%aux)
             ! parked: the vector goes back for the re-dispatch
             if (tctx%yield_flag) then
                call vs_set(vst, b + 4, v)
                exit
             end if
             if (tctx%has_error) cycle
             if (is_call_request(val)) then
                v = gc_slot(nd, 4)
                site = 0
                if (v%tag == GCT_INT) site = int(v%ival, kind=4)
                call enter_call(val, site)
             else
                call k_finish(val, tctx)
             end if
          end select
       case default
          val = exec_other(nd, vs_get(vst, b + 2))
          if (.not. tctx%has_error) call k_finish(val, tctx)
       end select
       call vs_set(vst, vbase + 1, val)
    end do
  end function run_loop

  ! A closure a helper wants called -- a reify or deftype method reached
  ! through `.` (eval_dot) -- as a request the loop honours itself. i1 =
  ! 1 tells it from the recur marker, the other OBJ_RECUR.
  function call_request(fn, argv) result(req)
    type(gc_value), intent(in) :: fn, argv
    type(gc_value) :: req
    req = gc_obj(OBJ_RECUR, [fn, argv], [fn, argv])
    call gc_set_i1(req, 1)
  end function call_request

  logical function is_call_request(v)
    type(gc_value), intent(in) :: v
    is_call_request = .false.
    if (gc_kind(v) == OBJ_RECUR) is_call_request = gc_i1(v) == 1
  end function is_call_request

  ! Runs the requested closure IN THE LOOP, in place of the node that
  ! asked: that node's frame becomes the callee's body frame, and the
  ! value the body finishes with is the node's. Through apply it would
  ! be a nested run, which PINS it (tasks.inc): a promise's deref is
  ! such a method, and it has to be able to yield. The callee also
  ! shows in a break's frames this way.
  subroutine enter_call(req, site)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: req
    integer, intent(in) :: site
    type(gc_value) :: frame, body, argv
    integer :: b
    logical :: ok
    tctx => ctx_self()
    vst => tctx%stk
    b = tctx%kst(tctx%ksp)%base
    call vs_set(vst, b + 3, gc_slot(req, 1))
    argv = gc_slot(req, 2)
    call push_frame(tctx, vs_get(vst, b + 3), site)
    if (tctx%has_error) return
    ok = bind_closure(vs_get(vst, b + 3), argv, frame, body)
    if (.not. ok) then
       call pop_frame(tctx)
       return
    end if
    call vs_set(vst, b + 1, body)
    call vs_set(vst, b + 2, frame)
    call vs_set(vst, b + 4, gc_nil())
    call vs_set(vst, b + 5, body)
    call vs_set(vst, b + 6, gc_nil())
    call vs_set(vst, b + 7, vs_get(vst, b + 3))
    tctx%kst(tctx%ksp)%pc = 0
    tctx%kst(tctx%ksp)%i = 0
    tctx%kst(tctx%ksp)%flags = ior(KF_FNBODY, KF_RESTART)
    ! ONE MORE call to pop when this frame finishes, not one: a method
    ! that is a fn's whole body -- a protocol fn dispatching to a reify
    ! -- turns that fn's own body frame into the callee's, and setting
    ! the count to 1 lost the fn's entry. Every spec conform leaked one,
    ! and every macro's spec check left dozens on the call stack.
    tctx%kst(tctx%ksp)%nfr = tctx%kst(tctx%ksp)%nfr + 1
    tctx%kst(tctx%ksp)%mode = 0
    tctx%kst(tctx%ksp)%aux = 0
    tctx%kst(tctx%ksp)%aux2 = 0
    if (step_at /= 0) call step_check()
  end subroutine enter_call

  ! (new C args...) with its arguments evaluated. The first time, the
  ! whole of eval_new (or, for N_NEWTYPE, the type by name); when that
  ! made an instance of the deftype registered under C, the type is kept
  ! in the node's slot 3 and every later time constructs from it
  ! -- the name no longer compared against eval_new's chain of host
  ! classes and looked up in the type table on every call (a record cost
  ! 1.7 us to make). A compiled `new` keeps the class it was compiled
  ! against in clj too, so a record redefined later is not what an
  ! older call site makes, there as here.
  recursive function new_cached(nd, argv) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd, argv
    type(gc_value) :: out, ty
    integer :: base
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, nd)
    call vs_set(vst, base + 2, argv)
    ty = gc_slot(nd, 3)
    if (gc_kind(ty) == OBJ_TYPE) then
       call vs_set(vst, base + 3, ty)
       out = construct_type_vals(vs_get(vst, base + 3), vs_get(vst, base + 2))
       call vs_leave(vst, base)
       return
    end if
    call sym_text(gc_slot(nd, 2), s=dlt_1)
    if (gc_i1(nd) == N_NEWTYPE) then
       ty = find_type_loading(dlt_1)
       if (gc_kind(ty) /= OBJ_TYPE) then
          call fail("no such class: " // dlt_1)
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 3, ty)
       out = construct_type_vals(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else
       out = eval_new(dlt_1, vs_get(vst, base + 2))
    end if
    if (.not. tctx%has_error) then
       call vs_set(vst, base + 2, out)
       ty = find_type(dlt_1)
       if (gc_kind(ty) == OBJ_TYPE .and. gc_kind(vs_get(vst, base + 2)) == OBJ_INST) then
          block
            type(gc_value) :: t1
            t1 = gc_slot(vs_get(vst, base + 2), 1)
            if (t1%tag == ty%tag .and. t1%ref == ty%ref) call gc_set_slot(vs_get(vst, base + 1), 3, ty)
          end block
       end if
       out = vs_get(vst, base + 2)
    end if
    call vs_leave(vst, base)
  end function new_cached

  ! The node kinds the loop leaves to a helper. Each helper evaluates
  ! its children through exec, nesting a run.
  recursive function exec_other(nd, frame) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, kids, v, fnv
    integer :: base, kind

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, nd)
    call vs_set(vst, base + 2, frame)
    kind = gc_i1(nd)
    kids = gc_slot(nd, 1)
    select case (kind)
    case (N_DEF)
       out = exec_def(nd, frame)
    case (N_LETFN)
       out = exec_letfn(nd, frame)
    case (N_DEFTYPE)
       out = exec_deftype(nd, frame)
    case (N_NEW, N_NEWTYPE)
       v = exec_args(kids, 0, frame)
       if (.not. tctx%has_error) then
          call vs_set(vst, base + 3, v)
          out = new_cached(vs_get(vst, base + 1), vs_get(vst, base + 3))
       end if
    case (N_SETBANG)
       out = exec_setbang(nd, frame)
    case (N_LATEVAR)
       v = resolve_var(gc_slot(nd, 2), gc_nil())
       if (.not. gcn_is_var(v)) then
          ! clotran.io/text-reader before clotran.io is loaded
          call sym_text(gc_slot(vs_get(vst, base + 1), 2), s=dlt_1)
          if (index(dlt_1, "/") > 1) then
             if (load_clotran_ns(dlt_1(1:index(dlt_1, "/") - 1))) &
                  v = resolve_var(gc_slot(vs_get(vst, base + 1), 2), gc_nil())
          end if
       end if
       if (gcn_is_var(v)) then
          out = gcn_var_value(v)
       else
          block
             call sym_text(gc_slot(vs_get(vst, base + 1), 2), s=dlt_1)
             call fail("Unable to resolve symbol: " // dlt_1)
          end block
       end if
    case (N_FAIL)
       block
          call sym_text(gc_slot(nd, 2), s=dlt_1)
          call fail(dlt_1)
       end block
    case (N_TOPDO)
       ! Each subform analysed after the previous one has run.
       call vs_set(vst, base + 3, gc_slot(nd, 2))
       do while (gcl_count(vs_get(vst, base + 3)) > 0)
          v = analyze_top(gcl_first(vs_get(vst, base + 3)))
          if (tctx%has_error) exit
          call vs_set(vst, base + 4, v)
          out = exec(vs_get(vst, base + 4), gc_nil())
          if (tctx%has_error) exit
          call vs_set(vst, base + 3, gcl_rest(vs_get(vst, base + 3), [vs_get(vst, base + 1)]))
       end do
    case default
       call fail("exec: unknown node kind")
    end select
    if (tctx%has_error) call note_position(vs_get(vst, base + 1))
    call vs_leave(vst, base)
  end function exec_other

  ! Appends "  at file:line:col" to the error once, from the innermost
  ! node that has a position -- the error propagates outward through
  ! every enclosing node, and only the first appends.
  subroutine note_position(nd)
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd
    type(gc_value) :: p
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    p = gc_slot(nd, 4)
    if (p%tag /= GCT_INT) return
    if (index(tctx%last_error, "  at ") > 0) return
    block
       call gcr_position(int(p%ival, kind=4), s=dlt_1)
       tctx%last_error = tctx%last_error // "  at " // dlt_1
    end block
  end subroutine note_position

  ! Alternating keys and values, as a map literal's children come.
  function vec_to_map(vals, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: vals
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, mp
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, vals)
    mp = gca_empty([roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, mp)
    do i = 0, gcv_count(vals) - 1, 2
       mp = gca_assoc(vs_get(vst, base + 2), gcv_nth(vs_get(vst, base + 1), i), gcv_nth(vs_get(vst, base + 1), i + 1), &
            [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 2, mp)
    end do
    out = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function vec_to_map

  function vec_to_set(vals, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: vals
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, mp
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, vals)
    mp = gca_hash_empty([roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, mp)
    do i = 0, gcv_count(vals) - 1
       mp = gca_assoc(vs_get(vst, base + 2), gcv_nth(vs_get(vst, base + 1), i), gcv_nth(vs_get(vst, base + 1), i), &
            [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 2, mp)
    end do
    out = gc_obj(OBJ_SET, [vs_get(vst, base + 2)], [roots, vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function vec_to_set

  ! def: the Var was interned at analysis; here it gets its value, its
  ! evaluated metadata, and -- if the value is a closure with no name
  ! yet -- the qualified name an arity error will report.
  recursive function exec_def(nd, frame) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, var, v, md, fnv, nmsym
    character(len=:), allocatable :: qual
    integer :: base, flags

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, nd)
    call vs_set(vst, base + 2, frame)
    var = gc_slot(nd, 2)
    call vs_set(vst, base + 3, var)
    flags = gc_i2(nd)
    if (iand(flags, 1) /= 0) then
       v = exec(gcv_nth(gc_slot(vs_get(vst, base + 1), 1), 0), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 4, v)
       ! the ROOT; a binding in force keeps showing its own value, as
       ! DefExpr's bindRoot does
       call gc_set_slot(vs_get(vst, base + 3), 1, vs_get(vst, base + 4))
       call gc_set_i1(vs_get(vst, base + 3), 1)
    end if
    md = gc_slot(vs_get(vst, base + 1), 3)
    if (gc_kind(md) == OBJ_AST) then
       md = exec(md, vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 5, md)
       call gc_set_slot(vs_get(vst, base + 3), 2, vs_get(vst, base + 5))
    end if
    ! The Var's metadata as DefExpr leaves it: what the form carried,
    ! plus :name, :ns, :file, :line and :column. clojure.test names a
    ! test by the first, and a def had none of them.
    call vs_set(vst, base + 5, gc_slot(vs_get(vst, base + 3), 2))
    if (.not. gca_is(vs_get(vst, base + 5))) call vs_set(vst, base + 5, gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 3)]))
    call brk_put(base + 5, "name", gc_slot(vs_get(vst, base + 3), 4), [vs_get(vst, base + 1), vs_get(vst, base + 3)], base)
    call brk_put(base + 5, "ns", gc_slot(vs_get(vst, base + 3), 3), [vs_get(vst, base + 1), vs_get(vst, base + 3)], base)
    block
      type(gc_value) :: pos
      character(len=:), allocatable :: fname
      integer :: line, col
      pos = gc_slot(vs_get(vst, base + 1), 4)
      ! a def whose form was not read from a file takes the top-level
      ! form being loaded (tctx%top_pos), as DefExpr takes LINE
      if (pos%tag /= GCT_INT) pos = gc_int(0_gc_ip)
      if (pos%ival < POS_SHIFT .and. tctx%top_pos >= POS_SHIFT) pos = gc_int(int(tctx%top_pos, gc_ip))
      if (pos%tag == GCT_INT) then
         if (pos%ival > 0) then
            call gcr_position_parts(int(pos%ival, kind=4), fname, line, col)
            if (len(fname) > 0) call brk_put(base + 5, "file", gc_str(fname, [vs_get(vst, base + 1), vs_get(vst, base + 3)]), &
                 [vs_get(vst, base + 1), vs_get(vst, base + 3)], base)
            call brk_put(base + 5, "line", gc_int(int(line, gc_ip)), [vs_get(vst, base + 1), vs_get(vst, base + 3)], base)
            call brk_put(base + 5, "column", gc_int(int(col, gc_ip)), [vs_get(vst, base + 1), vs_get(vst, base + 3)], base)
         end if
      end if
    end block
    call gc_set_slot(vs_get(vst, base + 3), 2, vs_get(vst, base + 5))
    fnv = strip_meta(gcn_var_value(vs_get(vst, base + 3)))
    if (gc_kind(fnv) == OBJ_CLOSURE) then
       if (tag_of(gc_slot(fnv, 5)) == GCT_NIL) then
          call vs_set(vst, base + 4, fnv)
          nmsym = gc_slot(vs_get(vst, base + 3), 4)
          block
             call gcn_name(gc_slot(vs_get(vst, base + 3), 3), s=dlt_1)
             call gc_ref_text(nmsym%ref, s=dlt_2)
             qual = dlt_1 // "/" // dlt_2
          end block
          call gc_set_slot(vs_get(vst, base + 4), 5, gc_sym(qual, [vs_get(vst, base + 3), vs_get(vst, base + 4)]))
       end if
    end if
    if (iand(flags, 2) /= 0) call var_set_macro(vs_get(vst, base + 3))
    out = vs_get(vst, base + 3)
    call vs_leave(vst, base)
  end function exec_def


  ! letfn*: every closure is made, stored, and then has its captures
  ! copied AGAIN, so each one sees the others.
  recursive function exec_letfn(nd, frame) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, v
    integer :: base, i, n, start
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, nd)
    call vs_set(vst, base + 2, frame)
    n = gc_i2(nd)
    start = int_of(gc_slot(nd, 2))
    do i = 0, n - 1
       v = exec(gcv_nth(gc_slot(vs_get(vst, base + 1), 1), i), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       call frame_set(vs_get(vst, base + 2), start + i, v)
    end do
    do i = 0, n - 1
       v = frame_get(vs_get(vst, base + 2), start + i)
       if (is_node_closure(v)) call refresh_captures(v, vs_get(vst, base + 2))
    end do
    out = exec(gcv_nth(gc_slot(vs_get(vst, base + 1), 1), n), vs_get(vst, base + 2))
    call vs_leave(vst, base)
  end function exec_letfn

  ! recur: arguments evaluated, THEN written to the target's slots (an
  ! argument may read a slot another argument replaces), then a marker
  ! the enclosing loop or fn body reads. Into a variadic fn the last
  ! argument is the rest parameter itself, as Clojure's recur binds it.
  recursive function exec_recur(nd, frame) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, rinfo, v
    integer :: base, i, n, nk, start
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    ! Every new value is computed before any slot is rebound, into stack
    ! slots base+3.. -- not a vector: that was an allocation per turn of
    ! every interpreted loop.
    nk = gcv_count(gc_slot(nd, 1))
    base = vs_enter(vst, 2 + nk)
    call vs_set(vst, base + 1, nd)
    call vs_set(vst, base + 2, frame)
    do i = 0, nk - 1
       v = exec(gcv_nth(gc_slot(vs_get(vst, base + 1), 1), i), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 3 + i, v)
    end do
    rinfo = gc_slot(vs_get(vst, base + 1), 2)
    start = int_of(gcv_nth(rinfo, 1))
    n = int_of(gcv_nth(rinfo, 2))
    do i = 0, min(n, nk) - 1
       call frame_set(vs_get(vst, base + 2), start + i, vs_get(vst, base + 3 + i))
    end do
    out = recur_marker()
    call vs_leave(vst, base)
  end function exec_recur

  recursive function exec_try(nd, frame) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, exc, catches, cl, fin
    integer :: base, i, n, ftop
    logical :: caught

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, nd)
    call vs_set(vst, base + 2, frame)
    ftop = tctx%fstack_top
    out = exec(gcv_nth(gc_slot(nd, 1), 0), frame)
    if (tctx%has_error) then
       ! the calls the error unwound out of are gone (see k_unwind)
       tctx%fstack_top = min(tctx%fstack_top, ftop)
       exc = thrown_value()
       if (exc%tag == GCT_NIL) then
          block
             call gce_error(s=dlt_1)
             exc = error_value(dlt_1, [vs_get(vst, base + 1)])
          end block
       end if
       call vs_set(vst, base + 3, exc)
       catches = gc_slot(vs_get(vst, base + 1), 2)
       n = gcv_count(catches)
       caught = .false.
       do i = 0, n - 1
          cl = gcv_nth(catches, i)
          call vs_set(vst, base + 4, cl)
          if (.not. catch_matches(gcv_nth(vs_get(vst, base + 4), 0), vs_get(vst, base + 3), gc_nil())) cycle
          call gce_clear_error()
          call frame_set(vs_get(vst, base + 2), int_of(gcv_nth(vs_get(vst, base + 4), 1)), vs_get(vst, base + 3))
          out = exec(gcv_nth(vs_get(vst, base + 4), 2), vs_get(vst, base + 2))
          caught = .true.
          exit
       end do
    end if
    fin = gcv_nth(gc_slot(vs_get(vst, base + 1), 1), 1)
    if (gc_kind(fin) == OBJ_AST) then
       block
         logical :: had
         type(gc_value) :: saved_exc, fv
         character(len=:), allocatable :: saved_msg
         had = tctx%has_error
         saved_msg = tctx%last_error
         saved_exc = thrown_value()
         call vs_set(vst, base + 5, saved_exc)
         call gce_clear_error()
         fv = exec(fin, vs_get(vst, base + 2))
         if (.not. tctx%has_error .and. had) then
            tctx%has_error = .true.
            tctx%last_error = saved_msg
            call set_thrown(vs_get(vst, base + 5))
         end if
       end block
    end if
    call vs_leave(vst, base)
  end function exec_try

  ! case*: the table walk, answering the branch node to run.
  function case_branch(nd, val) result(branch)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: nd, val
    type(gc_value) :: branch, info, tt, entry
    integer :: base, shift, mask, h
    logical :: hit

    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, nd)
    call vs_set(vst, base + 2, val)
    info = gc_slot(nd, 3)
    shift = int_of(gcv_nth(info, 0))
    mask = int_of(gcv_nth(info, 1))
    tt = gcv_nth(info, 2)
    if (tt%tag == GCT_KEY .and. gc_ref_is(tt%ref, "int")) then
       h = ival_of(vs_get(vst, base + 2))
    else
       ! the macro keyed the table with Util.hash, which is hashCode
       h = hash_code(vs_get(vst, base + 2))
    end if
    if (mask /= 0) h = iand(shifta(h, shift), mask)
    entry = strip_meta(gca_get(gc_slot(vs_get(vst, base + 1), 2), gc_int(h)))
    if (entry%tag == GCT_NIL) then
       ! A merged collision bucket is keyed by the hash OF ITS HASH:
       ! the macro's merged test is the int hash itself, which on the
       ! clj is an Integer whose hashCode is that number, while here
       ! it is a long whose hashCode differs when it is negative. So
       ! the second probe, and skip-check (below) says it was a merge.
       entry = strip_meta(gca_get(gc_slot(vs_get(vst, base + 1), 2), &
            gc_int(int(hash_code(gc_int(int(h, gc_ip))), gc_ip))))
    end if
    call vs_set(vst, base + 3, entry)
    hit = .false.
    if (gcv_is(vs_get(vst, base + 3))) then
       if (gcv_count(vs_get(vst, base + 3)) == 2) then
          if (in_skip(gcv_nth(info, 3), h)) then
             hit = .true.
          else
             hit = deep_equal(vs_get(vst, base + 2), gcv_nth(vs_get(vst, base + 3), 0), [vs_get(vst, base + 2), vs_get(vst, base + 3)])
          end if
       end if
    end if
    if (hit) then
       branch = gcv_nth(vs_get(vst, base + 3), 1)
    else
       branch = gcv_nth(gc_slot(vs_get(vst, base + 1), 1), 1)
    end if
    call vs_leave(vst, base)
  end function case_branch

  ! deftype*/reify*/proxy: the type from its spec, each method a closure
  ! over the current frame. i2 = 0 registers the type and answers it;
  ! 1 answers a fresh instance and registers nothing.
  recursive function exec_deftype(nd, frame) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, spec, methods, names, fns, fnv, ty
    integer :: base, i, n

    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, nd)
    call vs_set(vst, base + 2, frame)
    spec = gc_slot(nd, 2)
    call vs_set(vst, base + 3, spec)
    methods = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, methods)
    names = gcv_nth(spec, 3)
    fns = gcv_nth(spec, 4)
    n = gcv_count(names)
    do i = 0, n - 1
       fnv = exec(gcv_nth(gcv_nth(vs_get(vst, base + 3), 4), i), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 5, fnv)
       methods = gca_assoc(vs_get(vst, base + 4), gcv_nth(gcv_nth(vs_get(vst, base + 3), 3), i), vs_get(vst, base + 5), &
            [vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5)])
       call vs_set(vst, base + 4, methods)
    end do
    ty = gc_obj(OBJ_TYPE, [gcv_nth(vs_get(vst, base + 3), 0), gcv_nth(vs_get(vst, base + 3), 1), &
         vs_get(vst, base + 4), gcv_nth(vs_get(vst, base + 3), 2)], [vs_get(vst, base + 3), vs_get(vst, base + 4)])
    call vs_set(vst, base + 5, ty)
    if (gc_i2(nd) == 0) then
       call register_type(vs_get(vst, base + 5))
       out = vs_get(vst, base + 5)
    else
       out = gc_obj(OBJ_INST, [vs_get(vst, base + 5), gcv_empty([vs_get(vst, base + 5)]), gc_nil()], [vs_get(vst, base + 5)])
    end if
    call vs_leave(vst, base)
  end function exec_deftype

  ! The dispatch of a `.` node, its target and arguments already
  ! evaluated by the loop (run_loop, N_DOT): a native instance member
  ! on anything but a deftype instance is called directly; everything
  ! else is handed to eval_dot. Nothing here reads a local, so a block
  ! inside can yield (tasks.inc) and resume by dispatching again.
  recursive function dot_dispatch(nd, tv, argv, from) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: nd, tv, argv
    integer, intent(in) :: from
    type(gc_value) :: out, native
    integer :: base

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    out = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, nd)
    call vs_set(vst, base + 2, tv)
    call vs_set(vst, base + 3, argv)
    native = gc_slot(nd, 3)
    ! a method called on nil is a NullPointerException, on this path
    ! as on eval_dot's
    if (from == 1) then
       block
         type(gc_value) :: tv2
         tv2 = strip_meta(tv)
         if (tv2%tag == GCT_NIL) then
            block
               call sym_text(gc_slot(vs_get(vst, base + 1), 2), s=dlt_1)
               call raise_class("clotran.host.null_pointer_exception",  "Cannot invoke ." // dlt_1 // " on nil", [vs_get(vst, base + 1)])
            end block
            call vs_leave(vst, base)
            return
         end if
       end block
    end if
    if (from == 1 .and. gc_kind(native) == OBJ_BUILTIN .and. &
         gc_kind(strip_meta(tv)) /= OBJ_INST .and. .not. gcn_is_var(strip_meta(tv))) then
       ! (target args...) through the native
       call vs_set(vst, base + 3, cons_vec(vs_get(vst, base + 2), vs_get(vst, base + 3), [vs_get(vst, base + 1)]))
       out = apply(native, vs_get(vst, base + 3))
    else
       block
          call sym_text(gc_slot(vs_get(vst, base + 1), 2), s=dlt_1)
          out = eval_dot(vs_get(vst, base + 2), dlt_1, gc_i2(nd) == 1,  vs_get(vst, base + 3), from == 0)
       end block
    end if
    call vs_leave(vst, base)
  end function dot_dispatch


  recursive function exec_setbang(nd, frame) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: nd, frame
    type(gc_value) :: out, tgt, val
    integer :: base
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, nd)
    call vs_set(vst, base + 2, frame)
    select case (gc_i2(nd))
    case (0)
       val = exec(gcv_nth(gc_slot(nd, 1), 0), frame)
       if (.not. tctx%has_error) then
          ! Var.set: this thread's binding
          call gcn_var_set(gc_slot(vs_get(vst, base + 1), 2), val)
          out = val
       end if
    case (2)
       ! (set! (.__methodImplCache f) cache) -- the one host field with
       ! storage, in the closure slot a fn does not otherwise use.
       tgt = strip_meta(exec(gcv_nth(gc_slot(nd, 1), 0), frame))
       if (.not. tctx%has_error) then
          call vs_set(vst, base + 3, tgt)
          val = exec(gcv_nth(gc_slot(vs_get(vst, base + 1), 1), 1), vs_get(vst, base + 2))
          if (.not. tctx%has_error) then
             if (gc_kind(vs_get(vst, base + 3)) == OBJ_CLOSURE) call gc_set_slot(vs_get(vst, base + 3), 5, val)
             out = val
          end if
       end if
    case (3)
       ! Class/field: the value, discarded
       val = exec(gcv_nth(gc_slot(nd, 1), 0), frame)
       if (.not. tctx%has_error) out = val
    case default
       ! any other host field: the write is discarded, the value returned
       tgt = exec(gcv_nth(gc_slot(nd, 1), 0), frame)
       if (.not. tctx%has_error) then
          val = exec(gcv_nth(gc_slot(vs_get(vst, base + 1), 1), 1), vs_get(vst, base + 2))
          if (.not. tctx%has_error) out = val
       end if
    end select
    call vs_leave(vst, base)
  end function exec_setbang

  ! (new user.Name f1 f2) with the arguments already evaluated: the
  ! tail of construct_type, including defrecord's short constructors.
  function construct_type_vals(ty, argv) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: ty, argv
    type(gc_value) :: out, tmp
    character(len=24) :: want, got
    integer :: base, nf, na, drops

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    out = gc_nil()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, ty)
    call vs_set(vst, base + 2, argv)
    nf = gcv_count(gc_slot(vs_get(vst, base + 1), 2))
    na = gcv_count(vs_get(vst, base + 2))
    drops = alt_ctor_drops(gc_slot(vs_get(vst, base + 1), 2))
    if (na /= nf) then
       if (drops > 0 .and. (na == nf - drops .or. na == nf - 2)) then
          tmp = pad_record_fields(vs_get(vst, base + 2), gc_slot(vs_get(vst, base + 1), 2))
          call vs_set(vst, base + 2, tmp)
       else
          write(want, '(I0)') nf
          write(got, '(I0)') na
          block
             call class_text(vs_get(vst, base + 1), s=dlt_1)
             call fail(dlt_1 // " takes " // trim(want) // " fields, given " // trim(got))
          end block
          call vs_leave(vst, base)
          return
       end if
    end if
    out = gc_obj(OBJ_INST, [vs_get(vst, base + 1), vs_get(vst, base + 2), gc_nil()], [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function construct_type_vals
