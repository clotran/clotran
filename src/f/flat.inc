  ! ===================================================================
  ! flat.inc -- fn bodies as flat instructions (PLAN.md step 18).
  ! Included into Eval.f90.
  !
  ! An arity whose nodes are all ones this file knows gets, beside its
  ! tree, a CODE vector: fixed-width instructions over numbered
  ! registers. The registers are the fn's frame -- its locals, and
  ! temporaries above them -- so closures, captures, locals clearing,
  ! a break's view of the locals and the collector see what they see
  ! with the tree. Running it is one dispatch per instruction and no
  ! continuation frame per node; a call to an interpreted fn still
  ! pushes one frame for the callee, and this body waits in its own
  ! with the instruction counter, so a suspended context is still data.
  !
  ! Temporaries are used once: whatever reads one clears it, so a
  ! temporary never holds the head of a seq a callee is walking -- the
  ! retention step 16 and the apply fix were about.
  ! ===================================================================

  ! One instruction is FW integers (Eval.f90 declares FW and the F_*
  ! opcodes): op and up to five operands. Registers are frame slots
  ! (0-based); constants index the arity's constant vector (0-based);
  ! labels are code positions (1-based).

  ! --- the compiler -------------------------------------------------

  ! The flat form of one arity, or nil when it holds a node this file
  ! does not compile. `tbase` is the fn's slot count: temporaries go
  ! above it, and `ntemp` answers how many this arity needed.
  function flat_compile(ar, tbase, ntemp, roots) result(fl)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: ar
    integer, intent(in) :: tbase
    integer, intent(out) :: ntemp
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: fl, body, code, consts, c
    type(flat_buf) :: fb
    integer :: base, i, n
    vst => gc_my_stack()
    fl = gc_nil()
    ntemp = 0
    if (.not. flat_enabled()) return
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, ar)
    body = gcv_nth(ar, 3)
    call vs_set(vst, base + 2, body)
    call vs_set(vst, base + 3, gcv_empty([roots, vs_get(vst, base + 1)]))
    fb%cslot = base + 3
    fb%tbase = tbase
    allocate(fb%code(256))
    call fc(fb, vs_get(vst, base + 2), fb_temp(fb))
    if (fb%ok) call fb_emit(fb, F_RET, fb%tbase, 0, 0, 0, 0)
    ! a recur out of a node the tree runs nested would come back to
    ! this frame as the recur marker, which the flat body has no
    ! answer for: such an arity stays a tree
    if (fb%has_eval .and. fb%has_recur) fb%ok = .false.
    if (.not. fb%ok) then
       call vs_leave(vst, base)
       return
    end if
    n = fb%n
    code = gc_vec(n, [roots, vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, code)
    do i = 1, n
       call gc_vec_set(vs_get(vst, base + 4), i, gc_int(fb%code(i)))
    end do
    ! the constants as a raw vector too: read by index at run time
    n = gcv_count(vs_get(vst, base + 3))
    consts = gc_vec(n, [roots, vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)])
    do i = 1, n
       call gc_vec_set(consts, i, gcv_nth(vs_get(vst, base + 3), i - 1))
    end do
    call vs_set(vst, base + 3, consts)
    fl = mk_node(N_FLAT, gc_nil(), vs_get(vst, base + 4), vs_get(vst, base + 3), fb%maxtemp, &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    ! where the body is, for a break; the tree itself in slot 5
    c = gc_slot(vs_get(vst, base + 2), 4)
    call gc_set_slot(fl, 4, c)
    call gc_set_slot(fl, 5, vs_get(vst, base + 2))
    ntemp = fb%maxtemp
    call vs_leave(vst, base)
  end function flat_compile

  ! CLOTRAN_FLAT=0 compiles nothing, so every body runs as a tree: the
  ! gate's comparison, and the way to rule this file out of a bug.
  logical function flat_enabled()
    character(len=8) :: e
    if (flat_mode == 0) then
       call get_environment_variable("CLOTRAN_FLAT", e)
       if (trim(e) == "0") then
          flat_mode = 2
       else
          flat_mode = 1
       end if
    end if
    flat_enabled = flat_mode == 1
  end function flat_enabled

  subroutine fb_emit(fb, op, a, b, c, d, e)
    type(flat_buf), intent(inout) :: fb
    integer, intent(in) :: op, a, b, c, d, e
    integer, allocatable :: bigger(:)
    if (fb%n + FW > size(fb%code)) then
       allocate(bigger(2 * size(fb%code)))
       bigger(1:fb%n) = fb%code(1:fb%n)
       call move_alloc(bigger, fb%code)
    end if
    fb%code(fb%n + 1:fb%n + FW) = [op, a, b, c, d, e]
    fb%n = fb%n + FW
  end subroutine fb_emit

  ! the next temporary register
  integer function fb_temp(fb) result(r)
    type(flat_buf), intent(inout) :: fb
    r = fb%tbase + fb%ntemp
    fb%ntemp = fb%ntemp + 1
    fb%maxtemp = max(fb%maxtemp, fb%ntemp)
  end function fb_temp

  ! v's index among the constants, added
  integer function fb_const(fb, v) result(k)
    type(flat_buf), intent(inout) :: fb
    type(gc_value), intent(in) :: v
    type(gc_stack), pointer :: vst
    type(gc_value) :: cs
    vst => gc_my_stack()
    k = gcv_count(vs_get(vst, fb%cslot))
    cs = gcv_conj(vs_get(vst, fb%cslot), v, [v])
    call vs_set(vst, fb%cslot, cs)
  end function fb_const

  ! Code that leaves nd's value in register d.
  recursive subroutine fc(fb, nd, d)
    type(flat_buf), intent(inout) :: fb
    type(gc_value), intent(in) :: nd
    integer, intent(in) :: d
    type(gc_value) :: kids, v, rinfo
    integer :: kind, n, i, t, mark, j1, j2, a, f, start, site, lbl

    if (.not. fb%ok) return
    if (gc_kind(nd) /= OBJ_AST) then
       fb%ok = .false.
       return
    end if
    kind = gc_i1(nd)
    kids = gc_slot(nd, 1)
    mark = fb%ntemp
    select case (kind)
    case (N_CONST)
       v = gc_slot(nd, 2)
       if (v%tag == GCT_NIL) then
          call fb_emit(fb, F_NIL, d, 0, 0, 0, 0)
       else
          call fb_emit(fb, F_CONST, d, fb_const(fb, v), 0, 0, 0)
       end if
    case (N_LOCAL)
       if (tag_of(gc_slot(nd, 3)) == GCT_BOOL) then
          call fb_emit(fb, F_MOVEC, d, gc_i2(nd), 0, 0, 0)
       else
          call fb_emit(fb, F_MOVE, d, gc_i2(nd), 0, 0, 0)
       end if
    case (N_VAR)
       call fb_emit(fb, F_VAR, d, fb_const(fb, gc_slot(nd, 2)), 0, 0, 0)
    case (N_IF)
       t = fb_temp(fb)
       call fc(fb, gcv_nth(kids, 0), t)
       j1 = fb%n + 1
       call fb_emit(fb, F_JMPF, t, 0, 0, 0, 0)
       fb%ntemp = mark
       call fc(fb, gcv_nth(kids, 1), d)
       j2 = fb%n + 1
       call fb_emit(fb, F_JMP, 0, 0, 0, 0, 0)
       fb%code(j1 + 2) = fb%n + 1
       if (gcv_count(kids) > 2) then
          call fc(fb, gcv_nth(kids, 2), d)
       else
          call fb_emit(fb, F_NIL, d, 0, 0, 0, 0)
       end if
       fb%code(j2 + 1) = fb%n + 1
    case (N_DO)
       n = gcv_count(kids)
       if (n == 0) then
          call fb_emit(fb, F_NIL, d, 0, 0, 0, 0)
       else
          do i = 0, n - 2
             t = fb_temp(fb)
             call fc(fb, gcv_nth(kids, i), t)
             call fb_emit(fb, F_NIL, t, 0, 0, 0, 0)   ! a discarded value is let go
             fb%ntemp = mark
          end do
          call fc(fb, gcv_nth(kids, n - 1), d)
       end if
    case (N_LET, N_LOOP)
       n = gc_i2(nd)
       start = int_of(gc_slot(nd, 2))
       do i = 0, n - 1
          call fc(fb, gcv_nth(kids, i), start + i)
       end do
       if (kind == N_LOOP) then
          if (fb%nloop >= size(fb%loops)) then
             fb%ok = .false.
             return
          end if
          fb%nloop = fb%nloop + 1
          fb%loops(fb%nloop) = fb%n + 1
       end if
       call fc(fb, gcv_nth(kids, n), d)
       if (kind == N_LOOP) fb%nloop = fb%nloop - 1
    case (N_RECUR)
       fb%has_recur = .true.
       n = gcv_count(kids)
       a = fb%tbase + fb%ntemp
       do i = 0, n - 1
          t = fb_temp(fb)
       end do
       do i = 0, n - 1
          call fc(fb, gcv_nth(kids, i), a + i)
       end do
       rinfo = gc_slot(nd, 2)
       start = int_of(gcv_nth(rinfo, 1))
       if (int_of(gcv_nth(rinfo, 0)) == 0) then
          if (fb%nloop == 0) then
             fb%ok = .false.
             return
          end if
          lbl = fb%loops(fb%nloop)
       else
          lbl = 1   ! the fn's own recur: its parameters, then the body again
       end if
       call fb_emit(fb, F_RECUR, start, min(n, int_of(gcv_nth(rinfo, 2))), a, lbl, 0)
    case (N_CALL)
       n = gcv_count(kids) - 1
       f = fb_temp(fb)
       a = fb%tbase + fb%ntemp
       do i = 0, n - 1
          t = fb_temp(fb)
       end do
       v = gcv_nth(kids, 0)
       if (gc_kind(v) == OBJ_AST .and. gc_i1(v) == N_VAR .and. gc_i2(v) == 1) then
          call fb_emit(fb, F_DLVAR, f, fb_const(fb, v), 0, 0, 0)
       else
          call fc(fb, v, f)
       end if
       do i = 0, n - 1
          call fc(fb, gcv_nth(kids, i + 1), a + i)
       end do
       v = gc_slot(nd, 4)
       site = 0
       if (v%tag == GCT_INT) site = int(v%ival, kind=4)
       call fb_emit(fb, F_CALL, d, f, a, n, site)
    case (N_FN)
       call fb_emit(fb, F_FN, d, fb_const(fb, gc_slot(nd, 2)), 0, 0, 0)
    case (N_LAZY)
       call fb_emit(fb, F_LAZY, d, fb_const(fb, gc_slot(nd, 2)), 0, 0, 0)
    case (N_VECTOR, N_MAP, N_SET)
       n = gcv_count(kids)
       a = fb%tbase + fb%ntemp
       do i = 0, n - 1
          t = fb_temp(fb)
       end do
       do i = 0, n - 1
          call fc(fb, gcv_nth(kids, i), a + i)
       end do
       call fb_emit(fb, F_COLL, d, a, n, kind, 0)
    case (N_THROW)
       t = fb_temp(fb)
       call fc(fb, gcv_nth(kids, 0), t)
       call fb_emit(fb, F_THROW, t, 0, 0, 0, 0)
    case (N_DEF, N_DEFTYPE, N_LATEVAR, N_LETFN, N_NEW, N_NEWTYPE, N_SETBANG, N_FAIL)
       ! what the tree itself runs nested (exec_other), run the same way
       fb%has_eval = .true.
       call fb_emit(fb, F_EVAL, d, fb_const(fb, nd), 0, 0, 0)
    case default
       ! try, case, a host `.` call: stage 2
       fb%ok = .false.
    end select
    fb%ntemp = mark
  end subroutine fc

  ! The body a closure's arity runs: its flat form when it has one.
  function arity_body(ar) result(body)
    type(gc_value), intent(in) :: ar
    type(gc_value) :: body, fl
    body = gcv_nth(ar, 3)
    if (gcv_count(ar) < 5) return
    ! off means off, for an image made with it on as well
    if (.not. flat_enabled()) return
    fl = gcv_nth(ar, 4)
    if (fl%tag /= GCT_NIL) body = fl
  end function arity_body

  ! --- the executor --------------------------------------------------

  ! Runs the flat body on top of the continuation stack until it
  ! answers (k_finish), calls an interpreted fn (its frame pushed; this
  ! one resumes with the answer), fails, or yields. Frame slots of the
  ! body's continuation frame: 1 the node, 2 the registers, 3 the
  ! callee being called, 4 an interpreted callee's frame, back to the
  ! pool when it answers, 6 a call's arguments while it is parked.
  ! kst%pc is the next instruction; kst%aux, when set, is 1 + the
  ! register a pending callee's answer goes to; kst%i = -1 says the
  ! call at pc yielded and is dispatched again.
  recursive subroutine flat_run(tctx, vbase, val)
    type(eval_ctx), pointer, intent(in) :: tctx
    integer, intent(in) :: vbase
    type(gc_value), intent(inout) :: val
    type(gc_stack), pointer :: vst
    type(gc_value) :: nd, code, consts, fr, v, fnv, argv, body, newframe, wb, ar
    integer :: b, ks, pc, j, n, start, w(6), id
    logical :: ok, spare, scalar
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1

    vst => tctx%stk
    ks = tctx%ksp
    b = tctx%kst(ks)%base
    nd = vs_get(vst, b + 1)
    code = gc_slot(nd, 2)
    consts = gc_slot(nd, 3)
    fr = vs_get(vst, b + 2)
    ! a fresh entry: k_push does not reset aux
    if (tctx%kst(ks)%pc == 0) tctx%kst(ks)%aux = 0
    if (tctx%kst(ks)%aux > 0) then
       ! an interpreted callee answered
       call give_frame(vs_get(vst, b + 4))
       call vs_set(vst, b + 4, gc_nil())
       call frame_set(fr, tctx%kst(ks)%aux - 1, val)
       tctx%kst(ks)%aux = 0
    end if
    ! the loop's value slot held that answer; a builtin walking a seq
    ! must not find its head rooted there (as N_CALL's case 4)
    val = gc_nil()
    call vs_set(vst, vbase + 1, gc_nil())
    pc = tctx%kst(ks)%pc
    if (pc == 0) pc = 1

    do
       call gc_vec_word(code, pc, w)
       select case (w(1))
       case (F_CONST)
          call frame_set(fr, w(2), gc_vec_get(consts, w(3) + 1))
       case (F_NIL)
          call frame_set(fr, w(2), gc_nil())
       case (F_MOVE)
          call frame_set(fr, w(2), frame_get(fr, w(3)))
       case (F_MOVEC)
          call frame_set(fr, w(2), frame_get(fr, w(3)))
          call frame_set(fr, w(3), gc_nil())
       case (F_VAR)
          v = var_deref(gc_vec_get(consts, w(3) + 1), [consts])
          call frame_set(fr, w(2), v)
       case (F_DLVAR)
          ! a direct-linked head, as exec.inc's N_CALL reads one
          v = gc_vec_get(consts, w(3) + 1)
          fnv = gc_slot(v, 5)
          if (fnv%tag == GCT_INT) then
             if (fnv%ival /= link_epoch) then
                fnv = gcn_var_value(gc_slot(v, 2))
                if (gc_kind(fnv) == OBJ_COMPILED) call gc_set_slot(v, 3, fnv)
                call gc_set_slot(v, 5, gc_int(int(link_epoch, gc_ip)))
             end if
             call frame_set(fr, w(2), gc_slot(v, 3))
          else
             fnv = var_deref(gc_slot(v, 2), [consts])
             call frame_set(fr, w(2), fnv)
          end if
       case (F_JMPF)
          v = frame_get(fr, w(2))
          call frame_set(fr, w(2), gc_nil())
          if (.not. truthy(v)) then
             pc = w(3)
             cycle
          end if
       case (F_JMP)
          pc = w(2)
          cycle
       case (F_RET)
          val = frame_get(fr, w(2))
          call frame_set(fr, w(2), gc_nil())
          call k_finish(val, tctx)
          return
       case (F_RECUR)
          do j = 0, w(3) - 1
             call frame_set(fr, w(2) + j, frame_get(fr, w(4) + j))
             call frame_set(fr, w(4) + j, gc_nil())
          end do
          ! a SAFEPOINT per turn, as the run loop has per step: a loop
          ! that allocates nothing still stops for a collection
          if (gc_stop_pending()) call gc_poll()
          pc = w(5)
          cycle
       case (F_FN)
          v = make_closure_from(gc_vec_get(consts, w(3) + 1), fr, [nd])
          call frame_set(fr, w(2), v)
       case (F_LAZY)
          v = make_closure_from(gc_vec_get(consts, w(3) + 1), fr, [nd])
          call vs_set(vst, b + 3, v)
          v = gc_obj(OBJ_LAZY, [vs_get(vst, b + 3), gc_nil(), gc_nil()], [vs_get(vst, b + 3)])
          call gc_set_i1(v, LAZY_PENDING)
          call vs_set(vst, b + 3, gc_nil())
          call frame_set(fr, w(2), v)
       case (F_COLL)
          n = w(4)
          argv = gcv_build(n, [nd])
          call vs_set(vst, b + 6, argv)
          do j = 0, n - 1
             argv = gcv_put(vs_get(vst, b + 6), j, frame_get(fr, w(3) + j), [nd])
             call vs_set(vst, b + 6, argv)
             call frame_set(fr, w(3) + j, gc_nil())
          end do
          select case (w(5))
          case (N_VECTOR); v = vs_get(vst, b + 6)
          case (N_SET);    v = vec_to_set(vs_get(vst, b + 6), [nd])
          case default;    v = vec_to_map(vs_get(vst, b + 6), [nd])
          end select
          call vs_set(vst, b + 6, gc_nil())
          if (tctx%has_error) exit
          call frame_set(fr, w(2), v)
       case (F_THROW)
          v = frame_get(fr, w(2))
          call frame_set(fr, w(2), gc_nil())
          call set_thrown(v)
          tctx%has_error = .true.
          block
             call gcp_str(v, .true., s=dlt_1)
             tctx%last_error = dlt_1
          end block
          call capture_trace()
          exit
       case (F_EVAL)
          v = exec(gc_vec_get(consts, w(3) + 1), fr)
          if (tctx%has_error) exit
          call frame_set(fr, w(2), v)
       case (F_CALL)
          ! w: F_CALL d f a n site
          n = w(5)
          ! where this body is while the call runs, for a break
          ! (break_frames); pc too, which a builtin that breaks reads
          tctx%kst(ks)%aux2 = w(6)
          tctx%kst(ks)%pc = pc
          if (tctx%kst(ks)%i == -1) then
             ! the call yielded last time: dispatched again as it was
             tctx%kst(ks)%i = 0
             argv = vs_get(vst, b + 6)
             call vs_set(vst, b + 6, gc_nil())
             tctx%pending_site = w(6)
             v = apply(vs_get(vst, b + 3), argv)
             if (tctx%yield_flag) then
                call vs_set(vst, b + 6, argv)
                tctx%kst(ks)%i = -1
                exit
             end if
             call vs_set(vst, b + 3, gc_nil())
             if (tctx%has_error) exit
             call frame_set(fr, w(2), v)
             pc = pc + FW
             cycle
          end if
          v = frame_get(fr, w(3))
          call frame_set(fr, w(3), gc_nil())
          fnv = strip_meta(v)
          if (gcn_is_var(fnv)) fnv = gcn_var_value(fnv)
          call vs_set(vst, b + 3, fnv)
          ! a core wrapper called with its arity: its builtin, with the
          ! wrapper's call-stack entry around it (analyze.inc
          ! wrapper_builtin)
          wb = wrapper_of(fnv, n)
          if (wb%tag /= GCT_NIL) fnv = wb
          if (gc_kind(fnv) == OBJ_BUILTIN .and. gc_i1(fnv) /= B_RTFN .and. gc_i1(fnv) /= B_UUIDFN) then
             id = gc_i1(fnv)
             scalar = n >= 1 .and. n <= 2 .and. scalar_builtin(id)
             spare = .not. scalar .and. n >= 1 .and. n <= ARG_SPARE_MAX .and. args_reusable(id)
             if (scalar) then
                argv = scratch_args(n)
                do j = 1, n
                   call gc_vec_set(gc_slot(argv, 1), j, frame_get(fr, w(4) + j - 1))
                end do
             else if (spare) then
                argv = args_take(n, [nd])
                do j = 1, n
                   call gc_vec_set(gc_slot(argv, 1), j, frame_get(fr, w(4) + j - 1))
                end do
             else
                argv = flat_args(fr, w(4), n, b)
             end if
             do j = 0, n - 1
                call frame_set(fr, w(4) + j, gc_nil())
             end do
             if (wb%tag /= GCT_NIL) then
                call push_frame(tctx, vs_get(vst, b + 3), w(6))
                if (tctx%has_error) exit
             end if
             if (scalar .or. spare) then
                call vs_set(vst, b + 6, argv)
                tctx%pending_site = w(6)
                v = call_builtin(id, argv)
                if (spare) call args_give(vs_get(vst, b + 6), n)
                call vs_set(vst, b + 6, gc_nil())
             else
                tctx%pending_site = w(6)
                v = apply(fnv, argv)
                if (tctx%yield_flag) then
                   if (wb%tag /= GCT_NIL) call pop_frame(tctx)
                   ! parked: dispatched again, as the fn that was called
                   call vs_set(vst, b + 6, argv)
                   tctx%kst(ks)%i = -1
                   exit
                end if
             end if
             if (wb%tag /= GCT_NIL) call pop_frame(tctx)
             call vs_set(vst, b + 3, gc_nil())
             if (tctx%has_error) exit
             call frame_set(fr, w(2), v)
          else if (is_node_closure(fnv)) then
             ! an interpreted fn: its body in a frame of its own, this
             ! one waiting at the next instruction for the answer
             j = fixed_arity(fnv, n)
             if (j >= 0) then
                ar = gcv_nth(gcv_nth(gc_slot(fnv, 1), 1), j)
                start = int_of(gcv_nth(ar, 2))
                newframe = new_frame(int_of(gcv_nth(gc_slot(fnv, 1), 3)), [vs_get(vst, b + 3)])
                call vs_set(vst, b + 4, newframe)
                do j = 0, n - 1
                   call frame_set(newframe, start + j, frame_get(fr, w(4) + j))
                   call frame_set(fr, w(4) + j, gc_nil())
                end do
                call push_frame(tctx, vs_get(vst, b + 3), w(6))
                if (tctx%has_error) exit
                call bind_captures(vs_get(vst, b + 3), vs_get(vst, b + 4))
                body = arity_body(ar)
             else
                argv = flat_args(fr, w(4), n, b)
                do j = 0, n - 1
                   call frame_set(fr, w(4) + j, gc_nil())
                end do
                call push_frame(tctx, vs_get(vst, b + 3), w(6))
                if (tctx%has_error) exit
                ok = bind_closure(vs_get(vst, b + 3), argv, newframe, body)
                if (.not. ok) then
                   call pop_frame(tctx)
                   exit
                end if
                call vs_set(vst, b + 4, newframe)
             end if
             tctx%kst(ks)%pc = pc + FW
             tctx%kst(ks)%aux = w(2) + 1
             fnv = vs_get(vst, b + 3)
             call vs_set(vst, b + 3, gc_nil())
             call k_push(body, vs_get(vst, b + 4), ior(KF_FNBODY, KF_RESTART), body, tctx)
             call vs_set(vst, tctx%kst(tctx%ksp)%base + 7, fnv)
             if (step_at /= 0) call step_check()
             return
          else
             ! anything else callable: a keyword, a map, a compiled fn,
             ! a multimethod -- through apply, which may yield
             argv = flat_args(fr, w(4), n, b)
             do j = 0, n - 1
                call frame_set(fr, w(4) + j, gc_nil())
             end do
             tctx%pending_site = w(6)
             v = apply(vs_get(vst, b + 3), argv)
             if (tctx%yield_flag) then
                call vs_set(vst, b + 6, argv)
                tctx%kst(ks)%i = -1
                exit
             end if
             call vs_set(vst, b + 3, gc_nil())
             if (tctx%has_error) exit
             call frame_set(fr, w(2), v)
          end if
       case default
          call raise_class("IllegalStateException", "flat: bad instruction", [gc_value ::])
          exit
       end select
       pc = pc + FW
    end do
    ! failed or parked: the instruction stays where it was
    tctx%kst(ks)%pc = pc
  end subroutine flat_run

  ! A call's n arguments, registers a.. of fr, as a vector (rooted in
  ! the body's frame slot 6 while it is filled).
  function flat_args(fr, a, n, b) result(argv)
    type(gc_value), intent(in) :: fr
    integer, intent(in) :: a, n, b
    type(gc_value) :: argv
    type(gc_stack), pointer :: vst
    integer :: j
    vst => gc_my_stack()
    argv = gcv_build(n, [fr])
    call vs_set(vst, b + 6, argv)
    do j = 0, n - 1
       argv = gcv_put(vs_get(vst, b + 6), j, frame_get(fr, a + j), [fr])
       call vs_set(vst, b + 6, argv)
    end do
    call vs_set(vst, b + 6, gc_nil())
  end function flat_args
