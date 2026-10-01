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
    type(gc_value), intent(in) :: ar
    integer, intent(in) :: tbase
    integer, intent(out) :: ntemp
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: fl
    fl = flat_compile_body(gcv_nth(ar, 3), tbase, ntemp, [roots, ar])
  end function flat_compile

  ! The same for any body over a frame of tbase slots: an arity's, or
  ! a top-level form's (analyze_top), which is the REPL's.
  function flat_compile_body(body0, tbase, ntemp, roots) result(fl)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: body0
    integer, intent(in) :: tbase
    integer, intent(out) :: ntemp
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: fl, code, consts, c
    type(flat_buf) :: fb
    integer :: base, i, n
    vst => gc_my_stack()
    fl = gc_nil()
    ntemp = 0
    if (.not. flat_enabled()) return
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 2, body0)
    call vs_set(vst, base + 3, gcv_empty([roots, vs_get(vst, base + 1)]))
    fb%cslot = base + 3
    fb%tbase = tbase
    allocate(fb%code(256))
    call fc(fb, vs_get(vst, base + 2), fb_temp(fb))
    if (fb%ok) call fb_emit(fb, F_RET, fb%tbase, 0, 0, 0, 0)
    ! (a recur out of a node the tree runs nested is refused where that
    ! node is compiled: node_has_recur)
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
  end function flat_compile_body

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

  subroutine fb_emit(fb, op, a, b, c, d, e, f, g)
    type(flat_buf), intent(inout) :: fb
    integer, intent(in) :: op, a, b, c, d, e
    integer, intent(in), optional :: f, g
    integer :: f1, g1
    integer, allocatable :: bigger(:)
    if (fb%n + FW > size(fb%code)) then
       allocate(bigger(2 * size(fb%code)))
       bigger(1:fb%n) = fb%code(1:fb%n)
       call move_alloc(bigger, fb%code)
    end if
    f1 = 0
    g1 = 0
    if (present(f)) f1 = f
    if (present(g)) g1 = g
    fb%code(fb%n + 1:fb%n + FW) = [op, a, b, c, d, e, f1, g1]
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
    integer :: kind, n, i, t, mark, j1, j2, a, f, start, site, lbl, ra(2)

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
          fb%looptry(fb%nloop) = fb%ntry
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
          ! a jump out of a try would leave its handler installed
          if (fb%looptry(fb%nloop) /= fb%ntry) then
             fb%ok = .false.
             return
          end if
          lbl = fb%loops(fb%nloop)
       else
          if (fb%ntry /= 0) then
             fb%ok = .false.
             return
          end if
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
       ! a builtin head, folded at analysis: called by constant, no
       ! head register (flat_run's F_CALLB)
       if (gc_kind(v) == OBJ_AST .and. gc_i1(v) == N_CONST) then
          if (gc_kind(strip_meta(gc_slot(v, 2))) == OBJ_BUILTIN) then
             if (gc_i1(strip_meta(gc_slot(v, 2))) /= B_RTFN .and. gc_i1(strip_meta(gc_slot(v, 2))) /= B_UUIDFN) then
                ! the first two arguments by register: a local that is
                ! not cleared here is read where it is, with no move --
                ! when nothing evaluated after it could clear it: (f x (g x))
                ! clears x in its second argument, before the call reads
                ! the first
                ra = [a, a + 1]
                do i = 0, n - 1
                   v = gcv_nth(kids, i + 1)
                   if (n <= 2 .and. gc_kind(v) == OBJ_AST .and. flat_quiet_after(kids, i + 2)) then
                      if (gc_i1(v) == N_LOCAL .and. tag_of(gc_slot(v, 3)) /= GCT_BOOL) then
                         ra(i + 1) = gc_i2(v)
                         cycle
                      end if
                   end if
                   call fc(fb, v, a + i)
                end do
                v = gc_slot(nd, 4)
                site = 0
                if (v%tag == GCT_INT) site = int(v%ival, kind=4)
                call fb_emit(fb, F_CALLB, d, fb_const(fb, strip_meta(gc_slot(gcv_nth(kids, 0), 2))), a, n, site, ra(1), ra(2))
                fb%ntemp = mark
                return
             end if
          end if
       end if
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
    case (N_DOT)
       ! (. target member args...): the target in a (unless it is a
       ! class, which the node holds), the arguments after it
       n = gcv_count(kids)
       a = fb%tbase + fb%ntemp
       do i = 0, n - 1
          t = fb_temp(fb)
       end do
       do i = 0, n - 1
          call fc(fb, gcv_nth(kids, i), a + i)
       end do
       f = 1
       if (tag_of(gc_slot(nd, 3)) == GCT_SYM) f = 0
       v = gc_slot(nd, 4)
       site = 0
       if (v%tag == GCT_INT) site = int(v%ival, kind=4)
       call fb_emit(fb, F_DOT, d, fb_const(fb, nd), a, n - f, f, site)
    case (N_CASE)
       ! the test, then the table's answer (case_branch, the tree's own
       ! walk) as a jump: every distinct branch compiled here with its
       ! label, the labels in the constants beside the branch nodes
       t = fb_temp(fb)
       call fc(fb, gcv_nth(kids, 0), t)
       call fc_case(fb, nd, t, d)
    case (N_TRY)
       call fc_try(fb, nd, d)
    case (N_THROW)
       t = fb_temp(fb)
       call fc(fb, gcv_nth(kids, 0), t)
       call fb_emit(fb, F_THROW, t, 0, 0, 0, 0)
    case (N_NEW, N_NEWTYPE)
       ! the arguments in registers, then new_cached with the node
       n = gcv_count(kids)
       a = fb%tbase + fb%ntemp
       do i = 0, n - 1
          t = fb_temp(fb)
       end do
       do i = 0, n - 1
          call fc(fb, gcv_nth(kids, i), a + i)
       end do
       call fb_emit(fb, F_NEW, d, fb_const(fb, nd), a, n, 0)
    case (N_DEF, N_DEFTYPE, N_LATEVAR, N_LETFN, N_SETBANG, N_FAIL)
       ! what the tree itself runs nested (exec_other), run the same way --
       ! unless a recur of this body is inside it (node_has_recur)
       fb%has_eval = .true.
       if (node_has_recur(nd)) then
          fb%ok = .false.
          return
       end if
       call fb_emit(fb, F_EVAL, d, fb_const(fb, nd), 0, 0, 0)
    case default
       ! what is left: the top-level forms, which are not in a body
       fb%ok = .false.
    end select
    fb%ntemp = mark
  end subroutine fc

  ! Whether kids from..end are constants and locals not cleared there:
  ! nothing in them runs, so nothing can clear a local read before them.
  logical function flat_quiet_after(kids, from) result(quiet)
    type(gc_value), intent(in) :: kids
    integer, intent(in) :: from
    type(gc_value) :: k
    integer :: j
    quiet = .true.
    do j = from, gcv_count(kids) - 1
       k = gcv_nth(kids, j)
       if (gc_kind(k) /= OBJ_AST) then
          quiet = .false.
       else if (gc_i1(k) == N_CONST) then
          cycle
       else if (gc_i1(k) == N_LOCAL .and. tag_of(gc_slot(k, 3)) /= GCT_BOOL) then
          cycle
       else
          quiet = .false.
       end if
       if (.not. quiet) return
    end do
  end function flat_quiet_after

  ! v's index among the constants, reusing one already there when it
  ! is the same object (a case table names a branch under many keys)
  integer function fb_const_same(fb, v, from) result(k)
    type(flat_buf), intent(inout) :: fb
    type(gc_value), intent(in) :: v
    integer, intent(in) :: from
    type(gc_stack), pointer :: vst
    type(gc_value) :: c
    integer :: i
    vst => gc_my_stack()
    do i = from, gcv_count(vs_get(vst, fb%cslot)) - 1
       c = gcv_nth(vs_get(vst, fb%cslot), i)
       if (c%tag == v%tag .and. c%ref == v%ref) then
          k = i
          return
       end if
    end do
    k = fb_const(fb, v)
  end function fb_const_same

  ! constant k replaced (a label known only once its code is written)
  subroutine fb_const_set(fb, k, v)
    type(flat_buf), intent(inout) :: fb
    integer, intent(in) :: k
    type(gc_value), intent(in) :: v
    type(gc_stack), pointer :: vst
    type(gc_value) :: cs
    vst => gc_my_stack()
    cs = gcv_assoc(vs_get(vst, fb%cslot), k, v, [v])
    call vs_set(vst, fb%cslot, cs)
  end subroutine fb_const_set

  ! case*: F_CASE t k kb m kl -- the node at k, its m distinct branch
  ! nodes at kb.., their labels at kl..
  recursive subroutine fc_case(fb, nd, t, d)
    type(flat_buf), intent(inout) :: fb
    type(gc_value), intent(in) :: nd
    integer, intent(in) :: t, d
    type(gc_value) :: e
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: kc, kb, kl, m, i, j, ends(4096), nends
    kc = fb_const(fb, nd)
    ! the default first, then the table's, each once
    kb = fb_const(fb, gcv_nth(gc_slot(nd, 1), 1))
    m = 1
    call gca_entries(gc_slot(nd, 2), ks, vls)
    do i = 1, size(ks)
       e = strip_meta(vls(i))
       if (.not. gcv_is(e)) cycle
       if (gcv_count(e) /= 2) cycle
       j = fb_const_same(fb, gcv_nth(e, 1), kb)
       if (j == kb + m) m = m + 1
    end do
    if (m > size(ends)) then
       fb%ok = .false.
       return
    end if
    kl = fb%n   ! placeholder: the label constants follow
    kl = fb_const(fb, gc_int(0))
    do i = 2, m
       j = fb_const(fb, gc_int(0))
    end do
    call fb_emit(fb, F_CASE, t, kc, kb, m, kl)
    nends = 0
    do i = 0, m - 1
       block
         type(gc_stack), pointer :: vst
         vst => gc_my_stack()
         call fb_const_set(fb, kl + i, gc_int(fb%n + 1))
         call fc(fb, gcv_nth(vs_get(vst, fb%cslot), kb + i), d)
       end block
       if (.not. fb%ok) return
       nends = nends + 1
       ends(nends) = fb%n + 1
       call fb_emit(fb, F_JMP, 0, 0, 0, 0, 0)
    end do
    do i = 1, nends
       fb%code(ends(i) + 1) = fb%n + 1
    end do
  end subroutine fc_case

  ! try/catch/finally in the frame itself. F_TRY sv L saves the
  ! frame's handler (kst%mode) and the call-stack depth in sv, sv+1 and
  ! installs L; an error unwinding to this frame lands at L with the
  ! exception in sv+2 and its message in sv+3 (flat_catch). There each
  ! catch is tried in turn (F_CATCH); with a finally, the catches run
  ! under a second handler so a catch that throws still runs it; an
  ! exception no catch takes runs the finally and goes on (F_RETHROW).
  recursive subroutine fc_try(fb, nd, d)
    type(flat_buf), intent(inout) :: fb
    type(gc_value), intent(in) :: nd
    integer, intent(in) :: d
    type(gc_value) :: kids, fin, catches, cl
    integer :: sv, sv2, t, jt, jt2, jn, i, nc, ends(256), nends, k
    logical :: hasfin
    kids = gc_slot(nd, 1)
    fin = gcv_nth(kids, 1)
    hasfin = gc_kind(fin) == OBJ_AST
    catches = gc_slot(nd, 2)
    nc = gcv_count(catches)
    if (nc + 2 > size(ends)) then
       fb%ok = .false.
       return
    end if
    sv = fb_temp(fb)
    k = fb_temp(fb)
    k = fb_temp(fb)
    k = fb_temp(fb)
    t = fb_temp(fb)
    nends = 0
    jt = fb%n + 1
    call fb_emit(fb, F_TRY, sv, 0, 0, 0, 0)
    fb%ntry = fb%ntry + 1
    call fc(fb, gcv_nth(kids, 0), d)
    fb%ntry = fb%ntry - 1
    call fb_emit(fb, F_ENDTRY, sv, 0, 0, 0, 0)
    if (hasfin) then
       call fc(fb, fin, t)
       call fb_emit(fb, F_NIL, t, 0, 0, 0, 0)
    end if
    nends = nends + 1
    ends(nends) = fb%n + 1
    call fb_emit(fb, F_JMP, 0, 0, 0, 0, 0)
    ! the handler
    fb%code(jt + 2) = fb%n + 1
    call fb_emit(fb, F_HANDLER, sv, 0, 0, 0, 0)
    sv2 = -1
    jt2 = 0
    if (hasfin .and. nc > 0) then
       sv2 = fb_temp(fb)
       k = fb_temp(fb)
       k = fb_temp(fb)
       k = fb_temp(fb)
       jt2 = fb%n + 1
       call fb_emit(fb, F_TRY, sv2, 0, 0, 0, 0)
       fb%ntry = fb%ntry + 1
    end if
    do i = 0, nc - 1
       cl = gcv_nth(catches, i)
       jn = fb%n + 1
       call fb_emit(fb, F_CATCH, sv + 2, fb_const(fb, gcv_nth(cl, 0)), int_of(gcv_nth(cl, 1)), 0, 0)
       call fc(fb, gcv_nth(cl, 2), d)
       if (sv2 >= 0) then
          call fb_emit(fb, F_ENDTRY, sv2, 0, 0, 0, 0)
          call fc(fb, fin, t)
          call fb_emit(fb, F_NIL, t, 0, 0, 0, 0)
       end if
       nends = nends + 1
       ends(nends) = fb%n + 1
       call fb_emit(fb, F_JMP, 0, 0, 0, 0, 0)
       fb%code(jn + 4) = fb%n + 1
    end do
    ! no catch took it
    if (sv2 >= 0) then
       call fb_emit(fb, F_ENDTRY, sv2, 0, 0, 0, 0)
       fb%ntry = fb%ntry - 1
    end if
    if (hasfin) then
       call fc(fb, fin, t)
       call fb_emit(fb, F_NIL, t, 0, 0, 0, 0)
    end if
    call fb_emit(fb, F_RETHROW, sv + 2, sv + 3, 0, 0, 0)
    ! a catch that threw, with a finally to run
    if (sv2 >= 0) then
       fb%code(jt2 + 2) = fb%n + 1
       call fb_emit(fb, F_HANDLER, sv2, 0, 0, 0, 0)
       call fc(fb, fin, t)
       call fb_emit(fb, F_NIL, t, 0, 0, 0, 0)
       call fb_emit(fb, F_RETHROW, sv2 + 2, sv2 + 3, 0, 0, 0)
    end if
    do i = 1, nends
       fb%code(ends(i) + 1) = fb%n + 1
    end do
  end subroutine fc_try

  ! An error unwinding to a flat frame with a handler (kst%mode, the
  ! label of its F_HANDLER): the frame is not popped but lands there,
  ! the exception and its message in the try's registers, the outer
  ! handler and the call-stack depth put back, anything the frame was
  ! waiting on let go, and the error cleared -- what k_unwind does for
  ! the tree's N_TRY frame, before its catches are tried.
  subroutine flat_catch(tctx, b)
    type(eval_ctx), pointer, intent(in) :: tctx
    integer, intent(in) :: b
    type(gc_stack), pointer :: vst
    type(gc_value) :: nd, fr, exc, v
    integer :: ks, l, sv, w(FW)
    character(len=:), allocatable :: msg
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => tctx%stk
    ks = tctx%ksp
    l = tctx%kst(ks)%mode
    nd = vs_get(vst, b + 1)
    fr = vs_get(vst, b + 2)
    call gc_vec_word(gc_slot(nd, 2), l, w)
    sv = w(2)
    msg = tctx%last_error
    exc = thrown_value()
    if (exc%tag == GCT_NIL) then
       call gce_error(s=dlt_1)
       exc = error_value(dlt_1, [nd])
    end if
    call reg_set(fr, sv + 2, exc)
    v = gc_str(msg, [nd])
    call reg_set(fr, sv + 3, v)
    v = reg_get(fr, sv)
    tctx%kst(ks)%mode = int(v%ival)
    v = reg_get(fr, sv + 1)
    tctx%fstack_top = min(tctx%fstack_top, int(v%ival))
    call reg_set(fr, sv, gc_nil())
    call reg_set(fr, sv + 1, gc_nil())
    if (tctx%kst(ks)%aux == -1) call flat_release(vs_get(vst, b + 6))
    tctx%kst(ks)%aux = 0
    tctx%kst(ks)%i = 0
    call give_frame(vs_get(vst, b + 4))
    call vs_set(vst, b + 3, gc_nil())
    call vs_set(vst, b + 4, gc_nil())
    call vs_set(vst, b + 6, gc_nil())
    call gce_clear_error()
    tctx%kst(ks)%pc = l
  end subroutine flat_catch

  ! Whether a node holds a recur of ITS OWN fn or loop somewhere beneath
  ! it: a nested fn's or lazy-seq's recurs are that fn's, so their
  ! templates are not entered, and a constant is data. A node the tree
  ! runs nested (F_EVAL) holding one would answer the recur marker to a
  ! flat body with no answer for it, so such an arity stays a tree; a
  ! set!, def or var read beside a loop's recur does not.
  recursive logical function node_has_recur(v) result(yes)
    type(gc_value), intent(in) :: v
    type(gc_value) :: s
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: i, j
    yes = .false.
    if (gcv_is(v)) then
       do i = 0, gcv_count(v) - 1
          if (node_has_recur(gcv_nth(v, i))) then
             yes = .true.
             return
          end if
       end do
       return
    end if
    if (gca_is(v)) then
       call gca_entries(v, ks, vls)
       do i = 1, size(vls)
          if (node_has_recur(strip_meta(vls(i)))) then
             yes = .true.
             return
          end if
       end do
       return
    end if
    if (gc_kind(v) /= OBJ_AST) return
    select case (gc_i1(v))
    case (N_RECUR)
       yes = .true.
    case (N_FN, N_LAZY, N_CONST, N_FLAT)
       continue
    case default
       do j = 1, 3
          s = gc_slot(v, j)
          if (gc_kind(s) == OBJ_AST .or. gcv_is(s) .or. gca_is(s)) then
             if (node_has_recur(s)) then
                yes = .true.
                return
             end if
          end if
       end do
    end select
  end function node_has_recur

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

  ! --- the call table ------------------------------------------------
  !
  ! A fn template's eighth element (analyze_fn): what a call needs, as
  ! a raw vector read by index, where the template itself is persistent
  ! vectors walked one gcv_nth at a time -- ten to fifteen of them per
  ! call, 18% of a loop of calls. 1-based:
  !   1 slots in the frame   2 the self slot or -1   3 captures
  !   4 K, the largest fixed arity in the table
  !   5 + 4n .. 8 + 4n, for n = 0..K arguments: the fixed arity's first
  !     parameter slot or -1, its tree, its flat body or nil, the
  !     builtin it only wraps or nil
  !   then each capture's slot in the frame
  ! Variadic arities and anything past K (CT_MAXFIX, Eval.f90) take
  ! the general road.

  function call_table(tmpl, roots) result(ct)
    type(gc_value), intent(in) :: tmpl
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: ct, ars, ar, caps, wbs, fl
    integer :: k, i, nf, ncap, p, sz
    ars = gcv_nth(tmpl, 1)
    caps = gcv_nth(tmpl, 2)
    wbs = gcv_nth(tmpl, 6)
    ncap = gcv_count(caps) / 2
    k = -1
    do i = 0, gcv_count(ars) - 1
       ar = gcv_nth(ars, i)
       if (.not. truthy(gcv_nth(ar, 1))) k = max(k, int_of(gcv_nth(ar, 0)))
    end do
    k = min(k, CT_MAXFIX)
    sz = 4 + 4 * (k + 1) + ncap
    ct = gc_vec(sz, [roots, tmpl])
    call gc_vec_set(ct, 1, gcv_nth(tmpl, 3))
    call gc_vec_set(ct, 2, gcv_nth(tmpl, 4))
    call gc_vec_set(ct, 3, gc_int(ncap))
    call gc_vec_set(ct, 4, gc_int(k))
    do i = 0, k
       call gc_vec_set(ct, 5 + 4 * i, gc_int(-1))
    end do
    do i = 0, gcv_count(ars) - 1
       ar = gcv_nth(ars, i)
       if (truthy(gcv_nth(ar, 1))) cycle
       nf = int_of(gcv_nth(ar, 0))
       if (nf > k) cycle
       p = 5 + 4 * nf
       call gc_vec_set(ct, p, gcv_nth(ar, 2))
       call gc_vec_set(ct, p + 1, gcv_nth(ar, 3))
       fl = gc_nil()
       if (gcv_count(ar) >= 5) fl = gcv_nth(ar, 4)
       call gc_vec_set(ct, p + 2, fl)
       if (gcv_is(wbs)) call gc_vec_set(ct, p + 3, gcv_nth(wbs, i))
    end do
    do i = 0, ncap - 1
       call gc_vec_set(ct, 5 + 4 * (k + 1) + i, gcv_nth(caps, 2 * i + 1))
    end do
  end function call_table

  ! fn's call table, or nil for a fn made some other way
  function call_table_of(fn) result(ct)
    type(gc_value), intent(in) :: fn
    type(gc_value) :: ct, tm
    ct = gc_nil()
    tm = gc_slot(fn, 1)
    if (.not. gcv_is(tm)) return
    if (gcv_count(tm) < 8) return
    if (gc_kind(gc_slot(fn, 3)) == OBJ_ENV) return
    ct = gcv_nth(tm, 7)
  end function call_table_of

  integer function ct_int(ct, i)
    type(gc_value), intent(in) :: ct
    integer, intent(in) :: i
    type(gc_value) :: t
    t = gc_reg(ct, i)
    ct_int = int(t%ival)
  end function ct_int

  ! A frame for fn's fixed arity at table position p, its captures and
  ! its own name bound; the parameters are the caller's to set. fn and
  ! ct must be rooted by the caller (on its value stack): roots is
  ! passed on as it is, since [roots, fn, ct] is a heap temporary
  ! grown element by element, on every call.
  function ct_frame(fn, ct, roots) result(fr)
    type(gc_value), intent(in) :: fn, ct
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: fr, caps
    integer :: i, ncap, cb, self
    fr = new_frame(ct_int(ct, 1), roots)
    ncap = ct_int(ct, 3)
    if (ncap > 0) then
       cb = 5 + 4 * (ct_int(ct, 4) + 1)
       do i = 0, ncap - 1
          call reg_set(fr, ct_int(ct, cb + i), cap_of(fn, i, ncap))
       end do
    end if
    self = ct_int(ct, 2)
    if (self >= 0) call reg_set(fr, self, fn)
  end function ct_frame

  ! ct_frame's work onto registers on the stack, slots rb+1..: the
  ! captures and the fn's own name; the parameters are the caller's
  subroutine ct_stack_frame(vst, fn, ct, rb)
    type(gc_stack), pointer, intent(in) :: vst
    type(gc_value), intent(in) :: fn, ct
    integer, intent(in) :: rb
    type(gc_value) :: caps
    integer :: i, ncap, cb, self
    ncap = ct_int(ct, 3)
    if (ncap > 0) then
       cb = 5 + 4 * (ct_int(ct, 4) + 1)
       do i = 0, ncap - 1
          vst%vstack(rb + ct_int(ct, cb + i) + 1) = cap_of(fn, i, ncap)
       end do
    end if
    self = ct_int(ct, 2)
    if (self >= 0) vst%vstack(rb + self + 1) = fn
  end subroutine ct_stack_frame

  ! The body table position p runs: flat unless CLOTRAN_FLAT=0
  function ct_body(ct, p) result(body)
    type(gc_value), intent(in) :: ct
    integer, intent(in) :: p
    type(gc_value) :: body
    body = gc_reg(ct, p + 2)
    if (body%tag == GCT_NIL .or. .not. flat_enabled()) body = gc_reg(ct, p + 1)
  end function ct_body

  ! --- the executor --------------------------------------------------

  ! Register r (a 0-based frame slot) of a flat body's frame.
  function reg_get(fr, r) result(v)
    type(gc_value), intent(in) :: fr
    integer, intent(in) :: r
    type(gc_value) :: v
    type(gc_stack), pointer :: vst
    if (fr%tag == GCT_SFRAME) then
       ! the stack of the context running the body (flat_run's tctx%stk)
       vst => ctx_self_stack()
       v = vst%vstack(fr%ref + r + 1)
       return
    end if
    v = vec_store(vec_pool(fr%ref)%off + r)
  end function reg_get

  subroutine reg_set(fr, r, v)
    type(gc_value), intent(in) :: fr, v
    integer, intent(in) :: r
    type(gc_stack), pointer :: vst
    if (fr%tag == GCT_SFRAME) then
       ! the stack of the context running the body (flat_run's tctx%stk)
       vst => ctx_self_stack()
       vst%vstack(fr%ref + r + 1) = v
       return
    end if
    vec_store(vec_pool(fr%ref)%off + r) = v
    if (v%ref /= 0) then
       if (vec_mark(fr%ref) .and. .not. vec_rem(fr%ref)) call gc_reg_barrier(fr, v)
    end if
  end subroutine reg_set

  ! Runs the flat body on top of the continuation stack until it
  ! answers (k_finish), calls an interpreted fn (its frame pushed; this
  ! one resumes with the answer), fails, or yields. Frame slots of the
  ! body's continuation frame: 1 the node, 2 the registers, 3 the
  ! callee being called, 4 an interpreted callee's frame, back to the
  ! pool when it answers, 6 a call's arguments while it is parked.
  ! kst%pc is the next instruction; kst%aux, when set, is 1 + the
  ! register a pending callee's answer goes to; kst%i = -1 says the
  ! call at pc yielded and is dispatched again.
  recursive subroutine flat_run(tctx, kbot, vbase, val)
    type(eval_ctx), pointer, intent(in) :: tctx
    integer, intent(in) :: kbot, vbase
    type(gc_value), intent(inout) :: val
    type(gc_stack), pointer :: vst
    type(gc_value) :: nd, code, consts, fr, v, fnv, argv, body, newframe, wb, ar
    integer :: b, ks, pc, j, n, start, w(FW), id, cb, kb, rb
    logical :: ok, spare, scalar, done
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1

    vst => tctx%stk
    ! A TRAMPOLINE over flat frames: a call into a flat body, and a
    ! return to a flat body waiting on one, go on here rather than back
    ! through the run loop -- never below kbot, the run loop's own floor
    outer: do
    ! the run loop's safepoint, per frame entered; the answer in flight
    ! rooted in its slot while the world is stopped
    if (gc_stop_pending()) then
       call vs_set(vst, vbase + 1, val)
       call gc_poll()
       val = vs_get(vst, vbase + 1)
    end if
    ks = tctx%ksp
    b = tctx%kst(ks)%base
    nd = vs_get(vst, b + 1)
    code = gc_slot(nd, 2)
    consts = gc_slot(nd, 3)
    ! where the code and the constants lie in the vector store, read in
    ! place below: a live vector's payload never moves
    cb = vec_pool(code%ref)%off - 1
    kb = vec_pool(consts%ref)%off - 1
    fr = vs_get(vst, b + 2)
    ! THE REGISTERS ON THE STACK (PLAN 26.2): a frame made on the heap --
    ! by a caller that is not this executor -- is copied onto the value
    ! stack once, on the body's first entry, and the frame that stays in
    ! slot 2 says where; they go when the frame finishes (k_finish)
    ! (k_push did it: there the registers go right above the record, so
    ! they leave with it and take nothing of the caller's with them)
    if (fr%tag /= GCT_SFRAME) error stop "clotran: a flat body entered with its frame not on the stack"
    rb = fr%ref
    ! a fresh entry: k_push does not reset aux
    if (tctx%kst(ks)%pc == 0) tctx%kst(ks)%aux = 0
    if (tctx%kst(ks)%aux == -1) then
       ! a thunk flat_force ran answered: the cell settled, and the
       ! instruction that wanted it runs again
       tctx%kst(ks)%aux = 0
       call give_frame(vs_get(vst, b + 4))
       call vs_set(vst, b + 4, gc_nil())
       call force_settle(vs_get(vst, b + 6), val)
       call flat_release(vs_get(vst, b + 6))
       call vs_set(vst, b + 6, gc_nil())
       val = gc_nil()
       if (tctx%has_error) return
    end if
    if (tctx%kst(ks)%aux > 0) then
       ! an interpreted callee answered
       call give_frame(vs_get(vst, b + 4))
       call vs_set(vst, b + 4, gc_nil())
       vst%vstack(rb + tctx%kst(ks)%aux - 1 + 1) = val
       tctx%kst(ks)%aux = 0
    end if
    ! the loop's value slot held that answer; a builtin walking a seq
    ! must not find its head rooted there (as N_CALL's case 4)
    val = gc_nil()
    call vs_set(vst, vbase + 1, gc_nil())
    pc = tctx%kst(ks)%pc
    if (pc == 0) pc = 1

    do
       w = int(vec_store(cb + pc : cb + pc + FW - 1)%ival)
       select case (w(1))
       case (F_CONST)
          vst%vstack(rb + w(2) + 1) = vec_store(kb + w(3) + 1)
       case (F_NIL)
          vst%vstack(rb + w(2) + 1) = gc_nil()
       case (F_MOVE)
          vst%vstack(rb + w(2) + 1) = vst%vstack(rb + w(3) + 1)
       case (F_MOVEC)
          vst%vstack(rb + w(2) + 1) = vst%vstack(rb + w(3) + 1)
          vst%vstack(rb + w(3) + 1) = gc_nil()
       case (F_VAR)
          v = var_deref(vec_store(kb + w(3) + 1), [consts])
          vst%vstack(rb + w(2) + 1) = v
       case (F_DLVAR)
          ! a direct-linked head, as exec.inc's N_CALL reads one
          v = vec_store(kb + w(3) + 1)
          fnv = gc_slot(v, 5)
          if (fnv%tag == GCT_INT) then
             if (fnv%ival /= link_epoch) then
                fnv = gcn_var_value(gc_slot(v, 2))
                if (gc_kind(fnv) == OBJ_COMPILED) call gc_set_slot(v, 3, fnv)
                call gc_set_slot(v, 5, gc_int(int(link_epoch, gc_ip)))
             end if
             vst%vstack(rb + w(2) + 1) = gc_slot(v, 3)
          else
             fnv = var_deref(gc_slot(v, 2), [consts])
             vst%vstack(rb + w(2) + 1) = fnv
          end if
       case (F_JMPF)
          v = vst%vstack(rb + w(2) + 1)
          vst%vstack(rb + w(2) + 1) = gc_nil()
          if (.not. truthy(v)) then
             pc = w(3)
             cycle
          end if
       case (F_JMP)
          pc = w(2)
          cycle
       case (F_RET)
          val = vst%vstack(rb + w(2) + 1)
          vst%vstack(rb + w(2) + 1) = gc_nil()
          call k_finish(val, tctx)
          ! a flat caller waiting on this answer takes it here
          if (flat_top(tctx, kbot)) then
             if (tctx%kst(tctx%ksp)%aux > 0) cycle outer
          end if
          return
       case (F_RECUR)
          do j = 0, w(3) - 1
             vst%vstack(rb + w(2) + j + 1) = vst%vstack(rb + w(4) + j + 1)
             vst%vstack(rb + w(4) + j + 1) = gc_nil()
          end do
          ! a SAFEPOINT per turn, as the run loop has per step: a loop
          ! that allocates nothing still stops for a collection
          if (gc_stop_pending()) call gc_poll()
          pc = w(5)
          cycle
       case (F_FN)
          v = make_closure_from(vec_store(kb + w(3) + 1), fr, [nd])
          vst%vstack(rb + w(2) + 1) = v
       case (F_LAZY)
          v = make_closure_from(vec_store(kb + w(3) + 1), fr, [nd])
          call vs_set(vst, b + 3, v)
          v = gc_obj(OBJ_LAZY, [vs_get(vst, b + 3), gc_nil(), gc_nil()], [vs_get(vst, b + 3)])
          call gc_set_i1(v, LAZY_PENDING)
          call vs_set(vst, b + 3, gc_nil())
          vst%vstack(rb + w(2) + 1) = v
       case (F_COLL)
          n = w(4)
          argv = gcv_build(n, [nd])
          call vs_set(vst, b + 6, argv)
          do j = 0, n - 1
             argv = gcv_put(vs_get(vst, b + 6), j, vst%vstack(rb + w(3) + j + 1), [nd])
             call vs_set(vst, b + 6, argv)
             vst%vstack(rb + w(3) + j + 1) = gc_nil()
          end do
          select case (w(5))
          case (N_VECTOR); v = vs_get(vst, b + 6)
          case (N_SET);    v = vec_to_set(vs_get(vst, b + 6), [nd])
          case default;    v = vec_to_map(vs_get(vst, b + 6), [nd])
          end select
          call vs_set(vst, b + 6, gc_nil())
          if (tctx%has_error) exit
          vst%vstack(rb + w(2) + 1) = v
       case (F_THROW)
          v = vst%vstack(rb + w(2) + 1)
          vst%vstack(rb + w(2) + 1) = gc_nil()
          call set_thrown(v)
          tctx%has_error = .true.
          block
             call gcp_str(v, .true., s=dlt_1)
             tctx%last_error = dlt_1
          end block
          call capture_trace()
          exit
       case (F_EVAL)
          v = exec(vec_store(kb + w(3) + 1), fr)
          if (tctx%has_error) exit
          vst%vstack(rb + w(2) + 1) = v
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
             vst%vstack(rb + w(2) + 1) = v
             pc = pc + FW
             cycle
          end if
          v = vst%vstack(rb + w(3) + 1)
          vst%vstack(rb + w(3) + 1) = gc_nil()
          fnv = strip_meta(v)
          if (gcn_is_var(fnv)) fnv = gcn_var_value(fnv)
          call vs_set(vst, b + 3, fnv)
          ! (:k x): what apply's keyword road does -- a record's own
          ! lookup, else coll_get -- from the register, where the road
          ! through apply built an argument vector first
          if (fnv%tag == GCT_KEY .and. n == 1) then
             v = vst%vstack(rb + w(4) + 1)
             argv = strip_meta(v)
             ok = .false.
             if (gc_kind(argv) == OBJ_INST) then
                newframe = inst_lookup(argv, fnv, .false., gc_nil(), ok)
             end if
             if (.not. ok) newframe = coll_get(v, fnv)
             vst%vstack(rb + w(4) + 1) = gc_nil()
             call vs_set(vst, b + 3, gc_nil())
             if (tctx%has_error) exit
             vst%vstack(rb + w(2) + 1) = newframe
             pc = pc + FW
             cycle
          end if
          ! an interpreted fn's fixed arity, through its call table
          if (gc_kind(fnv) == OBJ_CLOSURE) then
             ar = call_table_of(fnv)
             if (ar%tag == GCT_VEC) then
                if (n <= ct_int(ar, 4)) then
                   j = 5 + 4 * n
                   start = ct_int(ar, j)
                   if (start >= 0) then
                      wb = gc_reg(ar, j + 3)
                      if (wb%tag /= GCT_NIL .and. step_at == 0) then
                         ! a core wrapper: its builtin, the wrapper's
                         ! call-stack entry around it -- none needed when
                         ! the answer is a slot already there
                         ! two machine integers through + < inc ..., as a
                         ! builtin head's are (F_CALLB): nothing to fail
                         if (n >= 1 .and. n <= 2) then
                            argv = gc_nil()
                            if (n == 2) argv = vst%vstack(rb + w(4) + 1 + 1)
                            if (flat_int_op(gc_i1(wb), n, vst%vstack(rb + w(4) + 1), argv, newframe)) then
                               vst%vstack(rb + w(4) + 1) = gc_nil()
                               if (n == 2) vst%vstack(rb + w(4) + 1 + 1) = gc_nil()
                               call vs_set(vst, b + 3, gc_nil())
                               vst%vstack(rb + w(2) + 1) = newframe
                               pc = pc + FW
                               cycle
                            end if
                         end if
                         if (n == 1) then
                            if (flat_seq_op(gc_i1(wb), vst%vstack(rb + w(4) + 1), newframe)) then
                               vst%vstack(rb + w(4) + 1) = gc_nil()
                               call vs_set(vst, b + 3, gc_nil())
                               vst%vstack(rb + w(2) + 1) = newframe
                               pc = pc + FW
                               cycle
                            end if
                            newframe = flat_force_target(gc_i1(wb), vst%vstack(rb + w(4) + 1))
                            if (newframe%tag /= GCT_NIL) then
                               ! the call runs again once the cell is
                               ! settled: its argument register is still
                               ! set, and its head goes back into its own
                               fnv = vs_get(vst, b + 3)
                               vst%vstack(rb + w(3) + 1) = fnv
                               if (flat_force(newframe, w(6))) then
                                  if (tctx%has_error) exit
                                  if (step_at /= 0) call step_check()
                                  if (flat_top(tctx, kbot)) cycle outer
                                  return
                               end if
                               vst%vstack(rb + w(3) + 1) = gc_nil()
                            end if
                         end if
                         fnv = wb
                         if (.not. flat_builtin(w(6))) exit
                         pc = pc + FW
                         cycle
                      end if
                      ! THE CALLEE'S REGISTERS ON THE STACK (PLAN 26.2): no heap
                      ! frame -- pushed, filled with its captures, its own name
                      ! and the arguments, which leave this frame's registers
                      call vs_set(vst, b + 6, ar)
                      body = ct_body(ar, j)
                      call push_frame(tctx, vs_get(vst, b + 3), w(6))
                      if (tctx%has_error) exit
                      tctx%kst(ks)%pc = pc + FW
                      tctx%kst(ks)%aux = w(2) + 1
                      fnv = vs_get(vst, b + 3)
                      call vs_set(vst, b + 3, gc_nil())
                      call vs_set(vst, b + 4, gc_nil())
                      call k_push(body, gc_nil(), ior(KF_FNBODY, KF_RESTART), body, tctx)
                      if (tctx%has_error) exit
                      call vs_set(vst, tctx%kst(tctx%ksp)%base + 7, fnv)
                      block
                        integer :: rb2, nr
                        ar = vs_get(vst, b + 6)
                        nr = ct_int(ar, 1)
                        rb2 = vs_enter(vst, nr)
                        call ct_stack_frame(vst, fnv, ar, rb2)
                        do id = 0, n - 1
                           vst%vstack(rb2 + start + id + 1) = vst%vstack(rb + w(4) + id + 1)
                           vst%vstack(rb + w(4) + id + 1) = gc_nil()
                        end do
                        call vs_set(vst, tctx%kst(tctx%ksp)%base + 2, gc_value(GCT_SFRAME, rb2, int(nr, gc_ip)))
                      end block
                      call vs_set(vst, b + 6, gc_nil())
                      if (step_at /= 0) call step_check()
                      if (flat_top(tctx, kbot)) cycle outer
                      return
                   end if
                end if
             end if
          end if
          ! a core wrapper called with its arity: its builtin, with the
          ! wrapper's call-stack entry around it (analyze.inc
          ! wrapper_builtin)
          wb = wrapper_of(fnv, n)
          if (wb%tag /= GCT_NIL) fnv = wb
          if (gc_kind(fnv) == OBJ_BUILTIN .and. gc_i1(fnv) /= B_RTFN .and. gc_i1(fnv) /= B_UUIDFN) then
             if (.not. flat_builtin(w(6))) exit
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
                   call frame_set(newframe, start + j, vst%vstack(rb + w(4) + j + 1))
                   vst%vstack(rb + w(4) + j + 1) = gc_nil()
                end do
                call push_frame(tctx, vs_get(vst, b + 3), w(6))
                if (tctx%has_error) exit
                call bind_captures(vs_get(vst, b + 3), vs_get(vst, b + 4))
                body = arity_body(ar)
             else
                argv = flat_args(fr, w(4), n, b)
                do j = 0, n - 1
                   vst%vstack(rb + w(4) + j + 1) = gc_nil()
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
             if (flat_top(tctx, kbot)) cycle outer
             return
          else
             ! anything else callable: a keyword, a map, a compiled fn,
             ! a multimethod -- through apply, which may yield
             argv = flat_args(fr, w(4), n, b)
             do j = 0, n - 1
                vst%vstack(rb + w(4) + j + 1) = gc_nil()
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
             vst%vstack(rb + w(2) + 1) = v
          end if
       case (F_CALLB)
          ! w: F_CALLB d k a n site -- the head a builtin constant, known
          ! when the body was compiled: nothing to resolve, and two
          ! machine integers through + < inc and the rest need no call
          n = w(5)
          tctx%kst(ks)%aux2 = w(6)
          tctx%kst(ks)%pc = pc
          fnv = vec_store(kb + w(3) + 1)
          if (n >= 1 .and. n <= 2) then
             v = vst%vstack(rb + w(7) + 1)
             argv = gc_nil()
             if (n == 2) argv = vst%vstack(rb + w(8) + 1)
             done = .false.
             if (n == 1) done = flat_seq_op(gc_i1(fnv), v, newframe)
             if (.not. done) done = flat_int_op(gc_i1(fnv), n, v, argv, newframe)
             if (done) then
                ! a temporary is cleared; a local read in place is not
                if (w(7) == w(4)) vst%vstack(rb + w(4) + 1) = gc_nil()
                if (n == 2 .and. w(8) == w(4) + 1) vst%vstack(rb + w(4) + 1 + 1) = gc_nil()
                vst%vstack(rb + w(2) + 1) = newframe
                pc = pc + FW
                cycle
             end if
             ! a pending cell whose thunk can run here, in the loop
             if (n == 1) then
                newframe = flat_force_target(gc_i1(fnv), v)
                if (newframe%tag /= GCT_NIL) then
                   if (flat_force(newframe, w(6))) then
                      if (tctx%has_error) exit
                      if (step_at /= 0) call step_check()
                      if (flat_top(tctx, kbot)) cycle outer
                      return
                   end if
                end if
             end if
             ! the general road wants its arguments in a row
             if (w(7) /= w(4)) vst%vstack(rb + w(4) + 1) = v
             if (n == 2 .and. w(8) /= w(4) + 1) vst%vstack(rb + w(4) + 1 + 1) = argv
          end if
          wb = gc_nil()
          call vs_set(vst, b + 3, fnv)
          if (.not. flat_builtin(w(6))) exit
       case (F_NEW)
          ! w: F_NEW d k a n
          argv = flat_args(fr, w(4), w(5), b)
          call vs_set(vst, b + 6, argv)
          do j = 0, w(5) - 1
             vst%vstack(rb + w(4) + j + 1) = gc_nil()
          end do
          v = new_cached(vec_store(kb + w(3) + 1), vs_get(vst, b + 6))
          call vs_set(vst, b + 6, gc_nil())
          if (tctx%has_error) exit
          vst%vstack(rb + w(2) + 1) = v
       case (F_CASE)
          ! w: F_CASE t k kb m kl
          v = vst%vstack(rb + w(2) + 1)
          vst%vstack(rb + w(2) + 1) = gc_nil()
          body = case_branch(vec_store(kb + w(3) + 1), v)
          if (tctx%has_error) exit
          done = .false.
          do j = 0, w(5) - 1
             argv = gc_vec_get(consts, w(4) + j + 1)
             if (argv%tag == body%tag .and. argv%ref == body%ref) then
                argv = gc_vec_get(consts, w(6) + j + 1)
                pc = int(argv%ival)
                done = .true.
                exit
             end if
          end do
          if (.not. done) then
             call raise_class("clotran.host.illegal_state_exception", "flat: case branch not compiled", [gc_value ::])
             exit
          end if
          cycle
       case (F_TRY)
          ! w: F_TRY sv L
          vst%vstack(rb + w(2) + 1) = gc_int(int(tctx%kst(ks)%mode, gc_ip))
          vst%vstack(rb + w(2) + 1 + 1) = gc_int(int(tctx%fstack_top, gc_ip))
          tctx%kst(ks)%mode = w(3)
       case (F_ENDTRY)
          v = vst%vstack(rb + w(2) + 1)
          tctx%kst(ks)%mode = int(v%ival)
          vst%vstack(rb + w(2) + 1) = gc_nil()
          vst%vstack(rb + w(2) + 1 + 1) = gc_nil()
       case (F_HANDLER)
          ! landed here by flat_catch, which did the work
       case (F_CATCH)
          ! w: F_CATCH ex kcls slot Lnext
          if (.not. catch_matches(vec_store(kb + w(3) + 1), vst%vstack(rb + w(2) + 1), gc_nil())) then
             if (tctx%has_error) exit
             pc = w(5)
             cycle
          end if
          vst%vstack(rb + w(4) + 1) = vst%vstack(rb + w(2) + 1)
          vst%vstack(rb + w(2) + 1) = gc_nil()
          vst%vstack(rb + w(2) + 1 + 1) = gc_nil()
       case (F_RETHROW)
          ! the exception no catch took, on its way as it was: its
          ! message and trace are the ones it was raised with
          v = vst%vstack(rb + w(2) + 1)
          argv = vst%vstack(rb + w(3) + 1)
          vst%vstack(rb + w(2) + 1) = gc_nil()
          vst%vstack(rb + w(3) + 1) = gc_nil()
          call set_thrown(v)
          tctx%has_error = .true.
          tctx%last_error = ""
          if (argv%tag == GCT_STR) then
             block
                call gc_ref_text(argv%ref, s=dlt_1)
                tctx%last_error = dlt_1
             end block
          end if
          exit
       case (F_DOT)
          ! w: F_DOT d k a n from site -- dispatched as exec.inc's N_DOT;
          ! the target (or the class) in slot 3, the arguments in slot 6
          ! while it runs, and both kept there if it parks, to dispatch
          ! again as it was
          tctx%kst(ks)%aux2 = w(7)
          tctx%kst(ks)%pc = pc
          v = vec_store(kb + w(3) + 1)
          if (tctx%kst(ks)%i == -2) then
             ! a native call below parked: its builtin again, on the
             ! same vector (the target first)
             tctx%kst(ks)%i = 0
             argv = vs_get(vst, b + 6)
             call vs_set(vst, b + 6, gc_nil())
             tctx%pending_site = w(7)
             v = apply(vs_get(vst, b + 3), argv)
             if (tctx%yield_flag) then
                call vs_set(vst, b + 6, argv)
                tctx%kst(ks)%i = -2
                exit
             end if
             call vs_set(vst, b + 3, gc_nil())
             if (tctx%has_error) exit
             vst%vstack(rb + w(2) + 1) = v
             pc = pc + FW
             cycle
          end if
          ! A NATIVE MEMBER on an evaluated target: what dot_dispatch
          ! would do -- the native with (target args...) -- straight from
          ! the registers, which hold them in a row already; no vector
          ! built and another built from it. nil, a deftype instance and
          ! a Var take dispatch's road.
          if (tctx%kst(ks)%i /= -1 .and. w(6) == 1) then
             fnv = gc_slot(v, 3)
             argv = strip_meta(vst%vstack(rb + w(4) + 1))
             if (gc_kind(fnv) == OBJ_BUILTIN .and. argv%tag /= GCT_NIL) then
                if (gc_i1(fnv) /= B_RTFN .and. gc_i1(fnv) /= B_UUIDFN .and. &
                     gc_kind(argv) /= OBJ_INST .and. .not. gcn_is_var(argv)) then
                   n = w(5) + 1
                   wb = gc_nil()
                   call vs_set(vst, b + 3, fnv)
                   if (.not. flat_builtin(w(7))) then
                      if (tctx%yield_flag) tctx%kst(ks)%i = -2
                      exit
                   end if
                   pc = pc + FW
                   cycle
                end if
             end if
          end if
          if (tctx%kst(ks)%i == -1) then
             tctx%kst(ks)%i = 0
             argv = vs_get(vst, b + 6)
          else
             if (w(6) == 1) then
                call vs_set(vst, b + 3, vst%vstack(rb + w(4) + 1))
                vst%vstack(rb + w(4) + 1) = gc_nil()
             else
                call vs_set(vst, b + 3, gc_slot(v, 3))
             end if
             argv = flat_args(fr, w(4) + w(6), w(5), b)
             do j = 0, w(5) - 1
                vst%vstack(rb + w(4) + w(6) + j + 1) = gc_nil()
             end do
          end if
          call vs_set(vst, b + 6, gc_nil())
          call vs_set(vst, vbase + 1, gc_nil())
          val = dot_dispatch(v, vs_get(vst, b + 3), argv, w(6))
          if (tctx%yield_flag) then
             call vs_set(vst, b + 6, argv)
             tctx%kst(ks)%i = -1
             val = gc_nil()
             exit
          end if
          call vs_set(vst, b + 3, gc_nil())
          if (tctx%has_error) exit
          if (is_call_request(val)) then
             ! a method that is a closure: its body in a frame of its own,
             ! as a call's (enter_call, for the tree)
             call vs_set(vst, b + 3, val)
             call push_frame(tctx, gc_slot(vs_get(vst, b + 3), 1), w(7))
             if (tctx%has_error) exit
             ok = bind_closure(gc_slot(vs_get(vst, b + 3), 1), gc_slot(vs_get(vst, b + 3), 2), newframe, body)
             if (.not. ok) then
                call pop_frame(tctx)
                exit
             end if
             call vs_set(vst, b + 4, newframe)
             fnv = gc_slot(vs_get(vst, b + 3), 1)
             call vs_set(vst, b + 3, gc_nil())
             val = gc_nil()
             tctx%kst(ks)%pc = pc + FW
             tctx%kst(ks)%aux = w(2) + 1
             call k_push(body, vs_get(vst, b + 4), ior(KF_FNBODY, KF_RESTART), body, tctx)
             call vs_set(vst, tctx%kst(tctx%ksp)%base + 7, fnv)
             if (step_at /= 0) call step_check()
             if (flat_top(tctx, kbot)) cycle outer
             return
          end if
          vst%vstack(rb + w(2) + 1) = val
          val = gc_nil()
       case default
          call raise_class("clotran.host.illegal_state_exception", "flat: bad instruction", [gc_value ::])
          exit
       end select
       pc = pc + FW
    end do
    ! failed or parked: the instruction stays where it was
    tctx%kst(ks)%pc = pc
    return
    end do outer

  contains

    ! The builtin fnv with registers w(4).. as arguments, the answer
    ! into w(2); with wb set, fnv is a wrapper's builtin and the
    ! wrapper (slot 3) is on the call stack while it runs. False when
    ! the body must stop here: an error, or the call parked.
    logical function flat_builtin(site) result(go)
      integer, intent(in) :: site
      go = .false.
      id = gc_i1(fnv)
      scalar = n >= 1 .and. n <= 2 .and. scalar_builtin(id)
      spare = .not. scalar .and. n >= 1 .and. n <= ARG_SPARE_MAX .and. args_reusable(id)
      if (scalar) then
         argv = scratch_args(n)
         do j = 1, n
            call gc_vec_set(gc_slot(argv, 1), j, vst%vstack(rb + w(4) + j - 1 + 1))
         end do
      else if (spare) then
         argv = args_take(n, [nd])
         do j = 1, n
            call gc_vec_set(gc_slot(argv, 1), j, vst%vstack(rb + w(4) + j - 1 + 1))
         end do
      else
         argv = flat_args(fr, w(4), n, b)
      end if
      do j = 0, n - 1
         vst%vstack(rb + w(4) + j + 1) = gc_nil()
      end do
      if (wb%tag /= GCT_NIL) then
         call push_frame(tctx, vs_get(vst, b + 3), site)
         if (tctx%has_error) return
      end if
      if (scalar .or. spare) then
         call vs_set(vst, b + 6, argv)
         tctx%pending_site = site
         v = call_builtin(id, argv)
         if (spare) call args_give(vs_get(vst, b + 6), n)
         call vs_set(vst, b + 6, gc_nil())
      else
         tctx%pending_site = site
         v = apply(fnv, argv)
         if (tctx%yield_flag) then
            if (wb%tag /= GCT_NIL) call pop_frame(tctx)
            ! parked: dispatched again, as the fn that was called
            call vs_set(vst, b + 6, argv)
            tctx%kst(ks)%i = -1
            return
         end if
      end if
      if (wb%tag /= GCT_NIL) call pop_frame(tctx)
      call vs_set(vst, b + 3, gc_nil())
      if (tctx%has_error) return
      vst%vstack(rb + w(2) + 1) = v
      go = .true.
    end function flat_builtin

    ! Claims the pending cell c (as gce_force does) and pushes its
    ! thunk's body as a callee, this frame waiting AT the instruction
    ! that wanted it, aux -1: on the answer the cell is settled and the
    ! instruction runs again, finding it realised. False when another
    ! thread holds c -- the builtin waits for it -- or it is no longer
    ! pending.
    logical function flat_force(c, site) result(started)
      type(gc_value), intent(in) :: c
      integer, intent(in) :: site
      type(gc_value) :: owner
      started = .false.
      call gc_state_lock()
      if (gc_i1(c) /= LAZY_PENDING) then
         call gc_state_unlock()
         return
      end if
      owner = gc_int(int(tctx%id, gc_ip))
      call gc_set_i1(c, LAZY_RUNNING)
      call gc_set_slot(c, 4, owner)
      call gc_state_unlock()
      started = .true.
      call vs_set(vst, b + 6, c)
      call vs_set(vst, b + 3, gc_slot(c, 1))
      call vs_set(vst, b + 4, call_table_of(vs_get(vst, b + 3)))
      newframe = ct_frame(vs_get(vst, b + 3), vs_get(vst, b + 4), [vs_get(vst, b + 6)])
      body = ct_body(vs_get(vst, b + 4), 5)
      call vs_set(vst, b + 4, newframe)
      call push_frame(tctx, vs_get(vst, b + 3), site)
      if (tctx%has_error) then
         call give_frame(vs_get(vst, b + 4))
         call vs_set(vst, b + 4, gc_nil())
         call flat_release(vs_get(vst, b + 6))
         call vs_set(vst, b + 6, gc_nil())
         return
      end if
      tctx%kst(ks)%pc = pc
      tctx%kst(ks)%aux = -1
      fnv = vs_get(vst, b + 3)
      call vs_set(vst, b + 3, gc_nil())
      call k_push(body, vs_get(vst, b + 4), ior(KF_FNBODY, KF_RESTART), body, tctx)
      call vs_set(vst, tctx%kst(tctx%ksp)%base + 7, fnv)
    end function flat_force
  end subroutine flat_run

  ! first, rest, next and seq where the answer is a slot already there:
  ! nil, a list, a lazy cell already realised. What call_builtin
  ! answers for them (sq_first, sq_rest, to_seq), without its argument
  ! vector or its dispatch; false for anything else -- a pending cell
  ! to force, a vector to view -- and the builtin decides. Nothing
  ! here can fail, so a wrapper needs no call-stack entry around it.
  logical function flat_seq_op(id, x0, out) result(done)
    integer, intent(in) :: id
    type(gc_value), intent(in) :: x0
    type(gc_value), intent(inout) :: out
    type(gc_value) :: x, t
    integer :: st
    done = .false.
    x = x0
    if (x%tag == GCT_NIL) then
       select case (id)
       case (B_FIRST, B_NEXT, B_SEQ)
          out = gc_nil()
          done = .true.
       end select
       return
    end if
    if (gcl_is(x)) then
       select case (id)
       case (B_FIRST)
          out = gc_nil()
          if (gcl_count(x) > 0) out = gcl_first(x)
          done = .true.
       case (B_SEQ)
          out = gc_nil()
          if (gcl_count(x) > 0) out = x
          done = .true.
       end select
       return
    end if
    if (gc_kind(x) /= OBJ_LAZY) return
    st = gc_i1(x)
    select case (id)
    case (B_SEQ)
       select case (st)
       case (LAZY_CONS);  out = x
       case (LAZY_EMPTY); out = gc_nil()
       case (LAZY_DELEG); out = gc_slot(x, 2)
       case default; return
       end select
    case (B_FIRST)
       if (st /= LAZY_CONS .and. st /= LAZY_EMPTY) return
       out = gc_nil()
       if (st == LAZY_CONS) out = gc_slot(x, 2)
    case (B_REST)
       if (st /= LAZY_CONS) return
       out = gc_slot(x, 3)
    case (B_NEXT)
       if (st == LAZY_EMPTY) then
          out = gc_nil()
       else if (st == LAZY_CONS) then
          ! (seq (rest x)), when that needs nothing done
          t = gc_slot(x, 3)
          if (t%tag == GCT_NIL) then
             out = gc_nil()
          else if (gcl_is(t)) then
             out = gc_nil()
             if (gcl_count(t) > 0) out = t
          else if (gc_kind(t) == OBJ_LAZY) then
             select case (gc_i1(t))
             case (LAZY_CONS);  out = t
             case (LAZY_EMPTY); out = gc_nil()
             case (LAZY_DELEG); out = gc_slot(t, 2)
             case default; return
             end select
          else
             return
          end if
       else
          return
       end if
    case default
       return
    end select
    done = .true.
  end function flat_seq_op

  ! The pending cell a one-argument first, rest, next or seq would
  ! force -- next forces x's tail once x itself is realised -- when its
  ! thunk is an interpreted fn with a fixed no-argument arity, which
  ! flat_run can then run as a callee in the loop rather than in a
  ! nested run (flat_force). nil otherwise, and the builtin forces it.
  function flat_force_target(id, x) result(c)
    integer, intent(in) :: id
    type(gc_value), intent(in) :: x
    type(gc_value) :: c, t, ct
    c = gc_nil()
    select case (id)
    case (B_FIRST, B_REST, B_SEQ, B_NEXT)
    case default
       return
    end select
    if (step_at /= 0) return
    if (gc_kind(x) /= OBJ_LAZY) return
    t = x
    if (id == B_NEXT .and. gc_i1(x) == LAZY_CONS) t = gc_slot(x, 3)
    if (gc_kind(t) /= OBJ_LAZY) return
    if (gc_i1(t) /= LAZY_PENDING .or. gc_i2(t) /= 0) return
    if (gc_kind(gc_slot(t, 1)) /= OBJ_CLOSURE) return
    ct = call_table_of(gc_slot(t, 1))
    if (ct%tag /= GCT_VEC) return
    if (ct_int(ct, 4) < 0) return
    if (ct_int(ct, 5) < 0) return
    c = t
  end function flat_force_target

  ! A cell flat_force claimed, given back: pending again if its thunk
  ! did not finish (it threw, and the unwinding came through), and
  ! anyone waiting for it woken -- gce_force's closing steps.
  subroutine flat_release(c)
    type(gc_value), intent(in) :: c
    if (gc_kind(c) /= OBJ_LAZY) return
    call gc_state_lock()
    if (gc_i1(c) == LAZY_RUNNING) call gc_set_i1(c, LAZY_PENDING)
    call gc_state_unlock()
    call gc_state_notify()
  end subroutine flat_release

  ! One or two machine integers through the commonest builtins, as
  ! call_builtin answers them. False for anything else -- a real, a
  ! big number, an overflow, which throws -- and the builtin decides.
  logical function flat_int_op(id, n, x, y, out) result(done)
    integer, intent(in) :: id, n
    type(gc_value), intent(in) :: x, y
    type(gc_value), intent(inout) :: out
    integer(gc_ip) :: a, c
    done = .false.
    if (x%tag /= GCT_INT) return
    a = x%ival
    if (n == 2) then
       if (y%tag /= GCT_INT) return
       c = y%ival
       select case (id)
       case (B_ADD)
          if (add_overflows(a, c)) return
          out = gc_int(a + c)
       case (B_SUB)
          if (c == -huge(c) - 1_gc_ip) return
          if (add_overflows(a, -c)) return
          out = gc_int(a - c)
       case (B_MUL)
          if (mul_overflows(a, c)) return
          out = gc_int(a * c)
       case (B_LT);  out = gc_bool(a < c)
       case (B_GT);  out = gc_bool(a > c)
       case (B_LTE); out = gc_bool(a <= c)
       case (B_GTE); out = gc_bool(a >= c)
       case (B_NUMEQ, B_EQ, B_IDENTICAL); out = gc_bool(a == c)
       case default; return
       end select
    else
       select case (id)
       case (B_INC, B_UINC)
          ! unchecked-inc wraps at the top; that one value goes to the
          ! builtin, which knows how (dotimes counts with it)
          if (a == huge(a)) return
          out = gc_int(a + 1_gc_ip)
       case (B_DEC, B_UDEC)
          if (a == -huge(a) - 1_gc_ip) return
          out = gc_int(a - 1_gc_ip)
       case (B_ZERO); out = gc_bool(a == 0)
       case (B_POS);  out = gc_bool(a > 0)
       case (B_NEG);  out = gc_bool(a < 0)
       case default; return
       end select
    end if
    done = .true.
  end function flat_int_op

  ! Whether the frame on top, above kbot, is a flat body flat_run can
  ! go on with: no error, nothing parked, no step to take in the loop.
  logical function flat_top(tctx, kbot) result(yes)
    type(eval_ctx), pointer, intent(in) :: tctx
    integer, intent(in) :: kbot
    type(gc_value) :: nd
    yes = .false.
    if (tctx%has_error .or. tctx%yield_flag) return
    if (tctx%ksp <= kbot) return
    nd = vs_get(tctx%stk, tctx%kst(tctx%ksp)%base + 1)
    if (gc_kind(nd) /= OBJ_AST) return
    yes = gc_i1(nd) == N_FLAT
  end function flat_top

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
       argv = gcv_put(vs_get(vst, b + 6), j, reg_get(fr, a + j), [fr])
       call vs_set(vst, b + 6, argv)
    end do
    call vs_set(vst, b + 6, gc_nil())
  end function flat_args
