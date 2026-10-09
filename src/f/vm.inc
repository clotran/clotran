  ! ===================================================================
  ! vm.inc -- fn bodies run by the GENERATED VM (PLAN step 30). Included
  ! into Eval.f90. CLOTRAN_VM=1 turns it on; off, nothing here runs.
  !
  ! ONE PROGRAM. Every fn the VM can run is one function of a single
  ! program that grows as fns are analysed: its arities are the
  ! function's clauses, compiled by the generated compiler
  ! (src/f/gen/vmc_gen.f90, vmicg_defs) at the end of the code, their
  ! superinstructions tagged by the generated pass (vmg_fuse), and run by
  ! the generated fused step (vmg_xstep). The fn's template carries its
  ! function id (index 9), so a clotran closure of it IS one of the
  ! machine's closures (VmRuntime rt_clop): a call from VM code to it is
  ! the machine's own call -- a record pushed and a jump -- and only a
  ! call of anything else goes up to the evaluator ((prim :invoke ..),
  ! which vmx2 makes of a call of what is not a closure).
  !
  ! The theorem (vmfg-correct) is about a program compiled whole and run
  ! from pc 0. What this file adds and the theorem does not cover, the
  ! fuzzers check (scripts/fuzz -m vm against clj):
  !   - the translation from clotran's tree to vmx2's core language;
  !   - the program built a function at a time, each where a whole
  !     compile would put it;
  !   - the entry from the evaluator: the frame a call would make (the
  !     arguments, the rest packed, the closure above), a call record
  !     returning to the halt at pc 0, and a jump to the clause.
  !
  ! The translation, node by node:
  !   const                 (:const v)
  !   a parameter           (:local i)
  !   a capture, the fn     (:capt i), the fn itself (:capt ncap)
  !   var                   (:prim :clotran.vm/deref (:const var))
  !   if, throw             (:if c a b), (:throw e)
  !   do                    nested (:let e1 ..), each value a dead local
  !   let                   nested (:let init ..), each binding a local
  !   loop                  the bindings as lets, then (:loop ((:local
  !                         ..)) body) over them: Clojure's loop binds in
  !                         sequence, vmx2's loop evaluates its
  !                         initial values together
  !   recur                 (:recur args); the fn's own recur, a loop
  !                         around the body over its parameters
  !   vector, map, set, new, a dot call, fn, lazy-seq
  !                         (:prim NODE parts..): the runtime does what
  !                         flat does with the node (vm_node_hook)
  !   a call of a builtin   (:prim builtin args)
  !   any other call        (:callv head args)
  ! and a last clause (0 .. :rest) for a call of no arity the fn has,
  ! clj's ArityException. Anything else -- try, letfn, case, def -- and
  ! the fn runs as before.
  ! ===================================================================

  ! CLOTRAN_VM=1: fn bodies the VM can run, it runs
  logical function vm_enabled()
    character(len=8) :: e
    if (vm_mode == 0) then
       call get_environment_variable("CLOTRAN_VM", e)
       vm_mode = merge(1, 2, trim(e) == "1")
       if (vm_mode == 1) then
          vmrt_call => vm_call_hook
          vmrt_deref => vm_deref_hook
          vmrt_node => vm_node_hook
          vmrt_arity => vm_arity_hook
          block
            character(len=8) :: tr
            call get_environment_variable("CLOTRAN_VM_TRACE", tr)
            vm_trace = (trim(tr) == "1")
          end block
          call vm_program_make()
       end if
    end if
    vm_enabled = vm_mode == 1
  end function vm_enabled

  ! The program's arrays, made once and never moved -- threads run it
  ! while another adds to it. pc 0 is the halt: a return with nothing
  ! under it, where an entry's call returns to.
  subroutine vm_program_make()
    allocate(vmp%code(0:4 * VMP_INSTRS - 1), vmp%pool(0:VMP_INSTRS - 1))
    allocate(vmp%cln(0:VMP_CLAUSES - 1), vmp%clent(0:VMP_CLAUSES - 1), vmp%clrest(0:VMP_CLAUSES - 1))
    allocate(vmp%fnfirst(0:VMP_FNS - 1), vmp%fncount(0:VMP_FNS - 1))
    allocate(vmp_fstart(0:VMP_FNS - 1), vmp_fnames(0:VMP_FNS - 1))
    vmp_fstart = huge(0_gc_ip)
    allocate(vmp%stk(0:0), vmp%ckind(0:0), vmp%ca(0:0), vmp%cb(0:0), vmp%cc(0:0), vmp%cprev(0:0))
    vmp%code = 0
    vmp%pool = gc_nil()
    vmp%cln = 0
    vmp%clent = 0
    vmp%clrest = 0
    vmp%fnfirst = 0
    vmp%fncount = 0
    vmp%code(0) = 11
    vmp_pc = 1
    vmp_ci = 0
    vmp_f = 0
  end subroutine vm_program_make

  ! the runtime's call: fn on the nargs values above argbase. A throw
  ! answers the thrown value -- or, for an error raised as a message
  ! alone, the value a catch would make of it -- and the error STAYS
  ! raised: the VM has no handlers yet, so the throw unwinds straight out
  ! of the run, nothing running between, and vm_run leaves it as it was
  recursive subroutine vm_call_hook(fn, argbase, nargs, out, ok)
    type(gc_value), intent(in) :: fn
    integer, intent(in) :: argbase, nargs
    type(gc_value), intent(out) :: out
    logical, intent(out) :: ok
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    tctx => ctx_self()
    vst => tctx%stk
    out = gce_apply_slots(vst, fn, argbase, nargs)
    call vm_took(tctx, ok, out, fn)
  end subroutine vm_call_hook

  subroutine vm_took(tctx, ok, out, root)
    type(eval_ctx), pointer, intent(in) :: tctx
    logical, intent(out) :: ok
    type(gc_value), intent(inout) :: out
    type(gc_value), intent(in) :: root
    ok = .not. tctx%has_error
    if (.not. ok) then
       out = thrown_value()
       if (out%tag == GCT_NIL) then
          block
            character(len=:), allocatable :: msg
            call gce_error(s=msg)
            out = error_value(msg, [root])
          end block
       end if
    end if
  end subroutine vm_took

  ! a call of no arity the fn has: clj's ArityException, the count the
  ! arguments' (the last clause's rest list), the fn named by its display
  ! name (the constant in argbase+1)
  recursive subroutine vm_arity_hook(name, argbase, nargs, out, ok)
    type(gc_value), intent(in) :: name
    integer, intent(in) :: argbase, nargs
    type(gc_value), intent(out) :: out
    logical, intent(out) :: ok
    type(eval_ctx), pointer :: tctx
    type(gc_stack), pointer :: vst
    character(len=:), allocatable :: who
    character(len=16) :: buf
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    call gcp_str(vs_get(vst, argbase + 1), .false., s=who)
    write(buf, '(i0)') seq_len(vs_get(vst, argbase + nargs))
    call raise_class("clotran.host.arity_exception", "Wrong number of args (" // trim(buf) // ") passed to: " // who, [name])
    call vm_took(tctx, ok, out, name)
  end subroutine vm_arity_hook

  function vm_deref_hook(var) result(v)
    type(gc_value), intent(in) :: var
    type(gc_value) :: v
    v = var_deref(var, [var])
  end function vm_deref_hook

  ! the runtime's node: what flat does for a node the VM leaves to it
  ! (F_COLL, F_NEW, F_DOT, F_FN, F_LAZY), on the n values above argbase --
  ! a collection's elements, new's and a dot call's arguments (the dot's
  ! target first when it is a value), a fn's captured values in the
  ! order of its template's captures. A throw as vm_call_hook's.
  recursive subroutine vm_node_hook(nd, argbase, n, out, ok)
    type(gc_value), intent(in) :: nd
    integer, intent(in) :: argbase, n
    type(gc_value), intent(out) :: out
    logical, intent(out) :: ok
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value) :: x, capv
    integer :: base, j, from, ncap, hi
    tctx => ctx_self()
    vst => tctx%stk
    out = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, nd)
    select case (gc_i1(nd))
    case (N_VECTOR, N_MAP, N_SET, N_NEW)
       call vs_set(vst, base + 2, vm_slots_vec(vst, argbase, 0, n, [nd]))
       select case (gc_i1(nd))
       case (N_VECTOR); out = vs_get(vst, base + 2)
       case (N_SET);    out = vec_to_set(vs_get(vst, base + 2), [nd])
       case (N_MAP);    out = vec_to_map(vs_get(vst, base + 2), [nd])
       case default;    out = new_cached(vs_get(vst, base + 1), vs_get(vst, base + 2))
       end select
    case (N_DOT)
       from = 1
       if (tag_of(gc_slot(nd, 3)) == GCT_SYM) from = 0
       if (from == 1) then
          call vs_set(vst, base + 3, vs_get(vst, argbase + 1))
       else
          call vs_set(vst, base + 3, gc_slot(nd, 3))
       end if
       call vs_set(vst, base + 2, vm_slots_vec(vst, argbase, from, n - from, [nd]))
       out = dot_dispatch(vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 2), from)
       if (.not. tctx%has_error .and. is_call_request(out)) then
          call vs_set(vst, base + 3, out)
          out = apply(gc_slot(vs_get(vst, base + 3), 1), gc_slot(vs_get(vst, base + 3), 2))
       end if
    case (N_FN, N_LAZY)
       ! a frame holding the captured values at the slots the template reads
       capv = gcv_nth(gc_slot(nd, 2), 2)
       ncap = gcv_count(capv) / 2
       hi = 0
       do j = 0, ncap - 1
          hi = max(hi, int_of(gcv_nth(capv, 2 * j)) + 1)
       end do
       x = gc_vec(max(hi, 1), [nd])
       call vs_set(vst, base + 2, x)
       do j = 0, ncap - 1
          call gc_vec_set(vs_get(vst, base + 2), int_of(gcv_nth(gcv_nth(gc_slot(nd, 2), 2), 2 * j)) + 1, &
               vs_get(vst, argbase + j + 1))
       end do
       out = make_closure_from(gc_slot(nd, 2), vs_get(vst, base + 2), [nd])
       if (gc_i1(nd) == N_LAZY) then
          call vs_set(vst, base + 3, out)
          out = gc_obj(OBJ_LAZY, [vs_get(vst, base + 3), gc_nil(), gc_nil()], [vs_get(vst, base + 3)])
          call gc_set_i1(out, LAZY_PENDING)
       end if
    end select
    call vm_took(tctx, ok, out, nd)
    call vs_leave(vst, base)
  end subroutine vm_node_hook

  ! slots argbase+from+1 .. +n as a vector
  function vm_slots_vec(vst, argbase, from, n, roots) result(v)
    type(gc_stack), pointer, intent(in) :: vst
    integer, intent(in) :: argbase, from, n
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: base, j
    base = vs_enter(vst, 1)
    v = gcv_build(n, roots)
    call vs_set(vst, base + 1, v)
    do j = 0, n - 1
       v = gcv_put(vs_get(vst, base + 1), j, vs_get(vst, argbase + from + j + 1), roots)
       call vs_set(vst, base + 1, v)
    end do
    v = vs_get(vst, base + 1)
    call vs_leave(vst, base)
  end function vm_slots_vec

  ! ---- THE TRANSLATION -------------------------------------------------

  ! (k a b ..): a list of values, each already rooted by the caller
  function vm_l(xs, roots) result(l)
    type(gc_value), intent(in) :: xs(:), roots(:)
    type(gc_value) :: l
    type(gc_stack), pointer :: vst
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    call vs_set(vst, base + 1, gc_nil())
    do i = size(xs), 1, -1
       l = gcl_cons(xs(i), vs_get(vst, base + 1), [roots, xs, vs_get(vst, base + 1)])
       call vs_set(vst, base + 1, l)
    end do
    l = vs_get(vst, base + 1)
    call vs_leave(vst, base)
  end function vm_l

  function vm_kw(name) result(k)
    character(len=*), intent(in) :: name
    type(gc_value) :: k
    k = rt_keyword(name)
  end function vm_kw

  ! The slots a body binds and reads, and whether it holds a node the VM
  ! cannot run; whether the fn's own recur is in it.
  recursive subroutine vm_scan(c, nd)
    type(vm_tr_ctx), intent(inout) :: c
    type(gc_value), intent(in) :: nd
    type(gc_value) :: kids, rinfo, head
    integer :: i, n, start
    if (.not. c%ok) return
    if (gc_kind(nd) /= OBJ_AST) then
       c%ok = .false.
       return
    end if
    kids = gc_slot(nd, 1)
    select case (gc_i1(nd))
    case (N_CONST, N_VAR)
    case (N_LOCAL)
       call vm_mark(c%reads, gc_i2(nd), c)
    case (N_IF, N_DO, N_THROW, N_VECTOR, N_MAP, N_SET, N_NEW, N_DOT, N_CALL)
       if (gcv_is(kids)) then
          do i = 0, gcv_count(kids) - 1
             call vm_scan(c, gcv_nth(kids, i))
          end do
       end if
       if (gc_i1(nd) == N_CALL) then
          head = gcv_nth(kids, 0)
          if (gc_kind(head) == OBJ_AST .and. gc_i1(head) == N_CONST) then
             ! a builtin that is a runtime fn of the analyzer's own, as flat refuses it
             if (gc_kind(strip_meta(gc_slot(head, 2))) == OBJ_BUILTIN) then
                if (gc_i1(strip_meta(gc_slot(head, 2))) == B_RTFN .or. gc_i1(strip_meta(gc_slot(head, 2))) == B_UUIDFN) &
                     c%ok = .false.
             end if
          end if
       end if
    case (N_FN, N_LAZY)
       ! the slots its template captures, read here
       head = gcv_nth(gc_slot(nd, 2), 2)
       do i = 0, gcv_count(head) / 2 - 1
          call vm_mark(c%reads, int_of(gcv_nth(head, 2 * i)), c)
       end do
    case (N_LET, N_LOOP)
       n = gc_i2(nd)
       start = int_of(gc_slot(nd, 2))
       do i = 0, n - 1
          call vm_mark(c%binds, start + i, c)
       end do
       do i = 0, gcv_count(kids) - 1
          call vm_scan(c, gcv_nth(kids, i))
       end do
    case (N_RECUR)
       rinfo = gc_slot(nd, 2)
       if (int_of(gcv_nth(rinfo, 0)) /= 0) c%fn_recur = .true.
       do i = 0, gcv_count(kids) - 1
          call vm_scan(c, gcv_nth(kids, i))
       end do
    case default
       c%ok = .false.
       if (gc_i1(nd) >= 0 .and. gc_i1(nd) <= 40) vm_refused_by(gc_i1(nd)) = vm_refused_by(gc_i1(nd)) + 1
    end select
  end subroutine vm_scan

  subroutine vm_mark(set, s, c)
    logical, intent(inout) :: set(0:)
    integer, intent(in) :: s
    type(vm_tr_ctx), intent(inout) :: c
    if (s < 0 .or. s > ubound(set, 1)) then
       c%ok = .false.
    else
       set(s) = .true.
    end if
  end subroutine vm_mark

  ! nd as core language: c%map holds each slot's local, c%capt each
  ! captured slot's capture index, c%depth the locals' count
  recursive function vm_tr(c, nd, roots) result(e)
    type(vm_tr_ctx), intent(inout) :: c
    type(gc_value), intent(in) :: nd, roots(:)
    type(gc_value) :: e, kids, x, head, v
    type(gc_stack), pointer :: vst
    integer :: base, i, n, start, nk, d0
    integer, allocatable :: saved(:)
    e = gc_nil()
    if (.not. c%ok) return
    vst => gc_my_stack()
    kids = gc_slot(nd, 1)
    nk = 0
    if (gcv_is(kids)) nk = gcv_count(kids)
    ! slots: 1 nd, 2 an accumulator vector, 3 4 scratch, 5 kw, 6 a second accumulator
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, nd)
    select case (gc_i1(nd))
    case (N_CONST)
       call vs_set(vst, base + 5, vm_kw("const"))
       e = vm_l([vs_get(vst, base + 5), gc_slot(nd, 2)], [roots, vs_get(vst, base + 1)])
    case (N_LOCAL)
       e = vm_slot_ref(c, gc_i2(nd), roots)
    case (N_VAR)
       e = vm_deref_of(gc_slot(nd, 2), [roots, vs_get(vst, base + 1)])
    case (N_IF)
       call vm_tr_kids(c, kids, 0, nk - 1, base + 2, roots)
       if (nk == 2) then
          call vs_set(vst, base + 5, vm_kw("const"))
          x = vm_l([vs_get(vst, base + 5), gc_nil()], [roots, vs_get(vst, base + 2)])
          call vs_set(vst, base + 3, x)
          x = gcv_conj(vs_get(vst, base + 2), vs_get(vst, base + 3), [roots, vs_get(vst, base + 2)])
          call vs_set(vst, base + 2, x)
       end if
       if (c%ok) e = vm_head_list("if", vs_get(vst, base + 2), roots)
    case (N_VECTOR, N_MAP, N_SET, N_NEW, N_DOT)
       ! the runtime's node on the parts' values (vm_node_hook)
       call vm_tr_kids(c, kids, 0, nk - 1, base + 2, roots)
       if (c%ok) e = vm_node_prim(vs_get(vst, base + 1), vs_get(vst, base + 2), roots)
    case (N_FN, N_LAZY)
       ! the captured slots' values, in the template's order
       call vs_set(vst, base + 2, gcv_empty(roots))
       x = gcv_nth(gc_slot(nd, 2), 2)
       call vs_set(vst, base + 6, x)
       do i = 0, gcv_count(vs_get(vst, base + 6)) / 2 - 1
          x = vm_slot_ref(c, int_of(gcv_nth(vs_get(vst, base + 6), 2 * i)), [roots, vs_get(vst, base + 2), &
               vs_get(vst, base + 6)])
          if (.not. c%ok) exit
          call vs_set(vst, base + 3, x)
          x = gcv_conj(vs_get(vst, base + 2), vs_get(vst, base + 3), [roots, vs_get(vst, base + 2), vs_get(vst, base + 6)])
          call vs_set(vst, base + 2, x)
       end do
       if (c%ok) e = vm_node_prim(vs_get(vst, base + 1), vs_get(vst, base + 2), roots)
    case (N_THROW)
       call vm_tr_kids(c, kids, 0, 0, base + 2, roots)
       if (c%ok) e = vm_head_list("throw", vs_get(vst, base + 2), roots)
    case (N_DO)
       if (nk == 0) then
          call vs_set(vst, base + 5, vm_kw("const"))
          e = vm_l([vs_get(vst, base + 5), gc_nil()], roots)
       else
          ! every value but the last a local no one reads
          d0 = c%depth
          call vm_tr_kids(c, kids, 0, nk - 2, base + 2, roots, bump=.true.)
          if (c%ok) then
             x = vm_tr(c, gcv_nth(kids, nk - 1), [roots, vs_get(vst, base + 2)])
             call vs_set(vst, base + 3, x)
             e = vm_wrap_lets(vs_get(vst, base + 2), vs_get(vst, base + 3), roots)
          end if
          c%depth = d0
       end if
    case (N_LET, N_LOOP)
       n = gc_i2(nd)
       start = int_of(gc_slot(nd, 2))
       d0 = c%depth
       allocate(saved(0:max(n, 1) - 1))
       do i = 0, n - 1
          saved(i) = c%map(start + i)
       end do
       ! the bindings, each a let, each in scope for the next
       call vs_set(vst, base + 2, gcv_empty(roots))
       do i = 0, n - 1
          if (.not. c%ok) exit
          x = vm_tr(c, gcv_nth(kids, i), [roots, vs_get(vst, base + 2)])
          call vs_set(vst, base + 3, x)
          x = gcv_conj(vs_get(vst, base + 2), vs_get(vst, base + 3), [roots, vs_get(vst, base + 2)])
          call vs_set(vst, base + 2, x)
          c%map(start + i) = c%depth
          c%depth = c%depth + 1
       end do
       if (c%ok .and. gc_i1(nd) == N_LOOP) then
          ! (:loop ((:local d0) ..) body), the slots now the loop's
          call vs_set(vst, base + 6, gcv_empty(roots))
          call vs_set(vst, base + 5, vm_kw("local"))
          do i = 0, n - 1
             x = vm_l([vs_get(vst, base + 5), gc_int(int(c%map(start + i), gc_ip))], [roots, vs_get(vst, base + 2), &
                  vs_get(vst, base + 6)])
             call vs_set(vst, base + 3, x)
             x = gcv_conj(vs_get(vst, base + 6), vs_get(vst, base + 3), [roots, vs_get(vst, base + 2), vs_get(vst, base + 6)])
             call vs_set(vst, base + 6, x)
          end do
          do i = 0, n - 1
             c%map(start + i) = c%depth + i
          end do
          c%depth = c%depth + n
          x = vm_tr(c, gcv_nth(kids, n), [roots, vs_get(vst, base + 2), vs_get(vst, base + 6)])
          call vs_set(vst, base + 3, x)
          if (c%ok) then
             x = vec_to_list(vs_get(vst, base + 6), [roots, vs_get(vst, base + 2), vs_get(vst, base + 3)])
             call vs_set(vst, base + 6, x)
             call vs_set(vst, base + 5, vm_kw("loop"))
             x = vm_l([vs_get(vst, base + 5), vs_get(vst, base + 6), vs_get(vst, base + 3)], [roots, vs_get(vst, base + 2)])
             call vs_set(vst, base + 3, x)
             e = vm_wrap_lets(vs_get(vst, base + 2), vs_get(vst, base + 3), roots)
          end if
       else if (c%ok) then
          x = vm_tr(c, gcv_nth(kids, n), [roots, vs_get(vst, base + 2)])
          call vs_set(vst, base + 3, x)
          if (c%ok) e = vm_wrap_lets(vs_get(vst, base + 2), vs_get(vst, base + 3), roots)
       end if
       do i = 0, n - 1
          c%map(start + i) = saved(i)
       end do
       c%depth = d0
    case (N_RECUR)
       call vm_tr_kids(c, kids, 0, nk - 1, base + 2, roots)
       if (c%ok) e = vm_head_list("recur", vs_get(vst, base + 2), roots)
    case (N_CALL)
       head = gcv_nth(kids, 0)
       call vm_tr_kids(c, kids, 1, nk - 1, base + 2, roots)
       if (c%ok) then
          if (gc_kind(head) == OBJ_AST .and. gc_i1(head) == N_CONST .and. &
               gc_kind(strip_meta(gc_slot(head, 2))) == OBJ_BUILTIN) then
             ! a builtin: the runtime's own operation, (:prim f args ..)
             call vs_set(vst, base + 4, gc_slot(head, 2))
             x = vec_to_list(vs_get(vst, base + 2), [roots, vs_get(vst, base + 4)])
             call vs_set(vst, base + 3, x)
             x = gcl_cons(vs_get(vst, base + 4), vs_get(vst, base + 3), [roots, vs_get(vst, base + 3), vs_get(vst, base + 4)])
             call vs_set(vst, base + 3, x)
             call vs_set(vst, base + 5, vm_kw("prim"))
             e = gcl_cons(vs_get(vst, base + 5), vs_get(vst, base + 3), [roots, vs_get(vst, base + 3), vs_get(vst, base + 5)])
          else
             ! anything else: the machine's call, (:callv f args ..) -- its
             ! own when f is one of its closures, the runtime's otherwise
             x = vm_tr(c, head, [roots, vs_get(vst, base + 2)])
             call vs_set(vst, base + 4, x)
             if (c%ok) then
                x = vec_to_list(vs_get(vst, base + 2), [roots, vs_get(vst, base + 4)])
                call vs_set(vst, base + 3, x)
                x = gcl_cons(vs_get(vst, base + 4), vs_get(vst, base + 3), [roots, vs_get(vst, base + 3), vs_get(vst, base + 4)])
                call vs_set(vst, base + 3, x)
                call vs_set(vst, base + 5, vm_kw("callv"))
                e = gcl_cons(vs_get(vst, base + 5), vs_get(vst, base + 3), [roots, vs_get(vst, base + 3), vs_get(vst, base + 5)])
             end if
          end if
       end if
    case default
       c%ok = .false.
    end select
    v = e
    call vs_leave(vst, base)
    e = v
  end function vm_tr

  ! a slot read: a local, a capture (:capt i), or the fn itself
  function vm_slot_ref(c, s, roots) result(e)
    type(vm_tr_ctx), intent(inout) :: c
    integer, intent(in) :: s
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: e
    type(gc_stack), pointer :: vst
    integer :: base
    e = gc_nil()
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    if (s < 0 .or. s > ubound(c%map, 1)) then
       c%ok = .false.
    else if (c%map(s) >= 0) then
       call vs_set(vst, base + 1, vm_kw("local"))
       e = vm_l([vs_get(vst, base + 1), gc_int(int(c%map(s), gc_ip))], roots)
    else if (c%capt(s) >= 0) then
       call vs_set(vst, base + 1, vm_kw("capt"))
       e = vm_l([vs_get(vst, base + 1), gc_int(int(c%capt(s), gc_ip))], roots)
    else
       c%ok = .false.
    end if
    call vs_leave(vst, base)
  end function vm_slot_ref

  ! (:prim :clotran.vm/deref (:const var))
  function vm_deref_of(var, roots) result(e)
    type(gc_value), intent(in) :: var, roots(:)
    type(gc_value) :: e, x
    type(gc_stack), pointer :: vst
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, vm_kw("const"))
    x = vm_l([vs_get(vst, base + 1), var], [roots, var])
    call vs_set(vst, base + 2, x)
    call vs_set(vst, base + 1, vm_kw("prim"))
    call vs_set(vst, base + 3, vm_kw("clotran.vm/deref"))
    e = vm_l([vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 2)], roots)
    call vs_leave(vst, base)
  end function vm_deref_of

  ! kids i..j translated into a vector in slot acc; bump: each a dead local
  recursive subroutine vm_tr_kids(c, kids, i, j, acc, roots, bump)
    type(vm_tr_ctx), intent(inout) :: c
    type(gc_value), intent(in) :: kids, roots(:)
    integer, intent(in) :: i, j, acc
    logical, intent(in), optional :: bump
    type(gc_stack), pointer :: vst
    type(gc_value) :: x
    integer :: k, base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, kids)
    call vs_set(vst, acc, gcv_empty(roots))
    do k = i, j
       if (.not. c%ok) exit
       x = vm_tr(c, gcv_nth(vs_get(vst, base + 1), k), [roots, vs_get(vst, acc)])
       call vs_set(vst, base + 2, x)
       x = gcv_conj(vs_get(vst, acc), vs_get(vst, base + 2), [roots, vs_get(vst, acc), vs_get(vst, base + 2)])
       call vs_set(vst, acc, x)
       if (present(bump)) c%depth = c%depth + 1
    end do
    call vs_leave(vst, base)
  end subroutine vm_tr_kids

  ! (:prim NODE items ..)
  function vm_node_prim(nd, items, roots) result(e)
    type(gc_value), intent(in) :: nd, items, roots(:)
    type(gc_value) :: e, x
    type(gc_stack), pointer :: vst
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    x = vec_to_list(items, [roots, items, nd])
    call vs_set(vst, base + 1, x)
    x = gcl_cons(nd, vs_get(vst, base + 1), [roots, nd, vs_get(vst, base + 1)])
    call vs_set(vst, base + 1, x)
    call vs_set(vst, base + 2, vm_kw("prim"))
    e = gcl_cons(vs_get(vst, base + 2), vs_get(vst, base + 1), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function vm_node_prim

  ! (kw items ..)
  function vm_head_list(kw, items, roots) result(e)
    character(len=*), intent(in) :: kw
    type(gc_value), intent(in) :: items, roots(:)
    type(gc_value) :: e, x
    type(gc_stack), pointer :: vst
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    x = vec_to_list(items, [roots, items])
    call vs_set(vst, base + 1, x)
    call vs_set(vst, base + 2, vm_kw(kw))
    e = gcl_cons(vs_get(vst, base + 2), vs_get(vst, base + 1), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function vm_head_list

  ! (:let i0 (:let i1 .. body))
  function vm_wrap_lets(inits, body, roots) result(e)
    type(gc_value), intent(in) :: inits, body, roots(:)
    type(gc_value) :: e
    type(gc_stack), pointer :: vst
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, inits)
    call vs_set(vst, base + 2, body)
    call vs_set(vst, base + 3, vm_kw("let"))
    do i = gcv_count(inits) - 1, 0, -1
       e = vm_l([vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 1), i), vs_get(vst, base + 2)], &
            [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 2, e)
    end do
    e = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function vm_wrap_lets

  function vec_to_list(v, roots) result(l)
    type(gc_value), intent(in) :: v, roots(:)
    type(gc_value) :: l
    type(gc_stack), pointer :: vst
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, v)
    call vs_set(vst, base + 2, gc_nil())
    do i = gcv_count(v) - 1, 0, -1
       l = gcl_cons(gcv_nth(vs_get(vst, base + 1), i), vs_get(vst, base + 2), [roots, vs_get(vst, base + 1), &
            vs_get(vst, base + 2)])
       call vs_set(vst, base + 2, l)
    end do
    l = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function vec_to_list

  ! ---- A FN: its arities one function of the program -------------------

  ! One arity ar of a fn whose frame has nslots slots, captures capv
  ! (outer, inner) pairs and the fn itself in self_slot, as a clause
  ! (n body) or (n body :rest); nil when the VM cannot run it.
  function vm_clause(ar, nslots, capv, self_slot, roots) result(cl)
    type(gc_value), intent(in) :: ar, capv, roots(:)
    integer, intent(in) :: nslots, self_slot
    type(gc_value) :: cl, x, body
    type(gc_stack), pointer :: vst
    type(vm_tr_ctx), allocatable :: c
    integer :: base, i, nfixed, start, nl, ncap, s
    logical :: variadic
    cl = gc_nil()
    if (nslots > 4000) return
    vst => gc_my_stack()
    nfixed = int_of(gcv_nth(ar, 0))
    variadic = truthy(gcv_nth(ar, 1))
    start = int_of(gcv_nth(ar, 2))
    body = gcv_nth(ar, 3)
    nl = nfixed
    if (variadic) nl = nl + 1
    ncap = gcv_count(capv) / 2
    allocate(c)
    allocate(c%reads(0:nslots + 8), c%binds(0:nslots + 8), c%map(0:nslots + 8), c%capt(0:nslots + 8))
    c%reads = .false.
    c%binds = .false.
    c%map = -1
    c%capt = -1
    call vm_scan(c, body)
    if (.not. c%ok) return
    ! the parameters the clause's locals, the captures and the fn its closure's
    do i = 0, nl - 1
       c%map(start + i) = i
    end do
    do i = 0, ncap - 1
       s = int_of(gcv_nth(capv, 2 * i + 1))
       if (s >= 0 .and. s <= ubound(c%capt, 1)) c%capt(s) = i
    end do
    if (self_slot >= 0 .and. self_slot <= ubound(c%capt, 1)) c%capt(self_slot) = ncap
    c%depth = nl
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, body)
    if (c%fn_recur) then
       ! (:loop ((:local 0) .. (:local nl-1)) body): the parameters the loop's
       call vs_set(vst, base + 3, gcv_empty(roots))
       call vs_set(vst, base + 5, vm_kw("local"))
       do i = 0, nl - 1
          x = vm_l([vs_get(vst, base + 5), gc_int(int(i, gc_ip))], [roots, vs_get(vst, base + 3)])
          call vs_set(vst, base + 4, x)
          x = gcv_conj(vs_get(vst, base + 3), vs_get(vst, base + 4), [roots, vs_get(vst, base + 3), vs_get(vst, base + 4)])
          call vs_set(vst, base + 3, x)
          c%map(start + i) = nl + i
       end do
       c%depth = 2 * nl
       x = vm_tr(c, vs_get(vst, base + 1), [roots, vs_get(vst, base + 3)])
       call vs_set(vst, base + 2, x)
       if (c%ok) then
          x = vec_to_list(vs_get(vst, base + 3), [roots, vs_get(vst, base + 2)])
          call vs_set(vst, base + 3, x)
          call vs_set(vst, base + 5, vm_kw("loop"))
          x = vm_l([vs_get(vst, base + 5), vs_get(vst, base + 3), vs_get(vst, base + 2)], roots)
          call vs_set(vst, base + 2, x)
       end if
    else
       x = vm_tr(c, vs_get(vst, base + 1), roots)
       call vs_set(vst, base + 2, x)
    end if
    if (c%ok) then
       if (variadic) then
          call vs_set(vst, base + 5, vm_kw("rest"))
          cl = vm_l([gc_int(int(nfixed, gc_ip)), vs_get(vst, base + 2), vs_get(vst, base + 5)], roots)
       else
          cl = vm_l([gc_int(int(nfixed, gc_ip)), vs_get(vst, base + 2)], roots)
       end if
    end if
    call vs_leave(vst, base)
  end function vm_clause

  ! The fn whose arities, frame size, captures and self slot these are,
  ! compiled as one function of the program: its id, or -1. clause0 the
  ! first arity's clause index (arity i is clause0 + i); consts the
  ! program's constants of it, which the caller keeps alive.
  function vm_compile_fn(arities, nslots, capv, self_slot, display, clause0, consts, roots) result(f)
    type(gc_value), intent(in) :: arities, capv, display, roots(:)
    integer, intent(in) :: nslots, self_slot
    integer, intent(out) :: clause0
    type(gc_value), intent(out) :: consts
    integer :: f
    type(gc_value) :: x
    type(gc_stack), pointer :: vst
    type(vm_state) :: t
    type(vc_state) :: cce
    integer :: base, i, na, p0, c0
    integer(gc_ip) :: sz, pend, j
    f = -1
    clause0 = -1
    consts = gc_nil()
    vst => gc_my_stack()
    na = gcv_count(arities)
    ! slots: 1 the clauses, 2 3 scratch, 4 kw, 5 kw
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, gcv_empty(roots))
    do i = 0, na - 1
       x = vm_clause(gcv_nth(arities, i), nslots, capv, self_slot, [roots, vs_get(vst, base + 1)])
       if (x%tag == GCT_NIL) then
          vm_n_refused = vm_n_refused + 1
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 2, x)
       x = gcv_conj(vs_get(vst, base + 1), vs_get(vst, base + 2), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 1, x)
    end do
    ! the last clause: a call of no arity the fn has, clj's ArityException
    ! (0 (:prim :clotran.vm/arity (:const name) (:local 0)) :rest)
    call vs_set(vst, base + 4, vm_kw("const"))
    x = vm_l([vs_get(vst, base + 4), display], [roots, vs_get(vst, base + 1), display])
    call vs_set(vst, base + 2, x)
    call vs_set(vst, base + 4, vm_kw("local"))
    x = vm_l([vs_get(vst, base + 4), gc_int(0_gc_ip)], [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, x)
    call vs_set(vst, base + 4, vm_kw("clotran.vm/arity"))
    call vs_set(vst, base + 5, vm_kw("prim"))
    x = vm_l([vs_get(vst, base + 5), vs_get(vst, base + 4), vs_get(vst, base + 2), vs_get(vst, base + 3)], &
         [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, x)
    call vs_set(vst, base + 4, vm_kw("rest"))
    x = vm_l([gc_int(0_gc_ip), vs_get(vst, base + 2), vs_get(vst, base + 4)], [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, x)
    x = gcv_conj(vs_get(vst, base + 1), vs_get(vst, base + 2), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 1, x)
    x = vec_to_list(vs_get(vst, base + 1), roots)
    call vs_set(vst, base + 1, x)
    ! its place in the program, reserved: the code, the clauses, the id
    sz = vmicg_size_clauses(vs_get(vst, base + 1))
    call gc_state_lock()
    if (vmp_pc + sz + 1 < VMP_INSTRS .and. vmp_ci + na + 1 < VMP_CLAUSES .and. vmp_f + 1 < VMP_FNS) then
       f = vmp_f
       c0 = vmp_ci
       p0 = int(vmp_pc)
       ! its place and name, for a trace, before another can see the id
       vmp_fstart(f) = p0
       call gcp_str(display, .false., s=vmp_fnames(f)%s)
       vmp_f = vmp_f + 1
       vmp_ci = vmp_ci + na + 1
       vmp_pc = vmp_pc + int(sz)
    end if
    call gc_state_unlock()
    if (f < 0) then
       vm_n_refused = vm_n_refused + 1
       call vs_leave(vst, base)
       return
    end if
    ! ((f . clauses)), compiled at p0 by the generated compiler
    x = gcl_cons(gc_int(int(f, gc_ip)), vs_get(vst, base + 1), [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, x)
    x = vm_l([vs_get(vst, base + 2)], roots)
    call vs_set(vst, base + 3, x)
    if (vm_trace) then
       block
         character(len=:), allocatable :: txt
         call gcp_str(vs_get(vst, base + 3), .true., s=txt)
         write(0, '(a, i0, a, i0, a, a)') 'vm: fn ', f, ' at ', p0, ' ', txt
       end block
    end if
    t = vmp
    t%status = 0
    allocate(cce%env(0:4095))
    cce%env = 0
    cce%err = 0
    call vmicg_defs(t, cce, vs_get(vst, base + 3), int(f, gc_ip), int(c0, gc_ip), int(p0, gc_ip), pend)
    deallocate(cce%env)
    if (cce%err /= 0 .or. t%status /= 0 .or. pend /= p0 + sz) then
       ! the place stays reserved and unreachable: no template names f
       vm_n_refused = vm_n_refused + 1
       f = -1
       call vs_leave(vst, base)
       return
    end if
    call vmg_fuse(t, int(p0, gc_ip), pend)
    ! every word the compile wrote inside the bounds a run assumes
    do j = 4 * p0, 4 * pend - 1
       if (vmp%code(j) < 0 .or. vmp%code(j) > 1099511627776_gc_ip) then
          vm_n_refused = vm_n_refused + 1
          f = -1
          call vs_leave(vst, base)
          return
       end if
    end do
    ! the constants, kept alive by the caller
    x = gc_vec(int(sz), [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, x)
    do j = 0, sz - 1
       call gc_vec_set(vs_get(vst, base + 2), int(j) + 1, vmp%pool(p0 + j))
    end do
    consts = vs_get(vst, base + 2)
    clause0 = c0
    vm_n_ok = vm_n_ok + 1
    call vs_leave(vst, base)
  end function vm_compile_fn

  ! ---- THE RUN -----------------------------------------------------------

  ! An arity's body, its clause ci of the program, on frame fr of a call of
  ! fn: the frame a call makes on the VM's stack -- the parameters, the
  ! rest already packed, the fn above them -- a call record returning to
  ! the halt at pc 0, and the clause's code until the halt.
  recursive subroutine vm_run(tctx, nd, fr, fn, val)
    type(eval_ctx), pointer, intent(in) :: tctx
    type(gc_value), intent(in) :: nd, fr, fn
    type(gc_value), intent(inout) :: val
    type(gc_stack), pointer :: vst
    type(vm_state), target :: st
    type(gc_value) :: info
    integer :: sbase, i, nl, start, ci, win, top, hi
    integer(gc_ip) :: steps, ct0
    character(len=:), allocatable :: msg
    logical :: reg
    vst => tctx%stk
    ci = gc_i2(nd)
    info = gc_slot(nd, 3)
    start = int_of(gcv_nth(info, 0))
    nl = int_of(gcv_nth(info, 1))
    ! the stack: a window of the value stack, as much as is free up to 64K
    ! slots; it is nil already (vs_leave clears what it releases)
    win = min(VM_WINDOW, (size(vst%vstack) - vst%vs_top) / 4)
    if (win < nl + 64) then
       call raise_class("clotran.host.stack_overflow_error", "stack overflow", [nd])
       val = gc_nil()
       return
    end if
    sbase = vs_enter(vst, win)
    do i = 0, nl - 1
       vst%vstack(sbase + i + 1) = frame_get(fr, start + i)
    end do
    vst%vstack(sbase + nl + 1) = fn
    st%stk(0:win - 1) => vst%vstack(sbase + 1:sbase + win)
    st%code => vmp%code
    st%pool => vmp%pool
    st%fnfirst => vmp%fnfirst
    st%fncount => vmp%fncount
    st%cln => vmp%cln
    st%clent => vmp%clent
    st%clrest => vmp%clrest
    ! the control stack: this thread's, from where an enclosing run left it
    if (.not. associated(vst%vm_ctl)) then
       allocate(vst%vm_ctl(0:VM_CTL - 1, 5))
       vst%vm_ctl_top = 0
    end if
    ct0 = vst%vm_ctl_top
    if (VM_CTL - ct0 < 64) then
       call vs_leave(vst, sbase)
       call raise_class("clotran.host.stack_overflow_error", "stack overflow", [nd])
       val = gc_nil()
       return
    end if
    st%ckind(0:VM_CTL - ct0 - 1) => vst%vm_ctl(ct0:VM_CTL - 1, 1)
    st%ca(0:VM_CTL - ct0 - 1) => vst%vm_ctl(ct0:VM_CTL - 1, 2)
    st%cb(0:VM_CTL - ct0 - 1) => vst%vm_ctl(ct0:VM_CTL - 1, 3)
    st%cc(0:VM_CTL - ct0 - 1) => vst%vm_ctl(ct0:VM_CTL - 1, 4)
    st%cprev(0:VM_CTL - ct0 - 1) => vst%vm_ctl(ct0:VM_CTL - 1, 5)
    ! the call record the entry's call pushed: back to the halt
    st%ckind(0) = 1
    st%ca(0) = 0
    st%cb(0) = 0
    st%cc(0) = 0
    st%cprev(0) = -1
    st%ctop = 1
    st%hidx = -1
    st%fb = 0
    st%sp = nl + 1
    st%pc = vmp%clent(ci)
    st%status = 0
    ! a run nested in this one (through the evaluator) takes the records
    ! above; this one's records are below at most how deep it calls, so
    ! it is told the whole rest and a nested one starts past the most
    ! this one can have used -- the records are counted as they are taken
    vst%vm_ctl_top = int(ct0)
    ! on the thread's list of runs, for a trace taken while it runs
    if (tctx%n_vm_runs < size(tctx%vm_runs)) then
       tctx%n_vm_runs = tctx%n_vm_runs + 1
       tctx%vm_runs(tctx%n_vm_runs)%st => st
       tctx%vm_runs(tctx%n_vm_runs)%fstop = tctx%fstack_top
       reg = .true.
    else
       reg = .false.
    end if
    hi = nl + 1
    steps = 0
    do
       if (st%status /= 0) exit
       if (st%code(4 * st%pc) == 11 .and. st%ctop == 0) exit
       vst%vm_ctl_top = int(ct0 + st%ctop + 1)
       call vmg_xstep(st)
       if (st%sp > hi) hi = int(st%sp)
       steps = steps + 1
       if (iand(steps, 4095_gc_ip) == 0) then
          if (gc_stop_pending()) call gc_poll()
       end if
    end do
    vst%vm_ctl_top = int(ct0)
    select case (int(st%status))
    case (0)
       val = st%stk(st%sp - 1)
    case (1)
       ! a throw nothing in the body caught: a call's error is still
       ! raised, as it was; the body's own (:throw e) raised as N_THROW does
       if (.not. tctx%has_error) then
          val = st%stk(0)
          call set_thrown(val)
          tctx%has_error = .true.
          call gcp_str(val, .true., s=msg)
          tctx%last_error = msg
          call capture_trace()
       end if
       val = gc_nil()
    case default
       if (.not. tctx%has_error) call raise_class("clotran.host.stack_overflow_error", "stack overflow", [nd])
       val = gc_nil()
    end select
    if (reg) then
       tctx%vm_runs(tctx%n_vm_runs)%st => null()
       tctx%n_vm_runs = tctx%n_vm_runs - 1
    end if
    if (vm_trace) then
       write(0, '(a, i0, a, i0, a, i0)') 'vm run clause ', ci, ' status ', st%status, ' steps ', steps
    end if
    ! only the slots the run touched to clear: the rest are nil still
    top = sbase + min(hi + 8, win)
    if (vst%vs_top > top) vst%vs_top = top
    call vs_leave(vst, sbase)
  end subroutine vm_run

  ! ---- TRACES ------------------------------------------------------------

  ! the function whose code holds pc, or -1
  integer function vm_fn_at(pc)
    integer(gc_ip), intent(in) :: pc
    integer :: lo, hi, mid
    vm_fn_at = -1
    lo = 0
    hi = vmp_f - 1
    do while (lo <= hi)
       mid = (lo + hi) / 2
       if (vmp_fstart(mid) <= pc) then
          vm_fn_at = mid
          lo = mid + 1
       else
          hi = mid - 1
       end if
    end do
  end function vm_fn_at

  ! The frames a trace shows, innermost first: idx(k) > 0 the frame stack's
  ! entry, < 0 a call inside a VM run, names(-idx(k)) its fn. A run's calls
  ! sit between the frame it was entered by and the frames pushed under it:
  ! the function at its pc, then each call record's caller but the entry's
  ! own, which is the frame stack's.
  subroutine trace_order(tctx, idx, names)
    type(eval_ctx), pointer, intent(in) :: tctx
    integer, allocatable, intent(out) :: idx(:)
    type(vm_fname), allocatable, intent(out) :: names(:)
    integer, allocatable :: buf(:)
    type(vm_fname), allocatable :: nb(:)
    integer :: i, r, j, n, nn, f
    allocate(buf(tctx%fstack_top + 64), nb(64))
    n = 0
    nn = 0
    do i = tctx%fstack_top, 1, -1
       do r = tctx%n_vm_runs, 1, -1
          if (tctx%vm_runs(r)%fstop /= i .or. .not. associated(tctx%vm_runs(r)%st)) cycle
          associate (st => tctx%vm_runs(r)%st)
            ! the function running, when it is not the entry's own
            if (st%ctop >= 2) then
               f = vm_fn_at(st%pc)
               if (f >= 0) call trace_push(n, nn, buf, nb, f)
            end if
            ! the innermost caller records: ctop-1 .. 2
            do j = int(st%ctop) - 1, 2, -1
               f = vm_fn_at(st%ca(j))
               if (f >= 0) call trace_push(n, nn, buf, nb, f)
            end do
          end associate
       end do
       if (n >= size(buf)) call grow_int(buf)
       n = n + 1
       buf(n) = i
    end do
    idx = buf(1:n)
    names = nb(1:max(nn, 0))
  end subroutine trace_order

  subroutine trace_push(n, nn, buf, nb, f)
    integer, intent(inout) :: n, nn
    integer, allocatable, intent(inout) :: buf(:)
    type(vm_fname), allocatable, intent(inout) :: nb(:)
    integer, intent(in) :: f
    type(vm_fname), allocatable :: t(:)
    if (nn >= size(nb)) then
       allocate(t(2 * size(nb)))
       t(1:nn) = nb(1:nn)
       call move_alloc(t, nb)
    end if
    nn = nn + 1
    nb(nn)%s = "?"
    if (allocated(vmp_fnames(f)%s)) nb(nn)%s = vmp_fnames(f)%s
    if (n >= size(buf)) call grow_int(buf)
    n = n + 1
    buf(n) = -nn
  end subroutine trace_push

  subroutine grow_int(a)
    integer, allocatable, intent(inout) :: a(:)
    integer, allocatable :: t(:)
    allocate(t(2 * size(a)))
    t(1:size(a)) = a
    call move_alloc(t, a)
  end subroutine grow_int

  ! CLOTRAN_STATS: how many fns the VM took
  subroutine vm_stats_print()
    integer :: k
    if (vm_mode /= 1) return
    write(0, '(a, i0, a, i0, a)') 'vm: ', vm_n_ok, ' fns compiled, ', vm_n_refused, ' refused'
    write(0, '(a, *(1x, i0, ":", i0))') 'vm: refused by node kind', (k, vm_refused_by(k), k = 0, 40)
  end subroutine vm_stats_print
