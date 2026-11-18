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
  !   a capture             (:capt i), read in place (exec-vmcs's ex-cs)
  !   the fn itself         a local: the clause's (:let (:capt ncap) ..)
  !                         after the parameters (when the body reads
  !                         it), as ex-fbtc's self let
  !   var                   (:prim :clotran.vm/deref (:const var))
  !   if, throw             (:if c a b), (:throw e)
  !   do                    nested (:let e1 ..), each value a dead local
  !   let                   nested (:let init ..), each binding a local
  !   loop                  inits reading none before them: (:loop (init
  !                         ..) body); else the bindings as lets, then
  !                         (:loop ((:local ..)) body) over them (generated,
  !                         vtg_tr / vtg_lind: ex-tr's, vmtrg.lisp)
  !   recur                 (:recur args); the fn's own recur, a loop
  !                         around the body over its parameters
  !   vector, map, set, new, a dot call
  !                         (:prim NODE parts..): the runtime does what
  !                         flat does with the node (vm_node_hook;
  !                         generated, vtg_cop: NAMED against ex-tr's
  !                         (:prim ex-cop parts..), ex-cop :vector, :map,
  !                         :set or (:host k C))
  !   fn                    (:prim NODE captures..) (vm_node_hook;
  !                         generated, vtg_fnhd / vtg_caps: NAMED against
  !                         ex-tr's (:mkclo tm captures..))
  !   lazy-seq              (:prim NODE (:prim FN captures..)): the closure
  !                         as a fn's, FN an N_FN node of the lazy seq's
  !                         template, and the N_LAZY node's kind 6 wrapping
  !                         it (vm_node_hook; generated, vtg_cop / vtg_fnhd /
  !                         vtg_caps: NAMED against ex-tr's (:prim (:host 15
  !                         C) (:mkclo tm captures..)))
  !   a call of a builtin   (:prim builtin args)
  !   any other call        an IFn constant's or Var's (:callv head args);
  !                         else ex-trcall's, head first and cast: (:let head
  !                         (:if (:prim :ifn p) (:applyv p args) (:throw
  !                         (:prim :clotran.vm/notfn p)))) (generated)
  !   case*                 (:let test (:if (:prim NODE (:const then) p)
  !                         then .. default)), an entry's test case_branch's
  !                         probe taking it (vm_node_hook; generated)
  !   letfn                 a let a fn, (:let (:prim NODE (:const j) caps..
  !                         earlier..) ..), then the body: fn j's closure,
  !                         the group's captures patched (vm_node_hook;
  !                         generated, vtg_lfinit)
  !   try                   (:try body walk), the walk at the thrown value's
  !                         local p (:if (:prim NODE (:const j) p) catch_j ..
  !                         (:prim NODE p)); with a finally F (:let (:try
  !                         that (:if F (:prim NODE p) (:prim NODE p))) (:if
  !                         F p p)): catch_matches the test, (:prim NODE p)
  !                         the rethrow -- the host's error raised again as
  !                         the VM caught it (vm_caught, vm_rethrow), where
  !                         exec-vmtr's ex-trh / ex-trfin have (:throw p)
  !                         (vm_node_hook; generated, vtg_catest, vtg_rethrow)
  ! and a last clause (0 .. :rest) for a call of no arity the fn has,
  ! clj's ArityException. Anything else -- def, set!, the host's forms --
  ! and the fn runs as before.
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
          vmrt_cast => vm_cast_hook
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
  ! raised while the VM unwinds: out of the run, vm_run leaves it as it
  ! was; into a (:try ..)'s handler, the next hook clears it (vm_caught)
  recursive subroutine vm_call_hook(fn, argbase, nargs, out, ok)
    type(gc_value), intent(in) :: fn
    integer, intent(in) :: argbase, nargs
    type(gc_value), intent(out) :: out
    logical, intent(out) :: ok
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value) :: b
    ! a builtin, or a core fn that only wraps one, on what is already there:
    ! answered in place, as gce_apply_slots's first test answers it -- they
    ! cannot fail, and every element of a seq a VM body walks comes here
    if (nargs == 1 .or. nargs == 2) then
       b = fn
       if (gc_kind(b) == OBJ_CLOSURE) b = wrapper_of(b, nargs)
       if (gc_kind(b) == OBJ_BUILTIN) then
          vst => gc_my_stack()
          ok = .true.
          if (gc_i1(b) >= 0 .and. gc_i1(b) <= 1023) bi_fast_n(gc_i1(b)) = bi_fast_n(gc_i1(b)) + 1
          if (nargs == 1) then
             if (flat_seq_op(gc_i1(b), vst%vstack(argbase + 1), out)) return
             if (flat_int_op(gc_i1(b), 1, vst%vstack(argbase + 1), vst%vstack(argbase + 1), out)) return
          else
             if (flat_int_op(gc_i1(b), 2, vst%vstack(argbase + 1), vst%vstack(argbase + 2), out)) return
             if (flat_cons_op(gc_i1(b), 2, vst%vstack(argbase + 1), vst%vstack(argbase + 2), out)) return
          end if
       end if
    end if
    tctx => ctx_self()
    vst => tctx%stk
    call vm_caught(tctx)
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
          ! the value the VM unwinds with is the raised one (vm_caught
          ! keeps it, vm_run's status 1 knows it)
          call set_thrown(out)
       end if
    end if
  end subroutine vm_took

  ! THE VM'S CATCH (exec-PLAN item 5(b)). A hook reports a throw by leaving
  ! the host's error raised while the VM unwinds; a hook entered with it
  ! still raised means the VM's (:try ..) caught it -- its catch walk's first
  ! test, a finally's first call, the rethrow at its end. Here the error
  ! is cleared, as exec_try's catch clears it, and kept: its value, message
  ! and trace on the run's list (the last four), the calls it unwound out
  ! of gone from the frame stack (exec_try's ftop). vm_run clears what is
  ! left at a normal end.
  subroutine vm_caught(tctx)
    type(eval_ctx), pointer, intent(in) :: tctx
    type(gc_value) :: v
    integer :: k
    if (.not. tctx%has_error) return
    if (tctx%n_vm_deep == 0 .and. tctx%n_vm_runs > 0) then
       associate (r => tctx%vm_runs(tctx%n_vm_runs))
         tctx%fstack_top = min(tctx%fstack_top, r%fstop)
         v = gc_root_get(r%exc_root)
         if (gc_vec_len(v) /= 4) then
            v = gc_vec(4, [thrown_value()])
            call gc_global_keep(r%exc_root, v)
         end if
         k = mod(r%nexc, 4) + 1
         r%nexc = r%nexc + 1
         call gc_vec_set(v, k, thrown_value())
         r%emsg(k)%s = ""
         if (allocated(tctx%last_error)) r%emsg(k)%s = tctx%last_error
         r%etr(k)%s = ""
         if (allocated(tctx%last_trace)) r%etr(k)%s = tctx%last_trace
       end associate
    end if
    call gce_clear_error()
  end subroutine vm_caught

  ! THE RETHROW (vmtrg's vtg-rethrow: vm.inc's (:prim NODE (:local p)) where
  ! exec-vmtr's ex-trh / ex-trfin have (:throw (:local p)) -- a catch walk's
  ! end, a finally's after an uncaught throw). p a host error vm_caught kept:
  ! raised again with its message and trace, as the tree's implicit rethrows
  ! keep them (k_unwind's pop, exec_core's action 22); else a value the VM
  ! threw itself, raised as N_THROW raises it. Either way (:throw . p).
  ! ponytail: four kept a run -- a finally that itself catches four host
  ! errors before its rethrow loses the first's message (the value's text)
  subroutine vm_rethrow(tctx, p)
    type(eval_ctx), pointer, intent(in) :: tctx
    type(gc_value), intent(in) :: p
    type(gc_value) :: v
    integer :: q, k
    character(len=:), allocatable :: msg
    if (tctx%n_vm_deep == 0 .and. tctx%n_vm_runs > 0) then
       associate (r => tctx%vm_runs(tctx%n_vm_runs))
         v = gc_root_get(r%exc_root)
         if (r%nexc > 0 .and. gc_vec_len(v) == 4) then
            do q = r%nexc, max(1, r%nexc - 3), -1
               k = mod(q - 1, 4) + 1
               if (.not. gc_identical(gc_vec_get(v, k), p)) cycle
               call set_thrown(p)
               tctx%has_error = .true.
               tctx%last_error = r%emsg(k)%s
               tctx%last_trace = r%etr(k)%s
               r%nexc = q - 1
               return
            end do
         end if
       end associate
    end if
    call set_thrown(p)
    tctx%has_error = .true.
    call gcp_str(p, .true., s=msg)
    tctx%last_error = msg
    call capture_trace()
  end subroutine vm_rethrow

  ! a call's cast, head first (ex-trcall): kind 9 (:prim :ifn v) is_ifn's
  ! answer, as exec_core's; kind 10 (:prim :clotran.vm/notfn v) its
  ! refusal, refuse_not_fn's error raised, as exec_core's action 23
  recursive subroutine vm_cast_hook(op, argbase, nargs, out, ok)
    type(gc_value), intent(in) :: op
    integer, intent(in) :: argbase, nargs
    type(gc_value), intent(out) :: out
    logical, intent(out) :: ok
    type(eval_ctx), pointer :: tctx
    type(gc_stack), pointer :: vst
    tctx => ctx_self()
    vst => tctx%stk
    call vm_caught(tctx)
    out = gc_nil()
    ok = .true.
    if (nargs /= 1) return
    if (gc_identical(op, vm_kw("ifn"))) then
       out = gc_bool(is_ifn(vs_get(vst, argbase + 1)))
    else
       call refuse_not_fn(vs_get(vst, argbase + 1))
       call vm_took(tctx, ok, out, op)
    end if
  end subroutine vm_cast_hook

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
    call vm_caught(tctx)
    out = gc_nil()
    call gcp_str(vs_get(vst, argbase + 1), .false., s=who)
    write(buf, '(i0)') seq_len(vs_get(vst, argbase + nargs))
    call raise_class("clotran.host.arity_exception", "Wrong number of args (" // trim(buf) // ") passed to: " // who, [name])
    call vm_took(tctx, ok, out, name)
  end subroutine vm_arity_hook

  ! a Var's value -- or, given a DIRECT-LINKED Var's node (DEVIATIONS 55),
  ! the fn the call site bound, as exec.inc's N_CALL reads it
  function vm_deref_hook(var) result(v)
    type(gc_value), intent(in) :: var
    type(gc_value) :: v, fnv
    if (gc_kind(var) == OBJ_AST) then
       fnv = gc_slot(var, 5)
       if (fnv%tag == GCT_INT) then
          if (fnv%ival /= link_epoch) then
             fnv = gcn_var_value(gc_slot(var, 2))
             if (gc_kind(fnv) == OBJ_COMPILED) call gc_set_slot(var, 3, fnv)
             call gc_set_slot(var, 5, gc_int(int(link_epoch, gc_ip)))
          end if
          v = gc_slot(var, 3)
       else
          v = var_deref(gc_slot(var, 2), [var])
       end if
       return
    end if
    v = var_deref(var, [var])
  end function vm_deref_hook

  ! what a Var node is read through: the node itself when it is direct-
  ! linked to a fn (vm_deref_hook), else its Var
  function vm_var_ref(nd) result(r)
    type(gc_value), intent(in) :: nd
    type(gc_value) :: r
    type(gc_value) :: ep
    r = gc_slot(nd, 2)
    if (gc_i2(nd) == 1) then
       ep = gc_slot(nd, 5)
       if (ep%tag == GCT_INT) r = nd
    end if
  end function vm_var_ref

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
    integer :: base, j, from, ncap, s0, jj, off, tot, f, q, o
    tctx => ctx_self()
    vst => tctx%stk
    call vm_caught(tctx)
    out = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, nd)
    select case (gc_i1(nd))
    case (N_TRY)
       ! (:prim nd (:const j) v): whether catch j's class takes v (vmtrg's
       ! vtg-catest, NAMED: the model's prim :isa, exec_try's catch_matches);
       ! (:prim nd p): the rethrow (vtg-rethrow, vm_rethrow)
       if (n == 2) then
          out = gc_bool(catch_matches(gcv_nth(gcv_nth(gc_slot(vs_get(vst, base + 1), 2), &
               int_of(vs_get(vst, argbase + 1))), 0), vs_get(vst, argbase + 2), gc_nil()))
       else if (n == 1) then
          call vm_rethrow(tctx, vs_get(vst, argbase + 1))
       end if
    case (N_CASE)
       ! (:prim nd (:const then) v): whether case_branch's probe of v takes
       ! the entry whose then is that node (vmtrg's vtg-cstest, NAMED: the
       ! model's prim :case of the entry's test and v)
       ! ponytail: one probe an entry walked, O(entries) a case where the
       ! tree's is one probe; cache the last (nd, v) if a hot case shows it
       if (n == 2) out = gc_bool(gc_identical(case_branch(vs_get(vst, base + 1), vs_get(vst, argbase + 2)), &
            vs_get(vst, argbase + 1)))
    case (N_LETFN)
       ! (:prim nd (:const j) caps.. earlier..), vmtrg's vtg-lfinit -- NAMED:
       ! the model's (:mkgrp (j . shape) caps..), x2-seal's j-th closure. Fn
       ! j's closure from its captures (every fn's, in turn, after j), then
       ! the group's patched as exec_letfn's refresh_captures does: its own
       ! capture of fn m < j the earlier let's closure m (args 2+tot+m), of
       ! itself itself, and each earlier closure's capture of fn j this one --
       ! after the last let one group, its fns identical as the tree's
       s0 = int_of(gc_slot(nd, 2))
       jj = int_of(vs_get(vst, argbase + 1))
       off = 1
       tot = 0
       do f = 0, gc_i2(nd) - 1
          q = gcv_count(gcv_nth(gc_slot(ast_kid(nd, int(f, int64)), 2), 2)) / 2
          if (f < jj) off = off + q
          tot = tot + q
       end do
       if (jj >= 0 .and. jj < gc_i2(nd) .and. n == 1 + tot + jj) then
          x = ast_kid(nd, int(jj, int64))
          capv = gcv_nth(gc_slot(x, 2), 2)
          ncap = gcv_count(capv) / 2
          call vm_node_hook(x, argbase + off, ncap, out, ok)
          if (ok) then
             call vs_set(vst, base + 2, out)
             do q = 0, ncap - 1
                o = int_of(gcv_nth(capv, 2 * q)) - s0
                if (o >= 0 .and. o < jj) then
                   call cap_put(out, q, ncap, vs_get(vst, argbase + 2 + tot + o))
                else if (o == jj) then
                   call cap_put(out, q, ncap, out)
                end if
             end do
             do f = 0, jj - 1
                capv = gcv_nth(gc_slot(ast_kid(nd, int(f, int64)), 2), 2)
                do q = 0, gcv_count(capv) / 2 - 1
                   if (int_of(gcv_nth(capv, 2 * q)) == s0 + jj) &
                        call cap_put(vs_get(vst, argbase + 2 + tot + f), q, gcv_count(capv) / 2, out)
                end do
             end do
          end if
       end if
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
    case (N_LAZY)
       ! (:prim NODE closure): the lazy seq of its fn, pending, as eval_new's
       ! clotran.host.lazy_seq (the closure built by its N_FN op, vtg_fnhd)
       if (n == 1) then
          call vs_set(vst, base + 3, vs_get(vst, argbase + 1))
          out = gc_obj(OBJ_LAZY, [vs_get(vst, base + 3), gc_nil(), gc_nil()], [vs_get(vst, base + 3)])
          call gc_set_i1(out, LAZY_PENDING)
       end if
    case (N_FN)
       ! the closure straight from the captured values, in its template's
       ! capture order: make_closure_from's two shapes, with no frame built
       ! to copy them out of
       call vs_set(vst, base + 2, gc_slot(nd, 2))
       ncap = gcv_count(gcv_nth(vs_get(vst, base + 2), 2)) / 2
       if (ncap <= 2) then
          capv = gc_nil()
          x = gc_nil()
          if (ncap >= 1) capv = vs_get(vst, argbase + 1)
          if (ncap >= 2) x = vs_get(vst, argbase + 2)
          out = gc_obj(OBJ_CLOSURE, [vs_get(vst, base + 2), capv, gc_nil(), x, gc_nil()], [nd])
       else
          x = gc_vec(ncap, [nd])
          call vs_set(vst, base + 3, x)
          do j = 0, ncap - 1
             call gc_vec_set(vs_get(vst, base + 3), j + 1, vs_get(vst, argbase + j + 1))
          end do
          out = gc_obj(OBJ_CLOSURE, [vs_get(vst, base + 2), vs_get(vst, base + 3), gc_nil(), gc_nil(), gc_nil()], [nd])
       end if
       call closure_note_table(out)
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
    type(gc_value) :: kids, head
    integer :: i, j, n, start
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
       do i = 0, gcv_count(kids) - 1
          call vm_scan(c, gcv_nth(kids, i))
       end do
    case (N_LETFN)
       ! its fns' captures read (each must be a fn), its slots bound, its body
       n = gc_i2(nd)
       start = int_of(gc_slot(nd, 2))
       do i = 0, n - 1
          head = gcv_nth(kids, i)
          if (gc_kind(head) /= OBJ_AST) then
             c%ok = .false.
             return
          end if
          if (gc_i1(head) /= N_FN) then
             c%ok = .false.
             return
          end if
          head = gcv_nth(gc_slot(head, 2), 2)
          do j = 0, gcv_count(head) / 2 - 1
             call vm_mark(c%reads, int_of(gcv_nth(head, 2 * j)), c)
          end do
          call vm_mark(c%binds, start + i, c)
       end do
       call vm_scan(c, gcv_nth(kids, n))
    case (N_TRY)
       ! the body, the finally, and each catch's body, its slot bound
       call vm_scan(c, gcv_nth(kids, 0))
       if (vtg_nk(nd) > 1) call vm_scan(c, gcv_nth(kids, 1))
       do i = 0, int(vtg_ncs(nd)) - 1
          call vm_mark(c%binds, int(vtg_cslot(nd, int(i, int64))), c)
          call vm_scan(c, vtg_cbody(nd, int(i, int64)))
       end do
    case (N_CASE)
       ! the test, the default, and each entry's then
       do i = 0, gcv_count(kids) - 1
          call vm_scan(c, gcv_nth(kids, i))
       end do
       do i = 0, int(vtg_ncs(nd)) - 1
          call vm_scan(c, vtg_cthen(nd, int(i, int64)))
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
    type(vm_tr_ctx), intent(inout), target :: c
    type(gc_value), intent(in) :: nd, roots(:)
    type(gc_value) :: e
    e = gc_nil()
    if (.not. c%ok) return
    if (gc_i1(nd) == N_CONST .or. gc_i1(nd) == N_VAR .or. gc_i1(nd) == N_LOCAL .or. gc_i1(nd) == N_IF .or. gc_i1(nd) == N_THROW &
         .or. gc_i1(nd) == N_LET .or. gc_i1(nd) == N_DO .or. gc_i1(nd) == N_LOOP .or. gc_i1(nd) == N_RECUR &
         .or. gc_i1(nd) == N_CALL .or. gc_i1(nd) == N_CASE .or. gc_i1(nd) == N_LETFN .or. gc_i1(nd) == N_TRY &
         .or. gc_i1(nd) == N_VECTOR .or. gc_i1(nd) == N_MAP .or. gc_i1(nd) == N_SET .or. gc_i1(nd) == N_NEW &
         .or. gc_i1(nd) == N_DOT .or. gc_i1(nd) == N_FN .or. gc_i1(nd) == N_LAZY) then
       e = vm_tr_gen(c, nd, roots)
       return
    end if
    ! every other kind: vm_scan refuses it, the fn stays the tree's
    c%ok = .false.
  end function vm_tr

  ! ---- THE GENERATED TRANSLATION'S HOST (model/vmtrg.lisp) ---------------
  ! A constant, a local, a Var, if, do, let*, loop, recur, throw, every call, case*, letfn,
  ! try, a vector, map, set, new or dot call, a fn and a lazy seq are translated by vtg_tr
  ! (src/f/gen/vm_tr_gen.inc), generated from model/vmtrg.lisp, which
  ! proves it pushes exactly exec-vmtr's ex-tr (vtg-tr-ex-tr). What it
  ! calls is here, each the shim vmtrg.lisp states: the tree's reads, the
  ! output stack (the value stack), and the scope (vm_tr_ctx's map and
  ! depth; vtg_local's map the positions with the fn's captures read in
  ! place, (:capt i), exec-vmcs's ex-cs -- exact). Named, not exact:
  ! vtg_blank blanks nothing and vtg_restore undoes binds only -- a blanked
  ! slot is read by no tree exec-vm's ex-vwf admits.

  ! nd by vtg_tr: the caller's roots kept on the value stack while it runs
  recursive function vm_tr_gen(c, nd, roots) result(e)
    type(vm_tr_ctx), intent(inout), target :: c
    type(gc_value), intent(in) :: nd, roots(:)
    type(gc_value) :: e
    type(gc_stack), pointer :: vst
    type(vtg_state) :: tb
    integer :: base, j
    vst => gc_my_stack()
    base = vs_enter(vst, size(roots) + 1)
    do j = 1, size(roots)
       call vs_set(vst, base + j, roots(j))
    end do
    call vs_set(vst, base + size(roots) + 1, nd)
    tb%c => c
    call vtg_tr(tb, 0_int64, nd, 0_int64)
    e = vs_get(vst, vst%vs_top)
    call vs_leave(vst, base)
  end function vm_tr_gen

  integer(int64) function vtg_kind(nd)
    type(gc_value), intent(in) :: nd
    vtg_kind = ast_kind(nd)
  end function vtg_kind
  integer(int64) function vtg_i2(nd)
    type(gc_value), intent(in) :: nd
    vtg_i2 = ast_i2(nd)
  end function vtg_i2
  ! a try's kids are its body and its finally, nil when it has none: then
  ! one (NAMED: the model's ex-nk, exec_core's nk of an N_TRY)
  integer(int64) function vtg_nk(nd)
    type(gc_value), intent(in) :: nd
    vtg_nk = ast_nkids(nd)
    if (ast_kind(nd) == N_TRY .and. vtg_nk > 1) then
       if (gc_kind(ast_kid(nd, 1_int64)) /= OBJ_AST) vtg_nk = 1
    end if
  end function vtg_nk
  function vtg_kid(nd, j) result(k)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: j
    type(gc_value) :: k
    k = ast_kid(nd, j)
  end function vtg_kid
  ! whether a fn's or lazy seq's captures name a slot in lo .. hi-1: its
  ! template's (outer, inner) pairs, the outer slot each first
  logical function vtg_rdcap(nd, lo, hi) result(yes)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: lo, hi
    type(gc_value) :: caps
    integer :: i, s
    yes = .false.
    if (gc_kind(nd) /= OBJ_AST) return
    caps = gcv_nth(gc_slot(nd, 2), 2)
    do i = 0, gcv_count(caps) / 2 - 1
       s = int_of(gcv_nth(caps, 2 * i))
       if (s >= lo .and. s < hi) yes = .true.
    end do
  end function vtg_rdcap
  ! a fn's captures (vmtrg's vtg-ncap, vtg-capo): its template's (outer,
  ! inner) pairs, how many, and capture j's outer slot -- NAMED: the model
  ! reads ex-outers of the template's list, here slot 2's vector
  integer(int64) function vtg_ncap(nd)
    type(gc_value), intent(in) :: nd
    vtg_ncap = 0
    if (gc_kind(nd) /= OBJ_AST) return
    vtg_ncap = gcv_count(gcv_nth(gc_slot(nd, 2), 2)) / 2
  end function vtg_ncap
  integer(int64) function vtg_capo(nd, j)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: j
    vtg_capo = 0
    if (j < 0 .or. j >= vtg_ncap(nd)) return
    vtg_capo = int_of(gcv_nth(gcv_nth(gc_slot(nd, 2), 2), int(2 * j)))
  end function vtg_capo
  ! a fn's captures for its scope (vmtrcl's vtg-nin, vtg-inr): how many,
  ! capture j's inner slot -- NAMED: tm here is the template's (outer,
  ! inner) pair vector vm_compile_fn is handed (capv), where the model reads
  ! ex-inners of the template's list
  integer(int64) function vtg_nin(tm)
    type(gc_value), intent(in) :: tm
    vtg_nin = gcv_count(tm) / 2
  end function vtg_nin
  integer(int64) function vtg_inr(tm, j)
    type(gc_value), intent(in) :: tm
    integer(int64), intent(in) :: j
    vtg_inr = 0
    if (j < 0 .or. j >= vtg_nin(tm)) return
    vtg_inr = int_of(gcv_nth(tm, int(2 * j + 1)))
  end function vtg_inr
  ! a case's table (slot 2: each [test then-node] by its key): how many
  ! entries, and entry j's then node, in gca_entries' order (vmtrg's
  ! vtg-ncs, vtg-cthen -- NAMED: the model reads ex-c's list in its order;
  ! the macro's tests are distinct, so at most one entry takes a value)
  ! ponytail: gca_entries each read, O(entries^2) a case translated once
  integer(int64) function vtg_ncs(nd)
    type(gc_value), intent(in) :: nd
    vtg_ncs = 0
    if (ast_kind(nd) == N_CASE) vtg_ncs = gca_count(gc_slot(nd, 2))
    if (ast_kind(nd) == N_TRY) vtg_ncs = gcv_count(gc_slot(nd, 2))
  end function vtg_ncs
  ! a try's catch j (slot 2's j-th, [class slot body]): its body, its slot
  function vtg_cbody(nd, j) result(b)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: j
    type(gc_value) :: b
    b = gc_nil()
    if (ast_kind(nd) == N_TRY .and. j >= 0 .and. j < vtg_ncs(nd)) b = gcv_nth(gcv_nth(gc_slot(nd, 2), int(j)), 2)
  end function vtg_cbody
  integer(int64) function vtg_cslot(nd, j)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: j
    vtg_cslot = 0
    if (ast_kind(nd) == N_TRY .and. j >= 0 .and. j < vtg_ncs(nd)) vtg_cslot = int_of(gcv_nth(gcv_nth(gc_slot(nd, 2), int(j)), 1))
  end function vtg_cslot
  function vtg_cthen(nd, j) result(t)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: j
    type(gc_value) :: t
    type(gc_value), allocatable :: ks(:), vls(:)
    t = gc_nil()
    if (ast_kind(nd) /= N_CASE) return
    call gca_entries(gc_slot(nd, 2), ks, vls)
    if (j >= 0 .and. j < size(vls)) t = gcv_nth(strip_meta(vls(j + 1)), 1)
  end function vtg_cthen
  ! slot 2: a constant's value, a let's first slot
  function vtg_c(nd) result(v)
    type(gc_value), intent(in) :: nd
    type(gc_value) :: v
    v = gc_nil()
    if (gc_kind(nd) == OBJ_AST) v = gc_slot(nd, 2)
  end function vtg_c
  integer(int64) function vtg_s2(nd)
    type(gc_value), intent(in) :: nd
    vtg_s2 = 0
    if (gc_kind(nd) == OBJ_AST) vtg_s2 = int_of(gc_slot(nd, 2))
  end function vtg_s2

  subroutine vtg_const(tb, v)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: v
    type(gc_value) :: k
    k = vm_kw("const")
    call anb_push(vm_l([k, v], [k, v]))
  end subroutine vtg_const
  ! a Var: (:prim :clotran.vm/deref (:const var)), the node itself when direct-linked
  subroutine vtg_deref(tb, nd)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: nd
    call anb_push(vm_deref_of(vm_var_ref(nd), [nd]))
  end subroutine vtg_deref
  ! a call whose head is read at translation (vmtrg.lisp's vtg-pk, exec-vmtr's
  ! ex-pk): 1 its head a constant builtin, not apply -- NAMED: OBJ_BUILTIN
  ! where the model asks prim :clotran.vm/builtin; 2 its head a DIRECT-LINKED
  ! Var whose bound fn only wraps a builtin at this arity (the fn fixed when
  ! the site was analysed, DEVIATIONS 55, so the builtin is too: no deref,
  ! no look-up of the wrapper each time) -- NAMED: vm_linked_builtin where
  ! the model asks i2 1 and prim :clotran.vm/wraps; 3 any other Var whose fn
  ! now only wraps a builtin at this arity, as core's first and next do --
  ! NAMED: vm_wraps where the model asks prim :clotran.vm/wraps; 4 any other
  ! constant or Var whose value is an IFn and not apply, (:callv head args..)
  ! -- NAMED: is_ifn of the constant, or of the Var's value or linked fn
  ! now (vtg_hv), where the model asks prim :ifn of v; 0 any other.
  ! vtg_hd pushes (:prim items.. args..)'s items: the constant, the wrapped
  ! builtin, or :clotran.vm/callw and (:const var), the runtime's call of
  ! what the Var holds then (the Var's node when it is direct-linked: the
  ! fn the site bound; NAMED: vm_var_ref's where the model's is v)
  integer(int64) function vtg_pk(nd)
    type(gc_value), intent(in) :: nd
    type(gc_value) :: h, f
    vtg_pk = 0
    if (ast_nkids(nd) < 1) return
    h = ast_kid(nd, 0_int64)
    if (ast_kind(h) == N_CONST) then
       f = strip_meta(gc_slot(h, 2))
       if (gc_kind(f) == OBJ_BUILTIN .and. gc_i1(f) /= B_APPLY) then
          vtg_pk = 1
       else if (vtg_ifn(f)) then
          vtg_pk = 4
       end if
    else if (vm_linked_builtin(h, int(ast_nkids(nd)) - 1)) then
       vtg_pk = 2
    else if (ast_kind(h) == N_VAR) then
       if (vm_wraps(h, int(ast_nkids(nd)) - 1)) then
          vtg_pk = 3
       else if (vtg_ifn(vtg_hv(h))) then
          vtg_pk = 4
       end if
    end if
  end function vtg_pk
  ! an IFn, not apply (vtg_pk 4's test)
  logical function vtg_ifn(f)
    type(gc_value), intent(in) :: f
    vtg_ifn = is_ifn(f)
    if (gc_kind(f) == OBJ_BUILTIN) vtg_ifn = vtg_ifn .and. gc_i1(f) /= B_APPLY
  end function vtg_ifn
  ! a Var node's value now: its linked fn, or its Var's value (vm_wraps')
  function vtg_hv(h) result(v)
    type(gc_value), intent(in) :: h
    type(gc_value) :: v
    v = gc_nil()
    if (.not. gcn_is_var(gc_slot(h, 2))) return
    v = vm_var_ref(h)
    if (gc_kind(v) == OBJ_AST) then
       v = strip_meta(gc_slot(h, 3))
    else
       v = strip_meta(gcn_var_value(v))
    end if
  end function vtg_hv
  subroutine vtg_hd(tb, nd)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: nd
    type(gc_value) :: h
    h = ast_kid(nd, 0_int64)
    if (vtg_pk(nd) == 4) then
       if (ast_kind(h) == N_CONST) then
          call vtg_const(tb, vtg_c(h))
       else
          call vtg_deref(tb, h)
       end if
    else if (ast_kind(h) == N_CONST) then
       call anb_push(gc_slot(h, 2))
    else if (vtg_pk(nd) == 2) then
       call anb_push(wrapper_of(strip_meta(gc_slot(h, 3)), int(ast_nkids(nd)) - 1))
    else
       call anb_push(vm_kw("clotran.vm/callw"))
       call anb_push(vm_l([vm_kw("const"), vm_var_ref(h)], [h]))
    end if
  end subroutine vtg_hd
  subroutine vtg_nil(tb)
    type(vtg_state), intent(inout) :: tb
    call vtg_const(tb, gc_nil())
  end subroutine vtg_nil
  subroutine vtg_local(tb, s)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: s
    call anb_push(vm_slot_ref(tb%c, int(s), [gc_value ::]))
  end subroutine vtg_local
  ! (op items..) of the top n: 1 :if, 2 :let, 3 :throw, 4 :loop, 5 :recur, 6 :prim, 7 :callv, 8 :applyv, 9 :try; 0 the items alone
  subroutine vtg_node(tb, op, n)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: op, n
    type(gc_stack), pointer :: vst
    type(gc_value) :: l, k
    integer :: j, top
    vst => gc_my_stack()
    top = vst%vs_top
    l = gc_nil()
    do j = top, top - int(n) + 1, -1
       l = gcl_cons(vs_get(vst, j), l, [l])
    end do
    if (op /= 0) then
       select case (op)
       case (1); k = vm_kw("if")
       case (2); k = vm_kw("let")
       case (4); k = vm_kw("loop")
       case (5); k = vm_kw("recur")
       case (6); k = vm_kw("prim")
       case (7); k = vm_kw("callv")
       case (8); k = vm_kw("applyv")
       case (9); k = vm_kw("try")
       case default; k = vm_kw("throw")
       end select
       l = gcl_cons(k, l, [l, k])
    end if
    call vs_leave(vst, top - int(n))
    call anb_push(l)
  end subroutine vtg_node
  ! slot s the next local, the old mapping on the trail
  subroutine vtg_bind(tb, s)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: s
    if (s < 0 .or. s > ubound(tb%c%map, 1)) then
       tb%c%ok = .false.
       return
    end if
    if (.not. allocated(tb%c%trs)) allocate(tb%c%trs(16), tb%c%tro(16))
    if (tb%c%ntr >= size(tb%c%trs)) then
       call grow_int(tb%c%trs)
       call grow_int(tb%c%tro)
    end if
    tb%c%ntr = tb%c%ntr + 1
    tb%c%trs(tb%c%ntr) = int(s)
    tb%c%tro(tb%c%ntr) = tb%c%map(s)
    tb%c%map(s) = tb%c%depth
    tb%c%depth = tb%c%depth + 1
  end subroutine vtg_bind
  ! a loop's slots s .. s+n-1 the next locals (each on the trail)
  ! capture j's inner slot s read in place (vmtrcl's vtg-capin -- NAMED:
  ! c%capt(s) = j, no local, where the model appends s to the scope; a slot
  ! out of the map's range is left unread, so a read of it refuses)
  subroutine vtg_capin(tb, s, j)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: s, j
    if (s >= 0 .and. s <= ubound(tb%c%capt, 1)) tb%c%capt(s) = int(j)
  end subroutine vtg_capin
  subroutine vtg_binds(tb, s, n)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: s, n
    integer(int64) :: j
    do j = 0, n - 1
       call vtg_bind(tb, s + j)
    end do
  end subroutine vtg_binds
  ! a dead local: the next local, no slot mapped to it (vtg_restore gives the depth back)
  subroutine vtg_dead(tb)
    type(vtg_state), intent(inout) :: tb
    tb%c%depth = tb%c%depth + 1
  end subroutine vtg_dead
  subroutine vtg_blank(tb, x)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: x
  end subroutine vtg_blank
  subroutine vtg_save(tb)
    type(vtg_state), intent(inout) :: tb
    if (.not. allocated(tb%c%svd)) allocate(tb%c%svd(16), tb%c%svt(16))
    if (tb%c%nsv >= size(tb%c%svd)) then
       call grow_int(tb%c%svd)
       call grow_int(tb%c%svt)
    end if
    tb%c%nsv = tb%c%nsv + 1
    tb%c%svd(tb%c%nsv) = tb%c%depth
    tb%c%svt(tb%c%nsv) = tb%c%ntr
  end subroutine vtg_save
  subroutine vtg_restore(tb)
    type(vtg_state), intent(inout) :: tb
    if (tb%c%nsv <= 0) return
    do while (tb%c%ntr > tb%c%svt(tb%c%nsv))
       tb%c%map(tb%c%trs(tb%c%ntr)) = tb%c%tro(tb%c%ntr)
       tb%c%ntr = tb%c%ntr - 1
    end do
    tb%c%depth = tb%c%svd(tb%c%nsv)
    tb%c%nsv = tb%c%nsv - 1
  end subroutine vtg_restore
  ! ex-trcall's parts (vmtrg.lisp's vtg-top, vtg-cast, vtg-notfn), the head
  ! bound at the last local, depth - 1 -- NAMED: the depth is the model's
  ! scope length less the m captures, as vtg_local's map: (:local p); the
  ! cast (:prim :ifn (:local p)), the runtime's kind 9, is_ifn -- NAMED: the
  ! model's prim :ifn, as exec_core's cast; its refusal (:throw (:prim
  ! :clotran.vm/notfn (:local p))), the runtime's kind 10, refuse_not_fn of
  ! the head -- NAMED: where the model's is (:throw (:const :not-fn)), the
  ! host's error as exec_core's action 23 throws it, nothing run between
  function vtg_toploc(tb) result(l)
    type(vtg_state), intent(inout) :: tb
    type(gc_value) :: l, k
    k = vm_kw("local")
    l = vm_l([k, gc_int(int(tb%c%depth - 1, gc_ip))], [k])
  end function vtg_toploc
  subroutine vtg_top(tb)
    type(vtg_state), intent(inout) :: tb
    call anb_push(vtg_toploc(tb))
  end subroutine vtg_top
  subroutine vtg_cast(tb)
    type(vtg_state), intent(inout) :: tb
    type(gc_value) :: l, k, i
    l = vtg_toploc(tb)
    k = vm_kw("prim")
    i = vm_kw("ifn")
    call anb_push(vm_l([k, i, l], [l]))
  end subroutine vtg_cast
  subroutine vtg_notfn(tb)
    type(vtg_state), intent(inout) :: tb
    type(gc_value) :: l, k, i
    l = vtg_toploc(tb)
    k = vm_kw("prim")
    i = vm_kw("clotran.vm/notfn")
    l = vm_l([k, i, l], [l])
    k = vm_kw("throw")
    call anb_push(vm_l([k, l], [l]))
  end subroutine vtg_notfn
  ! a collection's op (vmtrg's vtg-cop): the node itself, the op of the
  ! runtime's kind 6 (vm_node_hook builds it from the parts' values) --
  ! NAMED: the model's exec-tree ex-cop, :vector, :map, :set or (:host k C)
  subroutine vtg_cop(tb, nd)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: nd
    call anb_push(nd)
  end subroutine vtg_cop
  ! a fn's head items (vmtrg's vtg-fnhd): :prim and the N_FN node itself,
  ! the op of the runtime's kind 6 (vm_node_hook builds the closure from the
  ! captured values) -- NAMED: the model's :mkclo and the template, ex-tr's
  ! (:mkclo tm caps..). A lazy seq's closure (ex-tr's inner (:mkclo tm
  ! caps..)) is a fn's: an N_FN node of the N_LAZY node's template, made
  ! here (analyze_fn's shape: no kids, slot 2 the template), so the N_LAZY
  ! node's own kind 6 is only the wrap (vm_node_hook)
  subroutine vtg_fnhd(tb, nd)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: nd
    call anb_push(vm_kw("prim"))
    if (gc_i1(nd) == N_LAZY) then
       call anb_push(mk_node(N_FN, gc_nil(), gc_slot(nd, 2), gc_nil(), 0, [nd]))
    else
       call anb_push(nd)
    end if
  end subroutine vtg_fnhd
  ! a case's entry j's test items (vmtrg's vtg-cstest): the N_CASE node
  ! itself, the op of the runtime's kind 6 (vm_node_hook: case_branch's
  ! probe takes entry j), and (:const then_j) -- NAMED: the model's :case and
  ! (:const t), t the entry's test, exec-vm's prim :case under ex-caseok
  subroutine vtg_cstest(tb, nd, j)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: nd
    integer(int64), value :: j
    call anb_push(nd)
    call vtg_const(tb, vtg_cthen(nd, j))
  end subroutine vtg_cstest
  ! a try's parts (vmtrg's vtg-catest, vtg-rethrow, vtg-blankcs), the thrown
  ! value at the next local, the depth (p, as vtg_toploc's depth - 1 the
  ! last): catch j's test (:prim NODE (:const j) (:local p)), the try node
  ! the op of the runtime's kind 6 -- NAMED: the model's (:prim :isa (:const
  ! c) (:local p)), vm_node_hook's N_TRY answering catch_matches of catch j's
  ! class (exec-vm's prim :isa under ex-isaok); the rethrow (:prim NODE
  ! (:local p)) -- NAMED: the model's (:throw (:local p)) at ex-trh's end and
  ! twice in ex-trfin's handler, vm_node_hook's N_TRY answering p's throw,
  ! the host's error raised again from what vm_caught kept (vm_rethrow); the
  ! catches' blanks nothing, as vtg_blank
  function vtg_nextloc(tb) result(l)
    type(vtg_state), intent(inout) :: tb
    type(gc_value) :: l, k
    k = vm_kw("local")
    l = vm_l([k, gc_int(int(tb%c%depth, gc_ip))], [k])
  end function vtg_nextloc
  subroutine vtg_catest(tb, nd, j)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: nd
    integer(int64), value :: j
    type(gc_value) :: l, k, c
    l = vtg_nextloc(tb)
    c = vm_l([vm_kw("const"), gc_int(int(j, gc_ip))], [l, nd])
    k = vm_kw("prim")
    call anb_push(vm_l([k, nd, c, l], [l, nd, c]))
  end subroutine vtg_catest
  subroutine vtg_rethrow(tb, nd)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: nd
    type(gc_value) :: l, k
    l = vtg_nextloc(tb)
    k = vm_kw("prim")
    call anb_push(vm_l([k, nd, l], [l, nd]))
  end subroutine vtg_rethrow
  subroutine vtg_blankcs(tb, nd)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: nd
  end subroutine vtg_blankcs
  ! a letfn's j-th init (vmtrg's vtg-lfinit): (:prim NODE (:const j) caps..
  ! (:local d) .. (:local d+j-1)), the letfn node the op of the runtime's
  ! kind 6 (vm_node_hook), every fn's captures in turn -- an outer slot's
  ! read as vtg_local's, the group's own (:const nil) -- then the earlier
  ! lets' closures, d the depth at the letfn's scope (the inits are
  ! translated there; the lets bind d, d+1, ..). NAMED, where the model's is
  ! (:mkgrp (j . shape) caps..), a group capture (:const (:grp nil m)):
  ! vm_node_hook's N_LETFN answers fn j's closure, the group's captures
  ! patched among it and the earlier ones -- after the last let the one group
  ! exec_letfn makes, the model's x2-seal of the j-th up to identity
  subroutine vtg_lfinit(tb, nd, j)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: nd
    integer(int64), value :: j
    type(gc_stack), pointer :: vst
    type(gc_value) :: capv, k
    integer :: top0, f, q, o, s0, n
    vst => gc_my_stack()
    top0 = vst%vs_top
    n = gc_i2(nd)
    s0 = int_of(gc_slot(nd, 2))
    call anb_push(vm_kw("prim"))
    call anb_push(nd)
    call vtg_const(tb, gc_int(int(j, gc_ip)))
    do f = 0, n - 1
       capv = gcv_nth(gc_slot(ast_kid(nd, int(f, int64)), 2), 2)
       do q = 0, gcv_count(capv) / 2 - 1
          o = int_of(gcv_nth(capv, 2 * q))
          if (o >= s0 .and. o < s0 + n) then
             call vtg_nil(tb)
          else
             call anb_push(vm_slot_ref(tb%c, o, [gc_value ::]))
          end if
       end do
    end do
    do q = 0, int(j) - 1
       k = vm_kw("local")
       call anb_push(vm_l([k, gc_int(int(tb%c%depth + q, gc_ip))], [k]))
    end do
    call vtg_node(tb, 0_int64, int(vst%vs_top - top0, int64))
  end subroutine vtg_lfinit
  ! a letfn's slots the next locals, none blanked (vmtrg's vtg-lfbinds)
  subroutine vtg_lfbinds(tb, s, n)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: s, n
    call vtg_binds(tb, s, n)
  end subroutine vtg_lfbinds
  ! every other kind: vm_tr's own (which calls back for the kinds above)
  ! a number (gc_int), a keyword (0 :rest, 1 :clotran.vm/arity, 2 :prim, else
  ! :local), the self let's value: (:capt m), the runtime's closure, which
  ! holds itself past its m captures (VmRuntime rt_capt) -- NAMED: the model's
  ! (:mkclo tm (:capt 0) ..) remakes it (vmtrcl.lisp; tm unread here)
  subroutine vtg_num(tb, n)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: n
    call anb_push(gc_int(int(n, gc_ip)))
  end subroutine vtg_num
  subroutine vtg_key(tb, j)
    type(vtg_state), intent(inout) :: tb
    integer(int64), value :: j
    select case (j)
    case (0); call anb_push(vm_kw("rest"))
    case (1); call anb_push(vm_kw("clotran.vm/arity"))
    case (2); call anb_push(vm_kw("prim"))
    case default; call anb_push(vm_kw("local"))
    end select
  end subroutine vtg_key
  subroutine vtg_self(tb, tm, m)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: tm
    integer(int64), value :: m
    type(gc_value) :: k
    k = vm_kw("capt")
    call anb_push(vm_l([k, gc_int(int(m, gc_ip))], [k]))
  end subroutine vtg_self
  recursive subroutine vtg_other(tb, x)
    type(vtg_state), intent(inout) :: tb
    type(gc_value), value :: x
    call anb_push(vm_tr(tb%c, x, [gc_value ::]))
  end subroutine vtg_other


  ! a Var node's fn -- the one it is direct-linked to, else its Var's value
  ! now -- only wraps a builtin (not a runtime fn of the analyzer's own)
  ! when called with n arguments
  logical function vm_wraps(nd, n)
    type(gc_value), intent(in) :: nd
    integer, intent(in) :: n
    type(gc_value) :: v, wb
    vm_wraps = .false.
    if (.not. gcn_is_var(gc_slot(nd, 2))) return
    v = vm_var_ref(nd)
    if (gc_kind(v) == OBJ_AST) then
       v = strip_meta(gc_slot(nd, 3))
    else
       v = strip_meta(gcn_var_value(v))
    end if
    wb = wrapper_of(v, n)
    if (gc_kind(wb) /= OBJ_BUILTIN) return
    vm_wraps = gc_i1(wb) /= B_RTFN .and. gc_i1(wb) /= B_UUIDFN
  end function vm_wraps

  ! a DIRECT-LINKED Var node whose bound fn only wraps a builtin at n
  ! arguments: the site's builtin is fixed now, as its fn is
  logical function vm_linked_builtin(nd, n)
    type(gc_value), intent(in) :: nd
    integer, intent(in) :: n
    vm_linked_builtin = .false.
    if (gc_kind(nd) /= OBJ_AST) return
    if (gc_i1(nd) /= N_VAR) return
    if (.not. vm_wraps(nd, n)) return
    vm_linked_builtin = gc_kind(vm_var_ref(nd)) == OBJ_AST
  end function vm_linked_builtin

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
    type(gc_value) :: cl, body
    type(gc_stack), pointer :: vst
    type(vm_tr_ctx), allocatable, target :: c
    type(vtg_state) :: tb
    integer(int64) :: vari
    integer :: base, i, nfixed, start, nl, ncap, sl
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
    ! the parameters the clause's locals, the captures its closure's read
    ! in place, the fn the local after the parameters (ex-fbtc's self let:
    ! its value the closure, (:capt ncap) -- the runtime's closure holds
    ! itself past its captures, VmRuntime rt_capt -- where the model remakes
    ! it, (:mkclo template (:capt 0) ..): equal under the runtime's
    ! decoding), and only when the body reads it: a let a call costs fib
    ! a fifth (scripts/bench), and its slot is a position no name reaches
    ! otherwise (the sl decision is named: vmtrcl.lisp)
    sl = 0
    if (self_slot >= 0 .and. self_slot <= ubound(c%map, 1)) then
       if (c%reads(self_slot)) sl = 1
    end if
    ! the scope by vtg_scope (generated: vmtrcl.lisp's vtg-scope-fbcm, ex-fbcm
    ! at sl 1, ex-fbcm0 at sl 0): the parameters, the captures in place, the self
    tb%c => c
    call vtg_scope(tb, int(start, int64), int(nl, int64), int(self_slot, int64), int(sl, int64), capv)
    if (.not. c%ok) return
    ! the clause, (n body) or (n body :rest), by vtg_clause (generated:
    ! vmtrcl.lisp's vtg-clause-ex-clause, ex-clause; at sl 0 vtg-clause-ex-clause0,
    ! ex-clause0, which answers as ex-clause, ex-fbtc0-mx): the self slot's let
    ! when sl, the loop only when the body recurs to the fn (vtg_tlr); the
    ! caller's roots kept on the value stack while it runs
    base = vs_enter(vst, size(roots) + 1)
    do i = 1, size(roots)
       call vs_set(vst, base + i, roots(i))
    end do
    call vs_set(vst, base + size(roots) + 1, body)
    vari = 0
    if (variadic) vari = 1
    call vtg_clause(tb, int(nfixed, int64), vari, int(start, int64), body, gc_nil(), int(sl, int64), int(ncap, int64))
    if (c%ok) cl = vs_get(vst, vst%vs_top)
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
    type(vtg_state) :: tb
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
    ! the last clause: a call of no arity the fn has, clj's ArityException,
    ! by vtg_arcl (generated: vmtrcl.lisp's ex-arcl, ex-arcl-mxcl)
    ! (0 (:prim :clotran.vm/arity (:const name) (:local 0)) :rest)
    call vtg_arcl(tb, display)
    x = vs_get(vst, vst%vs_top)
    call vs_leave(vst, base + 5)
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
    ! and natively, under CLOTRAN_JIT=1 (vmjit.inc)
    if (vmj_enabled()) call vmj_compile(int(p0, c_int64_t), pend)
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
  ! The body nd of fn run on the VM: its entry values the frame fr's from
  ! the body's first slot, or, given argbase, the value stack's from
  ! argbase + 1 (a fixed arity's arguments, the caller's slots let go)
  recursive subroutine vm_run(tctx, nd, fr, fn, val, argbase)
    type(eval_ctx), pointer, intent(in) :: tctx
    type(gc_value), intent(in) :: nd, fr, fn
    type(gc_value), intent(inout) :: val
    integer, intent(in), optional :: argbase
    type(gc_stack), pointer :: vst
    type(vm_state), target :: st
    type(gc_value) :: info
    integer :: sbase, i, nl, start, ci, win, top, hi, fs0
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
    if (present(argbase)) then
       do i = 0, nl - 1
          vst%vstack(sbase + i + 1) = vst%vstack(argbase + i + 1)
          vst%vstack(argbase + i + 1) = gc_nil()
       end do
    else
       do i = 0, nl - 1
          vst%vstack(sbase + i + 1) = frame_get(fr, start + i)
       end do
    end if
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
       tctx%vm_runs(tctx%n_vm_runs)%nexc = 0
       reg = .true.
    else
       tctx%n_vm_deep = tctx%n_vm_deep + 1
       reg = .false.
    end if
    fs0 = tctx%fstack_top
    hi = nl + 1
    steps = 0
    do
    if (vmj_enabled()) then
       ! natively (vmjit.inc), the same steps
       call vmj_run(st, ct0, hi, steps)
    else
    do
       if (st%status /= 0) exit
       if (st%code(4 * st%pc) == 11 .and. st%ctop == 0) exit
       vst%vm_ctl_top = int(ct0 + st%ctop + 1)
       if (st%code(4 * st%pc) >= 0 .and. st%code(4 * st%pc) <= 63) &
            vm_op_n(st%code(4 * st%pc)) = vm_op_n(st%code(4 * st%pc)) + 1
       call vmg_xstep(st)
       if (st%sp > hi) hi = int(st%sp)
       steps = steps + 1
       if (iand(steps, 4095_gc_ip) == 0) then
          if (gc_stop_pending()) call gc_poll()
       end if
    end do
    end if
    ! the machine out of room (status 2) inside a (:try ..) of its own: the
    ! host's stack_overflow_error raised and thrown to its handler
    ! (vmg_unwind, as a prim's throw), as the tree's frame limit raises one
    ! a try catches -- outside vmfg-correct, whose status 2 is out of room,
    ! no answer (a host error still raised there the VM caught: cleared)
    if (st%status /= 2 .or. st%hidx < 0) exit
    if (tctx%has_error) call gce_clear_error()
    call raise_class("clotran.host.stack_overflow_error", "stack overflow", [nd])
    st%status = 0
    block
      type(gc_value) :: tv
      logical :: okx
      call vm_took(tctx, okx, tv, nd)
      call vmg_unwind(st, tv)
    end block
    end do
    vst%vm_ctl_top = int(ct0)
    select case (int(st%status))
    case (0)
       val = st%stk(st%sp - 1)
       ! a host error still raised: the VM caught it (vm_caught)
       if (tctx%has_error) then
          tctx%fstack_top = min(tctx%fstack_top, fs0)
          call gce_clear_error()
       end if
    case (1)
       ! a throw nothing in the body caught: a call's error is still
       ! raised, as it was; the body's own (:throw e) raised as N_THROW does
       ! -- and so when the error still raised is one the VM caught and
       ! another value is thrown (a finally's own throw: no hook between)
       if (tctx%has_error) then
          if (.not. gc_identical(thrown_value(), st%stk(0))) then
             tctx%fstack_top = min(tctx%fstack_top, fs0)
             call gce_clear_error()
          end if
       end if
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
       if (tctx%vm_runs(tctx%n_vm_runs)%nexc > 0) then
          call gc_global_keep(tctx%vm_runs(tctx%n_vm_runs)%exc_root, gc_nil())
          tctx%vm_runs(tctx%n_vm_runs)%nexc = 0
       end if
       tctx%n_vm_runs = tctx%n_vm_runs - 1
    else
       tctx%n_vm_deep = tctx%n_vm_deep - 1
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
    integer :: i, r, j, n, nn, f, lowc
    allocate(buf(tctx%fstack_top + 64), nb(64))
    n = 0
    nn = 0
    do i = tctx%fstack_top, 1, -1
       do r = tctx%n_vm_runs, 1, -1
          if (tctx%vm_runs(r)%fstop /= i .or. .not. associated(tctx%vm_runs(r)%st)) cycle
          associate (st => tctx%vm_runs(r)%st)
            ! the function running, when it is not the entry's own (a
            ! call record, kind 1, above the entry's at 0 -- a (:try ..)'s
            ! handler record, kind 2, is no call)
            lowc = 0
            do j = 1, int(st%ctop) - 1
               if (st%ckind(j) == 1) then
                  lowc = j
                  exit
               end if
            end do
            if (lowc > 0) then
               f = vm_fn_at(st%pc)
               if (f >= 0) call trace_push(n, nn, buf, nb, f)
            end if
            ! the innermost call records' callers, but the lowest's (the entry's own)
            do j = int(st%ctop) - 1, lowc + 1, -1
               if (st%ckind(j) /= 1) cycle
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
    write(0, '(a, *(1x, i0, ":", i0))') 'vm: steps by opcode', (k, vm_op_n(k), k = 0, 63)
    write(0, '(a, 8(1x, i0))') 'vm: prims arg arity deref callw invoke node other seq', vm_prim_n
  end subroutine vm_stats_print
