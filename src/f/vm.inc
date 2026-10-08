  ! ===================================================================
  ! vm.inc -- fn bodies run by the GENERATED VM (PLAN step 30). Included
  ! into Eval.f90. CLOTRAN_VM=1 turns it on; off, nothing here runs.
  !
  ! An arity whose nodes are all ones this file knows is translated to
  ! vmx2's core language, compiled by the generated compiler
  ! (src/f/gen/vmc_gen.f90, vmicg_program), its superinstructions tagged
  ! by the generated pass (vmg_fuse_prog), checked inside the bounds a
  ! run assumes (vmg_good), and run by the generated fused step
  ! (vmg_xstep). vmfg-correct is the theorem: what that pipeline runs
  ! answers what the core expression means. This file is the glue the
  ! theorem does not cover -- the translation from clotran's tree, and
  ! the runtime under the VM (VmRuntime.f90) -- and the fuzzers compare
  ! it with the tree and flat modes.
  !
  ! THE PROGRAM for an arity is one function, clause 0, whose parameters
  ! are the body's ENTRY values: the slots it reads but never binds --
  ! its arguments, its captures, the fn itself. Main calls it with each
  ! fetched by a prim, so the whole run is the compiled program from pc 0:
  !
  !   e    = (:callv (:mkclo 0) (:prim :clotran.vm/arg (:const 0)) ...)
  !   defs = ((0 (m body)))
  !
  ! The translation, node by node:
  !   const, local          (:const v), (:local i)
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
  !   a call                (:prim f args), f the builtin or Var the
  !                         analyzer wrote as the head; any other head
  !                         (:prim :clotran.vm/invoke head args)
  ! Anything else -- fn, try, letfn, case, interop -- and the arity runs
  ! as before.
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
          block
            character(len=8) :: tr
            call get_environment_variable("CLOTRAN_VM_TRACE", tr)
            vm_trace = (trim(tr) == "1")
          end block
          if (.not. allocated(vm_progs)) allocate(vm_progs(VM_PROGS_MAX))
       end if
    end if
    vm_enabled = vm_mode == 1
  end function vm_enabled

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
    ok = .not. tctx%has_error
    if (.not. ok) then
       out = thrown_value()
       if (out%tag == GCT_NIL) then
          block
            character(len=:), allocatable :: msg
            call gce_error(s=msg)
            out = error_value(msg, [fn])
          end block
       end if
    end if
  end subroutine vm_call_hook

  function vm_deref_hook(var) result(v)
    type(gc_value), intent(in) :: var
    type(gc_value) :: v
    v = var_deref(var, [var])
  end function vm_deref_hook

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

  ! The slots a body binds and the slots it reads, and whether it holds a
  ! node the VM cannot run (vm_scan); the fn's own recur's parameters.
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
    case (N_IF, N_DO, N_THROW)
       do i = 0, gcv_count(kids) - 1
          call vm_scan(c, gcv_nth(kids, i))
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
       if (int_of(gcv_nth(rinfo, 0)) /= 0) then
          c%fn_recur = .true.
          c%rstart = int_of(gcv_nth(rinfo, 1))
          c%rcount = int_of(gcv_nth(rinfo, 2))
       end if
       do i = 0, gcv_count(kids) - 1
          call vm_scan(c, gcv_nth(kids, i))
       end do
    case (N_CALL)
       head = gcv_nth(kids, 0)
       do i = 0, gcv_count(kids) - 1
          call vm_scan(c, gcv_nth(kids, i))
       end do
       if (gc_kind(head) == OBJ_AST .and. gc_i1(head) == N_CONST) then
          ! a builtin that is a runtime fn of the analyzer's own (B_RTFN),
          ! as flat refuses it
          if (gc_kind(strip_meta(gc_slot(head, 2))) == OBJ_BUILTIN) then
             if (gc_i1(strip_meta(gc_slot(head, 2))) == B_RTFN .or. gc_i1(strip_meta(gc_slot(head, 2))) == B_UUIDFN) &
                  c%ok = .false.
          end if
       end if
    case default
       c%ok = .false.
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

  ! nd as core language; c%map holds each slot's local, c%depth the count
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
    ! slots: 1 nd, 2 an accumulator vector, 3 4 scratch, 5 kw
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, nd)
    select case (gc_i1(nd))
    case (N_CONST)
       call vs_set(vst, base + 5, vm_kw("const"))
       e = vm_l([vs_get(vst, base + 5), gc_slot(nd, 2)], [roots, vs_get(vst, base + 1)])
    case (N_LOCAL)
       i = c%map(gc_i2(nd))
       if (i < 0) then
          c%ok = .false.
       else
          call vs_set(vst, base + 5, vm_kw("local"))
          e = vm_l([vs_get(vst, base + 5), gc_int(int(i, gc_ip))], roots)
       end if
    case (N_VAR)
       call vs_set(vst, base + 5, vm_kw("const"))
       x = vm_l([vs_get(vst, base + 5), gc_slot(nd, 2)], [roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 3, x)
       call vs_set(vst, base + 5, vm_kw("prim"))
       call vs_set(vst, base + 4, vm_kw("clotran.vm/deref"))
       e = vm_l([vs_get(vst, base + 5), vs_get(vst, base + 4), vs_get(vst, base + 3)], roots)
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
          if (gc_kind(head) == OBJ_AST .and. (gc_i1(head) == N_CONST .or. gc_i1(head) == N_VAR)) then
             ! the head a constant of the program: (:prim f args ..)
             call vs_set(vst, base + 4, gc_slot(head, 2))
          else
             x = vm_tr(c, head, [roots, vs_get(vst, base + 2)])
             call vs_set(vst, base + 3, x)
             x = vm_l([vs_get(vst, base + 3)], [roots, vs_get(vst, base + 2)])
             call vs_set(vst, base + 3, x)
             x = list_to_vec_prepend(vs_get(vst, base + 3), vs_get(vst, base + 2), [roots])
             call vs_set(vst, base + 2, x)
             call vs_set(vst, base + 4, vm_kw("clotran.vm/invoke"))
          end if
          if (c%ok) then
             x = vec_to_list(vs_get(vst, base + 2), [roots, vs_get(vst, base + 4)])
             call vs_set(vst, base + 3, x)
             x = gcl_cons(vs_get(vst, base + 4), vs_get(vst, base + 3), [roots, vs_get(vst, base + 3), vs_get(vst, base + 4)])
             call vs_set(vst, base + 3, x)
             call vs_set(vst, base + 5, vm_kw("prim"))
             e = gcl_cons(vs_get(vst, base + 5), vs_get(vst, base + 3), [roots, vs_get(vst, base + 3), vs_get(vst, base + 5)])
          end if
       end if
    case default
       c%ok = .false.
    end select
    v = e
    call vs_leave(vst, base)
    e = v
  end function vm_tr

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

  ! [first-of-l v0 v1 ..]: l's one element, then v's
  function list_to_vec_prepend(l, v, roots) result(out)
    type(gc_value), intent(in) :: l, v, roots(:)
    type(gc_value) :: out
    type(gc_stack), pointer :: vst
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, l)
    call vs_set(vst, base + 2, v)
    out = gcv_empty([roots, l, v])
    call vs_set(vst, base + 3, out)
    out = gcv_conj(vs_get(vst, base + 3), gcl_first(vs_get(vst, base + 1)), [roots, vs_get(vst, base + 1), &
         vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 3, out)
    do i = 0, gcv_count(v) - 1
       out = gcv_conj(vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 2), i), [roots, vs_get(vst, base + 2), &
            vs_get(vst, base + 3)])
       call vs_set(vst, base + 3, out)
    end do
    out = vs_get(vst, base + 3)
    call vs_leave(vst, base)
  end function list_to_vec_prepend

  ! ---- THE COMPILE -----------------------------------------------------

  ! The arity ar as an N_VMB node, or nil when the VM cannot run it.
  function vm_compile_arity(ar, nslots, roots) result(nd)
    type(gc_value), intent(in) :: ar, roots(:)
    integer, intent(in) :: nslots
    type(gc_value) :: nd, x, body
    type(gc_stack), pointer :: vst
    type(vm_tr_ctx), allocatable :: c
    type(vm_state) :: cst
    type(vc_state) :: cce
    integer :: base, i, m, s, p
    integer(gc_ip), parameter :: one = 1
    nd = gc_nil()
    if (nslots > 4000) return
    vst => gc_my_stack()
    body = gcv_nth(ar, 3)
    allocate(c)
    allocate(c%reads(0:nslots + 8), c%binds(0:nslots + 8), c%map(0:nslots + 8))
    c%reads = .false.
    c%binds = .false.
    c%map = -1
    call vm_scan(c, body)
    if (.not. c%ok) then
       vm_n_refused = vm_n_refused + 1
       return
    end if
    ! the entry values: read and never bound, and the fn recur's parameters
    if (c%fn_recur) then
       do s = c%rstart, c%rstart + c%rcount - 1
          call vm_mark(c%reads, s, c)
       end do
    end if
    m = 0
    allocate(c%entry(0:nslots + 8))
    do s = 0, ubound(c%reads, 1)
       if (c%reads(s) .and. .not. c%binds(s)) then
          c%map(s) = m
          c%entry(m) = s
          m = m + 1
       end if
    end do
    c%depth = m
    ! slots: 1 body, 2 the body's core, 3 4 scratch, 5 e, 6 defs, 7 kw
    base = vs_enter(vst, 8)
    call vs_set(vst, base + 1, body)
    if (c%fn_recur) then
       ! (:loop ((:local p0) ..) body): the parameters the loop's
       call vs_set(vst, base + 3, gcv_empty(roots))
       call vs_set(vst, base + 7, vm_kw("local"))
       do i = 0, c%rcount - 1
          x = vm_l([vs_get(vst, base + 7), gc_int(int(c%map(c%rstart + i), gc_ip))], [roots, vs_get(vst, base + 3)])
          call vs_set(vst, base + 4, x)
          x = gcv_conj(vs_get(vst, base + 3), vs_get(vst, base + 4), [roots, vs_get(vst, base + 3), vs_get(vst, base + 4)])
          call vs_set(vst, base + 3, x)
       end do
       do i = 0, c%rcount - 1
          c%map(c%rstart + i) = c%depth + i
       end do
       c%depth = c%depth + c%rcount
       x = vm_tr(c, vs_get(vst, base + 1), [roots, vs_get(vst, base + 3)])
       call vs_set(vst, base + 2, x)
       if (c%ok) then
          x = vec_to_list(vs_get(vst, base + 3), [roots, vs_get(vst, base + 2)])
          call vs_set(vst, base + 3, x)
          call vs_set(vst, base + 7, vm_kw("loop"))
          x = vm_l([vs_get(vst, base + 7), vs_get(vst, base + 3), vs_get(vst, base + 2)], roots)
          call vs_set(vst, base + 2, x)
       end if
    else
       x = vm_tr(c, vs_get(vst, base + 1), roots)
       call vs_set(vst, base + 2, x)
    end if
    if (.not. c%ok) then
       vm_n_refused = vm_n_refused + 1
       call vs_leave(vst, base)
       return
    end if
    ! defs = ((0 (m body)))
    x = vm_l([gc_int(int(m, gc_ip)), vs_get(vst, base + 2)], roots)
    call vs_set(vst, base + 3, x)
    x = vm_l([gc_int(0_gc_ip), vs_get(vst, base + 3)], roots)
    call vs_set(vst, base + 3, x)
    x = vm_l([vs_get(vst, base + 3)], roots)
    call vs_set(vst, base + 6, x)
    ! e = (:callv (:mkclo 0) (:prim :clotran.vm/arg (:const i)) ..)
    call vs_set(vst, base + 4, gc_nil())
    do i = m - 1, 0, -1
       call vs_set(vst, base + 7, vm_kw("const"))
       x = vm_l([vs_get(vst, base + 7), gc_int(int(i, gc_ip))], [roots, vs_get(vst, base + 4), vs_get(vst, base + 6)])
       call vs_set(vst, base + 3, x)
       call vs_set(vst, base + 7, vm_kw("clotran.vm/arg"))
       call vs_set(vst, base + 8, vm_kw("prim"))
       x = vm_l([vs_get(vst, base + 8), vs_get(vst, base + 7), vs_get(vst, base + 3)], [roots, vs_get(vst, base + 4), &
            vs_get(vst, base + 6)])
       call vs_set(vst, base + 3, x)
       x = gcl_cons(vs_get(vst, base + 3), vs_get(vst, base + 4), [roots, vs_get(vst, base + 3), vs_get(vst, base + 4), &
            vs_get(vst, base + 6)])
       call vs_set(vst, base + 4, x)
    end do
    call vs_set(vst, base + 7, vm_kw("mkclo"))
    x = vm_l([vs_get(vst, base + 7), gc_int(0_gc_ip)], [roots, vs_get(vst, base + 4), vs_get(vst, base + 6)])
    call vs_set(vst, base + 3, x)
    x = gcl_cons(vs_get(vst, base + 3), vs_get(vst, base + 4), [roots, vs_get(vst, base + 3), vs_get(vst, base + 4), &
         vs_get(vst, base + 6)])
    call vs_set(vst, base + 4, x)
    call vs_set(vst, base + 7, vm_kw("callv"))
    x = gcl_cons(vs_get(vst, base + 7), vs_get(vst, base + 4), [roots, vs_get(vst, base + 4), vs_get(vst, base + 6)])
    call vs_set(vst, base + 5, x)

    ! CLOTRAN_VM_TRACE=1: each arity's core language, on stderr
    block
      character(len=:), allocatable :: txt
      if (vm_trace) then
         call gcp_str(vs_get(vst, base + 6), .true., s=txt)
         write(0, '(a, *(1x, i0))') 'vm: entry slots', c%entry(0:m - 1)
         write(0, '(a, a)') 'vm: defs ', txt
      end if
    end block
    ! the generated compiler, the generated pass, the bounds
    call vm_state_empty(cst)
    allocate(cce%env(0:-1))
    call vmicg_program(cst, cce, vs_get(vst, base + 5), vs_get(vst, base + 6), one, 4_gc_ip)
    if (cce%err /= 0 .or. cst%status /= 0) then
       vm_n_refused = vm_n_refused + 1
       call vm_state_free(cst, .true.)
       deallocate(cce%env)
       call vs_leave(vst, base)
       return
    end if
    call vmg_fuse_prog(cst)
    deallocate(cce%env)
    if (.not. vmg_good(cst)) then
       vm_n_refused = vm_n_refused + 1
       call vm_state_free(cst, .true.)
       call vs_leave(vst, base)
       return
    end if
    p = vm_prog_add(cst, m, c%entry)
    if (p < 0) then
       vm_n_refused = vm_n_refused + 1
       call vm_state_free(cst, .true.)
       call vs_leave(vst, base)
       return
    end if
    ! the program's constants, kept alive by the node; the tree beside it
    x = gc_vec(size(cst%pool), [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, x)
    do i = 1, size(cst%pool)
       call gc_vec_set(vs_get(vst, base + 3), i, cst%pool(i - 1))
    end do
    call vm_state_free(cst, .false.)
    nd = mk_node(N_VMB, gc_nil(), vs_get(vst, base + 3), gc_nil(), p, [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 4, nd)
    call gc_set_slot(nd, 4, gc_slot(vs_get(vst, base + 1), 4))
    call gc_set_slot(nd, 5, vs_get(vst, base + 1))
    vm_n_ok = vm_n_ok + 1
    call vs_leave(vst, base)
  end function vm_compile_arity

  subroutine vm_state_empty(st)
    type(vm_state), intent(inout) :: st
    allocate(st%code(0:-1), st%pool(0:-1), st%stk(0:-1), st%ckind(0:-1), st%ca(0:-1), st%cb(0:-1), st%cc(0:-1))
    allocate(st%cprev(0:-1), st%fnfirst(0:-1), st%fncount(0:-1), st%cln(0:-1), st%clent(0:-1), st%clrest(0:-1))
  end subroutine vm_state_empty

  ! the compile's arrays let go; the program's too unless the table took them
  subroutine vm_state_free(st, all)
    type(vm_state), intent(inout) :: st
    logical, intent(in) :: all
    deallocate(st%stk, st%ckind, st%ca, st%cb, st%cc, st%cprev)
    if (all) deallocate(st%code, st%pool, st%fnfirst, st%fncount, st%cln, st%clent, st%clrest)
  end subroutine vm_state_free

  ! the program into the table: code, pool and the function table move;
  ! the stack it needs is at most one slot an instruction past its entry
  ! values, the control stack main's call and nothing else
  integer function vm_prog_add(cst, m, entry) result(p)
    type(vm_state), intent(inout) :: cst
    integer, intent(in) :: m, entry(0:)
    call gc_state_lock()
    if (n_vm_progs < VM_PROGS_MAX) then
       n_vm_progs = n_vm_progs + 1
       p = n_vm_progs
    else
       p = -1
    end if
    call gc_state_unlock()
    if (p < 0) return
    vm_progs(p)%code => cst%code
    vm_progs(p)%pool => cst%pool
    vm_progs(p)%fnfirst => cst%fnfirst
    vm_progs(p)%fncount => cst%fncount
    vm_progs(p)%cln => cst%cln
    vm_progs(p)%clent => cst%clent
    vm_progs(p)%clrest => cst%clrest
    vm_progs(p)%nent = m
    allocate(vm_progs(p)%entry(0:max(m, 1) - 1))
    vm_progs(p)%entry(0:m - 1) = entry(0:m - 1)
    vm_progs(p)%nstk = size(cst%code) / 4 + m + 8
    vm_progs(p)%nctl = 4
  end function vm_prog_add

  ! ---- THE RUN -----------------------------------------------------------

  ! An N_VMB body on frame fr: its entry values copied out of the frame,
  ! the VM's stack a window of the value stack, stepped until main
  ! returns. A throw nothing caught is raised again as clotran's error.
  recursive subroutine vm_run(tctx, nd, fr, val)
    type(eval_ctx), pointer, intent(in) :: tctx
    type(gc_value), intent(in) :: nd, fr
    type(gc_value), intent(inout) :: val
    type(gc_stack), pointer :: vst
    type(vm_state) :: st
    integer :: p, ebase, sbase, i, nstk, nctl, saved_rb
    integer(gc_ip) :: steps
    character(len=:), allocatable :: msg
    ! the control stack: main's call is its only record, so four, here
    integer(gc_ip), target :: ck(0:3), ca(0:3), cb(0:3), cc(0:3), cprev(0:3)
    vst => tctx%stk
    p = gc_i2(nd)
    nstk = vm_progs(p)%nstk
    nctl = vm_progs(p)%nctl
    ebase = vs_enter(vst, vm_progs(p)%nent + nstk)
    do i = 0, vm_progs(p)%nent - 1
       call vs_set(vst, ebase + i + 1, frame_get(fr, vm_entry_slot(nd, i)))
    end do
    sbase = ebase + vm_progs(p)%nent
    do i = 1, nstk
       vst%vstack(sbase + i) = gc_nil()
    end do
    st%stk(0:nstk - 1) => vst%vstack(sbase + 1:sbase + nstk)
    st%code => vm_progs(p)%code
    st%pool => vm_progs(p)%pool
    st%fnfirst => vm_progs(p)%fnfirst
    st%fncount => vm_progs(p)%fncount
    st%cln => vm_progs(p)%cln
    st%clent => vm_progs(p)%clent
    st%clrest => vm_progs(p)%clrest
    ck = 0
    ca = 0
    cb = 0
    cc = 0
    cprev = 0
    st%ckind(0:nctl - 1) => ck(0:nctl - 1)
    st%ca(0:nctl - 1) => ca(0:nctl - 1)
    st%cb(0:nctl - 1) => cb(0:nctl - 1)
    st%cc(0:nctl - 1) => cc(0:nctl - 1)
    st%cprev(0:nctl - 1) => cprev(0:nctl - 1)
    st%pc = 0
    st%fb = 0
    st%sp = 0
    st%status = 0
    st%ctop = 0
    st%hidx = -1
    saved_rb = vst%vm_args_rb
    vst%vm_args_rb = ebase
    steps = 0
    do
       if (st%status /= 0) exit
       if (st%code(4 * st%pc) == 11 .and. st%ctop == 0) exit
       call vmg_xstep(st)
       steps = steps + 1
       if (iand(steps, 4095_gc_ip) == 0) then
          if (gc_stop_pending()) call gc_poll()
       end if
    end do
    vst%vm_args_rb = saved_rb
    block
      character(len=:), allocatable :: txt
      if (vm_trace) then
         do i = 0, vm_progs(p)%nent - 1
            call gcp_str(vs_get(vst, ebase + i + 1), .true., s=txt)
            write(0, '(a, i0, a, i0, a, a)') 'vm run ', p, ' entry ', i, ': ', txt
         end do
         call gcp_str(st%stk(max(st%sp - 1, 0_gc_ip)), .true., s=txt)
         write(0, '(a, i0, a, i0, a, i0, a, a)') 'vm run ', p, ' status ', st%status, ' sp ', st%sp, ' top ', txt
      end if
    end block
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
       call raise_class("clotran.host.stack_overflow_error", "the VM's stack overflowed", [nd])
       val = gc_nil()
    end select
    call vs_leave(vst, ebase)
  end subroutine vm_run

  ! the frame slot entry value i comes from
  integer function vm_entry_slot(nd, i)
    type(gc_value), intent(in) :: nd
    integer, intent(in) :: i
    vm_entry_slot = vm_progs(gc_i2(nd))%entry(i)
  end function vm_entry_slot

  ! CLOTRAN_STATS: how many arities the VM took
  subroutine vm_stats_print()
    if (vm_mode /= 1) return
    write(0, '(a, i0, a, i0, a)') 'vm: ', vm_n_ok, ' arities compiled, ', vm_n_refused, ' refused'
  end subroutine vm_stats_print
