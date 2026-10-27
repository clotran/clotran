  ! ===================================================================
  ! analyze.inc -- the analysis pass. Included into Eval.f90.
  !
  ! Forms in, NODES out. A node is an OBJ_AST: i1 = kind (N_*), i2 = an
  ! integer operand, slot 1 = children (a persistent vector of nodes),
  ! slot 2 and 3 = payloads. Every symbol is resolved HERE, once, with
  ! the writing namespace and the lexical scope known -- which is what
  ! Compiler.analyze does and what the old walker did at every call.
  !
  ! Locals are frame SLOTS. Each fn* gets one frame of a fixed size,
  ! computed here; a let, loop or catch binding is a slot in the
  ! enclosing fn's frame, and a closure captures VALUES (flat closures,
  ! as Clojure's compiler does): a free variable of an inner fn becomes
  ! a capture pair (outer slot -> inner slot), copied when the closure
  ! is created. Locals are immutable in Clojure, so copying is exact;
  ! the two places that rebind -- recur and letfn -- are handled by
  ! the executor writing the slots.
  !
  ! The names, slots and captures are the generated analyzer locals'
  ! (src/f/gen/anlocal_gen.inc, model/anlocal.lisp): integers in the
  ! context's anl_state, nothing there for the collector. Scope objects
  ! are GC objects (K_SCOPE) for what else a block holds -- its recur
  ! target, its kinds and array hints -- because the analyser allocates
  ! constantly and everything it holds must be rootable. Same rule as
  ! everywhere: an intermediate lives in a value stack slot, never in a
  ! bare local across an allocation.
  ! ===================================================================

  ! --- scopes --------------------------------------------------------
  !
  ! The names, slots and captures are the GENERATED analyzer locals'
  ! (src/f/gen/anlocal_gen.inc, from model/anlocal.lisp): this context's
  ! anl_state holds a record per fn, block, binding and capture, and
  ! anlocal-proof.lisp proves a name resolves to its innermost binding
  ! and a fn captures exactly the names it uses from outside. A scope is
  ! still a heap object (K_SCOPE) for what the model does not hold: i2
  ! its block's record, slot 2 the enclosing block's scope (nil at a fn's
  ! root), slot 3 the fn's info, slot 4 a recur target, slot 5 the
  ! block's notes (kinds, array hints). The fn info: slot 2 the scope the
  ! fn is written in, slot 5 a deftype method's fields, i2 the self slot.
  !
  ! What is hand-written here is the shims the generated code is run
  ! through: the form reads (frm_*), the symbols' ids (anl_sym_id), the
  ! refusals' words and classes (anl_refuse), and turning what it reads
  ! back into the maps and vectors the analyzer keeps.

  ! The context's analyzer locals, their arrays made on first use.
  function anl_ls() result(ls)
    type(eval_ctx), pointer :: tctx
    type(anl_state), pointer :: ls
    tctx => ctx_self()
    ls => tctx%anl
    if (.not. associated(ls%fctr)) then
       call anl_alloc(ls%fctr); call anl_alloc(ls%fout); call anl_alloc(ls%fcap); call anl_alloc(ls%fvar)
       call anl_alloc(ls%fah); call anl_alloc(ls%fnl); call anl_alloc(ls%bpar); call anl_alloc(ls%bfn)
       call anl_alloc(ls%bhead); call anl_alloc(ls%xnm); call anl_alloc(ls%xsl); call anl_alloc(ls%xblk)
       call anl_alloc(ls%xnext); call anl_alloc(ls%cnm); call anl_alloc(ls%cout); call anl_alloc(ls%cin)
       call anl_alloc(ls%cbx); call anl_alloc(ls%cnext); call anl_alloc(ls%nsl); call anl_alloc(ls%nnm)
       call anl_alloc(ls%nnext); call anl_alloc(ls%an); call anl_alloc(ls%anext); call anl_alloc(ls%ev)
       call anl_alloc(ls%es)
    end if
  contains
    subroutine anl_alloc(a)
      integer(int64), pointer, contiguous, intent(inout) :: a(:)
      call rt_resize_int(a, 64_int64)
    end subroutine anl_alloc
  end function anl_ls

  ! A generated operation ran out of room past 2^40 records, or was asked
  ! to bind a slot it never reserved: the analyzer's own bug, said so.
  logical function anl_ok()
    type(anl_state), pointer :: ls
    character(len=24) :: buf
    ls => anl_ls()
    anl_ok = (ls%err == 0)
    if (.not. anl_ok) then
       write (buf, '(i0)') ls%err
       call fail("internal error: the analyzer's locals refused an operation (anlocal err " // trim(buf) // ")")
       ls%err = 0
    end if
  end function anl_ok

  ! The form reads model/anlocal.lisp's frm-* decode a form by.
  integer(int64) function frm_kind(x)
    type(gc_value), intent(in) :: x
    type(gc_value) :: v
    v = strip_meta(x)
    frm_kind = 0
    if (gcv_is(v)) then
       frm_kind = 1
    else if (v%tag == GCT_SYM) then
       frm_kind = 2
    end if
  end function frm_kind

  integer(int64) function frm_count(x)
    type(gc_value), intent(in) :: x
    type(gc_value) :: v
    v = strip_meta(x)
    frm_count = 0
    if (gcv_is(v)) frm_count = gcv_count(v)
  end function frm_count

  function frm_nth(x, i) result(e)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: i
    type(gc_value) :: e, v
    v = strip_meta(x)
    e = gc_nil()
    if (gcv_is(v) .and. i >= 0) then
       if (i < gcv_count(v)) e = gcv_nth(v, int(i))
    end if
  end function frm_nth

  ! a symbol with a namespace: clj's getNamespace() /= null
  integer(int64) function frm_qual(x)
    type(gc_value), intent(in) :: x
    type(gc_value) :: v
    character(len=:), allocatable :: kt
    integer :: slash
    v = strip_meta(x)
    frm_qual = 0
    if (v%tag /= GCT_SYM) return
    call gc_ref_text(v%ref, s=kt)
    slash = sym_slash(kt)
    if (slash > 1 .and. slash < len(kt)) frm_qual = 1
  end function frm_qual

  integer(int64) function frm_amp(x)
    type(gc_value), intent(in) :: x
    type(gc_value) :: v
    v = strip_meta(x)
    frm_amp = 0
    if (v%tag /= GCT_SYM) return
    if (gc_ref_is(v%ref, "&")) frm_amp = 1
  end function frm_amp

  ! The form reads model/anform.lisp's frf-* decode a special form by. A
  ! list is a cons list (the analyzer normalises a clause before asking).
  integer(int64) function frf_kind(x)
    type(gc_value), intent(in) :: x
    type(gc_value) :: v
    v = strip_meta(x)
    frf_kind = frm_kind(v)
    if (gcl_is(v)) then
       frf_kind = 3
    else if (v%tag == GCT_STR) then
       frf_kind = 4
    end if
  end function frf_kind

  integer(int64) function frf_len(x)
    type(gc_value), intent(in) :: x
    type(gc_value) :: v
    v = strip_meta(x)
    frf_len = 0
    if (gcl_is(v)) frf_len = gcl_count(v)
  end function frf_len

  function frf_nth(x, i) result(e)
    type(gc_value), intent(in) :: x
    integer(int64), intent(in) :: i
    type(gc_value) :: e, v
    v = strip_meta(x)
    e = gc_nil()
    if (gcl_is(v) .and. i >= 0) then
       if (i < gcl_count(v)) e = nth_of(v, int(i))
    end if
  end function frf_nth

  ! the symbols TryExpr compares a clause's head with: catch, finally
  integer(int64) function frf_word(x)
    type(gc_value), intent(in) :: x
    type(gc_value) :: v
    v = strip_meta(x)
    frf_word = 0
    if (v%tag /= GCT_SYM) return
    if (gc_ref_is(v%ref, "catch")) then
       frf_word = 1
    else if (gc_ref_is(v%ref, "finally")) then
       frf_word = 2
    end if
  end function frf_word

  ! HostExpr.maybeClass: a symbol naming a class -- an import, a host row,
  ! a deftype analysed so far; in clotran's own and Clojure's sources a
  ! class defined later too (defers_late_vars, DEVIATIONS 17, 32)
  integer(int64) function frf_class(x)
    type(gc_value), intent(in) :: x
    type(gc_value) :: v
    character(len=:), allocatable :: written, canonical
    v = strip_meta(x)
    frf_class = 0
    if (v%tag /= GCT_SYM) return
    call gc_ref_text(v%ref, s=written)
    call canon_class(written, c=canonical)
    if (known_class_name(canonical) .or. defers_late_vars()) frf_class = 1
  end function frf_class

  ! DefExpr's lookupVar(sym, true) for a def's name: 0 unqualified, or this
  ! namespace's (interned if new); 1 no such var ("Can't refer to qualified
  ! var that doesn't exist"); 2 another namespace's var
  integer(int64) function frf_defvar(x)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: x
    type(gc_value) :: v, nsv, cur, var, vns
    character(len=:), allocatable :: t
    integer :: sl, base
    v = strip_meta(x)
    frf_defvar = 0
    if (v%tag /= GCT_SYM) return
    call gc_ref_text(v%ref, s=t)
    sl = sym_slash(t)
    if (sl <= 1 .or. sl >= len(t)) return
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, v)
    nsv = alias_target(t(1:sl-1), [vs_get(vst, base + 1)])
    if (gc_kind(nsv) /= OBJ_NS) nsv = gcn_find(t(1:sl-1), [vs_get(vst, base + 1)])
    cur = gcn_current([vs_get(vst, base + 1)])
    if (gc_kind(nsv) /= OBJ_NS) then
       frf_defvar = 1
    else if (nsv%tag /= cur%tag .or. nsv%ref /= cur%ref) then
       call vs_set(vst, base + 2, nsv)
       var = gcn_lookup(vs_get(vst, base + 2), gc_sym(t(sl+1:), [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
       frf_defvar = 1
       if (gcn_is_var(var)) then
          vns = gc_slot(var, 3)
          if (vns%tag == nsv%tag .and. vns%ref == nsv%ref) frf_defvar = 2
       end if
    end if
    call vs_leave(vst, base)
  end function frf_defvar

  ! The id of a symbol, as model/anlocal.lisp's names are: one per symbol
  ! text, per context, kept in a vector of the symbols and a map back
  ! (anl_root); metadata is not part of a name.
  function anl_tab(roots) result(t)
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: t, m, v
    tctx => ctx_self()
    if (.not. gc_root_live(tctx%anl_root)) then
       m = gch_empty(roots)
       v = gcv_empty([roots, m])
       t = gc_obj(OBJ_AST, [m, v, gc_nil(), gc_nil()], [roots, m, v])
       call gc_global_keep(tctx%anl_root, t)
    end if
    t = gc_root_get(tctx%anl_root)
  end function anl_tab

  integer(int64) function anl_sym_find(sym)
    type(gc_value), intent(in) :: sym
    type(gc_value) :: t, k, hit
    anl_sym_find = -1
    k = strip_meta(sym)
    if (k%tag /= GCT_SYM) return
    t = anl_tab([k])
    hit = gch_get(gc_slot(t, 1), k)
    if (hit%tag == GCT_INT) anl_sym_find = hit%ival
  end function anl_sym_find

  integer(int64) function anl_sym_id(sym)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: sym
    type(gc_value) :: t, m, v
    integer :: base
    anl_sym_id = anl_sym_find(sym)
    if (anl_sym_id >= 0) return
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, strip_meta(sym))
    t = anl_tab([vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, t)
    anl_sym_id = gcv_count(gc_slot(t, 2))
    v = gcv_conj(gc_slot(vs_get(vst, base + 2), 2), vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, v)
    call gc_set_slot(vs_get(vst, base + 2), 2, vs_get(vst, base + 3))
    m = gch_assoc(gc_slot(vs_get(vst, base + 2), 1), vs_get(vst, base + 1), gc_int(anl_sym_id), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call gc_set_slot(vs_get(vst, base + 2), 1, m)
    call vs_leave(vst, base)
  end function anl_sym_id

  function anl_sym_of(id) result(sym)
    integer(int64), intent(in) :: id
    type(gc_value) :: sym, t
    t = anl_tab([gc_nil()])
    sym = gc_nil()
    if (id >= 0 .and. id < gcv_count(gc_slot(t, 2))) sym = gcv_nth(gc_slot(t, 2), int(id))
  end function anl_sym_of

  ! A refusal the generated checks decided (model/anlocal.lisp's codes),
  ! in clj's words and class; x the form it is about. A catch's name is
  ! "bind", not "let", as CatchExpr says it.
  subroutine anl_refuse(code, x, catch)
    integer(int64), intent(in) :: code
    type(gc_value), intent(in) :: x
    logical, intent(in) :: catch
    character(len=:), allocatable :: s
    type(gc_value) :: v
    character(len=*), parameter :: iae = "clotran.host.illegal_argument_exception"
    ! as clj's message writes it, by string concatenation: a string as
    ! its text, nil as null, anything else as printed
    v = strip_meta(x)
    if (v%tag == GCT_NIL) then
       s = "null"
    else
       call gcp_str(v, v%tag /= GCT_STR, s=s)
    end if
    select case (code)
    case (1)
       call raise_class(iae, "Bad binding form, expected vector", [x])
    case (2)
       call raise_class(iae, "Bad binding form, expected matched symbol expression pairs", [x])
    case (3)
       call raise_class(iae, "Bad binding form, expected symbol, got: " // s, [x])
    case (4)
       if (catch) then
          call fail("Can't bind qualified name:" // s)
       else
          call fail("Can't let qualified name: " // s)
       end if
    case (5)
       call raise_class(iae, "fn params must be Symbols", [x])
    case (6)
       call fail("Can't use qualified name as parameter: " // s)
    case (7)
       call fail("Invalid parameter list")
    case (8)
       call fail("Unexpected parameter")
    case (9)
       call fail("Can't specify more than 20 params")
    case (10)
       call fail("Can't have more than 1 variadic overload")
    case (11)
       call fail("Can't have 2 overloads with same arity")
    case (12)
       call fail("Can't have fixed arity function with more params than variadic function")
    end select
  end subroutine anl_refuse

  ! The special forms' refusals (model/anform.lisp's codes 21..38) in clj's
  ! words and classes; x the form, or the class form a code 33 names.
  subroutine anf_refuse(code, x)
    integer(int64), intent(in) :: code
    type(gc_value), intent(in) :: x
    character(len=:), allocatable :: s
    type(gc_value) :: v
    character(len=*), parameter :: iae = "clotran.host.illegal_argument_exception"
    v = strip_meta(x)
    if (v%tag == GCT_NIL) then
       s = "null"
    else
       call gcp_str(v, v%tag /= GCT_STR, s=s)
    end if
    select case (code)
    case (21); call fail("Too many arguments to if")
    case (22); call fail("Too few arguments to if")
    case (23); call fail("Too many arguments to def")
    case (24); call fail("Too few arguments to def")
    case (25); call fail("First argument to def must be a Symbol")
    case (26); call fail("Can't refer to qualified var that doesn't exist")
    case (27); call fail("Can't create defs outside of current ns")
    case (28); call quote_arity(x)
    case (29); call fail("Too few arguments to throw, throw expects a single Throwable instance")
    case (30); call fail("Too many arguments to throw, throw expects a single Throwable instance")
    case (31); call fail("Only catch or finally clause can follow catch in try expression")
    case (32); call fail("finally clause must be last in try expression")
    case (33); call raise_class(iae, "Unable to resolve classname: " // s, [x])
    case (34); call raise_class(iae, "Malformed assignment, expecting (set! target val)", [x])
    case (35); call raise_class(iae, "Invalid assignment target", [x])
    case (36); call raise_class(iae, "Malformed member expression, expecting (. target member ...)", [x])
    case (37); call raise_class(iae, "Malformed member expression", [x])
    case (38); call fail("wrong number of arguments, expecting: (new Classname args...)")
    end select
  contains
    ! ConstantExpr.Parser's ExceptionInfo, its data {:form form}
    subroutine quote_arity(form)
      type(gc_value), intent(in) :: form
      type(gc_stack), pointer :: vst
      type(eval_ctx), pointer :: tctx
      type(gc_value) :: e
      character(len=24) :: buf
      integer :: base
      vst => gc_my_stack()
      base = vs_enter(vst, 3)
      call vs_set(vst, base + 1, form)
      write (buf, '(i0)') gcl_count(strip_meta(form)) - 1
      call vs_set(vst, base + 2, gc_key("form", [vs_get(vst, base + 1)]))
      call vs_set(vst, base + 3, gca_assoc(gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)]), &
           vs_get(vst, base + 2), vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
      call vs_set(vst, base + 2, gc_str("Wrong number of args (" // trim(buf) // ") passed to quote", [vs_get(vst, base + 3)]))
      call vs_set(vst, base + 1, gc_sym("clotran.host.exception_info", [vs_get(vst, base + 2), vs_get(vst, base + 3)]))
      e = gc_obj(OBJ_ERR, [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)], &
           [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
      call set_thrown(e)
      tctx => ctx_self()
      tctx%has_error = .true.
      tctx%last_error = "Wrong number of args (" // trim(buf) // ") passed to quote"
      call capture_innermost()
      call vs_leave(vst, base)
    end subroutine quote_arity
  end subroutine anf_refuse

  ! A fresh fn scope: its info and its root block. `outer` is the block
  ! scope the fn is written in, or nil at top level.
  function new_fn_scope(outer, roots) result(sc)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: outer
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: sc, info
    integer :: base
    integer(int64) :: ob, b
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, outer)
    ob = -1
    if (gc_kind(outer) == OBJ_AST) ob = gc_i2(outer)
    call anl_new_fn(anl_ls(), ob, b)
    info = gc_obj(OBJ_AST, [gc_nil(), vs_get(vst, base + 1), gc_nil(), gc_nil()], [roots, vs_get(vst, base + 1)])
    call gc_set_i2(info, -1)          ! self slot: none
    call vs_set(vst, base + 2, info)
    sc = gc_obj(OBJ_AST, [gc_nil(), gc_nil(), vs_get(vst, base + 2), gc_nil()], [roots, vs_get(vst, base + 2)])
    call gc_set_i1(sc, K_SCOPE)
    call gc_set_i2(sc, int(b))
    call vs_leave(vst, base)
  end function new_fn_scope

  ! A nested block in the same fn: the parent's recur target unless the
  ! caller replaces it.
  function child_scope(parent, roots) result(sc)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: parent
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: sc
    integer :: base
    integer(int64) :: b
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    call vs_set(vst, base + 1, parent)
    call anl_child(anl_ls(), int(gc_i2(vs_get(vst, base + 1)), int64), b)
    sc = gc_obj(OBJ_AST, [gc_nil(), vs_get(vst, base + 1), &
         gc_slot(vs_get(vst, base + 1), 3), gc_slot(vs_get(vst, base + 1), 4)], &
         [roots, vs_get(vst, base + 1)])
    call gc_set_i1(sc, K_SCOPE)
    call gc_set_i2(sc, int(b))
    call vs_leave(vst, base)
  end function child_scope

  ! Every local visible in scope sc, name -> slot, the innermost binding
  ! of a name winning: this fn's blocks, what it captured, and the fns
  ! around it (anl_env).
  function locals_env(sc, roots) result(env)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: sc
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: env
    type(anl_state), pointer :: ls
    integer :: base
    integer(int64) :: i
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    env = gca_empty(roots)
    call vs_set(vst, base + 1, env)
    if (gc_kind(sc) == OBJ_AST) then
       ls => anl_ls()
       call anl_env(ls, int(gc_i2(sc), int64))
       do i = 0, ls%nev - 1
          env = gca_assoc(vs_get(vst, base + 1), anl_sym_of(ls%ev(i)), gc_int(ls%es(i)), [roots, vs_get(vst, base + 1)])
          call vs_set(vst, base + 1, env)
       end do
    end if
    env = vs_get(vst, base + 1)
    call vs_leave(vst, base)
  end function locals_env

  function scope_info(sc) result(info)
    type(gc_value), intent(in) :: sc
    type(gc_value) :: info
    info = gc_slot(sc, 3)
  end function scope_info

  ! The frame's size so far, of the fn scope sc is in.
  integer function scope_nslots(sc)
    type(gc_value), intent(in) :: sc
    scope_nslots = int(anl_nslots(anl_ls(), int(gc_i2(sc), int64)))
  end function scope_nslots

  ! Its captures, as the template keeps them: (outer, inner) slot pairs,
  ! flattened, in the order they were taken.
  function scope_caps(sc, roots) result(v)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: sc
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    type(anl_state), pointer :: ls
    integer :: base
    integer(int64) :: i
    integer(int64), allocatable :: os(:), is(:)
    ls => anl_ls()
    call anl_caps_of(ls, int(gc_i2(sc), int64))
    os = ls%ev(0:ls%nev - 1)
    is = ls%es(0:ls%nev - 1)
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    v = gcv_empty(roots)
    call vs_set(vst, base + 1, v)
    do i = size(os, kind=int64), 1, -1
       v = gcv_conj(vs_get(vst, base + 1), gc_int(os(i)), [roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 1, v)
       v = gcv_conj(vs_get(vst, base + 1), gc_int(is(i)), [roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 1, v)
    end do
    v = vs_get(vst, base + 1)
    call vs_leave(vst, base)
  end function scope_caps

  ! slot -> name, for every named slot of the fn, in the order they were
  ! named, so a paused frame can report its locals (exec.inc
  ! break_frames); nil when it has none.
  function scope_slot_names(sc, roots) result(m)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: sc
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m
    type(anl_state), pointer :: ls
    integer :: base
    integer(int64) :: i
    integer(int64), allocatable :: nms(:), sls(:)
    ls => anl_ls()
    call anl_names_of(ls, int(gc_i2(sc), int64))
    nms = ls%ev(0:ls%nev - 1)
    sls = ls%es(0:ls%nev - 1)
    m = gc_nil()
    if (size(nms) == 0) return
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    m = gca_empty(roots)
    call vs_set(vst, base + 1, m)
    do i = size(nms, kind=int64), 1, -1
       m = gca_assoc(vs_get(vst, base + 1), gc_int(sls(i)), anl_sym_of(nms(i)), [roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 1, m)
    end do
    m = vs_get(vst, base + 1)
    call vs_leave(vst, base)
  end function scope_slot_names

  ! Reserves n consecutive slots in the fn and returns the first.
  function reserve_slots(sc, n) result(start)
    type(gc_value), intent(in) :: sc
    integer, intent(in) :: n
    integer :: start
    integer(int64) :: s
    call anl_reserve(anl_ls(), int(gc_i2(sc), int64), int(n, int64), s)
    start = int(s)
  end function reserve_slots

  ! Makes `sym` name `slot` in this block.
  subroutine bind_name(sc, sym, slot, roots)
    type(gc_value), intent(in) :: sc, sym
    integer, intent(in) :: slot
    type(gc_value), intent(in) :: roots(:)
    integer(int64) :: id
    id = anl_sym_id(sym)
    call anl_bind(anl_ls(), int(gc_i2(sc), int64), id, int(slot, int64))
  end subroutine bind_name

  ! The slot sym is bound to in this very block, or -1 (the walks of
  ! local_array_hint and captured_kind ask it of each block in turn).
  integer function bound_here(sc, sym)
    type(gc_value), intent(in) :: sc, sym
    type(anl_state), pointer :: ls
    integer(int64) :: id, x
    bound_here = -1
    id = anl_sym_find(sym)
    if (id < 0) return
    ls => anl_ls()
    x = anl_xfind(ls, anl_g_bhead(ls, int(gc_i2(sc), int64)), id)
    if (x >= 0) bound_here = int(anl_g_xsl(ls, x))
  end function bound_here

  ! --- array hints ---------------------------------------------------
  !
  ! Clojure casts an array-hinted value WHERE IT IS USED as an array,
  ! not where it is bound: (fn [^doubles a] (count a)) given a vector
  ! answers 2, and (aget a 0) in the same fn throws ClassCastException.
  ! So a scope remembers which of its names carry an array hint -- in
  ! its fifth slot, a map from name to hint -- and aget, aset and
  ! alength look the name up the same way name resolution does, so
  ! shadowing and closures come out right without further thought.

  ! The array hint on a binding form, or "" -- doubles, longs, ints and
  ! the rest, the way Clojure spells them.
  subroutine array_hint_of(raw, h)
    type(gc_value), intent(in) :: raw
    character(len=:), allocatable, intent(out) :: h
    type(gc_value) :: md, tg
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    h = ""
    if (gc_kind(raw) /= OBJ_META) return
    md = gc_slot(raw, 2)
    if (.not. gca_is(md)) return
    tg = strip_meta(gca_get(md, gc_key("tag", [raw, md])))
    if (tg%tag /= GCT_SYM) return
    block
       call gc_ref_text(tg%ref, s=dlt_1)
    select case (dlt_1)
    case ("doubles", "longs", "ints", "floats", "shorts", "bytes", "booleans", "chars", "objects")
       block
          call gc_ref_text(tg%ref, s=dlt_2)
          h = dlt_2
       end block
    end select
    end block
  end subroutine array_hint_of

  ! Record the binding's array hint, if it has one, in the scope that
  ! binds it.
  subroutine bind_array_hint(sc, sym, raw, roots)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: sc, sym, raw
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m
    character(len=:), allocatable :: h
    integer :: base
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    block
       call array_hint_of(raw, h=dlt_1)
       h = dlt_1
    end block
    if (len(h) == 0) return
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, sc)
    call vs_set(vst, base + 2, sym)
    m = gc_slot(vs_get(vst, base + 1), 5)
    if (.not. gca_is(m)) m = gca_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, m)
    m = gca_assoc(vs_get(vst, base + 3), vs_get(vst, base + 2), gc_key(h, [roots, vs_get(vst, base + 1), vs_get(vst, base + 3)]), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call gc_set_slot(vs_get(vst, base + 1), 5, m)
    call vs_leave(vst, base)
  end subroutine bind_array_hint

  ! ---- primitive kinds, as Compiler.maybePrimitiveType answers them --
  !
  ! clj types an expression statically; two of its refusals follow from
  ! that (DEVIATIONS 48): a hinted let or loop local whose init is a
  ! primitive (LocalBinding), and a recur to a ^long or ^double fn
  ! parameter whose argument is not that primitive (RecurExpr). A node's
  ! kind here is PK_LONG .. PK_CHAR, PK_OBJ for an Object for certain, or
  ! 0 for not known -- and an unknown is never refused, so what clotran
  ! cannot type it lets through rather than refuse what clj accepts.

  ! The kind recorded for a local's slot in this fn's blocks, or 0.
  integer function local_kind(sc0, slot) result(k)
    type(gc_value), intent(in) :: sc0
    integer, intent(in) :: slot
    type(gc_value) :: sc, m, v
    k = 0
    sc = sc0
    do while (gc_kind(sc) == OBJ_AST)
       m = gc_slot(sc, 5)
       if (gca_is(m)) then
          if (gca_contains(m, gc_int(slot))) then
             v = gca_get(m, gc_int(slot))
             k = int(v%ival)
             return
          end if
       end if
       ! a fn's root block has no parent block: slots are the fn's own
       sc = gc_slot(sc, 2)
    end do
  end function local_kind

  ! m[:key], or nil when m is no map or has no such key.
  function gca_get_or_nil(m, key) result(v)
    type(gc_value), intent(in) :: m
    character(len=*), intent(in) :: key
    type(gc_value) :: v, k
    v = gc_nil()
    if (.not. gca_is(m)) return
    k = gc_key(key, [m])
    if (gca_contains(m, k)) v = gca_get(m, k)
  end function gca_get_or_nil

  ! The kind of the local `sym` names where it is bound, when that is an
  ! enclosing fn's: the walk local_array_hint makes, outward.
  recursive integer function captured_kind(sc0, sym) result(k)
    type(gc_value), intent(in) :: sc0, sym
    type(gc_value) :: sc
    logical :: crossed
    integer :: hit
    k = 0
    if (sym%tag /= GCT_SYM) return
    sc = sc0
    crossed = .false.
    do while (gc_kind(sc) == OBJ_AST)
       hit = bound_here(sc, sym)
       if (hit >= 0) then
          ! bound in this very fn: local_kind already answered
          if (.not. crossed) return
          k = local_kind(sc, hit)
          if (k == 0) k = captured_kind(sc, sym)
          return
       end if
       if (gc_kind(gc_slot(sc, 2)) == OBJ_AST) then
          sc = gc_slot(sc, 2)
       else
          sc = gc_slot(gc_slot(sc, 3), 2)
          crossed = .true.
       end if
    end do
  end function captured_kind

  ! Files `val` under `key` in the block's own map (slot 5, beside the
  ! array hints, which are keyed by symbol).
  subroutine block_note(sc, key, val, roots)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: sc, key, val
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, sc)
    call vs_set(vst, base + 2, key)
    call vs_set(vst, base + 3, val)
    m = gc_slot(vs_get(vst, base + 1), 5)
    if (.not. gca_is(m)) m = gca_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, m)
    m = gca_assoc(vs_get(vst, base + 4), vs_get(vst, base + 2), vs_get(vst, base + 3), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call gc_set_slot(vs_get(vst, base + 1), 5, m)
    call vs_leave(vst, base)
  end subroutine block_note

  subroutine bind_local_kind(sc, slot, kind, roots)
    type(gc_value), intent(in) :: sc
    integer, intent(in) :: slot, kind
    type(gc_value), intent(in) :: roots(:)
    if (kind /= 0) call block_note(sc, gc_int(slot), gc_int(kind), roots)
  end subroutine bind_local_kind

  ! A primitive kind's name, as Class.getName spells it.
  ! (A subroutine: a deferred-length function result is static in
  ! gfortran, shared by every thread -- scripts/no-static-slen.)
  subroutine prim_name(k, s)
    integer, intent(in) :: k
    character(len=:), allocatable, intent(out) :: s
    select case (k)
    case (PK_LONG); s = "long"
    case (PK_DOUBLE); s = "double"
    case (PK_INT); s = "int"
    case (PK_BOOL); s = "boolean"
    case (PK_FLOAT); s = "float"
    case (PK_SHORT); s = "short"
    case (PK_BYTE); s = "byte"
    case (PK_CHAR); s = "char"
    case default; s = "Object"
    end select
  end subroutine prim_name

  ! The kind of a call to clojure.core's `nm` with these argument nodes:
  ! what its :inline expands to answers statically in clj (a cast, a
  ! Numbers op, RT.count), for the arities it is inline at; 0 for the rest.
  recursive integer function core_call_kind(nm, kids, sc) result(k)
    character(len=*), intent(in) :: nm
    type(gc_value), intent(in) :: kids, sc
    integer :: nargs
    k = 0
    nargs = gcv_count(kids) - 1
    if (index(nm, "clotran-math-") == 1) then
       k = math_call_kind(nm(14:), kids, sc)
       return
    end if
    select case (nm)
    case ("abs")
       if (nargs == 1) k = arith_kind(kids, sc, 4)
    case ("long", "unchecked-long")
       if (nargs == 1) k = PK_LONG
    case ("double", "unchecked-double")
       if (nargs == 1) k = PK_DOUBLE
    case ("int", "unchecked-int")
       if (nargs == 1) k = PK_INT
    case ("boolean")
       if (nargs == 1) k = PK_BOOL
    case ("float", "unchecked-float")
       if (nargs == 1) k = PK_FLOAT
    case ("short", "unchecked-short")
       if (nargs == 1) k = PK_SHORT
    case ("byte", "unchecked-byte")
       if (nargs == 1) k = PK_BYTE
    case ("char", "unchecked-char")
       if (nargs == 1) k = PK_CHAR
    case ("count")
       if (nargs == 1) k = PK_INT
    case ("alength")
       ! an int when the array's type is known -- a hint, here -- and a
       ! reflective call, an Object, when it is not (not modelled: 0)
       if (nargs == 1) then
          if (array_elem_kind(gcv_nth(kids, 1)) /= -99) k = PK_INT
       end if
    case ("aget")
       ! a hinted array's element, its primitive
       if (nargs == 2) then
          k = array_elem_kind(gcv_nth(kids, 1))
          if (k == -99) k = 0
       end if
    case ("<", ">", "<=", ">=", "==", "=", "identical?")
       if (nargs == 2) k = PK_BOOL
    case ("zero?", "pos?", "neg?", "nil?")
       if (nargs == 1) k = PK_BOOL
    case ("bit-and", "bit-or", "bit-xor", "bit-and-not")
       if (nargs >= 2) k = PK_LONG
    case ("bit-shift-left", "bit-shift-right", "unsigned-bit-shift-right")
       if (nargs == 2) k = PK_LONG
    case ("bit-not")
       if (nargs == 1) k = PK_LONG
    case ("+", "*", "-")
       if (nargs >= 2) k = arith_kind(kids, sc, 1)
       if (nargs == 1 .and. nm == "-") k = arith_kind(kids, sc, 4)
    case ("max", "min")
       if (nargs >= 2) k = arith_kind(kids, sc, 5)
    case ("unchecked-add", "unchecked-multiply", "unchecked-subtract")
       if (nargs == 2) k = arith_kind(kids, sc, 1)
    case ("quot", "rem")
       if (nargs == 2) k = arith_kind(kids, sc, 3)
    case ("inc", "dec", "unchecked-inc", "unchecked-dec", "unchecked-negate")
       if (nargs == 1) k = arith_kind(kids, sc, 4)
    case ("inc'", "dec'")
       if (nargs == 1) k = arith_kind(kids, sc, 6)
    case ("+'", "*'", "-'")
       if (nargs >= 2) k = arith_kind(kids, sc, 2)
       if (nargs == 1 .and. nm == "-'") k = arith_kind(kids, sc, 6)
    case ("/")
       ! Numbers.divide(long, long) is a Number: a ratio, or not
       if (nargs >= 2) k = arith_kind(kids, sc, 2)
    end select
  end function core_call_kind

  ! The element kind of an array argument cast_array_arg put a hint's
  ! cast on -- (clotran-array-cast a :doubles) -- or -99 for an
  ! argument with no cast.
  integer function array_elem_kind(arg) result(k)
    type(gc_value), intent(in) :: arg
    type(gc_value) :: kids, h, kw
    character(len=:), allocatable :: nm
    k = -99
    if (gc_kind(arg) /= OBJ_AST) return
    if (gc_i1(arg) /= N_CALL) return
    kids = gc_slot(arg, 1)
    if (gcv_count(kids) /= 3) return
    h = gcv_nth(kids, 0)
    if (gc_kind(h) /= OBJ_AST) return
    if (gc_i1(h) /= N_CONST) return
    h = strip_meta(gc_slot(h, 2))
    if (gc_kind(h) /= OBJ_BUILTIN) return
    if (gc_i1(h) /= B_ARRAYCAST) return
    kw = gcv_nth(kids, 2)
    if (gc_kind(kw) /= OBJ_AST) return
    kw = strip_meta(gc_slot(kw, 2))
    if (kw%tag /= GCT_KEY) return
    call gc_ref_text(kw%ref, s=nm)
    select case (nm)
    case ("doubles"); k = PK_DOUBLE
    case ("longs"); k = PK_LONG
    case ("ints"); k = PK_INT
    case ("floats"); k = PK_FLOAT
    case ("shorts"); k = PK_SHORT
    case ("bytes"); k = PK_BYTE
    case ("chars"); k = PK_CHAR
    case ("booleans"); k = PK_BOOL
    case default; k = PK_OBJ
    end select
  end function array_elem_kind

  ! clotran.host.math's methods, typed as the Math methods they stand
  ! for: one signature is its primitive whatever it is given (the
  ! Compiler converts the argument); an overloaded one is primitive
  ! when its arguments are and an Object when one is (a reflective
  ! call), by the overload the arguments pick.
  recursive integer function math_call_kind(m, kids, sc) result(k)
    character(len=*), intent(in) :: m
    type(gc_value), intent(in) :: kids, sc
    integer :: i, a
    logical :: dbl
    k = 0
    select case (m)
    case ("E", "PI", "sin", "cos", "tan", "asin", "acos", "atan", "toRadians", "toDegrees", "exp", "log", &
         "log10", "sqrt", "cbrt", "ceil", "floor", "rint", "sinh", "cosh", "tanh", "expm1", "log1p", &
         "IEEEremainder", "atan2", "pow", "hypot", "random")
       k = PK_DOUBLE
       return
    end select
    dbl = .false.
    do i = 1, gcv_count(kids) - 1
       a = static_prim(gcv_nth(kids, i), sc)
       if (a == 0 .or. a == PK_BOOL) return
       if (a == PK_OBJ) then
          k = PK_OBJ
          return
       end if
       if (a == PK_DOUBLE .or. a == PK_FLOAT) dbl = .true.
    end do
    select case (m)
    case ("abs", "max", "min", "negateExact", "incrementExact", "decrementExact", &
         "addExact", "subtractExact", "multiplyExact", "floorDiv", "floorMod")
       k = merge(PK_DOUBLE, PK_LONG, dbl)
    case ("round")
       k = PK_LONG
    case ("getExponent")
       k = PK_INT
    case ("signum", "ulp", "nextUp", "nextDown", "copySign", "nextAfter", "scalb")
       k = PK_DOUBLE
    end select
  end function math_call_kind

  ! A Numbers op on these operands, folded left as the nary inline
  ! nests it, by Numbers' overloads (`how`):
  !   1 add, subtract, multiply: two primitive integers are a long; a
  !     primitive double beside anything typed is a double
  !     (Numbers.add(double, Object) is a double); else a Number
  !   2 divide and the promoting ops: the same, but two longs a Number
  !   3 quot, rem: an Object operand makes a Number, else as 1
  !   4 one operand (inc, dec, negate): its own kind
  !   5 max, min: a primitive only when both are the same one
  !     (Numbers.max(double, long) is an Object)
  !   6 one operand, promoting (inc', dec'): a double stays one
  ! Unknown anywhere is unknown.
  recursive integer function arith_kind(kids, sc, how) result(k)
    type(gc_value), intent(in) :: kids, sc
    integer, intent(in) :: how
    integer :: i, a
    k = 0
    do i = 1, gcv_count(kids) - 1
       a = static_prim(gcv_nth(kids, i), sc)
       if (a == 0 .or. a == PK_BOOL) then
          k = 0
          return
       end if
       ! a primitive integer is a long here, a float a double
       if (any(a == [PK_INT, PK_SHORT, PK_BYTE, PK_CHAR])) a = PK_LONG
       if (a == PK_FLOAT) a = PK_DOUBLE
       if (i == 1) then
          k = a
       else if (how == 5) then
          if (k /= a) k = PK_OBJ
       else if (how == 3 .and. (k == PK_OBJ .or. a == PK_OBJ)) then
          k = PK_OBJ
       else if (k == PK_DOUBLE .or. a == PK_DOUBLE) then
          k = PK_DOUBLE
       else if (k == PK_OBJ .or. a == PK_OBJ) then
          k = PK_OBJ
       else if (how == 2) then
          k = PK_OBJ
       end if
    end do
    if (how == 6 .and. k /= PK_DOUBLE .and. k /= 0) k = PK_OBJ
  end function arith_kind

  ! A call through a Var with `nargs` arguments, as InvokeExpr types it:
  ! an :inline expands to what is not modelled here (0); an :arglists
  ! vector of that count with a ^long or ^double in it is invokePrim,
  ! answering its return's primitive or an Object (FnMethod.primInterface);
  ! anything else is IFn.invoke, an Object.
  integer function var_call_kind(var, nargs) result(k)
    type(gc_value), intent(in) :: var
    integer, intent(in) :: nargs
    type(gc_stack), pointer :: vst
    type(gc_value) :: md, al, v, sq, vec
    integer :: i, base
    logical :: prim
    k = 0
    if (.not. gcn_is_var(var)) return
    vst => gc_my_stack()
    md = gc_slot(var, 2)
    if (gca_is(md)) then
       if (gca_contains(md, gc_key("inline", [var, md]))) return
       al = strip_meta(gca_get(md, gc_key("arglists", [var, md])))
       ! (quote ([x] ...)) as written, or the list it evaluates to
       if (gcl_is(al)) then
          v = strip_meta(gcl_first(al))
          if (v%tag == GCT_SYM) then
             if (gc_ref_is(v%ref, "quote")) al = strip_meta(gcl_first(gcl_rest(al, [var, md, al])))
          end if
       end if
       ! any seq: a list, or the indexed seq quote leaves -- each step
       ! rooted, prim_hint_kind allocating
       base = vs_enter(vst, 1)
       sq = to_seq(al, [var, md, al])
       call vs_set(vst, base + 1, sq)
       do while (sq%tag /= GCT_NIL)
          vec = sq_first(sq, [var, md, al, sq])
          if (gcv_is(strip_meta(vec))) then
             if (gcv_count(strip_meta(vec)) == nargs) then
                prim = prim_hint_kind(vec) > 0
                do i = 0, nargs - 1
                   if (prim_hint_kind(gcv_nth(strip_meta(vec), i)) > 0) prim = .true.
                end do
                k = PK_OBJ
                if (prim .and. prim_hint_kind(vec) > 0) k = prim_hint_kind(vec)
                if (prim .and. nargs > 4) k = 0
                call vs_leave(vst, base)
                return
             end if
          end if
          sq = to_seq(sq_rest(sq, [var, md, al, sq]), [var, md, al])
          call vs_set(vst, base + 1, sq)
       end do
       call vs_leave(vst, base)
    end if
    k = PK_OBJ
  end function var_call_kind

  ! clojure.core's Var named `nm`, or nil.
  function core_var(nm, roots) result(var)
    type(gc_value), intent(in) :: roots(:)
    character(len=*), intent(in) :: nm
    type(gc_value) :: var, nsv
    var = gc_nil()
    nsv = gcn_find("clojure.core")
    if (gc_kind(nsv) /= OBJ_NS) return
    var = gcn_lookup(nsv, gc_sym(nm, [roots, nsv]))
  end function core_var

  ! A recur, or a do ending in one.
  recursive logical function is_recur(nd) result(yes)
    type(gc_value), intent(in) :: nd
    integer :: n
    yes = .false.
    if (gc_kind(nd) /= OBJ_AST) return
    if (gc_i1(nd) == N_RECUR) then
       yes = .true.
    else if (gc_i1(nd) == N_DO) then
       n = gcv_count(gc_slot(nd, 1))
       if (n > 0) yes = is_recur(gcv_nth(gc_slot(nd, 1), n - 1))
    end if
  end function is_recur

  ! A node's primitive kind (above), in the scope it was analysed in.
  recursive integer function static_prim(nd, sc) result(k)
    type(gc_value), intent(in) :: nd, sc
    type(gc_value) :: kids, v, head
    character(len=:), allocatable :: nm
    integer :: n, a, b
    k = 0
    if (gc_kind(nd) /= OBJ_AST) return
    kids = gc_slot(nd, 1)
    select case (gc_i1(nd))
    case (N_CONST)
       v = strip_meta(gc_slot(nd, 2))
       select case (v%tag)
       case (GCT_INT); k = PK_LONG
       case (GCT_REAL); k = PK_DOUBLE
       case default; k = PK_OBJ
       end select
    case (N_LOCAL)
       k = local_kind(sc, gc_i2(nd))
       ! not bound in this fn: captured, and a primitive stays one in the
       ! closure (a closed-over field of its type)
       if (k == 0) k = captured_kind(sc, gc_slot(nd, 2))
    case (N_VECTOR, N_MAP, N_SET, N_FN, N_NEW)
       k = PK_OBJ
    case (N_DO)
       n = gcv_count(kids)
       if (n > 0) k = static_prim(gcv_nth(kids, n - 1), sc)
    case (N_LET, N_LOOP)
       ! [init_0 .. init_{n-1}, body], slot 2 the first slot: the body's
       ! kind when it is a literal, an outer local or one of these (whose
       ! kind is its init's -- a loop's only an Object for certain)
       n = gcv_count(kids)
       if (n == 0) return
       head = gcv_nth(kids, n - 1)
       do while (gc_kind(head) == OBJ_AST)
          if (gc_i1(head) /= N_DO) exit
          if (gcv_count(gc_slot(head, 1)) == 0) exit
          head = gcv_nth(gc_slot(head, 1), gcv_count(gc_slot(head, 1)) - 1)
       end do
       a = -1
       if (gc_kind(head) == OBJ_AST) then
          if (gc_i1(head) == N_LOCAL) a = gc_i2(head) - int_of(gc_slot(nd, 2))
       end if
       if (a >= 0 .and. a < gc_i2(nd)) then
          k = static_prim(gcv_nth(kids, a), sc)
          if (gc_i1(nd) == N_LOOP .and. k > 0) k = 0
       else if (gc_kind(head) == OBJ_AST) then
          if (gc_i1(head) /= N_LOCAL) k = static_prim(head, sc)
       end if
    case (N_IF)
       ! IfExpr: a primitive when both branches are the same one
       if (gcv_count(kids) >= 2) then
          a = static_prim(gcv_nth(kids, 1), sc)
          b = PK_OBJ
          if (gcv_count(kids) >= 3) b = static_prim(gcv_nth(kids, 2), sc)
          ! a branch that recurs never answers: the if is the other's
          ! type (IfExpr, Recur.class)
          if (is_recur(gcv_nth(kids, 1))) a = b
          if (gcv_count(kids) >= 3) then
             if (is_recur(gcv_nth(kids, 2))) b = a
          end if
          if (a == 0 .or. b == 0) then
             k = 0
          else if (a == b) then
             k = a
          else
             k = PK_OBJ
          end if
       end if
    case (N_CALL)
       if (gcv_count(kids) < 1) return
       head = gcv_nth(kids, 0)
       if (gc_kind(head) /= OBJ_AST) return
       select case (gc_i1(head))
       case (N_LOCAL, N_FN)
          ! invoked through IFn: an Object
          k = PK_OBJ
       case (N_CONST)
          v = strip_meta(gc_slot(head, 2))
          if (v%tag == GCT_KEY) then
             k = PK_OBJ
          else if (gc_kind(v) == OBJ_BUILTIN) then
             ! a core fn the analyser put its builtin in place of (inc,
             ! long, count, ...), or a host method row: named as the core
             ! fn that is the same operation
             v = gc_slot(v, 1)
             if (v%tag == GCT_SYM) then
                call gc_ref_text(v%ref, s=nm)
                k = core_call_kind(nm, kids, sc)
                if (k == 0) k = var_call_kind(core_var(nm, [nd, sc]), gcv_count(kids) - 1)
             end if
          else if (gc_kind(v) == OBJ_CLOSURE) then
             call fn_who(v, nm)
             if (index(nm, "clojure.core/") == 1) then
                k = core_call_kind(nm(14:), kids, sc)
                if (k == 0) k = var_call_kind(core_var(nm(14:), [nd, sc]), gcv_count(kids) - 1)
             end if
          end if
       case (N_VAR)
          v = gc_slot(gc_slot(head, 2), 4)
          if (v%tag == GCT_SYM) then
             call gc_ref_text(v%ref, s=nm)
             if (index(nm, "clojure.core/") == 1) k = core_call_kind(nm(14:), kids, sc)
          end if
          if (k == 0) k = var_call_kind(gc_slot(head, 2), gcv_count(kids) - 1)
       end select
    end select
  end function static_prim

  ! A fn arity's ^long and ^double parameters, for its recurs: the kinds
  ! and the names, filed on the arity's block. A return hint makes
  ! prim_hint_body wrap the body in a loop*, which is then the recur
  ! target: its kinds, names and the return's kind are left for that
  ! loop to take (take_arg_kinds). Every other parameter is an Object
  ! for certain. Not for a deftype or reify method, whose parameters
  ! take their types from the interface.
  subroutine note_arg_kinds(clause, params, nfixed, variadic, blk, start, roots)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: clause, params, blk
    integer, intent(in) :: nfixed, start
    logical, intent(in) :: variadic
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: kv, names
    integer :: kinds(max(nfixed, 1)), i, base, ret
    logical :: any_prim
    vst => gc_my_stack()
    any_prim = .false.
    do i = 0, nfixed - 1
       kinds(i + 1) = max(prim_hint_kind(gcv_nth(params, i)), 0)
       if (kinds(i + 1) > 0) then
          any_prim = .true.
       else
          call bind_local_kind(blk, start + i, PK_OBJ, roots)
       end if
    end do
    if (variadic) then
       call bind_local_kind(blk, start + nfixed, PK_OBJ, roots)
       return
    end if
    ret = max(prim_hint_kind(gcl_first(clause)), 0)
    if (.not. any_prim .and. ret == 0) return
    base = vs_enter(vst, 2)
    kv = int_vec([kinds(1:nfixed), ret], [roots, clause, params, blk])
    call vs_set(vst, base + 1, kv)
    names = gcv_empty([roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, names)
    do i = 0, nfixed - 1
       names = gcv_conj(vs_get(vst, base + 2), strip_meta(gcv_nth(params, i)), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 2, names)
    end do
    ! the kinds vector carries the return's kind last
    if (ret > 0) then
       call block_note(blk, gc_key("clotran/loop-kinds", [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)]), &
            vs_get(vst, base + 1), [roots, vs_get(vst, base + 2)])
       call block_note(blk, gc_key("clotran/loop-names", [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)]), &
            vs_get(vst, base + 2), [roots, vs_get(vst, base + 1)])
    else
       call block_note(blk, gc_key("clotran/recur-kinds", [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)]), &
            vs_get(vst, base + 1), [roots, vs_get(vst, base + 2)])
       call block_note(blk, gc_key("clotran/recur-names", [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)]), &
            vs_get(vst, base + 2), [roots, vs_get(vst, base + 1)])
    end if
    call vs_leave(vst, base)
  end subroutine note_arg_kinds

  ! The loop* a return-hinted arity's body was wrapped in takes the
  ! arguments' kinds its arity left (note_arg_kinds), once, and answers
  ! the return's kind -- 0 for any other loop.
  integer function take_arg_kinds(parent, blk, roots) result(ret)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: parent, blk
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: m, k, kv, nv
    integer :: base
    ret = 0
    if (gc_kind(parent) /= OBJ_AST) return
    m = gc_slot(parent, 5)
    if (.not. gca_is(m)) return
    vst => gc_my_stack()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, m)
    k = gc_key("clotran/loop-kinds", [roots, parent, blk, vs_get(vst, base + 1)])
    kv = gca_get(vs_get(vst, base + 1), k)
    if (gcv_is(kv)) then
       ret = int_of(gcv_nth(kv, gcv_count(kv) - 1))
       call vs_set(vst, base + 2, kv)
       k = gc_key("clotran/loop-names", [roots, parent, blk, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       nv = gca_get(vs_get(vst, base + 1), k)
       call vs_set(vst, base + 3, nv)
       call block_note(blk, gc_key("clotran/recur-kinds", [roots, parent, vs_get(vst, base + 2), vs_get(vst, base + 3)]), &
            vs_get(vst, base + 2), [roots, parent, vs_get(vst, base + 3)])
       call block_note(blk, gc_key("clotran/recur-names", [roots, parent, vs_get(vst, base + 2), vs_get(vst, base + 3)]), &
            vs_get(vst, base + 3), [roots, parent, vs_get(vst, base + 2)])
       call block_note(parent, gc_key("clotran/loop-kinds", [roots, parent, blk]), gc_nil(), [roots, blk])
    end if
    call vs_leave(vst, base)
  end function take_arg_kinds

  ! RecurExpr's check: an argument to a ^long or ^double fn parameter
  ! must be that primitive (an int to a long, a float to a double).
  ! `kids` are the argument nodes, without a method's this.
  logical function recur_args_ok(sc, kids, roots) result(ok)
    type(gc_value), intent(in) :: sc, kids
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: own, rinfo, up, m, kv, nv, kid, v
    integer :: i, p, k
    character(len=:), allocatable :: had, nm, need
    ok = .true.
    rinfo = gc_slot(sc, 4)
    ! the block that set this recur target: its children share the vector
    own = sc
    do
       up = gc_slot(own, 2)
       if (gc_kind(up) /= OBJ_AST) exit
       v = gc_slot(up, 4)
       if (v%ref /= rinfo%ref .or. v%tag /= rinfo%tag) exit
       own = up
    end do
    m = gc_slot(own, 5)
    if (.not. gca_is(m)) return
    kv = gca_get(m, gc_key("clotran/recur-kinds", [roots, sc, kids, m]))
    if (.not. gcv_is(kv)) return
    nv = gca_get(m, gc_key("clotran/recur-names", [roots, sc, kids, m, kv]))
    do i = 0, min(gcv_count(kv), gcv_count(kids)) - 1
       p = int_of(gcv_nth(kv, i))
       if (p <= 0) cycle
       kid = gcv_nth(kids, i)
       k = static_prim(kid, sc)
       if (k == 0) cycle
       if (p == PK_LONG .and. any(k == [PK_LONG, PK_INT, PK_SHORT, PK_BYTE, PK_CHAR])) cycle
       if (p == PK_DOUBLE .and. any(k == [PK_DOUBLE, PK_FLOAT])) cycle
       call prim_name(k, had)
       if (k == PK_OBJ .and. gc_i1(kid) == N_CONST) then
          v = strip_meta(gc_slot(kid, 2))
          if (v%tag /= GCT_NIL) call class_name_of(v, s=had)
       end if
       nm = "?"
       if (gcv_is(nv)) then
          v = gcv_nth(nv, i)
          if (v%tag == GCT_SYM) call gc_ref_text(v%ref, s=nm)
       end if
       ! clj finds it when the fn is EMITTED, after its whole body is
       ! analysed and after a return hint's check: filed on the arity's
       ! block, the first one, and raised when the arity is done
       if (int_of(gcv_nth(rinfo, 0)) == 0) own = gc_slot(own, 2)
       if (tag_of(gca_get_or_nil(gc_slot(own, 5), "clotran/recur-error")) == GCT_NIL) then
          block
            type(gc_stack), pointer :: vst
            integer :: base
            vst => gc_my_stack()
            base = vs_enter(vst, 1)
            call prim_name(p, need)
            call vs_set(vst, base + 1, gc_str(" recur arg for primitive local: " // nm // " is not matching primitive, had: " &
                 // had // ", needed: " // need, [roots, sc, kids, own]))
            call block_note(own, gc_key("clotran/recur-error", [roots, sc, kids, own, vs_get(vst, base + 1)]), &
                 vs_get(vst, base + 1), [roots, sc, kids])
            call vs_leave(vst, base)
          end block
       end if
       return
    end do
  end function recur_args_ok

  ! Whether a binding form carries a :tag, as Compiler.tagOf reads one.
  logical function has_tag(raw)
    type(gc_value), intent(in) :: raw
    type(gc_value) :: md, tg
    has_tag = .false.
    if (gc_kind(raw) /= OBJ_META) return
    md = gc_slot(raw, 2)
    if (.not. gca_is(md)) return
    tg = gc_key("tag", [raw, md])
    if (.not. gca_contains(md, tg)) return
    ! Compiler.tagOf: a symbol or a string; a class -- case's {:tag
    ! Object}, evaluated -- is no tag
    has_tag = any(tag_of(gca_get(md, tg)) == [GCT_SYM, GCT_STR])
  end function has_tag

  ! The array hint of the local `sym` names here, or nil. The walk is
  ! name resolution's: the innermost scope that BINDS the name decides,
  ! so a rebinding with no hint hides an outer one that had it.
  function local_array_hint(sc0, sym) result(h)
    type(gc_value), intent(in) :: sc0, sym
    type(gc_value) :: h, sc, m
    h = gc_nil()
    sc = sc0
    do while (gc_kind(sc) == OBJ_AST)
       if (bound_here(sc, sym) >= 0) then
          m = gc_slot(sc, 5)
          if (gca_is(m)) h = gca_get(m, sym)
          if (h%tag /= GCT_KEY) h = gc_nil()
          return
       end if
       if (gc_kind(gc_slot(sc, 2)) == OBJ_AST) then
          sc = gc_slot(sc, 2)
       else
          ! the fn's root block: carry on in the block the fn is written in
          sc = gc_slot(gc_slot(sc, 3), 2)
       end if
    end do
  end function local_array_hint

  ! If this call is aget, aset or alength and its array argument carries
  ! a hint -- on the expression itself, or on the local it names -- put
  ! the cast in front of it: (aget a i) becomes
  ! (aget (clotran-array-cast a :doubles) i). `rawargs` is the argument
  ! forms as written; core.clj's aget arrives here through its :inline
  ! as (. clotran.host.rt (aget a i)).
  recursive function cast_array_arg(rawargs, kids, sc, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: rawargs, kids, sc
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, head, fv, raw, h, cnode, cargs
    integer :: base, id
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    vst => gc_my_stack()
    out = kids
    if (gcv_count(kids) < 2) return
    head = gcv_nth(kids, 0)
    if (gc_kind(head) /= OBJ_AST) return
    if (gc_i1(head) /= N_CONST) return
    fv = strip_meta(gc_slot(head, 2))
    if (gc_kind(fv) /= OBJ_BUILTIN) return
    id = gc_i1(fv)
    if (id /= B_AGET .and. id /= B_ASET .and. id /= B_JASET .and. id /= B_ALENGTH) return
    raw = gcl_first(rawargs)
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, kids)
    h = gc_nil()
    block
       call array_hint_of(raw, h=dlt_1)
    if (len(dlt_1) > 0) then
       block
          call array_hint_of(raw, h=dlt_2)
          h = gc_key(dlt_2, [roots, vs_get(vst, base + 1)])
       end block
    else
       fv = strip_meta(raw)
       if (fv%tag == GCT_SYM) h = local_array_hint(sc, fv)
    end if
    end block
    if (tag_of(h) == GCT_NIL) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 2, h)
    ! [cast-fn, the argument's node, the hint]
    cargs = gcv_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, cargs)
    cnode = const_node(native(B_ARRAYCAST, "clotran-array-cast", [roots, vs_get(vst, base + 1), vs_get(vst, base + 3)]), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 3)])
    cargs = gcv_conj(vs_get(vst, base + 3), cnode, [roots, vs_get(vst, base + 1), vs_get(vst, base + 3), cnode])
    call vs_set(vst, base + 3, cargs)
    cargs = gcv_conj(vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 1), 1), [roots, vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 3, cargs)
    cnode = const_node(vs_get(vst, base + 2), [roots, vs_get(vst, base + 1), vs_get(vst, base + 3)])
    cargs = gcv_conj(vs_get(vst, base + 3), cnode, [roots, vs_get(vst, base + 1), vs_get(vst, base + 3), cnode])
    call vs_set(vst, base + 3, cargs)
    cnode = mk_node(N_CALL, vs_get(vst, base + 3), gc_nil(), gc_nil(), 0, [roots, vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, cnode)
    out = gcv_put(vs_get(vst, base + 1), 1, vs_get(vst, base + 4), [roots, vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call vs_leave(vst, base)
  end function cast_array_arg

  ! Declares a new local: one slot, bound in this block.
  function declare_local(sc, sym, roots) result(slot)
    type(gc_value), intent(in) :: sc, sym
    type(gc_value), intent(in) :: roots(:)
    integer :: slot
    slot = reserve_slots(sc, 1)
    call bind_name(sc, sym, slot, roots)
  end function declare_local

  ! The slot a symbol names, or -1 (anl_lookup): the blocks of this fn,
  ! then the fn's captures, then the ENCLOSING fn -- and a hit there
  ! becomes a capture, a fresh slot in this fn filled from the outer slot
  ! when the closure is made, transitively. A symbol no local was ever
  ! bound to has no id, and names no local.
  function lookup_local(sc, sym) result(slot)
    type(gc_value), intent(in) :: sc, sym
    integer :: slot
    integer(int64) :: id, k, bx
    slot = -1
    if (gc_kind(sc) /= OBJ_AST) return
    id = anl_sym_find(sym)
    if (id < 0) return
    call anl_lookup(anl_ls(), int(gc_i2(sc), int64), id, k, bx)
    if (bx >= 0) slot = int(k)
  end function lookup_local

  ! A deftype method's field, by name: [this mutable?] from the table
  ! clotran-fields* filed in the fn info's slot 5 (bind_fields), or nil
  ! -- nil too when a local of that name shadows it, in this fn or one
  ! around it, since the local wins as it does in clj. The walk crosses
  ! fns outward, so a fn inside the method sees the method's fields and
  ! reads them through its captured `this`.
  recursive function lookup_field_alias(sc, sym) result(al)
    type(gc_value), intent(in) :: sc, sym
    type(gc_value) :: al, info, m
    al = gc_nil()
    if (gc_kind(sc) /= OBJ_AST) return
    if (lookup_local(sc, sym) >= 0) return
    info = scope_info(sc)
    do while (gc_kind(info) == OBJ_AST)
       m = gc_slot(info, 5)
       if (gca_is(m)) then
          if (gca_contains(m, sym)) then
             al = gca_get(m, sym)
             return
          end if
       end if
       if (gc_kind(gc_slot(info, 2)) /= OBJ_AST) return
       info = scope_info(gc_slot(info, 2))
    end do
  end function lookup_field_alias

  ! Whether sym is a field of THIS fn (the method itself), not of a fn
  ! around it: a mutable field is read from a closure made in the method
  ! but not written there, as clj refuses it
  logical function field_of_this_fn(sc, sym)
    type(gc_value), intent(in) :: sc, sym
    type(gc_value) :: info, m
    field_of_this_fn = .false.
    if (gc_kind(sc) /= OBJ_AST) return
    info = scope_info(sc)
    if (gc_kind(info) /= OBJ_AST) return
    m = gc_slot(info, 5)
    if (.not. gca_is(m)) return
    field_of_this_fn = gca_contains(m, sym)
  end function field_of_this_fn

  ! (clotran-fields* this {f [this mutable?] ...} body...): the table of a
  ! deftype method's fields (bind_fields) into the fn info's slot 5, then
  ! the body. A mutable field is read and written through `this` wherever
  ! its name is not shadowed (analyze_symbol, analyze_setbang); a set! of
  ! an immutable one is clj's refusal.
  recursive function analyze_fields(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, body
    integer :: base
    tctx => ctx_self()
    vst => tctx%stk
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    ! the table, with the method's `this` under :this -- what a recur in
    ! the method passes for it (analyze_recur)
    call vs_set(vst, base + 3, gc_key("this", [vs_get(vst, base + 1)]))
    body = gca_assoc(gcl_first(gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)])), vs_get(vst, base + 3), &
         gcl_first(vs_get(vst, base + 1)), [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call gc_set_slot(scope_info(vs_get(vst, base + 2)), 5, body)
    body = gcl_rest(gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)]), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 1, body)
    nd = analyze_body(vs_get(vst, base + 1), vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_fields

  ! --- nodes ---------------------------------------------------------

  ! Whether the file being analysed may name a Var before its library
  ! loads (N_LATEVAR, DEVIATIONS 12): the vendored tree and clotran's own
  ! files, by their classpath names, and Clojure's own tests, derived or
  ! verbatim. A user's file gets clj's refusal when the form is analysed.
  ! Every interface a deftype* or reify* names is a class, as
  ! NewInstanceExpr resolves each and throws ClassNotFoundException for
  ! one that is not; a vendored or test file defers it (defers_late_vars).
  logical function ifaces_known(ifaces) result(ok)
    type(gc_value), intent(in) :: ifaces
    type(gc_value) :: s
    character(len=:), allocatable :: nm, c
    integer :: i
    ok = .true.
    if (.not. gcv_is(ifaces) .or. defers_late_vars()) return
    do i = 0, gcv_count(ifaces) - 1
       s = strip_meta(gcv_nth(ifaces, i))
       if (s%tag /= GCT_SYM) cycle
       call gc_ref_text(s%ref, s=nm)
       call canon_class(nm, c=c)
       if (known_class_name(c)) cycle
       call raise_class("clotran.host.class_not_found_exception", nm, [ifaces])
       ok = .false.
       return
    end do
  end function ifaces_known

  logical function defers_late_vars()
    character(len=:), allocatable :: nm
    call gcr_current_file(s=nm)
    defers_late_vars = index(nm, "clojure/") == 1 .or. index(nm, "clotran/") == 1 .or. &
         index(nm, "test_clojure/") > 0 .or. index(nm, "test/clj/derived/") > 0
  end function defers_late_vars

  ! 1 when a call through this Var from the namespace being analysed
  ! may bind to the callee at its first call (DEVIATIONS 55), else 0.
  integer function direct_link_flag(var) result(flag)
    type(gc_value), intent(in) :: var
    type(gc_value) :: md, nsv
    character(len=:), allocatable :: here, there, nm
    flag = 0
    if (.not. gcn_is_var(var)) return
    ! only what the vendored tree defines is direct-linked, as only what
    ! clj compiled into its jar is: a (ns clojure.zz) of the user's
    ! stays late-bound, as it does there
    call gcr_current_file(s=nm)
    if (index(nm, "clojure/") /= 1) return
    call gcn_name(gcn_current([var]), s=here)
    if (index(here, "clojure.") /= 1) return
    nsv = gc_slot(var, 3)
    if (gc_kind(nsv) /= OBJ_NS) return
    call gcn_name(nsv, s=there)
    if (index(there, "clojure.") /= 1) return
    call gcp_str(gc_slot(var, 4), .false., s=nm)
    if (index(nm, "*") == 1) return
    md = gc_slot(var, 2)
    if (gca_is(md)) then
       if (truthy(gca_get(md, gc_key("dynamic", [var])))) return
       if (truthy(gca_get(md, gc_key("redef", [var])))) return
       if (truthy(gca_get(md, gc_key("protocol", [var])))) return
       if (truthy(gca_get(md, gc_key("macro", [var])))) return
    end if
    flag = 1
  end function direct_link_flag

  function mk_node(kind, children, p1, p2, i2, roots) result(nd)
    integer, intent(in) :: kind, i2
    type(gc_value), intent(in) :: children, p1, p2
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: nd
    nd = gc_obj(OBJ_AST, [children, p1, p2, gc_nil()], [roots, children, p1, p2])
    call gc_set_i1(nd, kind)
    call gc_set_i2(nd, i2)
  end function mk_node

  ! A fn that only hands its parameters, in order, to one host builtin
  ! -- (fn [coll] (. clotran.host.rt (first coll))), which is what
  ! first, rest, next, seq, cons, inc, dec, pos? and most of core's
  ! primitives are -- answers that builtin, else nil; analyze_fn keeps
  ! the answer as the template's seventh element. A call to such a fn
  ! with its fixed arity then calls the builtin itself (exec.inc's
  ! N_CALL, gce_apply_slots, apply). Measured from compiled code, the
  ! closure was an interpreter entry of 470 ns around an 80 ns builtin,
  ! paid on every seq operation; clj inlines the static call to
  ! nothing. The fn VALUE stays the closure, so fn?, class, meta and a
  ! wrong-arity call are exactly what they were.
  ! Per ARITY: + = < conj assoc get nth are multi-arity, and their
  ! two-argument arity is the wrapper every hot call takes, so the
  ! answer is a vector with one entry per arity, nil where that arity
  ! is not a wrapper, or nil when none is.
  function wrapper_builtin(arities, captures) result(bs)
    type(gc_value), intent(in) :: arities, captures
    type(gc_value) :: bs, b
    integer :: i
    logical :: any
    bs = gc_nil()
    if (.not. gcv_is(arities) .or. .not. gcv_is(captures)) return
    if (gcv_count(captures) /= 0) return
    ! core's own wrappers only: a user's (defn f [x] (inc x)) keeps its
    ! frame, for the call stack a break shows and for stepping into it
    block
      type(gc_value) :: cur, core
      cur = gcn_current([arities, captures])
      core = gcn_find("clojure.core")
      if (cur%tag /= core%tag .or. cur%ref /= core%ref) return
    end block
    any = .false.
    bs = gcv_build(gcv_count(arities), [arities, captures])
    do i = 0, gcv_count(arities) - 1
       b = arity_builtin(gcv_nth(arities, i))
       if (b%tag /= GCT_NIL) any = .true.
       bs = gcv_put(bs, i, b, [arities, captures, bs])
    end do
    if (.not. any) bs = gc_nil()
  end function wrapper_builtin

  function arity_builtin(ar) result(b)
    type(gc_value), intent(in) :: ar
    type(gc_value) :: b, body, kids, head, kid
    integer :: nfixed, start, k
    b = gc_nil()
    if (truthy(gcv_nth(ar, 1))) return
    nfixed = int_of(gcv_nth(ar, 0))
    start = int_of(gcv_nth(ar, 2))
    body = gcv_nth(ar, 3)
    if (gc_kind(body) /= OBJ_AST) return
    if (gc_i1(body) == N_DO) then
       if (.not. gcv_is(gc_slot(body, 1))) return
       if (gcv_count(gc_slot(body, 1)) /= 1) return
       body = gcv_nth(gc_slot(body, 1), 0)
       if (gc_kind(body) /= OBJ_AST) return
    end if
    if (gc_i1(body) /= N_CALL) return
    kids = gc_slot(body, 1)
    if (.not. gcv_is(kids)) return
    if (gcv_count(kids) /= nfixed + 1) return
    head = gcv_nth(kids, 0)
    if (gc_kind(head) /= OBJ_AST) return
    if (gc_i1(head) /= N_CONST) return
    head = gc_slot(head, 2)
    if (gc_kind(head) /= OBJ_BUILTIN) return
    if (gc_i1(head) == B_RTFN .or. gc_i1(head) == B_UUIDFN) return
    do k = 0, nfixed - 1
       kid = gcv_nth(kids, k + 1)
       if (gc_kind(kid) /= OBJ_AST) return
       if (gc_i1(kid) /= N_LOCAL) return
       if (gc_i2(kid) /= start + k) return
    end do
    b = head
  end function arity_builtin

  function const_node(v, roots) result(nd)
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: nd
    nd = mk_node(N_CONST, gc_nil(), v, gc_nil(), 0, roots)
  end function const_node

  ! A node that fails with a message when executed. Used where the old
  ! walker reported an error at call time and no analysis-time answer
  ! exists, so the error still lands where the form runs.
  function fail_node(msg, roots) result(nd)
    type(gc_stack), pointer :: vst
    character(len=*), intent(in) :: msg
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: nd, s
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    s = gc_str(msg, roots)
    call vs_set(vst, base + 1, s)
    nd = mk_node(N_FAIL, gc_nil(), vs_get(vst, base + 1), gc_nil(), 0, roots)
    call vs_leave(vst, base)
  end function fail_node

  ! A form as a list: a macro assembles its expansion with cons and
  ! concat, so a clause of a try, an arity of a fn* or a method of a
  ! deftype can arrive as a lazy seq or a view, and anything that
  ! inspects a form's SHAPE has to realise it first.
  ! The metadata wrapper comes off first: clojure.walk rebuilds a seq
  ! with (with-meta (doall (map inner form)) (meta form)), and here a
  ! with-meta of nil still wraps, so every clause of a walked try
  ! arrived as OBJ_META over a lazy seq and was analysed as a call.
  function norm_form(v, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base
    vst => gc_my_stack()
    out = strip_meta(v)
    if (gc_kind(out) == OBJ_LAZY .or. gc_kind(out) == OBJ_SEQ) then
       base = vs_enter(vst, 1)
       call vs_set(vst, base + 1, out)
       out = seq_to_list(vs_get(vst, base + 1), [roots, vs_get(vst, base + 1)])
       call vs_leave(vst, base)
    end if
  end function norm_form

  ! A form as the analyser reads one: every seq in it a list. clj's
  ! compiler takes any ISeq where a list is written; the special forms
  ! here walk theirs as lists (fn*'s arities, catch, set!'s target, a
  ! . call), and syntax-quote -- read as clj reads it, (seq (concat
  ! ...)) -- hands a macro's caller nested seqs, not the cons lists
  ! the analysis-time expansion used to build. Called on what enters
  ! analysis: a top-level form, a macro's expansion, an :inline's. A
  ! (quote ...) is data and left as it is; metadata is kept; a form
  ! with no seq in it comes back itself, nothing copied.
  recursive function forms_as_lists(form, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: form
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, v, items, x, y, t
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i, n, k
    logical :: changed, proper
    vst => gc_my_stack()
    out = form
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, form)
    v = strip_meta(form)
    call vs_set(vst, base + 2, v)
    k = gc_kind(v)
    if (k == OBJ_CONS .or. k == OBJ_LAZY .or. k == OBJ_SEQ .or. k == OBJ_CHUNKSEQ) then
       ! a proper list of forms that need nothing stays as it is
       proper = .false.
       if (k == OBJ_CONS) then
          proper = .true.
          t = v
          do while (gcl_is(t))
             if (gcl_count(t) == 0) exit
             t = gcl_rest(t, [roots, vs_get(vst, base + 1)])
          end do
          if (.not. gcl_is(t) .and. t%tag /= GCT_NIL) proper = .false.
          if (proper .and. gcl_count(v) > 0) then
             x = strip_meta(gcl_first(v))
             if (x%tag == GCT_SYM) then
                if (gc_ref_is(x%ref, "quote")) then
                   call vs_leave(vst, base)
                   return
                end if
             end if
          end if
       end if
       items = coll_to_vector(vs_get(vst, base + 2), [roots, vs_get(vst, base + 1)])
       call vs_set(vst, base + 3, items)
       n = gcv_count(items)
       ! (quote ...) of any seq kind is data
       if (n > 0 .and. k /= OBJ_CONS) then
          x = strip_meta(gcv_nth(items, 0))
          if (x%tag == GCT_SYM) then
             if (gc_ref_is(x%ref, "quote")) then
                out = seq_to_list(vs_get(vst, base + 2), [roots, vs_get(vst, base + 1)])
                call rewrap(out)
                call vs_leave(vst, base)
                return
             end if
          end if
       end if
       changed = .not. proper
       do i = 0, n - 1
          x = gcv_nth(vs_get(vst, base + 3), i)
          y = forms_as_lists(x, [roots, vs_get(vst, base + 1), vs_get(vst, base + 3)])
          if (y%ref /= x%ref .or. y%tag /= x%tag) then
             changed = .true.
             call vs_set(vst, base + 4, y)
             call vs_set(vst, base + 3, gcv_assoc(vs_get(vst, base + 3), i, vs_get(vst, base + 4), &
                  [roots, vs_get(vst, base + 1), vs_get(vst, base + 4)]))
          end if
       end do
       if (.not. changed) then
          call vs_leave(vst, base)
          return
       end if
       out = gcl_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 3)])
       call vs_set(vst, base + 5, out)
       do i = n - 1, 0, -1
          call vs_set(vst, base + 5, gcl_cons(gcv_nth(vs_get(vst, base + 3), i), vs_get(vst, base + 5), &
               [roots, vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 5)]))
       end do
       out = vs_get(vst, base + 5)
       call rewrap(out)
    else if (gcv_is(v)) then
       changed = .false.
       call vs_set(vst, base + 3, v)
       do i = 0, gcv_count(v) - 1
          x = gcv_nth(vs_get(vst, base + 3), i)
          y = forms_as_lists(x, [roots, vs_get(vst, base + 1), vs_get(vst, base + 3)])
          if (y%ref /= x%ref .or. y%tag /= x%tag) then
             changed = .true.
             call vs_set(vst, base + 4, y)
             call vs_set(vst, base + 3, gcv_assoc(vs_get(vst, base + 3), i, vs_get(vst, base + 4), &
                  [roots, vs_get(vst, base + 1), vs_get(vst, base + 4)]))
          end if
       end do
       if (changed) then
          out = vs_get(vst, base + 3)
          call rewrap(out)
       end if
    else if (gca_is(v)) then
       ! a map literal's keys and values, rebuilt in order when one changed
       call gca_entries(v, ks, vls)
       changed = .false.
       do i = 1, size(ks)
          call vs_set(vst, base + 4, ks(i))
          y = forms_as_lists(ks(i), [roots, vs_get(vst, base + 1)])
          if (y%ref /= ks(i)%ref .or. y%tag /= ks(i)%tag) changed = .true.
          y = forms_as_lists(vls(i), [roots, vs_get(vst, base + 1)])
          if (y%ref /= vls(i)%ref .or. y%tag /= vls(i)%tag) changed = .true.
          if (changed) exit
       end do
       if (changed) then
          call vs_set(vst, base + 3, gca_empty([roots, vs_get(vst, base + 1)]))
          do i = 1, size(ks)
             call vs_set(vst, base + 4, forms_as_lists(ks(i), [roots, vs_get(vst, base + 1), vs_get(vst, base + 3)]))
             call vs_set(vst, base + 5, forms_as_lists(vls(i), [roots, vs_get(vst, base + 1), vs_get(vst, base + 3), &
                  vs_get(vst, base + 4)]))
             call vs_set(vst, base + 3, gca_assoc(vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5), &
                  [roots, vs_get(vst, base + 1), vs_get(vst, base + 4), vs_get(vst, base + 5)]))
          end do
          out = vs_get(vst, base + 3)
          call rewrap(out)
       end if
    end if
    call vs_leave(vst, base)
  contains
    ! the original's metadata on the rebuilt form
    subroutine rewrap(o)
      type(gc_value), intent(inout) :: o
      if (gc_kind(vs_get(vst, base + 1)) /= OBJ_META) return
      call vs_set(vst, base + 4, o)
      o = gc_obj(OBJ_META, [vs_get(vst, base + 4), gc_slot(vs_get(vst, base + 1), 2)], &
           [roots, vs_get(vst, base + 1), vs_get(vst, base + 4)])
    end subroutine rewrap
  end function forms_as_lists

  ! Analyses every form of a list or vector into a children vector.
  recursive function analyze_all(forms, sc, roots) result(out)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: forms, sc
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, nd, walk
    integer :: base, i, n

    tctx => ctx_self()
    vst => tctx%stk
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, forms)
    call vs_set(vst, base + 2, sc)
    out = gcv_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, out)
    if (gcv_is(forms)) then
       n = gcv_count(forms)
       do i = 0, n - 1
          nd = analyze(gcv_nth(vs_get(vst, base + 1), i), vs_get(vst, base + 2))
          if (tctx%has_error) exit
          out = gcv_conj(vs_get(vst, base + 3), nd, [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), nd])
          call vs_set(vst, base + 3, out)
       end do
    else
       walk = forms
       call vs_set(vst, base + 4, walk)
       do while (gcl_count(vs_get(vst, base + 4)) > 0)
          nd = analyze(gcl_first(vs_get(vst, base + 4)), vs_get(vst, base + 2))
          if (tctx%has_error) exit
          out = gcv_conj(vs_get(vst, base + 3), nd, [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), nd])
          call vs_set(vst, base + 3, out)
          walk = gcl_rest(vs_get(vst, base + 4), [roots, vs_get(vst, base + 3)])
          call vs_set(vst, base + 4, walk)
       end do
    end if
    out = vs_get(vst, base + 3)
    call vs_leave(vst, base)
  end function analyze_all

  ! A body (a list of forms) as one N_DO node.
  recursive function analyze_body(forms, sc, roots) result(nd)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: forms, sc
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: nd, kids
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    kids = analyze_all(forms, sc, roots)
    call vs_set(vst, base + 1, kids)
    nd = mk_node(N_DO, vs_get(vst, base + 1), gc_nil(), gc_nil(), 0, roots)
    call vs_leave(vst, base)
  end function analyze_body

  ! --- the analyser proper -------------------------------------------

  ! One form to one node, in scope `sc`.
  recursive function analyze(form0, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form0, sc
    type(gc_value) :: nd, form, head, kids, expanded, mvar
    integer :: base, slot
    character(len=:), allocatable :: hint

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    if (tctx%has_error) return
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 2, sc)
    ! the name a let or def gave this form reaches a fn* only through
    ! macroexpansion, as Compiler.analyze passes it; any other form drops it
    hint = ""
    if (allocated(tctx%fn_hint)) hint = tctx%fn_hint
    tctx%fn_hint = ""
    form = form0
    ! Metadata on a form is information about it, not part of what it
    ! means; only def looks at it (and does so from the raw form).
    !
    ! A COLLECTION LITERAL is the exception, and Clojure's Compiler
    ! says so: VectorExpr, MapExpr and SetExpr each end with
    !   if(form instanceof IObj && ((IObj) form).meta() != null)
    !      return new MetaExpr(ret, MapExpr.parse(..., meta));
    ! so the map is EVALUATED and the constructed collection carries
    ! it -- which is why (:tag (meta ^String [1])) is a Class and not
    ! a symbol. Dropping it here made clojure.zip unusable: `zipper`
    ! returns ^{:zip/branch? branch? ...} [root nil], and with the map
    ! gone every branch? call was (nil node).
    call vs_set(vst, base + 5, gc_nil())
    if (gc_kind(form) == OBJ_META) then
       if (literal_coll(strip_meta(form))) call vs_set(vst, base + 5, gc_slot(form, 2))
       form = strip_meta(form)
    end if
    ! A seq is code, like a list; realised once, here.
    if (gc_kind(form) == OBJ_LAZY .or. gc_kind(form) == OBJ_SEQ) then
       call vs_set(vst, base + 1, form)
       form = seq_to_list(vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    end if
    call vs_set(vst, base + 1, form)

    select case (form%tag)
    case (GCT_SYM)
       nd = analyze_symbol(vs_get(vst, base + 1), vs_get(vst, base + 2))
    case (GCT_OBJ)
       select case (gc_kind(form))
       case (OBJ_CONS)
          if (gcl_count(form) == 0) then
             nd = const_node(vs_get(vst, base + 1), [vs_get(vst, base + 2)])
          else
             tctx%fn_hint = hint
             nd = analyze_seq(vs_get(vst, base + 1), vs_get(vst, base + 2))
             if (tctx%has_error) then
                call trace_analysis_failure(vs_get(vst, base + 1))
                ! an analysis error names the innermost positioned form
                if (gc_i2(vs_get(vst, base + 1)) /= 0 .and. index(tctx%last_error, "  at ") == 0) then
                   block
                      call gcr_position(gc_i2(vs_get(vst, base + 1)), s=dlt_1)
                      tctx%last_error = tctx%last_error // "  at " // dlt_1
                   end block
                end if
             end if
             ! the source position, if the reader recorded one and the
             ! node has none of its own yet (a macro's expansion keeps
             ! the position of the form that was written)
             if (.not. tctx%has_error .and. gc_kind(nd) == OBJ_AST) then
                if (gc_i2(vs_get(vst, base + 1)) /= 0) then
                   block
                      type(gc_value) :: p
                      logical :: take
                      p = gc_slot(nd, 4)
                      take = (tag_of(p) == GCT_NIL)
                      ! an expansion's position has no file (an inlined core
                      ! call, (/ x 0) through Numbers/divide): the written
                      ! form's wins, as a frame's line names what was written
                      if (.not. take .and. p%tag == GCT_INT) take = (p%ival < POS_SHIFT)
                      if (take) call gc_set_slot(nd, 4, gc_int(gc_i2(vs_get(vst, base + 1))))
                   end block
                end if
             end if
          end if
       case (OBJ_VECTOR)
          kids = analyze_all(vs_get(vst, base + 1), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
          call vs_set(vst, base + 3, kids)
          if (.not. tctx%has_error) nd = mk_node(N_VECTOR, vs_get(vst, base + 3), gc_nil(), gc_nil(), 0, &
               [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       case (OBJ_MAP, OBJ_HAMT)
          nd = analyze_map(vs_get(vst, base + 1), vs_get(vst, base + 2))
       case (OBJ_SET)
          kids = analyze_all(set_elems(vs_get(vst, base + 1), vs_get(vst, base + 2)), vs_get(vst, base + 2), &
               [vs_get(vst, base + 1)])
          call vs_set(vst, base + 3, kids)
          if (.not. tctx%has_error) nd = mk_node(N_SET, vs_get(vst, base + 3), gc_nil(), gc_nil(), 0, &
               [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       case default
          ! closures, builtins, vars, types: self-evaluating
          nd = const_node(vs_get(vst, base + 1), [vs_get(vst, base + 2)])
       end select
    case default
       nd = const_node(vs_get(vst, base + 1), [vs_get(vst, base + 2)])
    end select
    ! MetaExpr: (with-meta <the collection> <the map>), built as a
    ! call to the builtin rather than to the NAME with-meta, so that a
    ! literal carrying metadata analyses the same during core.clj's
    ! bootstrap as after it.
    if (.not. tctx%has_error .and. tag_of(vs_get(vst, base + 5)) /= GCT_NIL &
         .and. gc_kind(nd) == OBJ_AST) then
       call vs_set(vst, base + 6, nd)
       nd = meta_call_node(vs_get(vst, base + 6), vs_get(vst, base + 5), vs_get(vst, base + 2))
    end if
    call vs_leave(vst, base)
  end function analyze

  ! Whether a form is a collection LITERAL -- the three Clojure's
  ! Compiler wraps in a MetaExpr. A list is code, not a literal, and
  ! its metadata is the caller's business.
  logical function literal_coll(v)
    type(gc_value), intent(in) :: v
    integer :: k
    literal_coll = .false.
    if (v%tag /= GCT_OBJ) return
    k = gc_kind(v)
    literal_coll = (k == OBJ_VECTOR .or. k == OBJ_MAP .or. k == OBJ_HAMT &
         .or. k == OBJ_SET)
  end function literal_coll

  ! (with-meta value-node meta-form): the metadata map is ANALYSED,
  ! so ^{:zip/branch? branch?} closes over the local.
  recursive function meta_call_node(vnode, mform, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: vnode, mform, sc
    type(gc_value) :: nd, kids, mn
    integer :: base
    tctx => ctx_self()
    vst => tctx%stk
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, vnode)
    call vs_set(vst, base + 2, mform)
    call vs_set(vst, base + 3, sc)
    mn = analyze(vs_get(vst, base + 2), vs_get(vst, base + 3))
    if (tctx%has_error) then
       nd = vs_get(vst, base + 1)
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 4, mn)
    kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call vs_set(vst, base + 5, kids)
    kids = gcv_conj(vs_get(vst, base + 5), &
         const_node(native(B_WITHMETA, "with-meta", [vs_get(vst, base + 5)]), &
                    [vs_get(vst, base + 5)]), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 5, kids)
    kids = gcv_conj(vs_get(vst, base + 5), vs_get(vst, base + 1), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 5, kids)
    kids = gcv_conj(vs_get(vst, base + 5), vs_get(vst, base + 4), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 5, kids)
    nd = mk_node(N_CALL, vs_get(vst, base + 5), gc_nil(), gc_nil(), 0, &
         [vs_get(vst, base + 5)])
    call vs_leave(vst, base)
  end function meta_call_node

  ! A map literal: children alternate key, value.
  recursive function analyze_map(form, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, kids, kn, vn
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, form)
    call vs_set(vst, base + 2, sc)
    call gca_entries(form, ks, vls)
    kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, kids)
    do i = 1, size(ks)
       kn = analyze(ks(i), vs_get(vst, base + 2))
       if (tctx%has_error) exit
       kids = gcv_conj(vs_get(vst, base + 3), kn, [vs_get(vst, base + 1), vs_get(vst, base + 2), kn])
       call vs_set(vst, base + 3, kids)
       vn = analyze(vls(i), vs_get(vst, base + 2))
       if (tctx%has_error) exit
       kids = gcv_conj(vs_get(vst, base + 3), vn, [vs_get(vst, base + 1), vs_get(vst, base + 2), vn])
       call vs_set(vst, base + 3, kids)
    end do
    if (.not. tctx%has_error) nd = mk_node(N_MAP, vs_get(vst, base + 3), gc_nil(), gc_nil(), 0, &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_map

  ! A symbol: a local, a static field, a Var, a class literal -- in the
  ! order Compiler.analyzeSymbol tries them.
  recursive function analyze_symbol(sym, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: sym, sc
    type(gc_value) :: nd, var, v, al
    character(len=:), allocatable :: t
    integer :: base, slot, sl

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, sym)
    call vs_set(vst, base + 2, sc)
    slot = lookup_local(vs_get(vst, base + 2), vs_get(vst, base + 1))
    if (slot >= 0) then
       nd = mk_node(N_LOCAL, gc_nil(), vs_get(vst, base + 1), gc_nil(), slot, [vs_get(vst, base + 2)])
       call vs_leave(vst, base)
       return
    end if
    ! a deftype method's mutable field: read through this, each time
    al = lookup_field_alias(vs_get(vst, base + 2), vs_get(vst, base + 1))
    if (gcv_is(al)) then
       if (truthy(gcv_nth(al, 1))) then
          call vs_set(vst, base + 3, al)
          call gc_ref_text(sym%ref, s=dlt_1)
          nd = analyze(field_read(gcv_nth(vs_get(vst, base + 3), 0), dlt_1, [vs_get(vst, base + 1), vs_get(vst, base + 2)]), &
               vs_get(vst, base + 2))
          call vs_leave(vst, base)
          return
       end if
    end if
    ! clotran.rt/array-list with clotran.rt not loaded yet
    block
       call gc_ref_text(sym%ref, s=dlt_1)
       call prepare_clotran_name(dlt_1)
    end block
    ! String/1: an array class (CLJ-2807), not a static field or a Var
    block
       logical :: ok_arr
       call gc_ref_text(sym%ref, s=dlt_1)
       call array_class_key(dlt_1, dlt_2, ok_arr)
       if (ok_arr) then
          v = gc_class(dlt_2, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call vs_set(vst, base + 3, v)
          nd = const_node(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call vs_leave(vst, base)
          return
       else if (len(dlt_2) > 0) then
          call raise_class("clotran.host.class_not_found_exception", dlt_2, &
               [vs_get(vst, base + 1), vs_get(vst, base + 2)])
          call vs_leave(vst, base)
          return
       end if
    end block
    if (is_static_call(sym)) then
       ! Class/field in value position: a static FIELD. Resolved now,
       ! since the answer cannot change; an unknown one fails where it
       ! is used rather than where it is written, as before.
       block
          call gc_ref_text(sym%ref, s=dlt_1)
          t = dlt_1
       end block
       sl = sym_slash(t)
       ! the one static whose value changes (RT/checkSpecAsserts, a box):
       ! read when run, not folded
       if (static_is_box(t(1:sl-1), t(sl+1:))) then
          nd = analyze(host_box_form([vs_get(vst, base + 1), vs_get(vst, base + 2)]), vs_get(vst, base + 2))
          call vs_leave(vst, base)
          return
       end if
       v = static_member(t(1:sl-1), t(sl+1:), vs_get(vst, base + 1))
       if (tctx%has_error) then
          call gce_clear_error()
          nd = fail_node("no such member: " // t, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       else
          call vs_set(vst, base + 3, v)
          nd = const_node(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       end if
       call vs_leave(vst, base)
       return
    end if
    var = resolve_var(vs_get(vst, base + 1), gc_nil())
    if (gcn_is_var(var)) then
       ! Compiler.resolveIn: another namespace's private Var is not
       ! reachable by its qualified name; #'ns/x still is
       block
          call gc_ref_text(sym%ref, s=dlt_1)
       if (sym_slash(dlt_1) > 1) then
          if (var_not_public(var)) then
             block
                call gc_ref_text(sym%ref, s=dlt_2)
                call fail("var: " // dlt_2 // " is not public")
             end block
             call vs_leave(vst, base)
             return
          end if
       end if
       end block
       ! Compiler.analyzeSymbol: a macro has no value to take --
       ! (apply and xs) and (map or a b) are errors, not nil
       block
          type(gc_value) :: md
          md = gc_slot(var, 2)
          if (gca_is(md)) then
             if (truthy(gca_get(md, gc_key("macro", [var])))) then
                block
                   call gcp_str(var, .false., s=dlt_1)
                   call fail("Can't take value of a macro: " // dlt_1)
                end block
                call vs_leave(vst, base)
                return
             end if
          end if
       end block
       call vs_set(vst, base + 3, var)
       ! i2 = 1: DIRECT-LINKED (DEVIATIONS 55). Clojure compiles its own
       ! namespaces with direct linking: a call from one core fn to
       ! another binds, when the caller is COMPILED, to the fn its Var
       ! holds then, and never goes through the Var again. The same
       ! here, at analysis: the fn goes in slot 3, the epoch in slot 5
       ! (exec.inc, N_CALL). A Var not yet bound to a fn -- a forward
       ! declaration -- stays late-bound, as in clj; so does one bound
       ! to a BUILTIN: the host binds Fortran builtins into clojure.core
       ! before core.clj defines the real thing (map, list, ...), and
       ! `declare`, analysed before core's `map`, must not keep the
       ! builtin -- clj has no such placeholder to link to. Taking the fn
       ! at the FIRST CALL instead was tried and is wrong: (with-redefs
       ! [first last] (first [1 2])) calls last for the first time inside
       ! the redefinition, and last's own `first` would have bound to it.
       nd = mk_node(N_VAR, gc_nil(), vs_get(vst, base + 3), gc_nil(), direct_link_flag(vs_get(vst, base + 3)), &
            [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       if (gc_i2(nd) == 1) then
          block
             type(gc_value) :: fv
             fv = gcn_var_value(vs_get(vst, base + 3))
             if (gc_kind(fv) == OBJ_CLOSURE .or. gc_kind(fv) == OBJ_COMPILED) then
                call gc_set_slot(nd, 3, fv)
                call gc_set_slot(nd, 5, gc_int(int(link_epoch, gc_ip)))
             end if
          end block
       end if
       call vs_leave(vst, base)
       return
    end if
    block
       call gc_ref_text(sym%ref, s=dlt_1)
    if (sym_slash(dlt_1) > 1) then
       ! A QUALIFIED symbol that does not resolve. In the vendored tree,
       ! clotran's own files and Clojure's own tests it is deferred to run
       ! time (N_LATEVAR): core.clj names clotran.io/text-reader before
       ! clotran.io is loaded, which loads it, and names libraries that are
       ! skipped (DEVIATIONS 12). Everywhere else it is Compiler.resolveIn's
       ! refusal when the form is analysed (DEVIATIONS 32 resolved).
       if (.not. defers_late_vars()) then
          block
             integer :: slash
             type(gc_value) :: nsv
             slash = sym_slash(dlt_1)
             nsv = alias_target(dlt_1(1:slash - 1), [vs_get(vst, base + 1)])
             if (gc_kind(nsv) /= OBJ_NS) nsv = gcn_find(dlt_1(1:slash - 1))
             if (gc_kind(nsv) == OBJ_NS) then
                if (gca_is(gc_slot(nsv, 4))) then
                   if (truthy(gca_get(gc_slot(nsv, 4), gc_key("clotran/placeholder", [nsv])))) nsv = gc_nil()
                end if
             end if
             if (gc_kind(nsv) == OBJ_NS) then
                call fail("No such var: " // dlt_1)
             else
                call fail("No such namespace: " // dlt_1(1:slash - 1))
             end if
          end block
          call vs_leave(vst, base)
          return
       end if
       nd = mk_node(N_LATEVAR, gc_nil(), vs_get(vst, base + 1), gc_nil(), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_leave(vst, base)
       return
    end if
    end block
    if (is_class_name(sym)) then
       ! A CLASS LITERAL evaluates to the class. A QUALIFIED name must name
       ! a class that exists -- a host row, a registered type, clotran's
       ! own -- as Class.forName must: user.Person from another namespace,
       ! or no.such.Klass, is Compiler's "Unable to resolve classname".
       ! A bare name is a class only as an import or a type clotran knows;
       ! any other capitalized name is an unresolved symbol, as in clj.
       block
          call gc_ref_text(sym%ref, s=dlt_1)
          call class_key(dlt_1, k=dlt_2)
          if (index(dlt_1, ".") > 0) then
             if (.not. known_class_name(dlt_1)) then
                call fail("Unable to resolve classname: " // dlt_1)
                call vs_leave(vst, base)
                return
             end if
          else if (.not. known_class_name(dlt_2)) then
             call fail("Unable to resolve symbol: " // dlt_1 // " in this context")
             call vs_leave(vst, base)
             return
          end if
          v = gc_class(dlt_2, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       end block
       call vs_set(vst, base + 3, v)
       nd = const_node(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_leave(vst, base)
       return
    end if
    block
       call gc_ref_text(sym%ref, s=dlt_1)
       call fail("Unable to resolve symbol: " // dlt_1 // " in this context")
    end block
    call vs_leave(vst, base)
  end function analyze_symbol

  ! A list form: special form, macro call, host sugar, or a call.
  ! The :inline fn of the Var `head` names, when its :inline-arities
  ! accept `argc`; nil otherwise. Compiler.isInline.
  recursive function inline_fn(head, argc) result(fn)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: head
    integer, intent(in) :: argc
    type(gc_value) :: fn, var, md, pred, ok
    integer :: base
    tctx => ctx_self()
    vst => tctx%stk
    fn = gc_nil()
    var = resolve_var(head, gc_nil())
    if (.not. gcn_is_var(var)) return
    md = gc_slot(var, 2)
    if (.not. gca_is(md)) return
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, md)
    fn = gca_get(vs_get(vst, base + 1), gc_key("inline", [vs_get(vst, base + 1)]))
    if (fn%tag == GCT_NIL) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 2, fn)
    pred = gca_get(vs_get(vst, base + 1), gc_key("inline-arities", [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
    if (pred%tag /= GCT_NIL) then
       ok = apply(pred, gcv_conj(gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2), pred]), gc_int(int(argc, gc_ip)), &
            [vs_get(vst, base + 1), vs_get(vst, base + 2), pred]))
       if (tctx%has_error .or. .not. truthy(ok)) fn = gc_nil()
    end if
    if (fn%tag /= GCT_NIL) fn = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function inline_fn

  ! A list of forms as a vector, for apply.
  function args_vector(forms, roots) result(v)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: forms
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, walk
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, forms)
    v = gcv_empty([roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, v)
    walk = vs_get(vst, base + 1)
    do while (gcl_count(walk) > 0)
       call vs_set(vst, base + 2, gcv_conj(vs_get(vst, base + 2), gcl_first(walk), [roots, vs_get(vst, base + 1), walk]))
       walk = gcl_rest(walk, [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 1, walk)
    end do
    v = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  end function args_vector

  recursive function analyze_seq(form, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, head, mvar, expanded
    integer :: base
    character(len=:), allocatable :: hint

    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    hint = tctx%fn_hint
    tctx%fn_hint = ""
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, form)
    call vs_set(vst, base + 2, sc)
    head = strip_meta(gcl_first(form))

    if (head%tag == GCT_SYM) then
       ! A LOCAL shadows a macro and host sugar, not a special form of
       ! Clojure's: Compiler.analyzeSeq asks specials.valAt(op) whatever
       ! the locals are, so (let [do f] (do 1)) is 1 and (let [proxy f]
       ! (proxy 1)) a call of the local -- proxy and clotran's own
       ! specials (defmacro*, lazy-seq*, clotran-fields*) are not Clojure's.
       ! The local is not looked up then, so no fn captures it.
       if (clj_special(head)) then
          if (gc_ref_is(head%ref, "fn*")) tctx%fn_hint = hint
          nd = analyze_special(head, vs_get(vst, base + 1), vs_get(vst, base + 2))
          call vs_leave(vst, base)
          return
       end if
       if (lookup_local(vs_get(vst, base + 2), head) < 0) then
          ! A special form is itself whatever a macro of that name says:
          ! Compiler.macroexpand1 asks isSpecial before isMacro, which is
          ! what lets clojure.spec.alpha define a macro named `def` and
          ! still write (defn ...) in the same file.
          if (is_special(head)) then
             if (gc_ref_is(head%ref, "fn*")) tctx%fn_hint = hint
             nd = analyze_special(head, vs_get(vst, base + 1), vs_get(vst, base + 2))
             call vs_leave(vst, base)
             return
          end if
          ! Macros are expanded next: `..` is a macro whose name looks
          ! like member sugar, and Compiler.macroexpand1 asks isMacro
          ! before it looks at the dot.
          mvar = macro_var(head, gc_nil())
          if (gcn_is_var(mvar)) then
             call vs_set(vst, base + 3, mvar)
             call check_specs(vs_get(vst, base + 3), vs_get(vst, base + 1))
             if (tctx%has_error) then
                call vs_leave(vst, base)
                return
             end if
             mvar = vs_get(vst, base + 3)
             call vs_set(vst, base + 3, gcn_var_value(mvar))
             ! &env: the locals in scope, as LOCAL_ENV holds them -- a map
             ! from each name to something truthy (Clojure's LocalBinding;
             ! the slot here). nil answered (contains? &env 'x) false for
             ! every local, and a macro could not tell one from a Var.
             call vs_set(vst, base + 4, locals_env(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 3)]))
             expanded = expand_macro(vs_get(vst, base + 3), vs_get(vst, base + 1), vs_get(vst, base + 4), mvar)
             if (tctx%has_error) then
                call vs_leave(vst, base)
                return
             end if
             call vs_set(vst, base + 4, expanded)
             call vs_set(vst, base + 4, forms_as_lists(vs_get(vst, base + 4), [vs_get(vst, base + 1)]))
             tctx%fn_hint = hint
             nd = analyze(vs_get(vst, base + 4), vs_get(vst, base + 2))
             call vs_leave(vst, base)
             return
          end if
          ! :inline, as Compiler.analyzeSeq does right after macroexpansion
          ! (isInline): a Var whose metadata carries an :inline fn, and
          ! whose :inline-arities -- if any -- accepts this argument count,
          ! has that fn applied to the argument FORMS and the result
          ! analysed instead of a call. core.clj gives 129 definitions one:
          ! (+ a b) becomes (. clotran.host.numbers (add a b)) and the
          ! static call resolves to the native here, so the arithmetic
          ! in a loop costs no closure call. preserveTag is not done: a
          ! :tag on the form is a hint nothing here reads.
          mvar = inline_fn(head, gcl_count(vs_get(vst, base + 1)) - 1)
          if (tctx%has_error) then
             call vs_leave(vst, base)
             return
          end if
          if (mvar%tag /= GCT_NIL) then
             call vs_set(vst, base + 3, mvar)
             expanded = apply(vs_get(vst, base + 3), args_vector(gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 3)]), [vs_get(vst, base + 3)]))
             if (tctx%has_error) then
                call vs_leave(vst, base)
                return
             end if
             call vs_set(vst, base + 4, expanded)
             call vs_set(vst, base + 4, forms_as_lists(vs_get(vst, base + 4), [vs_get(vst, base + 1)]))
             nd = analyze(vs_get(vst, base + 4), vs_get(vst, base + 2))
             call vs_leave(vst, base)
             return
          end if
          if (is_member_sym(head)) then
             nd = analyze_dot(member_to_dot(vs_get(vst, base + 1)), vs_get(vst, base + 2))
             call vs_leave(vst, base)
             return
          end if
          if (is_static_call(head)) then
             ! clotran.rt.TransformerIterator/create with clotran.rt not loaded yet
             block
               character(len=:), allocatable :: ht
               call gc_ref_text(head%ref, s=ht)
               call prepare_clotran_name(ht)
             end block
             nd = analyze_dot(static_to_dot(vs_get(vst, base + 1)), vs_get(vst, base + 2))
             call vs_leave(vst, base)
             return
          end if
          if (is_ctor_sym(head)) then
             nd = analyze_new(ctor_to_new(vs_get(vst, base + 1)), vs_get(vst, base + 2))
             call vs_leave(vst, base)
             return
          end if
       end if
    end if

    nd = analyze_call(vs_get(vst, base + 1), vs_get(vst, base + 2))
    call vs_leave(vst, base)
  end function analyze_seq

  ! CLOTRAN_TRACE_MACRO=1 also names the innermost list form whose
  ! analysis failed, which is how a structural surprise in a
  ! macro-built form gets found.
  subroutine trace_analysis_failure(form)
    type(gc_value), intent(in) :: form
    character(len=:), allocatable :: t
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    if (trace_macros == 0) call read_trace_macros()
    if (trace_macros /= 1) return
    block
       call gcp_str(form, .true., s=dlt_1)
       t = dlt_1
    end block
    if (len(t) > 300) t = t(1:300) // "..."
    write(0, '(A,A)') "analysis failed in: ", t
  end subroutine trace_analysis_failure

  ! (f a b) -> N_CALL with children [f a b].
  recursive function analyze_call(form, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, kids
    integer :: base
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, form)
    call vs_set(vst, base + 2, sc)
    kids = analyze_all(vs_get(vst, base + 1), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, kids)
    if (.not. tctx%has_error) then
       kids = cast_array_arg(gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)]), vs_get(vst, base + 3), vs_get(vst, base + 2), &
            [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
       call vs_set(vst, base + 3, kids)
    end if
    if (.not. tctx%has_error) call instance_of_head(base + 3)
    if (.not. tctx%has_error) nd = mk_node(N_CALL, vs_get(vst, base + 3), gc_nil(), gc_nil(), 0, &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_call

  ! (instance? C x), C a class literal, is the type test itself, as the
  ! clj compiler makes it (Compiler, InvokeExpr.parse: a head that
  ! is the Var clojure.core/instance?, two arguments, the first a Class
  ! constant -> InstanceOfExpr): the isInstance builtin becomes the
  ! head, and the Var is not called. It was two interpreted calls and a
  ! host dispatch -- chunked-seq? cost 400 ns, per element of every
  ! reduce1 and map.
  subroutine instance_of_head(slot)
    integer, intent(in) :: slot
    type(gc_stack), pointer :: vst
    type(gc_value) :: kids, h, var, nm, ns, core, c, b
    integer :: base
    vst => gc_my_stack()
    kids = vs_get(vst, slot)
    if (gcv_count(kids) /= 3) return
    h = gcv_nth(kids, 0)
    if (gc_kind(h) /= OBJ_AST) return
    if (gc_i1(h) /= N_VAR) return
    var = gc_slot(h, 2)
    if (gc_kind(var) /= OBJ_VAR) return
    nm = gc_slot(var, 4)
    if (nm%tag /= GCT_SYM) return
    if (.not. gc_ref_is(nm%ref, "instance?")) return
    ns = gc_slot(var, 3)
    core = gcn_find("clojure.core")
    if (ns%tag /= core%tag .or. ns%ref /= core%ref) return
    c = gcv_nth(kids, 1)
    if (gc_kind(c) /= OBJ_AST) return
    if (gc_i1(c) /= N_CONST) return
    if (tag_of(strip_meta(gc_slot(c, 2))) /= GCT_CLASS) return
    base = vs_enter(vst, 1)
    b = native(B_INSTANCE, "instance?", [kids])
    call vs_set(vst, base + 1, b)
    b = const_node(vs_get(vst, base + 1), [kids])
    call vs_set(vst, base + 1, b)
    kids = gcv_assoc(vs_get(vst, slot), 0, vs_get(vst, base + 1), [vs_get(vst, base + 1)])
    call vs_set(vst, slot, kids)
    call vs_leave(vst, base)
  end subroutine instance_of_head


  ! --- host sugar, rewritten into the canonical forms ----------------

  ! (.member target args) -> (. target member args)   [the shape eval_dot reads]
  function member_to_dot(form) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: form
    type(gc_value) :: out, head, rest, args
    character(len=:), allocatable :: hname
    integer :: base
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, form)
    head = gcl_first(form)
    block
       call gc_ref_text(head%ref, s=dlt_1)
       hname = dlt_1
    end block
    call vs_set(vst, base + 2, gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)]))
    call vs_set(vst, base + 3, gc_sym(hname(2:), [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
    call vs_set(vst, base + 4, gcl_rest(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)]))
    args = gcl_cons(vs_get(vst, base + 3), vs_get(vst, base + 4), [vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
    call vs_set(vst, base + 4, args)
    args = gcl_cons(gcl_first(vs_get(vst, base + 2)), vs_get(vst, base + 4), [vs_get(vst, base + 2), vs_get(vst, base + 4)])
    call vs_set(vst, base + 4, args)
    out = gcl_cons(gc_sym(".", [vs_get(vst, base + 4)]), vs_get(vst, base + 4), [vs_get(vst, base + 4)])
    call vs_leave(vst, base)
  end function member_to_dot

  ! (Class/member args) -> (. Class (member args))
  function static_to_dot(form) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: form
    type(gc_value) :: out, head, args
    character(len=:), allocatable :: t
    integer :: base, slash
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, form)
    head = gcl_first(form)
    block
       call gc_ref_text(head%ref, s=dlt_1)
       t = dlt_1
    end block
    slash = sym_slash(t)
    call vs_set(vst, base + 2, gc_sym(t(slash+1:), [vs_get(vst, base + 1)]))
    call vs_set(vst, base + 3, gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
    args = gcl_cons(vs_get(vst, base + 2), vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 3, args)                              ! (member args)
    call vs_set(vst, base + 4, gcl_empty([vs_get(vst, base + 3)]))
    args = gcl_cons(vs_get(vst, base + 3), vs_get(vst, base + 4), [vs_get(vst, base + 3), vs_get(vst, base + 4)])
    call vs_set(vst, base + 3, args)                              ! ((member args))
    call vs_set(vst, base + 4, gc_sym(t(1:slash-1), [vs_get(vst, base + 3)]))
    args = gcl_cons(vs_get(vst, base + 4), vs_get(vst, base + 3), [vs_get(vst, base + 3), vs_get(vst, base + 4)])
    call vs_set(vst, base + 3, args)                              ! (Class (member args))
    out = gcl_cons(gc_sym(".", [vs_get(vst, base + 3)]), vs_get(vst, base + 3), [vs_get(vst, base + 3)])
    call vs_leave(vst, base)
  end function static_to_dot

  ! (Class. args) -> (new Class args)
  function ctor_to_new(form) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: form
    type(gc_value) :: out, head, args
    character(len=:), allocatable :: t
    integer :: base
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, form)
    head = gcl_first(form)
    block
       call gc_ref_text(head%ref, s=dlt_1)
       t = dlt_1
    end block
    call vs_set(vst, base + 2, gc_sym(t(1:len(t)-1), [vs_get(vst, base + 1)]))
    call vs_set(vst, base + 3, gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
    args = gcl_cons(vs_get(vst, base + 2), vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    call vs_set(vst, base + 3, args)
    out = gcl_cons(gc_sym("new", [vs_get(vst, base + 3)]), vs_get(vst, base + 3), [vs_get(vst, base + 3)])
    call vs_leave(vst, base)
  end function ctor_to_new

  ! (. target member args...) or (. target (member args...)).
  !
  ! A static call on a host class is resolved to its native NOW, so
  ! (clotran.host.rt/first x) is an ordinary call of a constant --
  ! that is most of what core.clj does. Everything else keeps the
  ! shape and is handed to eval_dot at run time with its parts already
  ! evaluated (N_DOT), because eval_dot holds the instance rules: a
  ! deftype answers its own methods before any host member does.
  recursive function analyze_dot(form, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, args, target, rest, member, margs, kids, fnv, tn
    character(len=:), allocatable :: mname
    logical :: is_call
    integer :: base

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 8)
    call vs_set(vst, base + 1, form)
    call vs_set(vst, base + 2, sc)
    args = gcl_rest(form, [vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, args)
    if (gcl_count(vs_get(vst, base + 3)) < 2) then
       call fail("Malformed member expression")
       call vs_leave(vst, base)
       return
    end if
    target = gcl_first(vs_get(vst, base + 3))
    call vs_set(vst, base + 4, target)
    rest = gcl_rest(vs_get(vst, base + 3), [vs_get(vst, base + 1)])
    member = strip_meta(gcl_first(rest))
    if (gc_kind(member) == OBJ_LAZY .or. gc_kind(member) == OBJ_SEQ) then
       call vs_set(vst, base + 5, member)
       member = seq_to_list(vs_get(vst, base + 5), [vs_get(vst, base + 1), vs_get(vst, base + 5)])
    end if
    call vs_set(vst, base + 5, member)
    ! the member as HostExpr.Parser reads it (model/anform.lisp anf-dot-member),
    ! after it has analysed a target that names no class: a target that cannot
    ! be analysed is the refusal then
    if (anf_dot_member(frf_len(vs_get(vst, base + 1)), vs_get(vst, base + 5)) /= 0) then
       if (frf_class(vs_get(vst, base + 4)) == 0) then
          tn = analyze(vs_get(vst, base + 4), vs_get(vst, base + 2))
          if (tctx%has_error) then
             call vs_leave(vst, base)
             return
          end if
       end if
       call anf_refuse(37_int64, vs_get(vst, base + 1))
       call vs_leave(vst, base)
       return
    end if
    if (gcl_is(vs_get(vst, base + 5))) then
       is_call = .true.
       margs = gcl_rest(vs_get(vst, base + 5), [vs_get(vst, base + 1)])
       member = strip_meta(gcl_first(vs_get(vst, base + 5)))
    else
       margs = gcl_rest(gcl_rest(vs_get(vst, base + 3), [vs_get(vst, base + 1)]), [vs_get(vst, base + 1)])
       is_call = (gcl_count(margs) > 0)
    end if
    call vs_set(vst, base + 6, margs)
    call vs_set(vst, base + 5, member)
    block
       call gc_ref_text(member%ref, s=dlt_1)
       mname = dlt_1
    end block
    ! A member name reached through syntax-quote arrives qualified --
    ! defmethod's template says addMethod and the reader makes it
    ! clojure.core/addMethod. HostExpr.Parser reads sym.name only, and
    ! so does this.
    if (sym_slash(mname) > 1) then
       mname = mname(sym_slash(mname) + 1:)
       member = gc_sym(mname, [vs_get(vst, base + 1), vs_get(vst, base + 5)])
       call vs_set(vst, base + 5, member)
    end if

    ! A host class as the target: a static member, resolved once.
    if (target%tag == GCT_SYM) then
       if (lookup_local(vs_get(vst, base + 2), target) < 0) then
          block
             call gc_ref_text(target%ref, s=dlt_1)
          if (gc_kind(find_type(dlt_1)) /= OBJ_TYPE .and. is_host_class(target)) then
             block
                call gc_ref_text(target%ref, s=dlt_2)
                ! (. Class member) of the writable static: read when run
                if (static_is_box(dlt_2, mname)) then
                   nd = analyze(host_box_form([vs_get(vst, base + 1), vs_get(vst, base + 2)]), vs_get(vst, base + 2))
                   call vs_leave(vst, base)
                   return
                end if
                fnv = static_member(dlt_2, mname, vs_get(vst, base + 1))
             end block
             if (tctx%has_error) then
                ! Not a static of that class: a member of the CLASS
                ! OBJECT, (.isAssignableFrom String Object) or (.getName
                ! String), left to eval_dot below. A member neither has
                ! still fails there by name.
                call gce_clear_error()
             else
                call vs_set(vst, base + 7, fnv)
                ! (. Class member) with no arguments is a FIELD if there is
                ! one, else the zero-argument METHOD, as the Reflector
                ! decides: (. clotran.host.var create) makes a Var, where
                ! it answered the builtin itself. PersistentList/creator
                ! is the one field here whose value is a function.
                if (.not. is_call .and. gc_kind(fnv) == OBJ_BUILTIN .and. mname /= "creator") is_call = .true.
                if (.not. is_call) then
                   nd = const_node(vs_get(vst, base + 7), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
                   call vs_leave(vst, base)
                   return
                end if
                ! (native args...) as a plain call
                tn = const_node(vs_get(vst, base + 7), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
                call vs_set(vst, base + 8, tn)
                kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 8)])
                call vs_set(vst, base + 7, kids)
                kids = gcv_conj(vs_get(vst, base + 7), vs_get(vst, base + 8), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
                call vs_set(vst, base + 7, kids)
                kids = analyze_all(vs_get(vst, base + 6), vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 7)])
                call vs_set(vst, base + 8, kids)
                if (tctx%has_error) then
                   call vs_leave(vst, base)
                   return
                end if
                kids = concat_vecs(vs_get(vst, base + 7), vs_get(vst, base + 8), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
                call vs_set(vst, base + 7, kids)
                kids = cast_array_arg(vs_get(vst, base + 6), vs_get(vst, base + 7), vs_get(vst, base + 2), &
                     [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 6), vs_get(vst, base + 7)])
                call vs_set(vst, base + 7, kids)
                nd = mk_node(N_CALL, vs_get(vst, base + 7), gc_nil(), gc_nil(), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
                call vs_leave(vst, base)
                return
             end if
          end if
          end block
          ! A deftype class, or a class name is_host_class does not know:
          ! left to eval_dot, target passed as the symbol, unevaluated.
          block
             call gc_ref_text(target%ref, s=dlt_1)
          if (gc_kind(find_type(dlt_1)) == OBJ_TYPE .or. is_class_name(target)) then
             ! the class in full, once, here, as analyze_new does: a bare name
             ! is resolved by the namespace being analysed, not the one running
             block
                character(len=:), allocatable :: canonical
                call canon_class(dlt_1, c=canonical)
                if (canonical /= dlt_1) call vs_set(vst, base + 4, gc_sym(canonical, [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
             end block
             ! a class name nothing knows -- no import, no deftype* analysed so far
             ! (declare_type_name), no host row -- is Compiler.resolveIn's refusal
             ! when analysed (DEVIATIONS 32), outside the files that defer
             block
                character(len=:), allocatable :: canonical
                call canon_class(dlt_1, c=canonical)
                if (.not. known_class_name(canonical) .and. .not. defers_late_vars()) then
                   call fail("No such namespace: " // dlt_1)
                   call vs_leave(vst, base)
                   return
                end if
             end block
             kids = analyze_all(vs_get(vst, base + 6), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
             call vs_set(vst, base + 7, kids)
             if (.not. tctx%has_error) then
                nd = mk_node(N_DOT, vs_get(vst, base + 7), vs_get(vst, base + 5), vs_get(vst, base + 4), &
                     merge(1, 0, is_call), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
             end if
             call vs_leave(vst, base)
             return
          end if
          end block
       end if
    end if

    ! An instance member: children [target args...]; the native it
    ! names, if any, cached in slot 3 for the executor's fast path.
    tn = analyze(vs_get(vst, base + 4), vs_get(vst, base + 2))
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 8, tn)
    kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 8)])
    call vs_set(vst, base + 7, kids)
    kids = gcv_conj(vs_get(vst, base + 7), vs_get(vst, base + 8), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 7, kids)
    kids = analyze_all(vs_get(vst, base + 6), vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 7)])
    call vs_set(vst, base + 8, kids)
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    kids = concat_vecs(vs_get(vst, base + 7), vs_get(vst, base + 8), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 7, kids)
    fnv = instance_member(mname, vs_get(vst, base + 1))
    if (tctx%has_error) then
       call gce_clear_error()
       fnv = gc_nil()
    end if
    call vs_set(vst, base + 8, fnv)
    nd = mk_node(N_DOT, vs_get(vst, base + 7), vs_get(vst, base + 5), vs_get(vst, base + 8), &
         merge(1, 0, is_call), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_dot

  ! (new Class args...). A deftype constructs directly (N_NEWTYPE, by
  ! name, looked up at run time so a redefined type is found); a host
  ! class goes to eval_new with its arguments evaluated (N_NEW).
  recursive function analyze_new(form, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, cls, kids, args
    integer :: base
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, form)
    call vs_set(vst, base + 2, sc)
    args = gcl_rest(form, [vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, args)
    cls = strip_meta(gcl_first(vs_get(vst, base + 3)))
    if (anf_new(vs_get(vst, base + 1)) /= 0) then
       call anf_refuse(anf_new(vs_get(vst, base + 1)), frf_nth(vs_get(vst, base + 1), 1_int64))
       call vs_leave(vst, base)
       return
    end if
    ! the class in full, once, here: a bare name through the imports
    block
      character(len=:), allocatable :: written, canonical
      call gc_ref_text(cls%ref, s=written)
      call canon_class(written, c=canonical)
      ! a name no import, no deftype* analysed so far and no host row knows
      ! was refused above (anf_new's frf_class, DEVIATIONS 17, 32): a
      ! deftype's bare name means it only where imported
      if (canonical /= written) cls = gc_sym(canonical, [vs_get(vst, base + 1), vs_get(vst, base + 3)])
    end block
    call vs_set(vst, base + 4, cls)
    ! (new clotran.host.lazy_seq (fn* [] body...)) is what the lazy-seq
    ! macro writes, and it is the N_LAZY node, not a generic new: the
    ! generic path evaluated the fn outside the run loop and then found
    ! LazySeq by comparing its name down a chain of constructors --
    ! 680 ns for every lazy cell core.clj makes, against 200
    if (gc_ref_is(cls%ref, "clotran.host.lazy_seq")) then
       block
         type(gc_value) :: ctor, fhead, fparams
         ctor = gcl_rest(vs_get(vst, base + 3), [vs_get(vst, base + 1)])
         if (gcl_count(ctor) == 1) then
            ctor = strip_meta(gcl_first(ctor))
            if (gcl_is(ctor)) then
               if (gcl_count(ctor) >= 2) then
                  fhead = strip_meta(gcl_first(ctor))
                  fparams = strip_meta(gcl_first(gcl_rest(ctor, [vs_get(vst, base + 1)])))
                  if (fhead%tag == GCT_SYM .and. gcv_is(fparams)) then
                     if (gc_ref_is(fhead%ref, "fn*") .and. gcv_count(fparams) == 0) then
                        call vs_set(vst, base + 5, ctor)
                        nd = analyze_lazy(gcl_rest(gcl_rest(vs_get(vst, base + 5), [vs_get(vst, base + 1)]), &
                             [vs_get(vst, base + 1), vs_get(vst, base + 5)]), vs_get(vst, base + 2))
                        call vs_leave(vst, base)
                        return
                     end if
                  end if
               end if
            end if
         end if
       end block
    end if
    kids = analyze_all(gcl_rest(vs_get(vst, base + 3), [vs_get(vst, base + 1)]), vs_get(vst, base + 2), &
         [vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call vs_set(vst, base + 5, kids)
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    block
       call gc_ref_text(cls%ref, s=dlt_1)
    if (gc_kind(find_type(dlt_1)) == OBJ_TYPE) then
       nd = mk_node(N_NEWTYPE, vs_get(vst, base + 5), vs_get(vst, base + 4), gc_nil(), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    else
       nd = mk_node(N_NEW, vs_get(vst, base + 5), vs_get(vst, base + 4), gc_nil(), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    end if
    end block
    call vs_leave(vst, base)
  end function analyze_new

  function concat_vecs(a, b, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: a, b
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, a)
    call vs_set(vst, base + 2, b)
    call vs_set(vst, base + 3, a)
    do i = 0, gcv_count(b) - 1
       out = gcv_conj(vs_get(vst, base + 3), gcv_nth(vs_get(vst, base + 2), i), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call vs_set(vst, base + 3, out)
    end do
    out = vs_get(vst, base + 3)
    call vs_leave(vst, base)
  end function concat_vecs

  ! --- special forms -------------------------------------------------

  recursive function analyze_special(head, form, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: head, form, sc
    type(gc_value) :: nd, rest
    integer :: base
    integer(int64) :: code

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    nd = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, form)
    call vs_set(vst, base + 2, sc)
    rest = gcl_rest(form, [vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, rest)

    ! the special forms' refusals are the generated checks' (model/anform.lisp)
    code = 0
    if (gc_ref_is(head%ref, "quote")) then
       code = anf_quote(frf_len(form))
    else if (gc_ref_is(head%ref, "if")) then
       code = anf_if(frf_len(form))
    else if (gc_ref_is(head%ref, "throw")) then
       code = anf_throw(frf_len(form))
    else if (gc_ref_is(head%ref, "def") .or. gc_ref_is(head%ref, "defmacro*")) then
       code = anf_def(form, 0_int64)
    else if (gc_ref_is(head%ref, "set!")) then
       code = anf_set(frf_len(form))
       if (code == 0) code = anf_set_target(frf_nth(form, 1_int64))
    else if (gc_ref_is(head%ref, ".")) then
       code = anf_dot(form)
    end if
    if (code /= 0) then
       call anf_refuse(code, vs_get(vst, base + 1))
       call vs_leave(vst, base)
       return
    end if

    if (gc_ref_is(head%ref, "quote")) then
       nd = const_node(gcl_first(vs_get(vst, base + 3)), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    else if (gc_ref_is(head%ref, "if")) then
       nd = analyze_if(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "do")) then
       nd = analyze_body(vs_get(vst, base + 3), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
    else if (gc_ref_is(head%ref, "def")) then
       nd = analyze_def(vs_get(vst, base + 1), vs_get(vst, base + 2), .false.)
    else if (gc_ref_is(head%ref, "defmacro*")) then
       nd = analyze_def(vs_get(vst, base + 1), vs_get(vst, base + 2), .true.)
    else if (gc_ref_is(head%ref, "clotran-fields*")) then
       nd = analyze_fields(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "let*")) then
       nd = analyze_let(vs_get(vst, base + 3), vs_get(vst, base + 2), .false.)
    else if (gc_ref_is(head%ref, "loop*")) then
       nd = analyze_let(vs_get(vst, base + 3), vs_get(vst, base + 2), .true.)
    else if (gc_ref_is(head%ref, "letfn*")) then
       nd = analyze_letfn(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "fn*")) then
       nd = analyze_fn(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "recur")) then
       nd = analyze_recur(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "var")) then
       nd = analyze_varq(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "lazy-seq*")) then
       nd = analyze_lazy(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "throw")) then
       nd = analyze_one(N_THROW, gcl_first(vs_get(vst, base + 3)), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "try")) then
       nd = analyze_try(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "case*")) then
       nd = analyze_case(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "deftype*")) then
       nd = analyze_deftype(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "reify*")) then
       nd = analyze_reify(vs_get(vst, base + 3), vs_get(vst, base + 2), .false.)
    else if (gc_ref_is(head%ref, "proxy")) then
       nd = analyze_reify(vs_get(vst, base + 3), vs_get(vst, base + 2), .true.)
    else if (gc_ref_is(head%ref, "monitor-enter") .or. gc_ref_is(head%ref, "monitor-exit")) then
       ! A monitor, held by one thread at a time (PLAN.md step 14f): the
       ! call (clojure.core/clotran-monitor-enter x), or -exit, analysed
       ! as any call is
       block
         type(gc_value) :: f, s
         integer :: lb
         lb = vs_enter(vst, 1)
         if (gc_ref_is(head%ref, "monitor-enter")) then
            s = gc_sym("clojure.core/clotran-monitor-enter", [vs_get(vst, base + 1), vs_get(vst, base + 2)])
         else
            s = gc_sym("clojure.core/clotran-monitor-exit", [vs_get(vst, base + 1), vs_get(vst, base + 2)])
         end if
         call vs_set(vst, lb + 1, s)
         f = gcl_cons(vs_get(vst, lb + 1), vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
         call vs_set(vst, lb + 1, f)
         nd = analyze(vs_get(vst, lb + 1), vs_get(vst, base + 2))
         call vs_leave(vst, lb)
       end block
    else if (gc_ref_is(head%ref, "clojure.core/import*")) then
       ! (clotran-import* "a.B"), a call: the import is recorded when it RUNS,
       ! as ImportExpr.eval records it (B_IMPORT, DEVIATIONS 17), and answers
       ! the class, so (import ...) and definterface are the last class named
       block
         type(gc_value) :: cn
         cn = strip_meta(gcl_first(vs_get(vst, base + 3)))
         if (cn%tag == GCT_STR .or. cn%tag == GCT_SYM) then
            call gc_ref_text(cn%ref, s=dlt_1)
            call vs_set(vst, base + 3, gc_str(dlt_1, [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
            cn = gcl_cons(vs_get(vst, base + 3), gcl_empty([vs_get(vst, base + 1), vs_get(vst, base + 3)]), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, cn)
            cn = gcl_cons(gc_sym("clojure.core/clotran-import*", [vs_get(vst, base + 3)]), vs_get(vst, base + 3), [vs_get(vst, base + 3)])
            call vs_set(vst, base + 3, cn)
            nd = analyze(vs_get(vst, base + 3), vs_get(vst, base + 2))
         else
            nd = const_node(gc_nil(), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
         end if
       end block
    else if (gc_ref_is(head%ref, "set!")) then
       nd = analyze_setbang(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "new")) then
       nd = analyze_new(vs_get(vst, base + 1), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, ".")) then
       nd = analyze_dot(vs_get(vst, base + 1), vs_get(vst, base + 2))
    else
       block
          call gc_ref_text(head%ref, s=dlt_1)
          call fail("unknown special form: " // dlt_1)
       end block
    end if
    call vs_leave(vst, base)
  end function analyze_special

  ! A node of `kind` with one child.
  recursive function analyze_one(kind, form, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    integer, intent(in) :: kind
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, c, kids
    integer :: base
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, form)
    call vs_set(vst, base + 2, sc)
    c = analyze(vs_get(vst, base + 1), vs_get(vst, base + 2))
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 3, c)
    kids = gcv_conj(gcv_empty([vs_get(vst, base + 3)]), vs_get(vst, base + 3), [vs_get(vst, base + 3)])
    call vs_set(vst, base + 3, kids)
    nd = mk_node(kind, vs_get(vst, base + 3), gc_nil(), gc_nil(), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_one

  recursive function analyze_if(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, kids
    integer :: base
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    kids = analyze_all(vs_get(vst, base + 1), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, kids)
    if (.not. tctx%has_error) nd = mk_node(N_IF, vs_get(vst, base + 3), gc_nil(), gc_nil(), 0, &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_if

  ! (def name init?) -- the Var is INTERNED NOW, unbound if new, so a
  ! recursive reference in the init resolves, as DefExpr does. Its
  ! metadata (evaluated, like Compiler does) and init are children.
  ! i2: bit 1 = has an init, bit 2 = defmacro*.
  recursive function analyze_def(form, sc, is_macro) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form, sc
    logical, intent(in) :: is_macro
    type(gc_value) :: nd, nm, md, var, kids, c
    integer :: base, flags
    integer(int64) :: init, doc

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 7)
    call vs_set(vst, base + 1, form)
    call vs_set(vst, base + 2, sc)
    ! the generated check passed it (analyze_special, anf_def): a symbol, of
    ! this namespace if qualified; anf_def says where the init and the
    ! docstring are
    init = anf_def(form, 1_int64)
    doc = anf_def(form, 2_int64)
    nm = frf_nth(form, 1_int64)
    md = gc_nil()
    if (gc_kind(nm) == OBJ_META) then
       md = gc_slot(nm, 2)
       nm = strip_meta(nm)
    end if
    ! A qualified name -- (def ns/x ...) -- is allowed only for the
    ! current namespace, and defines the bare name: DefExpr's rule. A
    ! def inside a syntax-quote template arrives this way, as
    ! clojure.pprint's defdirectives does.
    call vs_set(vst, base + 4, md)
    block
      character(len=:), allocatable :: t
      integer :: sl
      block
         call gc_ref_text(nm%ref, s=dlt_1)
         t = dlt_1
      end block
      sl = sym_slash(t)
      if (sl > 1 .and. sl < len(t)) then
         nm = gc_sym(t(sl+1:), [vs_get(vst, base + 1), vs_get(vst, base + 4)])
      end if
    end block
    call vs_set(vst, base + 3, nm)
    var = gcn_lookup(gcn_current([vs_get(vst, base + 1)]), vs_get(vst, base + 3))
    if (gcn_is_var(var)) then
       ! A name this namespace only REFERS -- clojure.core's num -- is
       ! not ours to write. DefExpr interns a Var HERE (Namespace.intern
       ! warns and replaces the mapping) and leaves the foreign root
       ! alone; using the referred Var redefined clojure.core/num for the
       ! whole program the first time a package wrote (defn- num ..).
       if (gc_kind(gc_slot(var, 3)) == OBJ_NS) then
          block
             call gcn_name(gc_slot(var, 3), s=dlt_1)
             call gcn_name(gcn_current([vs_get(vst, base + 1)]), s=dlt_2)
             if (dlt_1 /= dlt_2) var = gc_nil()
          end block
       end if
    end if
    if (.not. gcn_is_var(var)) then
       var = gcn_intern(gcn_current([vs_get(vst, base + 1)]), vs_get(vst, base + 3), gc_nil(), &
            [vs_get(vst, base + 1), vs_get(vst, base + 3)])
       call gc_set_i1(var, 0)
    end if
    call vs_set(vst, base + 5, var)

    ! (def name "doc" init): DefExpr's four-element form. The docstring
    ! joins the metadata as :doc and the init is what follows it -- it
    ! used to BE the init, and (def x "doc" 1) bound the string.
    if (doc > 0) then
       c = frf_nth(vs_get(vst, base + 1), doc)
       call vs_set(vst, base + 7, c)
       if (md%tag == GCT_NIL) md = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 7)])
       call vs_set(vst, base + 4, md)
       md = gca_assoc(vs_get(vst, base + 4), gc_key("doc", [vs_get(vst, base + 1), vs_get(vst, base + 4), vs_get(vst, base + 7)]), &
            vs_get(vst, base + 7), [vs_get(vst, base + 1), vs_get(vst, base + 4), vs_get(vst, base + 7)])
       call vs_set(vst, base + 4, md)
    end if

    flags = 0
    if (is_macro) flags = 2
    kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 5)])
    call vs_set(vst, base + 6, kids)
    if (init > 0) then
       flags = flags + 1
       ! DefExpr.Parser: analyze(init, v.sym.name)
       call gc_ref_text(nm%ref, s=dlt_1)
       tctx%fn_hint = dlt_1(index(dlt_1, "/", back=.true.) + 1:)
       c = analyze(frf_nth(vs_get(vst, base + 1), init), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       kids = gcv_conj(vs_get(vst, base + 6), c, [vs_get(vst, base + 1), vs_get(vst, base + 5), c])
       call vs_set(vst, base + 6, kids)
    end if
    if (md%tag /= GCT_NIL) then
       c = analyze(vs_get(vst, base + 4), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
    else
       c = gc_nil()
    end if
    nd = mk_node(N_DEF, vs_get(vst, base + 6), vs_get(vst, base + 5), c, flags, [vs_get(vst, base + 1), vs_get(vst, base + 2), c])
    call vs_leave(vst, base)
  end function analyze_def

  ! let* and loop*: a child block, n slots reserved together, each init
  ! analysed BEFORE its name is bound (sequential scope), then the body.
  ! Children: [init_0 .. init_{n-1}, body]; slot 3 = the first slot as
  ! an int; i2 = n. A loop is also a recur target for its body.
  recursive function analyze_let(rest, sc, is_loop) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    logical, intent(in) :: is_loop
    type(gc_value) :: nd, binds, blk, kids, c, k, rinfo
    integer :: base, i, n, start, ret
    logical :: args_loop

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    ! LetExpr.Parser's checks (model/anlocal.lisp anl-shape, anl-name-code)
    binds = gcl_first(rest)
    if (anl_shape(binds) /= 0) then
       call anl_refuse(anl_shape(binds), binds, .false.)
       call vs_leave(vst, base)
       return
    end if
    binds = strip_meta(binds)
    call vs_set(vst, base + 3, binds)
    n = gcv_count(binds) / 2
    blk = child_scope(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, blk)
    start = reserve_slots(vs_get(vst, base + 4), n)
    ret = 0
    args_loop = .false.
    if (is_loop) then
       rinfo = int_vec([0, start, n], [vs_get(vst, base + 1), vs_get(vst, base + 4)])
       call gc_set_slot(vs_get(vst, base + 4), 4, rinfo)
       ! the loop* prim_hint_body wraps a ^long-returning fn's body in
       ! IS its arguments: a recur to it is checked as one to them
       ret = take_arg_kinds(vs_get(vst, base + 2), vs_get(vst, base + 4), [vs_get(vst, base + 1)])
       args_loop = gcv_is(gca_get_or_nil(gc_slot(vs_get(vst, base + 4), 5), "clotran/recur-kinds"))
    end if
    kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call vs_set(vst, base + 5, kids)
    do i = 0, n - 1
       ! the name is checked before its init is analysed, as clj does
       k = gcv_nth(vs_get(vst, base + 3), 2 * i)
       if (anl_name_code(k) /= 0) then
          call anl_refuse(anl_name_code(k), k, .false.)
          call vs_leave(vst, base)
          return
       end if
       ! Compiler.LetExpr.Parser: analyze(init, sym.name)
       k = strip_meta(gcv_nth(vs_get(vst, base + 3), 2 * i))
       if (k%tag == GCT_SYM) then
          call gc_ref_text(k%ref, s=dlt_1)
          tctx%fn_hint = dlt_1
       end if
       c = analyze(gcv_nth(vs_get(vst, base + 3), 2 * i + 1), vs_get(vst, base + 4))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       kids = gcv_conj(vs_get(vst, base + 5), c, [vs_get(vst, base + 1), vs_get(vst, base + 4), c])
       call vs_set(vst, base + 5, kids)
       ! LocalBinding: a hinted local with a primitive init is refused; a
       ! let local is its init's kind, a loop local only an Object for
       ! certain (a primitive one is boxed when a recur does not match)
       block
         integer :: pk
         pk = static_prim(gcv_nth(vs_get(vst, base + 5), i), vs_get(vst, base + 4))
         if (pk > 0 .and. has_tag(gcv_nth(vs_get(vst, base + 3), 2 * i))) then
            call raise_class("clotran.host.unsupported_operation_exception", &
                 "Can't type hint a local with a primitive initializer", [vs_get(vst, base + 1)])
            call vs_leave(vst, base)
            return
         end if
         ! a loop local is its init's primitive through the body, as clj's
         ! first pass types it -- an int a long, a float a double
         ! (LetExpr.Parser); its errors are final there too, the boxing
         ! of a mismatched recur only re-analysing a loop that had none
         if (is_loop .and. pk == PK_INT) pk = PK_LONG
         if (is_loop .and. pk == PK_FLOAT) pk = PK_DOUBLE
         ! the arguments a return-hinted fn's loop* stands for are typed
         ! by their hints, and never boxed
         if (args_loop) then
            pk = int_of(gcv_nth(gca_get_or_nil(gc_slot(vs_get(vst, base + 4), 5), "clotran/recur-kinds"), i))
            if (pk == 0) pk = PK_OBJ
         end if
         call bind_local_kind(vs_get(vst, base + 4), start + i, pk, [vs_get(vst, base + 1), vs_get(vst, base + 5)])
       end block
       k = strip_meta(gcv_nth(vs_get(vst, base + 3), 2 * i))
       call bind_name(vs_get(vst, base + 4), k, start + i, [vs_get(vst, base + 1), vs_get(vst, base + 5)])
       call bind_array_hint(vs_get(vst, base + 4), k, gcv_nth(vs_get(vst, base + 3), 2 * i), &
            [vs_get(vst, base + 1), vs_get(vst, base + 5)])
    end do
    c = analyze_body(gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)]), vs_get(vst, base + 4), &
         [vs_get(vst, base + 1), vs_get(vst, base + 5)])
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    kids = gcv_conj(vs_get(vst, base + 5), c, [vs_get(vst, base + 1), vs_get(vst, base + 4), c])
    call vs_set(vst, base + 5, kids)
    ! ObjMethod.emitBody: a ^long or ^double return takes a body of that
    ! primitive (a long an int, a double a float), or one not typed
    if (ret > 0) then
       block
         integer :: bk
         character(len=:), allocatable :: rn, bn
         bk = static_prim(c, vs_get(vst, base + 4))
         if (bk > 0 .and. bk /= ret .and. .not. (ret == PK_LONG .and. bk == PK_INT) &
              .and. .not. (ret == PK_DOUBLE .and. bk == PK_FLOAT)) then
            call prim_name(ret, rn)
            call prim_name(bk, bn)
            call raise_class("clotran.host.illegal_argument_exception", "Mismatched primitive return, expected: " // &
                 rn // ", had: " // bn, [vs_get(vst, base + 1)])
            call vs_leave(vst, base)
            return
         end if
       end block
    end if
    nd = mk_node(merge(N_LOOP, N_LET, is_loop), vs_get(vst, base + 5), gc_int(start), gc_nil(), n, &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_let

  ! A persistent vector of ints.
  function int_vec(ints, roots) result(out)
    type(gc_stack), pointer :: vst
    integer, intent(in) :: ints(:)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 1)
    out = gcv_empty(roots)
    call vs_set(vst, base + 1, out)
    do i = 1, size(ints)
       out = gcv_conj(vs_get(vst, base + 1), gc_int(ints(i)), roots)
       call vs_set(vst, base + 1, out)
    end do
    out = vs_get(vst, base + 1)
    call vs_leave(vst, base)
  end function int_vec

  ! (letfn* [name (fn* ...) ...] body): every name in scope in every
  ! init. Children: [fn_0 .. fn_{n-1}, body]; slot 2 = first slot; i2 = n.
  recursive function analyze_letfn(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, binds, blk, kids, c, k
    integer :: base, i, n, start

    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    ! LetFnExpr.Parser's checks (model/anlocal.lisp anl-shape, anl-name-code)
    binds = gcl_first(rest)
    if (anl_shape(binds) /= 0) then
       call anl_refuse(anl_shape(binds), binds, .false.)
       call vs_leave(vst, base)
       return
    end if
    binds = strip_meta(binds)
    call vs_set(vst, base + 3, binds)
    n = gcv_count(binds) / 2
    blk = child_scope(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, blk)
    start = reserve_slots(vs_get(vst, base + 4), n)
    do i = 0, n - 1
       k = gcv_nth(vs_get(vst, base + 3), 2 * i)
       if (anl_name_code(k) /= 0) then
          call anl_refuse(anl_name_code(k), k, .false.)
          call vs_leave(vst, base)
          return
       end if
       k = strip_meta(k)
       call bind_name(vs_get(vst, base + 4), k, start + i, [vs_get(vst, base + 1)])
    end do
    kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call vs_set(vst, base + 5, kids)
    do i = 0, n - 1
       c = analyze(gcv_nth(vs_get(vst, base + 3), 2 * i + 1), vs_get(vst, base + 4))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       kids = gcv_conj(vs_get(vst, base + 5), c, [vs_get(vst, base + 1), vs_get(vst, base + 4), c])
       call vs_set(vst, base + 5, kids)
    end do
    c = analyze_body(gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)]), vs_get(vst, base + 4), &
         [vs_get(vst, base + 1), vs_get(vst, base + 5)])
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    kids = gcv_conj(vs_get(vst, base + 5), c, [vs_get(vst, base + 1), vs_get(vst, base + 4), c])
    call vs_set(vst, base + 5, kids)
    nd = mk_node(N_LETFN, vs_get(vst, base + 5), gc_int(start), gc_nil(), n, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_letfn

  ! (fn* name? [params] body...) or (fn* name? ([params] body...)+)
  !
  ! The template (slot 2 of N_FN) is a persistent vector:
  !   [name, arities, captures, nslots, selfslot]
  ! and each arity is [nfixed, variadic?, first-param-slot, body].
  ! Parameters take consecutive slots; a variadic arity's rest
  ! parameter is the slot after its fixed ones. One frame serves every
  ! arity, so nslots is the total. Captures are (outer, inner) slot
  ! pairs, flattened, filled in by lookup_local as the body is analysed.
  recursive function analyze_fn(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, head, name, fsc, arities, clauses, clause, ar, tmpl, walk
    integer :: base, self_slot, nfixed, i, nflat, vmfid, vmci
    logical :: hints
    character(len=:), allocatable :: own, outer, saved

    ! captured ONCE: a method's own clauses are exempt from fn hint
    ! rules, and any fn* nested in its body is not
    tctx => ctx_self()
    vst => tctx%stk
    hints = .not. tctx%analyzing_method
    tctx%analyzing_method = .false.
    nd = gc_nil()
    base = vs_enter(vst, 9)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    head = strip_meta(gcl_first(rest))
    name = gc_nil()
    call vs_set(vst, base + 3, rest)
    if (head%tag == GCT_SYM) then
       name = head
       call vs_set(vst, base + 3, gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)]))
    end if
    call vs_set(vst, base + 4, name)
    ! its display name, as clj names its class: the enclosing fn's, or
    ! the namespace's, then its own name, or what a let or def bound it
    ! to, or fn (Compiler FnExpr.parse)
    own = "fn"
    if (allocated(tctx%fn_hint)) then
       if (len(tctx%fn_hint) > 0) own = tctx%fn_hint
    end if
    tctx%fn_hint = ""
    if (name%tag == GCT_SYM) call gc_ref_text(name%ref, s=own)
    saved = ""
    if (allocated(tctx%fn_path)) saved = tctx%fn_path
    outer = saved
    if (len(outer) == 0) call gcn_name(gcn_current([vs_get(vst, base + 1), vs_get(vst, base + 4)]), s=outer)
    tctx%fn_path = outer // "/" // own
    fsc = new_fn_scope(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call vs_set(vst, base + 5, fsc)
    self_slot = -1
    if (name%tag == GCT_SYM) then
       self_slot = declare_local(vs_get(vst, base + 5), vs_get(vst, base + 4), [vs_get(vst, base + 1)])
       call gc_set_i2(scope_info(vs_get(vst, base + 5)), self_slot)
    end if

    ! One arity or several: (fn* [..] ..) versus (fn* ([..] ..) ...)
    head = strip_meta(gcl_first(vs_get(vst, base + 3)))
    if (gcv_is(head)) then
       ! single arity: the whole rest is the one clause
       call vs_set(vst, base + 6, gcl_cons(vs_get(vst, base + 3), gcl_empty([vs_get(vst, base + 3)]), [vs_get(vst, base + 3)]))
    else
       call vs_set(vst, base + 6, vs_get(vst, base + 3))
    end if
    arities = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 5), vs_get(vst, base + 6)])
    call vs_set(vst, base + 7, arities)
    walk = vs_get(vst, base + 6)
    call vs_set(vst, base + 8, walk)
    do while (gcl_count(vs_get(vst, base + 8)) > 0)
       clause = norm_form(strip_meta(gcl_first(vs_get(vst, base + 8))), [vs_get(vst, base + 7), vs_get(vst, base + 8)])
       ar = analyze_arity(clause, vs_get(vst, base + 5), hints)
       if (tctx%has_error) then
          tctx%fn_path = saved
          call vs_leave(vst, base)
          return
       end if
       ! FnExpr.parse, after each method: one variadic, each fixed arity
       ! once (model/anlocal.lisp anl-arity)
       block
         integer(int64) :: code
         call anl_arity(anl_ls(), int(gc_i2(vs_get(vst, base + 5)), int64), int(int_of(gcv_nth(ar, 0)), int64), &
              merge(1_int64, 0_int64, truthy(gcv_nth(ar, 1))), code)
         if (code /= 0) then
            call anl_refuse(code, gc_nil(), .false.)
            tctx%fn_path = saved
            call vs_leave(vst, base)
            return
         end if
       end block
       arities = gcv_conj(vs_get(vst, base + 7), ar, [vs_get(vst, base + 1), vs_get(vst, base + 5), ar])
       call vs_set(vst, base + 7, arities)
       walk = gcl_rest(vs_get(vst, base + 8), [vs_get(vst, base + 7)])
       call vs_set(vst, base + 8, walk)
    end do

    if (anl_arity_end(anl_ls(), int(gc_i2(vs_get(vst, base + 5)), int64)) /= 0) then
       call anl_refuse(12_int64, gc_nil(), .false.)
       tctx%fn_path = saved
       call vs_leave(vst, base)
       return
    end if

    ! every recur in tail position of its target (the tail check), then
    ! locals clearing, per arity, now that the frame size is known
    do i = 0, gcv_count(vs_get(vst, base + 7)) - 1
       if (.not. tail_ok(gcv_nth(gcv_nth(vs_get(vst, base + 7), i), 3), 1)) then
          tctx%fn_path = saved
          call vs_leave(vst, base)
          return
       end if
       if (.not. recur_count_ok()) then
          tctx%fn_path = saved
          call vs_leave(vst, base)
          return
       end if
    end do
    call vs_set(vst, base + 9, scope_caps(vs_get(vst, base + 5), [vs_get(vst, base + 1), vs_get(vst, base + 7)]))
    do i = 0, gcv_count(vs_get(vst, base + 7)) - 1
       call apply_clears(gcv_nth(gcv_nth(vs_get(vst, base + 7), i), 3), scope_nslots(vs_get(vst, base + 5)))
    end do

    ! with CLOTRAN_VM=1, the fn one function of the generated VM's program
    ! where it can run every arity (vm.inc): each arity's body then an
    ! N_VMB naming its clause, the function's constants kept alive by it
    vmfid = -1
    if (vm_enabled()) then
       block
         type(gc_value) :: consts, nm
         nm = gc_str(tctx%fn_path, [vs_get(vst, base + 5), vs_get(vst, base + 7)])
         call vs_set(vst, base + 8, nm)
         vmfid = vm_compile_fn(vs_get(vst, base + 7), scope_nslots(vs_get(vst, base + 5)), &
              vs_get(vst, base + 9), self_slot, vs_get(vst, base + 8), vmci, consts, &
              [vs_get(vst, base + 5), vs_get(vst, base + 7), vs_get(vst, base + 8)])
         if (vmfid >= 0) then
            call vs_set(vst, base + 6, consts)
            do i = 0, gcv_count(vs_get(vst, base + 7)) - 1
               block
                 type(gc_value) :: info, nd2, ar0, ar2
                 integer :: nl
                 ar0 = gcv_nth(vs_get(vst, base + 7), i)
                 nl = int_of(gcv_nth(ar0, 0))
                 if (truthy(gcv_nth(ar0, 1))) nl = nl + 1
                 info = int_vec([int_of(gcv_nth(ar0, 2)), nl], [vs_get(vst, base + 5), vs_get(vst, base + 6), vs_get(vst, base + 7)])
                 call vs_set(vst, base + 8, info)
                 nd2 = mk_node(N_VMB, gc_nil(), vs_get(vst, base + 6), vs_get(vst, base + 8), vmci + i, &
                      [vs_get(vst, base + 5), vs_get(vst, base + 7)])
                 call gc_set_slot(nd2, 4, gc_slot(gcv_nth(gcv_nth(vs_get(vst, base + 7), i), 3), 4))
                 call gc_set_slot(nd2, 5, gcv_nth(gcv_nth(vs_get(vst, base + 7), i), 3))
                 call vs_set(vst, base + 8, nd2)
                 ar2 = gcv_conj(gcv_nth(vs_get(vst, base + 7), i), vs_get(vst, base + 8), [vs_get(vst, base + 5), vs_get(vst, base + 7)])
                 call vs_set(vst, base + 8, ar2)
                 arities = gcv_assoc(vs_get(vst, base + 7), i, vs_get(vst, base + 8), [vs_get(vst, base + 5)])
                 call vs_set(vst, base + 7, arities)
               end block
            end do
            call vs_set(vst, base + 6, gc_nil())
         end if
       end block
    end if

    ! the flat form of each arity, beside its tree (flat.inc); its
    ! temporaries widen the frame past the named slots
    nflat = 0
    do i = 0, gcv_count(vs_get(vst, base + 7)) - 1
       if (vmfid >= 0) exit
       block
         type(gc_value) :: fl, ar2
         integer :: nt
         nt = 0
         fl = flat_compile(gcv_nth(vs_get(vst, base + 7), i), scope_nslots(vs_get(vst, base + 5)), nt, &
              [vs_get(vst, base + 5), vs_get(vst, base + 7)])
         if (fl%tag /= GCT_NIL) then
            call vs_set(vst, base + 8, fl)
            ar2 = gcv_conj(gcv_nth(vs_get(vst, base + 7), i), vs_get(vst, base + 8), [vs_get(vst, base + 5), vs_get(vst, base + 7)])
            call vs_set(vst, base + 8, ar2)
            arities = gcv_assoc(vs_get(vst, base + 7), i, vs_get(vst, base + 8), [vs_get(vst, base + 5)])
            call vs_set(vst, base + 7, arities)
            nflat = max(nflat, nt)
         end if
       end block
    end do

    ! [name arities captures nslots selfslot slotnames]
    tmpl = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 5), vs_get(vst, base + 7)])
    call vs_set(vst, base + 8, tmpl)
    tmpl = gcv_conj(vs_get(vst, base + 8), vs_get(vst, base + 4), [vs_get(vst, base + 5), vs_get(vst, base + 7)])
    call vs_set(vst, base + 8, tmpl)
    tmpl = gcv_conj(vs_get(vst, base + 8), vs_get(vst, base + 7), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 8, tmpl)
    tmpl = gcv_conj(vs_get(vst, base + 8), vs_get(vst, base + 9), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 8, tmpl)
    tmpl = gcv_conj(vs_get(vst, base + 8), gc_int(scope_nslots(vs_get(vst, base + 5)) + nflat), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 8, tmpl)
    tmpl = gcv_conj(vs_get(vst, base + 8), gc_int(self_slot), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 8, tmpl)
    ! slot -> name, for the debugger; an empty map when the fn has no
    ! named locals at all
    block
      type(gc_value) :: nm
      nm = scope_slot_names(vs_get(vst, base + 5), [vs_get(vst, base + 8)])
      if (.not. gca_is(nm)) nm = gca_empty([vs_get(vst, base + 5), vs_get(vst, base + 8)])
      tmpl = gcv_conj(vs_get(vst, base + 8), nm, [vs_get(vst, base + 5)])
      call vs_set(vst, base + 8, tmpl)
    end block
    ! the builtin this fn only wraps, or nil (wrapper_builtin)
    block
      type(gc_value) :: wb
      wb = wrapper_builtin(vs_get(vst, base + 7), vs_get(vst, base + 9))
      tmpl = gcv_conj(vs_get(vst, base + 8), wb, [vs_get(vst, base + 5), wb])
      call vs_set(vst, base + 8, tmpl)
    end block
    ! and what a call reads, as one raw vector (flat.inc call_table)
    block
      type(gc_value) :: ct
      ct = call_table(vs_get(vst, base + 8), vmfid, [vs_get(vst, base + 5)])
      tmpl = gcv_conj(vs_get(vst, base + 8), ct, [vs_get(vst, base + 5), ct])
      call vs_set(vst, base + 8, tmpl)
    end block
    ! and the display name, for frames and traces (fn_display)
    call vs_set(vst, base + 6, gc_str(tctx%fn_path, [vs_get(vst, base + 5), vs_get(vst, base + 8)]))
    tmpl = gcv_conj(vs_get(vst, base + 8), vs_get(vst, base + 6), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 8, tmpl)
    ! and the generated VM's function id, or -1 (vm.inc; VmRuntime rt_clop)
    tmpl = gcv_conj(vs_get(vst, base + 8), gc_int(int(vmfid, gc_ip)), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 8, tmpl)
    tctx%fn_path = saved
    nd = mk_node(N_FN, gc_nil(), vs_get(vst, base + 8), gc_nil(), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_fn

  ! ([params] body...) -> [nfixed variadic? first-slot body]
  ! A hint's primitive kind: 1 long, 2 double, -1 a primitive Clojure
  ! refuses on a fn (int, float, ...), 0 anything else -- no hint, a
  ! class, an array type.
  integer function prim_hint_kind(v)
    type(gc_value), intent(in) :: v
    type(gc_value) :: md, tg
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    prim_hint_kind = 0
    if (gc_kind(v) /= OBJ_META) return
    md = gc_slot(v, 2)
    if (.not. gca_is(md)) return
    tg = strip_meta(gca_get(md, gc_key("tag", [v, md])))
    if (tg%tag /= GCT_SYM) return
    block
       call gc_ref_text(tg%ref, s=dlt_1)
    select case (dlt_1)
    case ("long");   prim_hint_kind = 1
    case ("double"); prim_hint_kind = 2
    case ("int", "float", "short", "byte", "char", "boolean"); prim_hint_kind = -1
    end select
    end block
  end function prim_hint_kind

  ! Clojure's PRIMITIVE HINTS on a fn, as a rewrite of its body.
  !
  ! A ^long or ^double parameter is CONVERTED on the way in, by RT's
  ! longCast and doubleCast -- (fn [^long n] n) given 1.5 answers 1,
  ! and given "a" throws ClassCastException -- and a ^long or ^double
  ! on the parameter VECTOR converts what the fn returns. clotran used
  ! to ignore both, so a wrong argument quietly gave a non-Clojure
  ! answer. Clj does this in the method it emits; here it is
  !
  !   (fn [^long n acc] body)         (let* [n (long n)] body)
  !   (fn ^long [^long n acc] body)   (long (loop* [n (long n) acc acc] body))
  !
  ! The return case needs the loop so that a recur in body stays in
  ! tail position and still targets the whole arity. With no return
  ! hint a let is enough: a recur rebinds the parameters and the body,
  ! let and all, runs again and converts again.
  !
  ! And the forms Clojure refuses, refused the same way: more than four
  ! primitive parameters, a variadic primitive fn, and a hint of a
  ! primitive other than long or double.
  !
  ! `enabled` is false for a deftype or reify METHOD, whose parameters
  ! take their types from the interface and may be ^int, or number
  ! more than four.
  recursive function prim_hint_body(rawparams, params, nfixed, variadic, body, enabled, roots) result(out)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: rawparams, params, body
    integer, intent(in) :: nfixed
    logical, intent(in) :: variadic, enabled
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, bindings, x, form
    integer :: kinds(max(nfixed, 1)), ret, i, base
    logical :: any_prim

    vst => gc_my_stack()
    out = body
    if (.not. enabled) return
    any_prim = .false.
    do i = 0, nfixed - 1
       kinds(i + 1) = prim_hint_kind(gcv_nth(params, i))
       if (kinds(i + 1) < 0) then
          call raise_class("clotran.host.illegal_argument_exception", "Only long and double primitives are supported", roots)
          return
       end if
       if (kinds(i + 1) > 0) any_prim = .true.
    end do
    ret = prim_hint_kind(rawparams)
    if (ret < 0) ret = 0
    if (.not. any_prim .and. ret == 0) return
    if (variadic) then
       call raise_class("clotran.host.runtime_exception", "fns taking primitives cannot be variadic", roots)
       return
    end if
    if (nfixed > 4) then
       call raise_class("clotran.host.illegal_argument_exception", "fns taking primitives support only 4 or fewer args", roots)
       return
    end if

    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, body)
    bindings = gcv_empty([roots, [vs_get(vst, base + 1)]])
    call vs_set(vst, base + 2, bindings)
    do i = 0, nfixed - 1
       ! a let binds only what converts; a loop has to bind every
       ! parameter, since recur's arity is the loop's
       if (kinds(i + 1) == 0 .and. ret == 0) cycle
       x = strip_meta(gcv_nth(params, i))
       call vs_set(vst, base + 3, x)
       bindings = gcv_conj(vs_get(vst, base + 2), vs_get(vst, base + 3), [roots, [vs_get(vst, base + 2), vs_get(vst, base + 3)]])
       call vs_set(vst, base + 2, bindings)
       if (kinds(i + 1) == 0) then
          x = vs_get(vst, base + 3)
       else
          x = gcl_cons(vs_get(vst, base + 3), gcl_empty([roots, [vs_get(vst, base + 2), vs_get(vst, base + 3)]]), &
               [roots, [vs_get(vst, base + 2), vs_get(vst, base + 3)]])
          call vs_set(vst, base + 4, x)
          x = gcl_cons(cast_fn(kinds(i + 1), [roots, [vs_get(vst, base + 2), vs_get(vst, base + 4)]]), &
               vs_get(vst, base + 4), [roots, [vs_get(vst, base + 2), vs_get(vst, base + 4)]])
       end if
       call vs_set(vst, base + 4, x)
       bindings = gcv_conj(vs_get(vst, base + 2), vs_get(vst, base + 4), [roots, [vs_get(vst, base + 2), vs_get(vst, base + 4)]])
       call vs_set(vst, base + 2, bindings)
    end do
    ! (let* bindings . body) or (loop* bindings . body)
    form = gcl_cons(vs_get(vst, base + 2), vs_get(vst, base + 1), [roots, [vs_get(vst, base + 1), vs_get(vst, base + 2)]])
    call vs_set(vst, base + 5, form)
    if (ret /= 0) then
       x = gc_sym("loop*", [roots, [vs_get(vst, base + 5)]])
    else
       x = gc_sym("let*", [roots, [vs_get(vst, base + 5)]])
    end if
    form = gcl_cons(x, vs_get(vst, base + 5), [roots, [vs_get(vst, base + 5)]])
    call vs_set(vst, base + 5, form)
    if (ret /= 0) then
       ! (cast (loop* ...))
       form = gcl_cons(vs_get(vst, base + 5), gcl_empty([roots, [vs_get(vst, base + 5)]]), [roots, [vs_get(vst, base + 5)]])
       call vs_set(vst, base + 5, form)
       form = gcl_cons(cast_fn(ret, [roots, [vs_get(vst, base + 5)]]), vs_get(vst, base + 5), [roots, [vs_get(vst, base + 5)]])
       call vs_set(vst, base + 5, form)
    end if
    ! the new body is that one form
    out = gcl_cons(vs_get(vst, base + 5), gcl_empty([roots, [vs_get(vst, base + 5)]]), [roots, [vs_get(vst, base + 5)]])
    call vs_leave(vst, base)
  end function prim_hint_body

  ! The cast a primitive hint means, as the function itself -- not the
  ! name `long`, which a program may shadow or which may not be defined
  ! yet while core.clj is loading.
  function cast_fn(kind, roots) result(f)
    integer, intent(in) :: kind
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: f, nsv, v
    if (kind == 1) then
       ! under *unchecked-math* when the fn is analysed, RT's
       ! uncheckedLongCast, as Compiler.emitUnboxArg chooses
       nsv = gcn_find("clojure.core")
       v = gc_nil()
       if (gc_kind(nsv) == OBJ_NS) v = gcn_var_value(gcn_lookup(nsv, gc_sym("*unchecked-math*", [roots, nsv])))
       if (v%tag /= GCT_NIL .and. .not. (v%tag == GCT_BOOL .and. v%ival == 0)) then
          f = native(B_LONGCAST, "unchecked-long", roots)
       else
          f = native(B_NUMLONG, "long", roots)
       end if
    else
       f = native(B_DBLCAST, "double", roots)
    end if
  end function cast_fn

  recursive function analyze_arity(clause, fsc, hints) result(ar)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: clause, fsc
    logical, intent(in) :: hints
    type(gc_value) :: ar, params, blk, p, body, rinfo
    integer :: base, i, n, amp, start, nfixed
    logical :: variadic

    tctx => ctx_self()
    vst => tctx%stk
    ar = gc_nil()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, clause)
    call vs_set(vst, base + 2, fsc)
    params = strip_meta(gcl_first(clause))
    if (.not. gcv_is(params)) then
       call fail("fn* needs a parameter vector")
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 3, params)
    ! FnMethod.parse's walk (model/anlocal.lisp anl-params): the required
    ! parameters, then & and at most one rest parameter
    if (anl_params(params, 0_int64) /= 0) then
       call anl_refuse(anl_params(params, 0_int64), frm_nth(params, anl_params(params, 1_int64)), .false.)
       call vs_leave(vst, base)
       return
    end if
    n = gcv_count(params)
    nfixed = int(anl_params(params, 2_int64))
    variadic = (anl_params(params, 3_int64) == 1)
    amp = nfixed
    blk = child_scope(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, blk)
    start = reserve_slots(vs_get(vst, base + 4), merge(nfixed + 1, nfixed, variadic))
    do i = 0, nfixed - 1
       p = strip_meta(gcv_nth(vs_get(vst, base + 3), i))
       call bind_name(vs_get(vst, base + 4), p, start + i, [vs_get(vst, base + 1)])
       call bind_array_hint(vs_get(vst, base + 4), p, gcv_nth(vs_get(vst, base + 3), i), [vs_get(vst, base + 1)])
    end do
    if (variadic) then
       p = strip_meta(gcv_nth(vs_get(vst, base + 3), amp + 1))
       call bind_name(vs_get(vst, base + 4), p, start + nfixed, [vs_get(vst, base + 1)])
    end if
    ! The body is a recur target: kind 1 fixed, 2 variadic.
    rinfo = int_vec([merge(2, 1, variadic), start, merge(nfixed + 1, nfixed, variadic)], &
         [vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call gc_set_slot(vs_get(vst, base + 4), 4, rinfo)
    if (hints) call note_arg_kinds(vs_get(vst, base + 1), vs_get(vst, base + 3), nfixed, variadic, &
         vs_get(vst, base + 4), start, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    body = prim_hint_body(gcl_first(vs_get(vst, base + 1)), vs_get(vst, base + 3), nfixed, variadic, &
         gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)]), hints, &
         [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3), vs_get(vst, base + 4)])
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 5, body)
    body = analyze_body(vs_get(vst, base + 5), vs_get(vst, base + 4), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 5)])
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 5, body)
    ! a recur argument that did not match (recur_args_ok), as emitting
    ! the arity finds it
    block
      type(gc_value) :: re
      character(len=:), allocatable :: rm
      re = gca_get_or_nil(gc_slot(vs_get(vst, base + 4), 5), "clotran/recur-error")
      if (re%tag == GCT_STR) then
         call gc_ref_text(re%ref, s=rm)
         call raise_class("clotran.host.illegal_argument_exception", rm, [vs_get(vst, base + 1)])
         call vs_leave(vst, base)
         return
      end if
    end block
    ar = gcv_empty([vs_get(vst, base + 5)])
    ar = gcv_conj(ar, gc_int(nfixed), [vs_get(vst, base + 5), ar])
    ar = gcv_conj(ar, gc_bool(variadic), [vs_get(vst, base + 5), ar])
    ar = gcv_conj(ar, gc_int(start), [vs_get(vst, base + 5), ar])
    ar = gcv_conj(ar, vs_get(vst, base + 5), [vs_get(vst, base + 5), ar])
    call vs_leave(vst, base)
  end function analyze_arity

  ! (recur args...) -> the nearest loop or fn. Slot 2 = [kind start n].
  recursive function analyze_recur(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, kids, rinfo, m, tmp
    integer :: base, n, want, i
    logical :: method, bad
    character(len=16) :: wb, gb
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    rinfo = gc_slot(sc, 4)
    if (.not. gcv_is(rinfo)) then
       call fail("Can only recur from tail position of a loop or fn")
       call vs_leave(vst, base)
       return
    end if
    n = int_of(gcv_nth(rinfo, 2))
    ! a recur to a deftype or reify METHOD leaves out `this`, which is
    ! supplied as clj supplies it (DEVIATIONS 19 resolved): the method is
    ! the fn whose info carries a field table (clotran-fields*), and its
    ! first parameter is passed through unchanged
    method = .false.
    want = n
    if (int_of(gcv_nth(rinfo, 0)) /= 0) then
       m = gc_slot(scope_info(sc), 5)
       if (gca_is(m)) then
          method = .true.
          want = n - 1
       end if
    end if
    bad = (gcl_count(rest) /= want)
    if (bad .and. .not. allocated(tctx%recur_pend)) then
       write(wb, '(I0)') want
       write(gb, '(I0)') gcl_count(rest)
       tctx%recur_pend = "Mismatched argument count to recur, expected: " // trim(wb) // " args, got: " // trim(gb)
    end if
    kids = analyze_all(vs_get(vst, base + 1), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, kids)
    if (.not. tctx%has_error .and. .not. method .and. .not. bad) then
       if (.not. recur_args_ok(vs_get(vst, base + 2), vs_get(vst, base + 3), [vs_get(vst, base + 1)])) then
          call vs_leave(vst, base)
          return
       end if
    end if
    if (method .and. .not. bad .and. .not. tctx%has_error) then
       ! [this args...]: the local in the method's first parameter slot
       m = gc_slot(scope_info(vs_get(vst, base + 2)), 5)
       tmp = mk_node(N_LOCAL, gc_nil(), gca_get(m, gc_key("this", [vs_get(vst, base + 1)])), gc_nil(), &
            int_of(gcv_nth(gc_slot(vs_get(vst, base + 2), 4), 1)), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
       call vs_set(vst, base + 4, tmp)
       tmp = gcv_empty([vs_get(vst, base + 3), vs_get(vst, base + 4)])
       call vs_set(vst, base + 5, tmp)
       tmp = gcv_conj(vs_get(vst, base + 5), vs_get(vst, base + 4), [vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 5)])
       call vs_set(vst, base + 5, tmp)
       do i = 0, gcv_count(vs_get(vst, base + 3)) - 1
          tmp = gcv_conj(vs_get(vst, base + 5), gcv_nth(vs_get(vst, base + 3), i), [vs_get(vst, base + 3), vs_get(vst, base + 5)])
          call vs_set(vst, base + 5, tmp)
       end do
       call vs_set(vst, base + 3, vs_get(vst, base + 5))
    end if
    if (.not. tctx%has_error) nd = mk_node(N_RECUR, vs_get(vst, base + 3), gc_slot(vs_get(vst, base + 2), 4), gc_nil(), n, &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_recur

  ! ns/name as an unbound Var in ns, created if need be; nil for a bare
  ! name, which has no namespace to be unbound in.
  function intern_unbound(sym, roots) result(var)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: sym
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: var, ns, nm
    character(len=:), allocatable :: t
    integer :: sl, base
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    var = gc_nil()
    block
       call gc_ref_text(sym%ref, s=dlt_1)
       t = dlt_1
    end block
    sl = sym_slash(t)
    if (sl <= 1 .or. sl >= len(t)) return
    base = vs_enter(vst, 2)
    ns = gcn_find(t(1:sl-1))
    if (gc_kind(ns) /= OBJ_NS) then
       ! a namespace made HERE stands for a skipped library: marked, so
       ! that (var ns/x) keeps interning into it and refuses a real one
       ns = gcn_find_or_create(t(1:sl-1), roots)
       call vs_set(vst, base + 1, ns)
       call vs_set(vst, base + 2, gca_empty([roots, vs_get(vst, base + 1)]))
       call vs_set(vst, base + 2, gca_assoc(vs_get(vst, base + 2), gc_key("clotran/placeholder", [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)]), &
            gc_bool(.true.), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)]))
       call gc_set_slot(vs_get(vst, base + 1), 4, vs_get(vst, base + 2))
    end if
    call vs_set(vst, base + 1, ns)
    nm = gc_sym(t(sl+1:), [roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, nm)
    var = gcn_lookup(vs_get(vst, base + 1), vs_get(vst, base + 2))
    if (.not. gcn_is_var(var)) then
       var = gcn_intern(vs_get(vst, base + 1), vs_get(vst, base + 2), gc_nil(), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
       call gc_set_i1(var, 0)
    end if
    call vs_leave(vst, base)
  end function intern_unbound

  ! (var sym) -> the Var itself, resolved now.
  recursive function analyze_varq(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, sym, var
    integer :: base
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    nd = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    sym = strip_meta(gcl_first(rest))
    if (sym%tag /= GCT_SYM) then
       call fail("var needs a symbol")
       call vs_leave(vst, base)
       return
    end if
    var = resolve_var(sym, gc_nil())
    if (.not. gcn_is_var(var)) then
       ! ... but a namespace that EXISTS and has no such var is
       ! Compiler.lookupVar's error: #'user/x from another namespace
       ! must not create user/x. A namespace that does not exist is the
       ! skipped-library case below.
       block
          integer :: slash
          type(gc_value) :: nsv
          call gc_ref_text(sym%ref, s=dlt_1)
          slash = sym_slash(dlt_1)
          if (slash > 1 .and. slash < len(dlt_1)) then
             nsv = gcn_find(dlt_1(1:slash - 1))
             if (gc_kind(nsv) == OBJ_NS) then
                if (gca_is(gc_slot(nsv, 4))) then
                   ! a placeholder for a skipped library (intern_unbound): not real
                   if (truthy(gca_get(gc_slot(nsv, 4), gc_key("clotran/placeholder", [nsv])))) nsv = gc_nil()
                end if
             end if
             if (gc_kind(nsv) == OBJ_NS) then
                ! the namespace's own interns, private ones included:
                ! #'clojure.uuid/default-uuid-reader is a defn-
                var = gca_get(gc_slot(nsv, 2), gc_sym(dlt_1(slash + 1:), [vs_get(vst, base + 1), vs_get(vst, base + 2)]))
                if (.not. gcn_is_var(var)) then
                   call fail("Unable to resolve var: " // dlt_1 // " in this context")
                   call vs_leave(vst, base)
                   return
                end if
             end if
          end if
       end block
       ! A QUALIFIED name that does not resolve is interned unbound, in
       ! its namespace, created if need be -- the var-quote's half of
       ! deviation 32. core.clj's default-data-readers holds
       ! #'clojure.uuid/default-uuid-reader, and clojure.uuid is a
       ! skipped library: the map loads, and only reading a #uuid
       ! literal fails.
       ! ... and only there: a user's #'nosuch/x is clj's refusal (DEVIATIONS 32)
       if (.not. gcn_is_var(var) .and. .not. defers_late_vars()) then
          call gc_ref_text(sym%ref, s=dlt_1)
          call fail("Unable to resolve var: " // dlt_1 // " in this context")
          call vs_leave(vst, base)
          return
       end if
       if (.not. gcn_is_var(var)) var = intern_unbound(sym, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
       if (.not. gcn_is_var(var)) then
          block
             call gc_ref_text(sym%ref, s=dlt_1)
             call fail("Unable to resolve var: " // dlt_1)
          end block
          call vs_leave(vst, base)
          return
       end if
    end if
    call vs_set(vst, base + 3, var)
    nd = const_node(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_varq

  ! (lazy-seq* body...) -> a no-argument fn whose closure becomes the
  ! thunk of a pending lazy seq.
  recursive function analyze_lazy(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, fnform, fnode
    integer :: base
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    ! ([] body...) as the single clause of a fn*
    fnform = gcl_cons(gcv_empty([vs_get(vst, base + 1)]), vs_get(vst, base + 1), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, fnform)
    fnode = analyze_fn(vs_get(vst, base + 3), vs_get(vst, base + 2))
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 4, fnode)
    nd = mk_node(N_LAZY, gc_nil(), gc_slot(vs_get(vst, base + 4), 2), gc_nil(), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_lazy

  ! (try body* (catch C e h*)* (finally f*)?), walked a clause at a time as
  ! TryExpr.Parser walks it: the generated anf_try_step says what each clause
  ! is and what is refused (model/anform.lisp), the body is analysed when the
  ! first catch or finally is reached, anf_catch checks a catch's class and
  ! name. Children: [body, finally or nil]; slot 2 the catches, each
  ! [class, slot, handler].
  recursive function analyze_try(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, body, fin, catches, item, cl, blk, cb, kids, cname
    integer :: base, i, n, slot
    integer(int64) :: st, act, code, lastp
    logical :: body_done

    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 8)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    n = gcl_count(rest)
    catches = gcv_empty([vs_get(vst, base + 1)])
    call vs_set(vst, base + 5, catches)
    call vs_set(vst, base + 6, gc_nil())
    st = 0
    body_done = .false.
    do i = 0, n - 1
       item = norm_form(nth_of(vs_get(vst, base + 1), i), [vs_get(vst, base + 1), vs_get(vst, base + 5), vs_get(vst, base + 6)])
       call vs_set(vst, base + 4, item)
       lastp = merge(1_int64, 0_int64, i == n - 1)
       act = anf_try_step(st, vs_get(vst, base + 4), lastp, 1_int64)
       code = anf_try_step(st, vs_get(vst, base + 4), lastp, 0_int64)
       st = anf_try_step(st, vs_get(vst, base + 4), lastp, 2_int64)
       if (act /= 0 .and. .not. body_done) then
          if (.not. analyze_try_body(i)) return
          body_done = .true.
       end if
       if (code /= 0) then
          call anf_refuse(code, vs_get(vst, base + 4))
          call vs_leave(vst, base)
          return
       end if
       if (act == 1) then
          code = anf_catch(vs_get(vst, base + 4))
          if (code == 33) then
             call anf_refuse(code, frf_nth(vs_get(vst, base + 4), 1_int64))
          else if (code /= 0) then
             call anl_refuse(code, frf_nth(vs_get(vst, base + 4), 2_int64), .true.)
          end if
          if (code /= 0) then
             call vs_leave(vst, base)
             return
          end if
          cname = strip_meta(frf_nth(vs_get(vst, base + 4), 1_int64))
          call vs_set(vst, base + 7, cname)
          blk = child_scope(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 5), vs_get(vst, base + 7)])
          call vs_set(vst, base + 8, blk)
          slot = declare_local(vs_get(vst, base + 8), strip_meta(frf_nth(vs_get(vst, base + 4), 2_int64)), [vs_get(vst, base + 1)])
          cb = analyze_body(gcl_rest(gcl_rest(gcl_rest(vs_get(vst, base + 4), [vs_get(vst, base + 1)]), &
               [vs_get(vst, base + 1)]), [vs_get(vst, base + 1)]), vs_get(vst, base + 8), [vs_get(vst, base + 1), vs_get(vst, base + 5)])
          if (tctx%has_error) then
             call vs_leave(vst, base)
             return
          end if
          call vs_set(vst, base + 8, cb)
          cl = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 5), vs_get(vst, base + 7), vs_get(vst, base + 8)])
          cl = gcv_conj(cl, vs_get(vst, base + 7), [vs_get(vst, base + 5), vs_get(vst, base + 8), cl])
          cl = gcv_conj(cl, gc_int(slot), [vs_get(vst, base + 5), vs_get(vst, base + 8), cl])
          cl = gcv_conj(cl, vs_get(vst, base + 8), [vs_get(vst, base + 5), cl])
          catches = gcv_conj(vs_get(vst, base + 5), cl, [vs_get(vst, base + 1), cl])
          call vs_set(vst, base + 5, catches)
       else if (act == 2) then
          fin = analyze_body(gcl_rest(vs_get(vst, base + 4), [vs_get(vst, base + 1)]), vs_get(vst, base + 2), &
               [vs_get(vst, base + 1), vs_get(vst, base + 5)])
          if (tctx%has_error) then
             call vs_leave(vst, base)
             return
          end if
          call vs_set(vst, base + 6, fin)
       end if
    end do
    if (.not. body_done) then
       if (.not. analyze_try_body(n)) return
    end if
    kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 5), vs_get(vst, base + 6)])
    kids = gcv_conj(kids, vs_get(vst, base + 3), [vs_get(vst, base + 5), vs_get(vst, base + 6), kids])
    kids = gcv_conj(kids, vs_get(vst, base + 6), [vs_get(vst, base + 5), kids])
    call vs_set(vst, base + 7, kids)
    nd = mk_node(N_TRY, vs_get(vst, base + 7), vs_get(vst, base + 5), gc_nil(), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  contains
    ! the body: the forms before clause k, analysed into slot 3; false (the
    ! frame left) on an error
    logical function analyze_try_body(k) result(ok)
      integer, intent(in) :: k
      integer :: j
      body = gcl_empty([vs_get(vst, base + 1)])
      call vs_set(vst, base + 3, body)
      do j = k - 1, 0, -1
         body = gcl_cons(nth_of(vs_get(vst, base + 1), j), vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
         call vs_set(vst, base + 3, body)
      end do
      body = analyze_body(vs_get(vst, base + 3), vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 5)])
      ok = .not. tctx%has_error
      if (.not. ok) then
         call vs_leave(vst, base)
         return
      end if
      call vs_set(vst, base + 3, body)
    end function analyze_try_body
  end function analyze_try

  ! (case* expr shift mask default map table-type test-type skip-check?)
  ! Children: [expr, default]; slot 2 = the map with each [test then]
  ! rebuilt as [test then-node]; slot 3 = [shift mask test-type skip].
  recursive function analyze_case(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, kids, c, tbl, entry, ent2, mp, tn, info, skip
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i, n

    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 8)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    n = gcl_count(rest)
    if (n < 7) then
       call fail("case* needs 7 or 8 forms")
       call vs_leave(vst, base)
       return
    end if
    kids = gcv_empty([vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, kids)
    c = analyze(nth_of(vs_get(vst, base + 1), 0), vs_get(vst, base + 2))
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    kids = gcv_conj(vs_get(vst, base + 3), c, [vs_get(vst, base + 1), c])
    call vs_set(vst, base + 3, kids)
    c = analyze(nth_of(vs_get(vst, base + 1), 3), vs_get(vst, base + 2))
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    kids = gcv_conj(vs_get(vst, base + 3), c, [vs_get(vst, base + 1), c])
    call vs_set(vst, base + 3, kids)

    tbl = strip_meta(nth_of(vs_get(vst, base + 1), 4))
    call vs_set(vst, base + 4, tbl)
    mp = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)])
    call vs_set(vst, base + 5, mp)
    call gca_entries(vs_get(vst, base + 4), ks, vls)
    do i = 1, size(ks)
       entry = strip_meta(vls(i))
       call vs_set(vst, base + 6, entry)
       if (.not. (gcv_is(entry) .and. gcv_count(entry) == 2)) cycle
       tn = analyze(gcv_nth(vs_get(vst, base + 6), 1), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 7, tn)
       ent2 = gcv_empty([vs_get(vst, base + 5), vs_get(vst, base + 6), vs_get(vst, base + 7)])
       ent2 = gcv_conj(ent2, gcv_nth(vs_get(vst, base + 6), 0), [vs_get(vst, base + 5), vs_get(vst, base + 7), ent2])
       ent2 = gcv_conj(ent2, vs_get(vst, base + 7), [vs_get(vst, base + 5), ent2])
       call vs_set(vst, base + 8, ent2)
       mp = gca_assoc(vs_get(vst, base + 5), ks(i), vs_get(vst, base + 8), [vs_get(vst, base + 1), vs_get(vst, base + 5), vs_get(vst, base + 8)])
       call vs_set(vst, base + 5, mp)
    end do
    skip = gc_nil()
    if (n >= 8) skip = strip_meta(nth_of(vs_get(vst, base + 1), 7))
    call vs_set(vst, base + 6, skip)
    info = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 5), vs_get(vst, base + 6)])
    info = gcv_conj(info, gc_int(ival_of(nth_of(vs_get(vst, base + 1), 1))), [vs_get(vst, base + 5), vs_get(vst, base + 6), info])
    info = gcv_conj(info, gc_int(ival_of(nth_of(vs_get(vst, base + 1), 2))), [vs_get(vst, base + 5), vs_get(vst, base + 6), info])
    info = gcv_conj(info, strip_meta(nth_of(vs_get(vst, base + 1), 6)), [vs_get(vst, base + 5), vs_get(vst, base + 6), info])
    info = gcv_conj(info, vs_get(vst, base + 6), [vs_get(vst, base + 5), info])
    call vs_set(vst, base + 7, info)
    nd = mk_node(N_CASE, vs_get(vst, base + 3), vs_get(vst, base + 5), vs_get(vst, base + 7), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_case

  ! (deftype* tagname classname [fields] :implements [ifaces] opts (method [this args] body)*)
  ! Slot 2 = spec [class-text fields ifaces names fn-nodes]; i2 = 0.
  recursive function analyze_deftype(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, w, cname, k, fields, ifaces, spec
    integer :: base
    character(len=:), allocatable :: cn
    logical :: stub

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    w = gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, w)
    cname = strip_meta(gcl_first(vs_get(vst, base + 3)))
    if (cname%tag /= GCT_SYM) then
       call fail("deftype* needs a class name")
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 4, cname)
    ! the class name is KNOWN from here (known_class_name): the forms
    ! after this deftype* in the same expansion name it in full
    block
       character(len=:), allocatable :: nsn, sn
       call gc_ref_text(cname%ref, s=cn)
       if (index(cn, ".") == 0) then
          call gcn_name(gcn_current([vs_get(vst, base + 1)]), s=nsn)
          cn = nsn // "." // cn
       end if
       call declare_type_name(cn)
       ! and by its short name inside its own methods only, as clj's
       ! compile stub is (Compiler.COMPILE_STUB_SYM, HostExpr.maybeClass):
       ! the (import ...) deftype expands to records it for what follows
       call canon_class(cn(index(cn, ".", back=.true.) + 1:), c=sn)
       stub = sn /= cn
       if (stub) call record_import(cn)
    end block
    w = gcl_rest(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call vs_set(vst, base + 3, w)
    fields = strip_meta(gcl_first(vs_get(vst, base + 3)))
    call vs_set(vst, base + 5, fields)
    w = gcl_rest(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 4), vs_get(vst, base + 5)])
    call vs_set(vst, base + 3, w)
    ifaces = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 5)])
    call vs_set(vst, base + 6, ifaces)
    do while (gcl_count(vs_get(vst, base + 3)) > 0)
       k = strip_meta(gcl_first(vs_get(vst, base + 3)))
       if (k%tag /= GCT_KEY) exit
       w = gcl_rest(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 6)])
       call vs_set(vst, base + 3, w)
       if (gc_ref_is(k%ref, "implements")) call vs_set(vst, base + 6, strip_meta(gcl_first(vs_get(vst, base + 3))))
       w = gcl_rest(vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 6)])
       call vs_set(vst, base + 3, w)
    end do
    if (.not. ifaces_known(vs_get(vst, base + 6))) then
       if (stub) call forget_import(cn)
       call vs_leave(vst, base)
       return
    end if
    block
       call class_of_text(vs_get(vst, base + 4), s=dlt_1)
       ! no enclosing local: a deftype is a class, not a closure, as
       ! NewInstanceExpr compiles its methods (reify is, below)
       spec = type_spec(dlt_1, vs_get(vst, base + 5), vs_get(vst, base + 6),  vs_get(vst, base + 3), gc_nil())
    end block
    if (stub) call forget_import(cn)
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 6, spec)
    nd = mk_node(N_DEFTYPE, gc_nil(), vs_get(vst, base + 6), gc_nil(), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_deftype

  ! (reify* [ifaces] (method [this args] body)*) and
  ! (proxy [supers] [ctor-args] (name [args] body)*): a nameless type,
  ! instantiated on the spot. i2 = 1.
  recursive function analyze_reify(rest, sc, is_proxy) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    logical, intent(in) :: is_proxy
    type(gc_value) :: nd, ifaces, methods, spec
    character(len=24) :: buf
    character(len=:), allocatable :: cname, who
    integer :: base

    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    ifaces = strip_meta(gcl_first(rest))
    call vs_set(vst, base + 3, ifaces)
    methods = gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, methods)
    if (is_proxy) then
       if (.not. gcv_is(vs_get(vst, base + 3))) then
          call fail("proxy needs a vector of superclasses")
          call vs_leave(vst, base)
          return
       end if
       methods = gcl_rest(vs_get(vst, base + 4), [vs_get(vst, base + 3), vs_get(vst, base + 4)])   ! past ctor args
       call vs_set(vst, base + 4, methods)
       methods = proxy_methods(vs_get(vst, base + 4), [vs_get(vst, base + 3)])
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 4, methods)
       write(buf, '(I0)') gc_next(proxy_id)
       buf = "clotran.proxy__" // trim(buf)
       cname = trim(buf)
    else
       if (.not. ifaces_known(vs_get(vst, base + 3))) then
          call vs_leave(vst, base)
          return
       end if
       ! named as clj's compiler names it, after the fn it is written in:
       ! clojure.core$future_call$reify__3, so pprint's map-ref-type calls
       ! a future a Future (a top-level one is user$reify__3)
       write(buf, '(I0)') gc_next(reify_id)
       who = ""
       if (allocated(tctx%fn_path)) who = tctx%fn_path
       if (len(who) == 0) call gcn_name(gcn_current([vs_get(vst, base + 1)]), s=who)
       call who_class_name(who // "/reify__" // trim(buf), cname)
       ! reify always implements IObj: the reify macro does not say so,
       ! NewInstanceExpr adds it, and its meta/withMeta are the
       ! instance's own slot (B_META, B_WITHMETA)
       if (gcv_is(vs_get(vst, base + 3))) then
          spec = gc_sym("clotran.host.i_obj", [vs_get(vst, base + 3)])
          call vs_set(vst, base + 6, spec)
          ifaces = gcv_conj(vs_get(vst, base + 3), vs_get(vst, base + 6), [vs_get(vst, base + 3), vs_get(vst, base + 6)])
          call vs_set(vst, base + 3, ifaces)
       end if
    end if
    call vs_set(vst, base + 5, gcv_empty([vs_get(vst, base + 3), vs_get(vst, base + 4)]))
    spec = type_spec(cname, vs_get(vst, base + 5), vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 2))
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 6, spec)
    nd = mk_node(N_DEFTYPE, gc_nil(), vs_get(vst, base + 6), gc_nil(), 1, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
  end function analyze_reify

  ! A type's spec: [class-text fields iface-keys names fn-nodes]. Method
  ! forms sharing a name become the clauses of ONE fn*, each with the
  ! type's fields bound around its body (method_clauses, bind_fields),
  ! and that fn* is analysed in the enclosing scope -- which is what
  ! lets a reify body close over its surroundings.
  recursive function type_spec(cname, fields, ifaces, methods, sc) result(spec)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    character(len=*), intent(in) :: cname
    type(gc_value), intent(in) :: fields, ifaces, methods, sc
    type(gc_value) :: spec, m, mname, names, fns, seen, clauses, fnform, fnode, tmp
    integer :: base

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    spec = gc_nil()
    base = vs_enter(vst, 11)
    call vs_set(vst, base + 1, fields)
    call vs_set(vst, base + 2, ifaces)
    call vs_set(vst, base + 11, iface_keys(vs_get(vst, base + 2)))
    ! an interface a type implements is a class from here: nominal, as
    ! every interface is here, and (instance? some.IFace x) resolves it
    block
       integer :: ii
       type(gc_value) :: isym
       character(len=:), allocatable :: itext
       if (gcv_is(vs_get(vst, base + 2))) then
          do ii = 0, gcv_count(vs_get(vst, base + 2)) - 1
             isym = strip_meta(gcv_nth(vs_get(vst, base + 2), ii))
             if (isym%tag /= GCT_SYM) cycle
             call gc_ref_text(isym%ref, s=itext)
             if (index(itext, ".") > 0) call declare_type_name(itext)
          end do
       end if
    end block
    call vs_set(vst, base + 3, methods)
    call vs_set(vst, base + 4, sc)
    names = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 5, names)
    fns = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 5)])
    call vs_set(vst, base + 6, fns)
    seen = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 5), vs_get(vst, base + 6)])
    call vs_set(vst, base + 7, seen)
    call vs_set(vst, base + 8, vs_get(vst, base + 3))
    do while (gcl_count(vs_get(vst, base + 8)) > 0)
       m = norm_form(strip_meta(gcl_first(vs_get(vst, base + 8))), [vs_get(vst, base + 5), vs_get(vst, base + 6), vs_get(vst, base + 7), vs_get(vst, base + 8)])
       mname = strip_meta(gcl_first(m))
       if (mname%tag == GCT_SYM) then
          block
             call bare_name(mname, s=dlt_1)
             tmp = gc_key(dlt_1, [vs_get(vst, base + 5), vs_get(vst, base + 6), vs_get(vst, base + 7), vs_get(vst, base + 8)])
          end block
          call vs_set(vst, base + 9, tmp)
          if (.not. gca_contains(vs_get(vst, base + 7), vs_get(vst, base + 9))) then
             block
                call bare_name(mname, s=dlt_1)
                clauses = method_clauses(dlt_1, vs_get(vst, base + 3), vs_get(vst, base + 1))
             end block
             call vs_set(vst, base + 10, clauses)
             ! a method an interface declares ^void answers nil, as in clj
             if (method_is_void(vs_get(vst, base + 11), vs_get(vst, base + 9))) then
                clauses = void_clauses(vs_get(vst, base + 10), [vs_get(vst, base + 5), vs_get(vst, base + 6), &
                     vs_get(vst, base + 7), vs_get(vst, base + 8), vs_get(vst, base + 9), vs_get(vst, base + 11)])
                call vs_set(vst, base + 10, clauses)
             end if
             fnform = vs_get(vst, base + 10)      ! the clause list IS fn*'s rest
             tctx%analyzing_method = .true.
             fnode = analyze_fn(fnform, vs_get(vst, base + 4))
             if (tctx%has_error) then
                call vs_leave(vst, base)
                return
             end if
             call vs_set(vst, base + 10, fnode)
             names = gcv_conj(vs_get(vst, base + 5), vs_get(vst, base + 9), [vs_get(vst, base + 6), vs_get(vst, base + 7), vs_get(vst, base + 10)])
             call vs_set(vst, base + 5, names)
             fns = gcv_conj(vs_get(vst, base + 6), vs_get(vst, base + 10), [vs_get(vst, base + 5), vs_get(vst, base + 7)])
             call vs_set(vst, base + 6, fns)
             seen = gca_assoc(vs_get(vst, base + 7), vs_get(vst, base + 9), gc_bool(.true.), &
                  [vs_get(vst, base + 5), vs_get(vst, base + 6), vs_get(vst, base + 9)])
             call vs_set(vst, base + 7, seen)
          end if
       end if
       tmp = gcl_rest(vs_get(vst, base + 8), [vs_get(vst, base + 5), vs_get(vst, base + 6), vs_get(vst, base + 7)])
       call vs_set(vst, base + 8, tmp)
    end do
    call vs_set(vst, base + 8, vs_get(vst, base + 11))
    tmp = gc_str(cname, [vs_get(vst, base + 1), vs_get(vst, base + 5), vs_get(vst, base + 6), vs_get(vst, base + 8)])
    call vs_set(vst, base + 9, tmp)
    spec = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 5), vs_get(vst, base + 6), vs_get(vst, base + 8), vs_get(vst, base + 9)])
    spec = gcv_conj(spec, vs_get(vst, base + 9), [vs_get(vst, base + 1), vs_get(vst, base + 5), vs_get(vst, base + 6), vs_get(vst, base + 8), spec])
    spec = gcv_conj(spec, vs_get(vst, base + 1), [vs_get(vst, base + 5), vs_get(vst, base + 6), vs_get(vst, base + 8), spec])
    spec = gcv_conj(spec, vs_get(vst, base + 8), [vs_get(vst, base + 5), vs_get(vst, base + 6), spec])
    spec = gcv_conj(spec, vs_get(vst, base + 5), [vs_get(vst, base + 6), spec])
    spec = gcv_conj(spec, vs_get(vst, base + 6), [spec])
    call vs_leave(vst, base)
  end function type_spec

  ! `x -> expanded to cons/concat calls, then analysed. Done here, once,
  ! rather than at every evaluation of the macro body that contains it
  ! (DEVIATIONS 6 moves from "at eval time" to "at analysis time").
  ! (. Class field), the dot form of a static: three elements, the dot,
  ! a class name, a field symbol
  logical function static_dot_field(form)
    type(gc_value), intent(in) :: form
    type(gc_value) :: h, c, m
    static_dot_field = .false.
    if (gcl_count(form) /= 3) return
    h = strip_meta(gcl_first(form))
    if (h%tag /= GCT_SYM) return
    if (.not. gc_ref_is(h%ref, ".")) return
    c = strip_meta(gcl_first(gcl_rest(form, [form])))
    m = strip_meta(gcl_first(gcl_rest(gcl_rest(form, [form]), [form])))
    if (c%tag /= GCT_SYM .or. m%tag /= GCT_SYM) return
    static_dot_field = is_class_name(c)
  end function static_dot_field

  ! that form as the symbol Class/field
  function static_dot_symbol(form) result(sym)
    type(gc_value), intent(in) :: form
    type(gc_value) :: sym, c, m
    character(len=:), allocatable :: ct, mt
    c = strip_meta(gcl_first(gcl_rest(form, [form])))
    m = strip_meta(gcl_first(gcl_rest(gcl_rest(form, [form]), [form])))
    call gc_ref_text(c%ref, s=ct)
    call gc_ref_text(m%ref, s=mt)
    sym = gc_sym(ct // "/" // mt, [form])
  end function static_dot_symbol

  ! (set! target value). A symbol target is a Var (resolved now); a
  ! (.field obj) target is a host field write, which for the one field
  ! with storage -- a fn's __methodImplCache -- lands in the closure.
  ! i2: 0 = Var in slot 2, 1 = field; children [obj?, value].
  recursive function analyze_setbang(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, tgt, var, kids, c, objf, al
    integer :: base
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 5)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    tgt = strip_meta(gcl_first(rest))
    call vs_set(vst, base + 3, tgt)
    kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, kids)
    if (tgt%tag == GCT_SYM .and. is_static_call(tgt)) then
       ! Class/field: a host static field. There is no storage behind
       ! it; the value is evaluated and the write discarded, as for any
       ! other host field.
       c = analyze(gcl_first(gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)])), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       kids = gcv_conj(vs_get(vst, base + 4), c, [vs_get(vst, base + 1), vs_get(vst, base + 3), c])
       call vs_set(vst, base + 4, kids)
       kids = gcv_conj(vs_get(vst, base + 4), vs_get(vst, base + 4), [vs_get(vst, base + 1), vs_get(vst, base + 3)])   ! placeholder obj slot
       call vs_set(vst, base + 4, kids)
       nd = mk_node(N_SETBANG, vs_get(vst, base + 4), gc_nil(), vs_get(vst, base + 3), 3, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    else if (tgt%tag == GCT_SYM) then
       ! a deftype method's field: (set! f v) is (set! (.-f this) v) for
       ! a mutable one in the method itself; clj's refusal for an
       ! immutable one, and for a mutable one from a fn made in the method
       al = lookup_field_alias(vs_get(vst, base + 2), tgt)
       if (gcv_is(al)) then
          call gc_ref_text(tgt%ref, s=dlt_1)
          if (truthy(gcv_nth(al, 1)) .and. field_of_this_fn(vs_get(vst, base + 2), tgt)) then
             call vs_set(vst, base + 5, gcv_nth(al, 0))
             call vs_set(vst, base + 5, gcl_cons(vs_get(vst, base + 5), gcl_empty([vs_get(vst, base + 5)]), [vs_get(vst, base + 5)]))
             call vs_set(vst, base + 5, gcl_cons(gc_sym(".-" // dlt_1, [vs_get(vst, base + 5)]), vs_get(vst, base + 5), [vs_get(vst, base + 5)]))
             call vs_set(vst, base + 5, gcl_cons(vs_get(vst, base + 5), gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1), vs_get(vst, base + 5)]), &
                  [vs_get(vst, base + 1), vs_get(vst, base + 5)]))
             call vs_set(vst, base + 5, gcl_cons(gc_sym("set!", [vs_get(vst, base + 5)]), vs_get(vst, base + 5), [vs_get(vst, base + 5)]))
             nd = analyze(vs_get(vst, base + 5), vs_get(vst, base + 2))
          else
             call raise_class("clotran.host.illegal_argument_exception", "Cannot assign to non-mutable: " // dlt_1, [vs_get(vst, base + 1)])
          end if
          call vs_leave(vst, base)
          return
       end if
       if (lookup_local(vs_get(vst, base + 2), tgt) >= 0) then
          ! A local -- a let binding, a parameter, or an immutable field
          ! bound as one (bind_fields) -- is not an assignable place:
          ! clj's AssignExpr refuses every local binding that is not a
          ! mutable field with this wording, when the form is analysed (a
          ! deftype's methods with the deftype)
          block
             call gc_ref_text(tgt%ref, s=dlt_1)
             call raise_class("clotran.host.illegal_argument_exception", "Cannot assign to non-mutable: " // dlt_1, [vs_get(vst, base + 1)])
          end block
          call vs_leave(vst, base)
          return
       end if
       var = resolve_var(tgt, gc_nil())
       if (.not. gcn_is_var(var)) then
          block
             call gc_ref_text(tgt%ref, s=dlt_1)
             ! the target analysed, as AssignExpr.Parser does: a symbol nothing binds
             call fail("Unable to resolve symbol: " // dlt_1 // " in this context")
          end block
          call vs_leave(vst, base)
          return
       end if
       call vs_set(vst, base + 5, var)
       c = analyze(gcl_first(gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)])), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       kids = gcv_conj(vs_get(vst, base + 4), c, [vs_get(vst, base + 1), vs_get(vst, base + 5), c])
       call vs_set(vst, base + 4, kids)
       nd = mk_node(N_SETBANG, vs_get(vst, base + 4), vs_get(vst, base + 5), gc_nil(), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    else if (gcl_is(tgt) .and. static_dot_field(tgt)) then
       ! (set! (. Class field) v): the static as Class/field names it --
       ! written when it is a box (RT/checkSpecAsserts, exec_setbang), else
       ! the value, discarded
       call vs_set(vst, base + 5, static_dot_symbol(vs_get(vst, base + 3)))
       c = analyze(gcl_first(gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)])), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       kids = gcv_conj(vs_get(vst, base + 4), c, [vs_get(vst, base + 1), vs_get(vst, base + 5), c])
       call vs_set(vst, base + 4, kids)
       kids = gcv_conj(vs_get(vst, base + 4), vs_get(vst, base + 4), [vs_get(vst, base + 1), vs_get(vst, base + 5)])   ! placeholder obj slot
       call vs_set(vst, base + 4, kids)
       nd = mk_node(N_SETBANG, vs_get(vst, base + 4), gc_nil(), vs_get(vst, base + 5), 3, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    else if (gcl_is(tgt)) then
       ! (.field obj) -- the object, then the value
       objf = gcl_first(gcl_rest(vs_get(vst, base + 3), [vs_get(vst, base + 1)]))
       call vs_set(vst, base + 5, objf)
       c = analyze(vs_get(vst, base + 5), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       kids = gcv_conj(vs_get(vst, base + 4), c, [vs_get(vst, base + 1), vs_get(vst, base + 3), c])
       call vs_set(vst, base + 4, kids)
       c = analyze(gcl_first(gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)])), vs_get(vst, base + 2))
       if (tctx%has_error) then
          call vs_leave(vst, base)
          return
       end if
       kids = gcv_conj(vs_get(vst, base + 4), c, [vs_get(vst, base + 1), vs_get(vst, base + 3), c])
       call vs_set(vst, base + 4, kids)
       nd = mk_node(N_SETBANG, vs_get(vst, base + 4), gc_nil(), strip_meta(gcl_first(vs_get(vst, base + 3))), &
            merge(2, 1, is_cache_field(vs_get(vst, base + 3))), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    else
       call fail("set! needs a var")
    end if
    call vs_leave(vst, base)
  end function analyze_setbang

  ! --- the passes over the tree: tail check, locals clearing ---------
  !
  ! GENERATED (src/f/gen/anpass_gen.inc, from model/anpass.lisp, included
  ! below in Eval.f90): the tail check (anp_tc) and locals clearing --
  ! has_fn_recur (anp_hfr), reads_in (anp_rd), liveness (anp_live),
  ! apply_clears (anp_clears). A local is nil-ed after its LAST read, as
  ! Clojure's compiler does ("locals clearing"), so a frame does not pin
  ! what it no longer needs: reduce's own `coll` parameter held the head
  ! of the whole realised range for the length of the reduce, 640 MB at
  ! 100000 elements. Conservative rules, each a way a later read could
  ! exist: a read inside a loop body is never the clearing read (the body
  ! runs again); a body that recurs to its fn is not cleared at all; a
  ! slot an inner fn captures is read when the closure is made (and again
  ! by letfn); among alternatives the after-sets are merged, so nothing is
  ! cleared early on any path. anpass.lisp proves it (tr-sound): no read
  ! marked for clearing is followed, on any run exec.inc can make, by
  ! another read of its slot.
  !
  ! What is hand-written here is the passes' reads of a node, each
  ! answering what model/anpass.lisp's ast-* answers of the node it
  ! decodes to, and the driver that sizes the live sets' array.

  integer(int64) function ast_kind(nd)
    type(gc_value), intent(in) :: nd
    ast_kind = 0
    if (gc_kind(nd) == OBJ_AST) ast_kind = gc_i1(nd)
  end function ast_kind

  integer(int64) function ast_i2(nd)
    type(gc_value), intent(in) :: nd
    ast_i2 = 0
    if (gc_kind(nd) == OBJ_AST) ast_i2 = gc_i2(nd)
  end function ast_i2

  integer(int64) function ast_nkids(nd)
    type(gc_value), intent(in) :: nd
    ast_nkids = 0
    if (gc_kind(nd) == OBJ_AST) ast_nkids = gcv_count(gc_slot(nd, 1))
  end function ast_nkids

  function ast_kid(nd, i) result(k)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: i
    type(gc_value) :: k
    k = gc_nil()
    if (gc_kind(nd) == OBJ_AST .and. i >= 0 .and. i < huge(0)) k = gcv_nth(gc_slot(nd, 1), int(i))
  end function ast_kid

  ! slot 3: a def's metadata node
  function ast_s3(nd) result(k)
    type(gc_value), intent(in) :: nd
    type(gc_value) :: k
    k = gc_nil()
    if (gc_kind(nd) == OBJ_AST) k = gc_slot(nd, 3)
  end function ast_s3

  ! a fn's capture pairs (outer slot, inner slot), in its template's third
  integer(int64) function ast_ncaps(nd)
    type(gc_value), intent(in) :: nd
    ast_ncaps = 0
    if (gc_kind(nd) == OBJ_AST) ast_ncaps = gcv_count(gcv_nth(gc_slot(nd, 2), 2)) / 2
  end function ast_ncaps

  integer(int64) function ast_cap(nd, i)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: i
    ast_cap = 0
    if (gc_kind(nd) == OBJ_AST .and. i >= 0 .and. i < huge(0) / 2) &
         ast_cap = int_of(gcv_nth(gcv_nth(gc_slot(nd, 2), 2), 2 * int(i)))
  end function ast_cap

  ! the alternatives: a case's branch bodies (its map's entries, in the
  ! order gca_entries gives them), a try's catch bodies, a deftype's fns
  integer(int64) function ast_nalts(nd)
    type(gc_value), intent(in) :: nd
    ast_nalts = 0
    if (gc_kind(nd) /= OBJ_AST) return
    select case (gc_i1(nd))
    case (N_CASE)
       ast_nalts = gca_count(gc_slot(nd, 2))
    case (N_TRY)
       ast_nalts = gcv_count(gc_slot(nd, 2))
    case (N_DEFTYPE)
       ast_nalts = gcv_count(gcv_nth(gc_slot(nd, 2), 4))
    end select
  end function ast_nalts

  function ast_alt(nd, i) result(k)
    type(gc_value), intent(in) :: nd
    integer(int64), intent(in) :: i
    type(gc_value) :: k, entry
    type(gc_value), allocatable :: ks(:), vls(:)
    k = gc_nil()
    if (gc_kind(nd) /= OBJ_AST .or. i < 0 .or. i >= huge(0)) return
    select case (gc_i1(nd))
    case (N_CASE)
       call gca_entries(gc_slot(nd, 2), ks, vls)
       if (i < size(vls)) then
          entry = strip_meta(vls(i + 1))
          if (gcv_is(entry)) k = gcv_nth(entry, 1)
       end if
    case (N_TRY)
       k = gcv_nth(gcv_nth(gc_slot(nd, 2), int(i)), 2)
    case (N_DEFTYPE)
       k = gcv_nth(gcv_nth(gc_slot(nd, 2), 4), int(i))
    end select
  end function ast_alt

  ! a recur's target: nonzero the fn, 0 a loop
  integer(int64) function ast_rfn(nd)
    type(gc_value), intent(in) :: nd
    ast_rfn = 0
    if (gc_kind(nd) == OBJ_AST) then
       if (gc_i1(nd) == N_RECUR) ast_rfn = int_of(gcv_nth(gc_slot(nd, 2), 0))
    end if
  end function ast_rfn

  ! The tail check of a body standing as tt says (anpass.lisp's anp-tc: 1
  ! a fn's, 0 the top level's): fails the analysis as clj's compiler
  ! does, and answers whether it passed.
  logical function tail_ok(body, tt)
    type(gc_value), intent(in) :: body
    integer, intent(in) :: tt
    integer(int64) :: code
    code = anp_tc(0_int64, body, 0_int64, 0_int64, int(tt, int64))
    tail_ok = (code == 0)
    if (code == 1) call fail("Can only recur from tail position")
    if (code == 2) call fail("Cannot recur across try")
  end function tail_ok

  ! After the tail check passed: the argument count a recur gave
  ! (analyze_recur held it), which clj checks only for a recur in tail
  ! position.
  logical function recur_count_ok()
    type(eval_ctx), pointer :: cx
    character(len=:), allocatable :: pm
    cx => ctx_self()
    recur_count_ok = .true.
    if (allocated(cx%recur_pend)) then
       pm = cx%recur_pend
       deallocate(cx%recur_pend)
       ! an IllegalArgumentException, as RecurExpr.Parser throws it
       call raise_class("clotran.host.illegal_argument_exception", pm, [gc_nil()])
       recur_count_ok = .false.
    end if
  end function recur_count_ok

  ! CLOTRAN_KEEP_LOCALS=1 turns the clearing pass off, so a paused frame
  ! shows every local it ever bound rather than nil for the ones already
  ! read. Clojure has the same switch, :disable-locals-clearing, and for
  ! the same reason: cleared locals are invisible to a debugger.
  logical function keep_locals()
    character(len=8) :: b
    if (keep_locals_mode == 0) then
       keep_locals_mode = 1
       call get_environment_variable("CLOTRAN_KEEP_LOCALS", b)
       if (trim(b) == "1") keep_locals_mode = 2
    end if
    keep_locals = (keep_locals_mode == 2)
  end function keep_locals


  ! The clearing pass over one body with `nslots` slots: generated
  ! (anp_clears), run with live sets for 16 nested alternatives and 64
  ! marks at first, the arrays doubled and the pass run again while it
  ! says they ran out. The marked reads get slot 3 = true, which exec.inc
  ! reads to clear. A body that recurs to its fn gets no clearing at all.
  subroutine apply_clears(body, nslots)
    type(gc_value), intent(in) :: body
    integer, intent(in) :: nslots
    type(anp_state) :: ps
    integer(int64) :: nlv, nmk, i
    if (keep_locals()) return
    if (nslots <= 0) return
    nlv = 32 * int(nslots, int64) + 32
    nmk = 64
    do
       if (allocated(ps%lv)) deallocate(ps%lv)
       if (allocated(ps%mk)) deallocate(ps%mk)
       allocate(ps%lv(0:nlv - 1), ps%mk(0:nmk - 1))
       call anp_clears(ps, body, int(nslots, int64))
       if (ps%err == 0) exit
       ! no clearing rather than a pass that never fits: nothing is lost
       if (nlv > 2_int64**30) return
       nlv = 2 * nlv
       nmk = 2 * nmk
    end do
    do i = 0, ps%nmk - 1
       call gc_set_slot(ps%mk(i), 3, gc_bool(.true.))
    end do
  end subroutine apply_clears

  ! --- the top level -------------------------------------------------

  ! A top-level form: analysed in a fresh fn scope (its lets need
  ! slots), wrapped as N_TOP with the frame size. A top-level `do` is
  ! NOT analysed as a unit: Compiler.eval evaluates its subforms one by
  ! one, each analysed after the previous has run, so an (ns ...) or a
  ! def earlier in the same do is visible to the rest.
  ! A top-level form's analysis, and of any analysed while it is (a
  ! macro's expansion evaluated): the analyzer locals' records it adds
  ! are dropped when it is done -- none older is changed by it -- so
  ! the context's arrays hold one nest of top-level forms at a time.
  recursive function analyze_top(form0) result(nd)
    type(gc_value), intent(in) :: form0
    type(gc_value) :: nd
    type(anl_state), pointer :: ls
    integer(int64) :: nf, nb, nx, nc, na, nn
    ls => anl_ls()
    nf = ls%nf; nb = ls%nb; nx = ls%nx; nc = ls%nc; na = ls%na; nn = ls%nn
    nd = analyze_top1(form0)
    if (.not. anl_ok()) nd = gc_nil()
    ls%nf = nf; ls%nb = nb; ls%nx = nx; ls%nc = nc; ls%na = na; ls%nn = nn
  end function analyze_top

  recursive function analyze_top1(form0) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form0
    type(gc_value) :: nd, form, head, sc, body
    integer :: base

    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 4)
    ! every seq in it a list (forms_as_lists), as for a macro's expansion
    call vs_set(vst, base + 1, form0)
    form = forms_as_lists(vs_get(vst, base + 1), [vs_get(vst, base + 1)])
    if (gc_kind(form) == OBJ_META) form = strip_meta(form)
    call vs_set(vst, base + 1, form)
    if (gcl_is(form)) then
       if (gcl_count(form) > 0) then
          head = strip_meta(gcl_first(form))
          if (head%tag == GCT_SYM) then
             if (gc_ref_is(head%ref, "do")) then
                nd = mk_node(N_TOPDO, gc_nil(), gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)]), gc_nil(), 0, &
                     [vs_get(vst, base + 1)])
                call vs_leave(vst, base)
                return
             end if
          end if
       end if
    end if
    sc = new_fn_scope(gc_nil(), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, sc)
    body = analyze(vs_get(vst, base + 1), vs_get(vst, base + 2))
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 3, body)
    if (.not. tail_ok(vs_get(vst, base + 3), 0)) then
       call vs_leave(vst, base)
       return
    end if
    if (.not. recur_count_ok()) then
       call vs_leave(vst, base)
       return
    end if
    call apply_clears(vs_get(vst, base + 3), scope_nslots(vs_get(vst, base + 2)))
    ! the flat form beside the tree (flat.inc): a loop typed at the
    ! REPL runs as one in a fn does; its temporaries widen the frame
    block
      type(gc_value) :: fl
      integer :: nt
      fl = flat_compile_body(vs_get(vst, base + 3), scope_nslots(vs_get(vst, base + 2)), nt, &
           [vs_get(vst, base + 1), vs_get(vst, base + 2)])
      call vs_set(vst, base + 4, fl)
      nd = mk_node(N_TOP, gc_nil(), vs_get(vst, base + 3), vs_get(vst, base + 4), &
           scope_nslots(vs_get(vst, base + 2)) + nt, &
           [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4)])
    end block
    call vs_leave(vst, base)
  end function analyze_top1
