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
  ! Scope objects are GC objects too (K_SCOPE, K_FNINFO), because the
  ! analyser allocates constantly and everything it holds must be
  ! rootable. Same rule as everywhere: an intermediate lives in a value
  ! stack slot, never in a bare local across an allocation.
  ! ===================================================================

  ! --- scopes --------------------------------------------------------

  ! A fresh fn scope: a FNINFO for the fn and its root block. `outer` is
  ! the block scope the fn is written in, or nil at top level.
  function new_fn_scope(outer, roots) result(sc)
    type(gc_value), intent(in) :: outer
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: sc, info, caps, cmap, names
    integer :: base
    base = vs_enter(4)
    call vs_set(base + 1, outer)
    caps = gcv_empty([roots, vs_get(base + 1)])
    call vs_set(base + 2, caps)
    cmap = gca_empty([roots, vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, cmap)
    info = gc_obj(OBJ_AST, [vs_get(base + 2), vs_get(base + 1), vs_get(base + 3), gc_nil()], &
         [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    ! i1 is the SLOT COUNTER, from zero. It was set to K_FNINFO (101) as
    ! a kind tag nothing ever read, and reserve_slots counted on from
    ! there: every frame in the system had 101 slots nobody used, a
    ! 128-slot arena run per call, and memory to match.
    call gc_set_i1(info, 0)
    call gc_set_i2(info, -1)          ! self slot: none
    call vs_set(base + 4, info)
    names = gca_empty([roots, vs_get(base + 4)])
    call vs_set(base + 3, names)
    sc = gc_obj(OBJ_AST, [vs_get(base + 3), gc_nil(), vs_get(base + 4), gc_nil()], &
         [roots, vs_get(base + 3), vs_get(base + 4)])
    call gc_set_i1(sc, K_SCOPE)
    call vs_leave(base)
  end function new_fn_scope

  ! A nested block in the same fn: empty names, same fninfo, the
  ! parent's recur target unless the caller replaces it.
  function child_scope(parent, roots) result(sc)
    type(gc_value), intent(in) :: parent
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: sc, names
    integer :: base
    base = vs_enter(2)
    call vs_set(base + 1, parent)
    names = gca_empty([roots, vs_get(base + 1)])
    call vs_set(base + 2, names)
    sc = gc_obj(OBJ_AST, [vs_get(base + 2), vs_get(base + 1), &
         gc_slot(vs_get(base + 1), 3), gc_slot(vs_get(base + 1), 4)], &
         [roots, vs_get(base + 1), vs_get(base + 2)])
    call gc_set_i1(sc, K_SCOPE)
    call vs_leave(base)
  end function child_scope

  function scope_info(sc) result(info)
    type(gc_value), intent(in) :: sc
    type(gc_value) :: info
    info = gc_slot(sc, 3)
  end function scope_info

  ! Reserves n consecutive slots in the fn and returns the first.
  function reserve_slots(sc, n) result(start)
    type(gc_value), intent(in) :: sc
    integer, intent(in) :: n
    integer :: start
    type(gc_value) :: info
    info = scope_info(sc)
    start = gc_i1(info)
    call gc_set_i1(info, start + n)
  end function reserve_slots

  ! Makes `sym` name `slot` in this block.
  subroutine bind_name(sc, sym, slot, roots)
    type(gc_value), intent(in) :: sc, sym
    integer, intent(in) :: slot
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: names
    integer :: base
    base = vs_enter(3)
    call vs_set(base + 1, sc)
    call vs_set(base + 2, sym)
    names = gca_assoc(gc_slot(vs_get(base + 1), 1), vs_get(base + 2), gc_int(slot), &
         [roots, vs_get(base + 1), vs_get(base + 2)])
    call gc_set_slot(vs_get(base + 1), 1, names)
    ! ...and the other way round, at the FN level: slot -> name, for
    ! every block of the fn, so a paused frame can report its locals by
    ! name (the debugger, exec.inc break_frames). The scope map above is
    ! per block and gone after analysis; this one rides on the template.
    call vs_set(base + 3, scope_info(vs_get(base + 1)))
    names = gc_slot(vs_get(base + 3), 4)
    if (.not. gca_is(names)) names = gca_empty([roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    names = gca_assoc(names, gc_int(slot), vs_get(base + 2), &
         [roots, vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call gc_set_slot(vs_get(base + 3), 4, names)
    call vs_leave(base)
  end subroutine bind_name

  ! Declares a new local: one slot, bound in this block.
  function declare_local(sc, sym, roots) result(slot)
    type(gc_value), intent(in) :: sc, sym
    type(gc_value), intent(in) :: roots(:)
    integer :: slot
    slot = reserve_slots(sc, 1)
    call bind_name(sc, sym, slot, roots)
  end function declare_local

  ! The slot a symbol names, or -1. Walks the blocks of this fn, then the
  ! fn's captures, then the ENCLOSING fn -- and a hit there becomes a
  ! capture: a fresh slot in this fn, filled from the outer slot when
  ! the closure is made. Transitive through any depth of nesting, since
  ! the enclosing fn resolves the same way.
  recursive function lookup_local(sc, sym) result(slot)
    type(gc_value), intent(in) :: sc, sym
    integer :: slot
    type(gc_value) :: blk, info, hit, caps, cmap
    integer :: outer, base

    slot = -1
    blk = sc
    do while (gc_kind(blk) == OBJ_AST)
       if (gca_contains(gc_slot(blk, 1), sym)) then
          hit = gca_get(gc_slot(blk, 1), sym)
          slot = int(hit%ival, kind=4)
          return
       end if
       blk = gc_slot(blk, 2)
    end do
    info = scope_info(sc)
    if (gca_contains(gc_slot(info, 3), sym)) then
       hit = gca_get(gc_slot(info, 3), sym)
       slot = int(hit%ival, kind=4)
       return
    end if
    if (gc_kind(gc_slot(info, 2)) /= OBJ_AST) return
    outer = lookup_local(gc_slot(info, 2), sym)
    if (outer < 0) return

    base = vs_enter(3)
    call vs_set(base + 1, info)
    call vs_set(base + 2, sym)
    slot = gc_i1(vs_get(base + 1))
    call gc_set_i1(vs_get(base + 1), slot + 1)
    caps = gcv_conj(gc_slot(vs_get(base + 1), 1), gc_int(outer), [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, caps)
    caps = gcv_conj(vs_get(base + 3), gc_int(slot), [vs_get(base + 1), vs_get(base + 2)])
    call gc_set_slot(vs_get(base + 1), 1, caps)
    cmap = gca_assoc(gc_slot(vs_get(base + 1), 3), vs_get(base + 2), gc_int(slot), &
         [vs_get(base + 1), vs_get(base + 2)])
    call gc_set_slot(vs_get(base + 1), 3, cmap)
    call vs_leave(base)
  end function lookup_local

  ! --- nodes ---------------------------------------------------------

  function mk_node(kind, children, p1, p2, i2, roots) result(nd)
    integer, intent(in) :: kind, i2
    type(gc_value), intent(in) :: children, p1, p2
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: nd
    nd = gc_obj(OBJ_AST, [children, p1, p2, gc_nil()], [roots, children, p1, p2])
    call gc_set_i1(nd, kind)
    call gc_set_i2(nd, i2)
  end function mk_node

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
    character(len=*), intent(in) :: msg
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: nd, s
    integer :: base
    base = vs_enter(1)
    s = gc_str(msg, roots)
    call vs_set(base + 1, s)
    nd = mk_node(N_FAIL, gc_nil(), vs_get(base + 1), gc_nil(), 0, roots)
    call vs_leave(base)
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
    type(gc_value), intent(in) :: v
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base
    out = strip_meta(v)
    if (gc_kind(out) == OBJ_LAZY .or. gc_kind(out) == OBJ_SEQ) then
       base = vs_enter(1)
       call vs_set(base + 1, out)
       out = seq_to_list(vs_get(base + 1), [roots, vs_get(base + 1)])
       call vs_leave(base)
    end if
  end function norm_form

  ! Analyses every form of a list or vector into a children vector.
  recursive function analyze_all(forms, sc, roots) result(out)
    type(gc_value), intent(in) :: forms, sc
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out, nd, walk
    integer :: base, i, n

    base = vs_enter(4)
    call vs_set(base + 1, forms)
    call vs_set(base + 2, sc)
    out = gcv_empty([roots, vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, out)
    if (gcv_is(forms)) then
       n = gcv_count(forms)
       do i = 0, n - 1
          nd = analyze(gcv_nth(vs_get(base + 1), i), vs_get(base + 2))
          if (has_error) exit
          out = gcv_conj(vs_get(base + 3), nd, [vs_get(base + 1), vs_get(base + 2), nd])
          call vs_set(base + 3, out)
       end do
    else
       walk = forms
       call vs_set(base + 4, walk)
       do while (gcl_count(vs_get(base + 4)) > 0)
          nd = analyze(gcl_first(vs_get(base + 4)), vs_get(base + 2))
          if (has_error) exit
          out = gcv_conj(vs_get(base + 3), nd, [vs_get(base + 1), vs_get(base + 2), nd])
          call vs_set(base + 3, out)
          walk = gcl_rest(vs_get(base + 4), [vs_get(base + 3)])
          call vs_set(base + 4, walk)
       end do
    end if
    out = vs_get(base + 3)
    call vs_leave(base)
  end function analyze_all

  ! A body (a list of forms) as one N_DO node.
  recursive function analyze_body(forms, sc, roots) result(nd)
    type(gc_value), intent(in) :: forms, sc
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: nd, kids
    integer :: base
    base = vs_enter(1)
    kids = analyze_all(forms, sc, roots)
    call vs_set(base + 1, kids)
    nd = mk_node(N_DO, vs_get(base + 1), gc_nil(), gc_nil(), 0, roots)
    call vs_leave(base)
  end function analyze_body

  ! --- the analyser proper -------------------------------------------

  ! One form to one node, in scope `sc`.
  recursive function analyze(form0, sc) result(nd)
    type(gc_value), intent(in) :: form0, sc
    type(gc_value) :: nd, form, head, kids, expanded, mvar
    integer :: base, slot

    nd = gc_nil()
    if (has_error) return
    base = vs_enter(4)
    call vs_set(base + 2, sc)
    form = form0
    ! Metadata on a form is information about it, not part of what it
    ! means; only def looks at it (and does so from the raw form).
    if (gc_kind(form) == OBJ_META) form = strip_meta(form)
    ! A seq is code, like a list; realised once, here.
    if (gc_kind(form) == OBJ_LAZY .or. gc_kind(form) == OBJ_SEQ) then
       call vs_set(base + 1, form)
       form = seq_to_list(vs_get(base + 1), [vs_get(base + 1), vs_get(base + 2)])
    end if
    call vs_set(base + 1, form)

    select case (form%tag)
    case (GCT_SYM)
       nd = analyze_symbol(vs_get(base + 1), vs_get(base + 2))
    case (GCT_OBJ)
       select case (gc_kind(form))
       case (OBJ_CONS)
          if (gcl_count(form) == 0) then
             nd = const_node(vs_get(base + 1), [vs_get(base + 2)])
          else
             nd = analyze_seq(vs_get(base + 1), vs_get(base + 2))
             if (has_error) then
                call trace_analysis_failure(vs_get(base + 1))
                ! an analysis error names the innermost positioned form
                if (gc_i2(vs_get(base + 1)) /= 0 .and. index(last_error, "  at ") == 0) &
                     last_error = last_error // "  at " // gcr_position(gc_i2(vs_get(base + 1)))
             end if
             ! the source position, if the reader recorded one and the
             ! node has none of its own yet (a macro's expansion keeps
             ! the position of the form that was written)
             if (.not. has_error .and. gc_kind(nd) == OBJ_AST) then
                if (gc_i2(vs_get(base + 1)) /= 0 .and. tag_of(gc_slot(nd, 4)) == GCT_NIL) &
                     call gc_set_slot(nd, 4, gc_int(gc_i2(vs_get(base + 1))))
             end if
          end if
       case (OBJ_VECTOR)
          kids = analyze_all(vs_get(base + 1), vs_get(base + 2), [vs_get(base + 1)])
          call vs_set(base + 3, kids)
          if (.not. has_error) nd = mk_node(N_VECTOR, vs_get(base + 3), gc_nil(), gc_nil(), 0, &
               [vs_get(base + 1), vs_get(base + 2)])
       case (OBJ_MAP, OBJ_HAMT)
          nd = analyze_map(vs_get(base + 1), vs_get(base + 2))
       case (OBJ_SET)
          kids = analyze_all(set_elems(vs_get(base + 1), vs_get(base + 2)), vs_get(base + 2), &
               [vs_get(base + 1)])
          call vs_set(base + 3, kids)
          if (.not. has_error) nd = mk_node(N_SET, vs_get(base + 3), gc_nil(), gc_nil(), 0, &
               [vs_get(base + 1), vs_get(base + 2)])
       case default
          ! closures, builtins, vars, types: self-evaluating
          nd = const_node(vs_get(base + 1), [vs_get(base + 2)])
       end select
    case default
       nd = const_node(vs_get(base + 1), [vs_get(base + 2)])
    end select
    call vs_leave(base)
  end function analyze

  ! A map literal: children alternate key, value.
  recursive function analyze_map(form, sc) result(nd)
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, kids, kn, vn
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i
    nd = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, form)
    call vs_set(base + 2, sc)
    call gca_entries(form, ks, vls)
    kids = gcv_empty([vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 3, kids)
    do i = 1, size(ks)
       kn = analyze(ks(i), vs_get(base + 2))
       if (has_error) exit
       kids = gcv_conj(vs_get(base + 3), kn, [vs_get(base + 1), vs_get(base + 2), kn])
       call vs_set(base + 3, kids)
       vn = analyze(vls(i), vs_get(base + 2))
       if (has_error) exit
       kids = gcv_conj(vs_get(base + 3), vn, [vs_get(base + 1), vs_get(base + 2), vn])
       call vs_set(base + 3, kids)
    end do
    if (.not. has_error) nd = mk_node(N_MAP, vs_get(base + 3), gc_nil(), gc_nil(), 0, &
         [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_map

  ! A symbol: a local, a static field, a Var, a class literal -- in the
  ! order Compiler.analyzeSymbol tries them.
  recursive function analyze_symbol(sym, sc) result(nd)
    type(gc_value), intent(in) :: sym, sc
    type(gc_value) :: nd, var, v
    character(len=:), allocatable :: t
    integer :: base, slot, sl

    nd = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, sym)
    call vs_set(base + 2, sc)
    slot = lookup_local(vs_get(base + 2), vs_get(base + 1))
    if (slot >= 0) then
       nd = mk_node(N_LOCAL, gc_nil(), vs_get(base + 1), gc_nil(), slot, [vs_get(base + 2)])
       call vs_leave(base)
       return
    end if
    if (is_static_call(sym)) then
       ! Class/field in value position: a static FIELD. Resolved now,
       ! since the answer cannot change; an unknown one fails where it
       ! is used rather than where it is written, as before.
       t = gc_ref_text(sym%ref)
       sl = index(t, "/")
       v = static_member(t(1:sl-1), t(sl+1:), vs_get(base + 1))
       if (has_error) then
          call gce_clear_error()
          nd = fail_node("no such member: " // t, [vs_get(base + 1), vs_get(base + 2)])
       else
          call vs_set(base + 3, v)
          nd = const_node(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 2)])
       end if
       call vs_leave(base)
       return
    end if
    var = resolve_var(vs_get(base + 1), gc_nil())
    if (gcn_is_var(var)) then
       call vs_set(base + 3, var)
       nd = mk_node(N_VAR, gc_nil(), vs_get(base + 3), gc_nil(), 0, [vs_get(base + 1), vs_get(base + 2)])
       call vs_leave(base)
       return
    end if
    if (index(gc_ref_text(sym%ref), "/") > 1) then
       ! A QUALIFIED symbol that does not resolve: core.clj's slurp names
       ! jio/reader, and clojure.java.io is skipped by name here. Clojure
       ! would fail to compile; clotran defers to run time, so the
       ! function is defined and only a CALL of it fails. Unqualified
       ! symbols are not deferred -- that is a real compile error.
       nd = mk_node(N_LATEVAR, gc_nil(), vs_get(base + 1), gc_nil(), 0, [vs_get(base + 1), vs_get(base + 2)])
       call vs_leave(base)
       return
    end if
    if (is_class_name(sym)) then
       ! A CLASS LITERAL evaluates to the keyword naming clotran's type
       ! tag, java.lang implicitly imported (Object == java.lang.Object).
       v = gc_key(class_key(gc_ref_text(sym%ref)), [vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 3, v)
       nd = const_node(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 2)])
       call vs_leave(base)
       return
    end if
    call fail("Unable to resolve symbol: " // gc_ref_text(sym%ref) // " in this context")
    call vs_leave(base)
  end function analyze_symbol

  ! A list form: special form, macro call, host sugar, or a call.
  ! The :inline fn of the Var `head` names, when its :inline-arities
  ! accept `argc`; nil otherwise. Compiler.isInline.
  recursive function inline_fn(head, argc) result(fn)
    type(gc_value), intent(in) :: head
    integer, intent(in) :: argc
    type(gc_value) :: fn, var, md, pred, ok
    integer :: base
    fn = gc_nil()
    var = resolve_var(head, gc_nil())
    if (.not. gcn_is_var(var)) return
    md = gc_slot(var, 2)
    if (.not. gca_is(md)) return
    base = vs_enter(2)
    call vs_set(base + 1, md)
    fn = gca_get(vs_get(base + 1), gc_key("inline", [vs_get(base + 1)]))
    if (fn%tag == GCT_NIL) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 2, fn)
    pred = gca_get(vs_get(base + 1), gc_key("inline-arities", [vs_get(base + 1), vs_get(base + 2)]))
    if (pred%tag /= GCT_NIL) then
       ok = apply(pred, gcv_conj(gcv_empty([vs_get(base + 1), vs_get(base + 2), pred]), gc_int(int(argc, gc_ip)), &
            [vs_get(base + 1), vs_get(base + 2), pred]))
       if (has_error .or. .not. truthy(ok)) fn = gc_nil()
    end if
    if (fn%tag /= GCT_NIL) fn = vs_get(base + 2)
    call vs_leave(base)
  end function inline_fn

  ! A list of forms as a vector, for apply.
  function args_vector(forms, roots) result(v)
    type(gc_value), intent(in) :: forms
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v, walk
    integer :: base
    base = vs_enter(2)
    call vs_set(base + 1, forms)
    v = gcv_empty([roots, vs_get(base + 1)])
    call vs_set(base + 2, v)
    walk = vs_get(base + 1)
    do while (gcl_count(walk) > 0)
       call vs_set(base + 2, gcv_conj(vs_get(base + 2), gcl_first(walk), [roots, vs_get(base + 1), walk]))
       walk = gcl_rest(walk, [roots, vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 1, walk)
    end do
    v = vs_get(base + 2)
    call vs_leave(base)
  end function args_vector

  recursive function analyze_seq(form, sc) result(nd)
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, head, mvar, expanded
    integer :: base

    nd = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, form)
    call vs_set(base + 2, sc)
    head = strip_meta(gcl_first(form))

    if (head%tag == GCT_SYM) then
       ! A LOCAL shadows everything: a special form name, a macro, host
       ! sugar. (let [do 1] (do)) is a call of the local.
       if (lookup_local(vs_get(base + 2), head) < 0) then
          ! Macros are expanded first: `..` is a macro whose name looks
          ! like member sugar, and Compiler.macroexpand1 asks isMacro
          ! before it looks at the dot.
          mvar = macro_var(head, gc_nil())
          if (gcn_is_var(mvar)) then
             call vs_set(base + 3, gcn_var_value(mvar))
             expanded = expand_macro(vs_get(base + 3), vs_get(base + 1), gc_nil())
             if (has_error) then
                call vs_leave(base)
                return
             end if
             call vs_set(base + 4, expanded)
             nd = analyze(vs_get(base + 4), vs_get(base + 2))
             call vs_leave(base)
             return
          end if
          ! :inline, as Compiler.analyzeSeq does right after macroexpansion
          ! (isInline): a Var whose metadata carries an :inline fn, and
          ! whose :inline-arities -- if any -- accepts this argument count,
          ! has that fn applied to the argument FORMS and the result
          ! analysed instead of a call. core.clj gives 129 definitions one:
          ! (+ a b) becomes (. clojure.lang.Numbers (add a b)) and the
          ! static call resolves to the native here, so the arithmetic
          ! in a loop costs no closure call. preserveTag is not done: a
          ! :tag on the form is a hint nothing here reads.
          mvar = inline_fn(head, gcl_count(vs_get(base + 1)) - 1)
          if (has_error) then
             call vs_leave(base)
             return
          end if
          if (mvar%tag /= GCT_NIL) then
             call vs_set(base + 3, mvar)
             expanded = apply(vs_get(base + 3), args_vector(gcl_rest(vs_get(base + 1), [vs_get(base + 3)]), [vs_get(base + 3)]))
             if (has_error) then
                call vs_leave(base)
                return
             end if
             call vs_set(base + 4, expanded)
             nd = analyze(vs_get(base + 4), vs_get(base + 2))
             call vs_leave(base)
             return
          end if
          if (is_special(head)) then
             nd = analyze_special(head, vs_get(base + 1), vs_get(base + 2))
             call vs_leave(base)
             return
          end if
          if (is_member_sym(head)) then
             nd = analyze_dot(member_to_dot(vs_get(base + 1)), vs_get(base + 2))
             call vs_leave(base)
             return
          end if
          if (is_static_call(head)) then
             nd = analyze_dot(static_to_dot(vs_get(base + 1)), vs_get(base + 2))
             call vs_leave(base)
             return
          end if
          if (is_ctor_sym(head)) then
             nd = analyze_new(ctor_to_new(vs_get(base + 1)), vs_get(base + 2))
             call vs_leave(base)
             return
          end if
       end if
    end if

    nd = analyze_call(vs_get(base + 1), vs_get(base + 2))
    call vs_leave(base)
  end function analyze_seq

  ! CLOTRAN_TRACE_MACRO=1 also names the innermost list form whose
  ! analysis failed, which is how a structural surprise in a
  ! macro-built form gets found.
  subroutine trace_analysis_failure(form)
    type(gc_value), intent(in) :: form
    character(len=:), allocatable :: t
    if (trace_macros == 0) call read_trace_macros()
    if (trace_macros /= 1) return
    t = gcp_str(form, .true.)
    if (len(t) > 300) t = t(1:300) // "..."
    write(0, '(A,A)') "analysis failed in: ", t
  end subroutine trace_analysis_failure

  ! (f a b) -> N_CALL with children [f a b].
  recursive function analyze_call(form, sc) result(nd)
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, kids
    integer :: base
    nd = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, form)
    call vs_set(base + 2, sc)
    kids = analyze_all(vs_get(base + 1), vs_get(base + 2), [vs_get(base + 1)])
    call vs_set(base + 3, kids)
    if (.not. has_error) nd = mk_node(N_CALL, vs_get(base + 3), gc_nil(), gc_nil(), 0, &
         [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_call

  ! --- host sugar, rewritten into the canonical forms ----------------

  ! (.member target args) -> (. target member args)   [the shape eval_dot reads]
  function member_to_dot(form) result(out)
    type(gc_value), intent(in) :: form
    type(gc_value) :: out, head, rest, args
    character(len=:), allocatable :: hname
    integer :: base
    base = vs_enter(4)
    call vs_set(base + 1, form)
    head = gcl_first(form)
    hname = gc_ref_text(head%ref)
    call vs_set(base + 2, gcl_rest(vs_get(base + 1), [vs_get(base + 1)]))
    call vs_set(base + 3, gc_sym(hname(2:), [vs_get(base + 1), vs_get(base + 2)]))
    call vs_set(base + 4, gcl_rest(vs_get(base + 2), [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)]))
    args = gcl_cons(vs_get(base + 3), vs_get(base + 4), [vs_get(base + 2), vs_get(base + 3), vs_get(base + 4)])
    call vs_set(base + 4, args)
    args = gcl_cons(gcl_first(vs_get(base + 2)), vs_get(base + 4), [vs_get(base + 2), vs_get(base + 4)])
    call vs_set(base + 4, args)
    out = gcl_cons(gc_sym(".", [vs_get(base + 4)]), vs_get(base + 4), [vs_get(base + 4)])
    call vs_leave(base)
  end function member_to_dot

  ! (Class/member args) -> (. Class (member args))
  function static_to_dot(form) result(out)
    type(gc_value), intent(in) :: form
    type(gc_value) :: out, head, args
    character(len=:), allocatable :: t
    integer :: base, slash
    base = vs_enter(4)
    call vs_set(base + 1, form)
    head = gcl_first(form)
    t = gc_ref_text(head%ref)
    slash = index(t, "/")
    call vs_set(base + 2, gc_sym(t(slash+1:), [vs_get(base + 1)]))
    call vs_set(base + 3, gcl_rest(vs_get(base + 1), [vs_get(base + 1), vs_get(base + 2)]))
    args = gcl_cons(vs_get(base + 2), vs_get(base + 3), [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_set(base + 3, args)                              ! (member args)
    call vs_set(base + 4, gcl_empty([vs_get(base + 3)]))
    args = gcl_cons(vs_get(base + 3), vs_get(base + 4), [vs_get(base + 3), vs_get(base + 4)])
    call vs_set(base + 3, args)                              ! ((member args))
    call vs_set(base + 4, gc_sym(t(1:slash-1), [vs_get(base + 3)]))
    args = gcl_cons(vs_get(base + 4), vs_get(base + 3), [vs_get(base + 3), vs_get(base + 4)])
    call vs_set(base + 3, args)                              ! (Class (member args))
    out = gcl_cons(gc_sym(".", [vs_get(base + 3)]), vs_get(base + 3), [vs_get(base + 3)])
    call vs_leave(base)
  end function static_to_dot

  ! (Class. args) -> (new Class args)
  function ctor_to_new(form) result(out)
    type(gc_value), intent(in) :: form
    type(gc_value) :: out, head, args
    character(len=:), allocatable :: t
    integer :: base
    base = vs_enter(3)
    call vs_set(base + 1, form)
    head = gcl_first(form)
    t = gc_ref_text(head%ref)
    call vs_set(base + 2, gc_sym(t(1:len(t)-1), [vs_get(base + 1)]))
    call vs_set(base + 3, gcl_rest(vs_get(base + 1), [vs_get(base + 1), vs_get(base + 2)]))
    args = gcl_cons(vs_get(base + 2), vs_get(base + 3), [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_set(base + 3, args)
    out = gcl_cons(gc_sym("new", [vs_get(base + 3)]), vs_get(base + 3), [vs_get(base + 3)])
    call vs_leave(base)
  end function ctor_to_new

  ! (. target member args...) or (. target (member args...)).
  !
  ! A static call on a host class is resolved to its native NOW, so
  ! (clojure.lang.RT/first x) is an ordinary call of a constant --
  ! that is most of what core.clj does. Everything else keeps the
  ! shape and is handed to eval_dot at run time with its parts already
  ! evaluated (N_DOT), because eval_dot holds the instance rules: a
  ! deftype answers its own methods before any host member does.
  recursive function analyze_dot(form, sc) result(nd)
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, args, target, rest, member, margs, kids, fnv, tn
    character(len=:), allocatable :: mname
    logical :: is_call
    integer :: base

    nd = gc_nil()
    base = vs_enter(8)
    call vs_set(base + 1, form)
    call vs_set(base + 2, sc)
    args = gcl_rest(form, [vs_get(base + 1)])
    call vs_set(base + 3, args)
    if (gcl_count(vs_get(base + 3)) < 2) then
       call fail("Malformed member expression")
       call vs_leave(base)
       return
    end if
    target = gcl_first(vs_get(base + 3))
    call vs_set(base + 4, target)
    rest = gcl_rest(vs_get(base + 3), [vs_get(base + 1)])
    member = strip_meta(gcl_first(rest))
    if (gc_kind(member) == OBJ_LAZY .or. gc_kind(member) == OBJ_SEQ) then
       call vs_set(base + 5, member)
       member = seq_to_list(vs_get(base + 5), [vs_get(base + 1), vs_get(base + 5)])
    end if
    call vs_set(base + 5, member)
    if (gcl_is(vs_get(base + 5))) then
       is_call = .true.
       margs = gcl_rest(vs_get(base + 5), [vs_get(base + 1)])
       member = strip_meta(gcl_first(vs_get(base + 5)))
    else
       margs = gcl_rest(gcl_rest(vs_get(base + 3), [vs_get(base + 1)]), [vs_get(base + 1)])
       is_call = (gcl_count(margs) > 0)
    end if
    call vs_set(base + 6, margs)
    call vs_set(base + 5, member)
    if (member%tag /= GCT_SYM) then
       call fail(". needs a member name")
       call vs_leave(base)
       return
    end if
    mname = gc_ref_text(member%ref)
    ! A member name reached through syntax-quote arrives qualified --
    ! defmethod's template says addMethod and the reader makes it
    ! clojure.core/addMethod. HostExpr.Parser reads sym.name only, and
    ! so does this.
    if (index(mname, "/") > 1) then
       mname = mname(index(mname, "/") + 1:)
       member = gc_sym(mname, [vs_get(base + 1), vs_get(base + 5)])
       call vs_set(base + 5, member)
    end if

    ! A host class as the target: a static member, resolved once.
    if (target%tag == GCT_SYM) then
       if (lookup_local(vs_get(base + 2), target) < 0) then
          if (gc_kind(find_type(gc_ref_text(target%ref))) /= OBJ_TYPE .and. is_host_class(target)) then
             fnv = static_member(gc_ref_text(target%ref), mname, vs_get(base + 1))
             if (has_error) then
                call gce_clear_error()
                nd = fail_node("no such member: " // gc_ref_text(target%ref) // "/" // mname, &
                     [vs_get(base + 1), vs_get(base + 2)])
                call vs_leave(base)
                return
             end if
             call vs_set(base + 7, fnv)
             if (.not. is_call) then
                nd = const_node(vs_get(base + 7), [vs_get(base + 1), vs_get(base + 2)])
                call vs_leave(base)
                return
             end if
             ! (native args...) as a plain call
             tn = const_node(vs_get(base + 7), [vs_get(base + 1), vs_get(base + 2)])
             call vs_set(base + 8, tn)
             kids = gcv_empty([vs_get(base + 1), vs_get(base + 2), vs_get(base + 8)])
             call vs_set(base + 7, kids)
             kids = gcv_conj(vs_get(base + 7), vs_get(base + 8), [vs_get(base + 1), vs_get(base + 2)])
             call vs_set(base + 7, kids)
             kids = analyze_all(vs_get(base + 6), vs_get(base + 2), [vs_get(base + 1), vs_get(base + 7)])
             call vs_set(base + 8, kids)
             if (has_error) then
                call vs_leave(base)
                return
             end if
             kids = concat_vecs(vs_get(base + 7), vs_get(base + 8), [vs_get(base + 1), vs_get(base + 2)])
             call vs_set(base + 7, kids)
             nd = mk_node(N_CALL, vs_get(base + 7), gc_nil(), gc_nil(), 0, [vs_get(base + 1), vs_get(base + 2)])
             call vs_leave(base)
             return
          end if
          ! A deftype class, or a class name is_host_class does not know:
          ! left to eval_dot, target passed as the symbol, unevaluated.
          if (gc_kind(find_type(gc_ref_text(target%ref))) == OBJ_TYPE .or. is_class_name(target)) then
             kids = analyze_all(vs_get(base + 6), vs_get(base + 2), [vs_get(base + 1)])
             call vs_set(base + 7, kids)
             if (.not. has_error) then
                nd = mk_node(N_DOT, vs_get(base + 7), vs_get(base + 5), vs_get(base + 4), &
                     merge(1, 0, is_call), [vs_get(base + 1), vs_get(base + 2)])
             end if
             call vs_leave(base)
             return
          end if
       end if
    end if

    ! An instance member: children [target args...]; the native it
    ! names, if any, cached in slot 3 for the executor's fast path.
    tn = analyze(vs_get(base + 4), vs_get(base + 2))
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 8, tn)
    kids = gcv_empty([vs_get(base + 1), vs_get(base + 2), vs_get(base + 8)])
    call vs_set(base + 7, kids)
    kids = gcv_conj(vs_get(base + 7), vs_get(base + 8), [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 7, kids)
    kids = analyze_all(vs_get(base + 6), vs_get(base + 2), [vs_get(base + 1), vs_get(base + 7)])
    call vs_set(base + 8, kids)
    if (has_error) then
       call vs_leave(base)
       return
    end if
    kids = concat_vecs(vs_get(base + 7), vs_get(base + 8), [vs_get(base + 1), vs_get(base + 2)])
    call vs_set(base + 7, kids)
    fnv = instance_member(mname, vs_get(base + 1))
    if (has_error) then
       call gce_clear_error()
       fnv = gc_nil()
    end if
    call vs_set(base + 8, fnv)
    nd = mk_node(N_DOT, vs_get(base + 7), vs_get(base + 5), vs_get(base + 8), &
         merge(1, 0, is_call), [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_dot

  ! (new Class args...). A deftype constructs directly (N_NEWTYPE, by
  ! name, looked up at run time so a redefined type is found); a host
  ! class goes to eval_new with its arguments evaluated (N_NEW).
  recursive function analyze_new(form, sc) result(nd)
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, cls, kids, args
    integer :: base
    nd = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, form)
    call vs_set(base + 2, sc)
    args = gcl_rest(form, [vs_get(base + 1)])
    call vs_set(base + 3, args)
    cls = strip_meta(gcl_first(vs_get(base + 3)))
    if (cls%tag /= GCT_SYM) then
       call fail("new needs a class name")
       call vs_leave(base)
       return
    end if
    call vs_set(base + 4, cls)
    kids = analyze_all(gcl_rest(vs_get(base + 3), [vs_get(base + 1)]), vs_get(base + 2), &
         [vs_get(base + 1), vs_get(base + 4)])
    call vs_set(base + 5, kids)
    if (has_error) then
       call vs_leave(base)
       return
    end if
    if (gc_kind(find_type(gc_ref_text(cls%ref))) == OBJ_TYPE) then
       nd = mk_node(N_NEWTYPE, vs_get(base + 5), vs_get(base + 4), gc_nil(), 0, [vs_get(base + 1), vs_get(base + 2)])
    else
       nd = mk_node(N_NEW, vs_get(base + 5), vs_get(base + 4), gc_nil(), 0, [vs_get(base + 1), vs_get(base + 2)])
    end if
    call vs_leave(base)
  end function analyze_new

  function concat_vecs(a, b, roots) result(out)
    type(gc_value), intent(in) :: a, b
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base, i
    base = vs_enter(3)
    call vs_set(base + 1, a)
    call vs_set(base + 2, b)
    call vs_set(base + 3, a)
    do i = 0, gcv_count(b) - 1
       out = gcv_conj(vs_get(base + 3), gcv_nth(vs_get(base + 2), i), [roots, vs_get(base + 1), vs_get(base + 2)])
       call vs_set(base + 3, out)
    end do
    out = vs_get(base + 3)
    call vs_leave(base)
  end function concat_vecs

  ! --- special forms -------------------------------------------------

  recursive function analyze_special(head, form, sc) result(nd)
    type(gc_value), intent(in) :: head, form, sc
    type(gc_value) :: nd, rest
    integer :: base

    nd = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, form)
    call vs_set(base + 2, sc)
    rest = gcl_rest(form, [vs_get(base + 1)])
    call vs_set(base + 3, rest)

    if (gc_ref_is(head%ref, "quote")) then
       nd = const_node(gcl_first(vs_get(base + 3)), [vs_get(base + 1), vs_get(base + 2)])
    else if (gc_ref_is(head%ref, "if")) then
       nd = analyze_if(vs_get(base + 3), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "do")) then
       nd = analyze_body(vs_get(base + 3), vs_get(base + 2), [vs_get(base + 1)])
    else if (gc_ref_is(head%ref, "def")) then
       nd = analyze_def(vs_get(base + 3), vs_get(base + 2), .false.)
    else if (gc_ref_is(head%ref, "defmacro*")) then
       nd = analyze_def(vs_get(base + 3), vs_get(base + 2), .true.)
    else if (gc_ref_is(head%ref, "let*")) then
       nd = analyze_let(vs_get(base + 3), vs_get(base + 2), .false.)
    else if (gc_ref_is(head%ref, "loop*")) then
       nd = analyze_let(vs_get(base + 3), vs_get(base + 2), .true.)
    else if (gc_ref_is(head%ref, "letfn*")) then
       nd = analyze_letfn(vs_get(base + 3), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "fn*")) then
       nd = analyze_fn(vs_get(base + 3), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "recur")) then
       nd = analyze_recur(vs_get(base + 3), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "var")) then
       nd = analyze_varq(vs_get(base + 3), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "lazy-seq*")) then
       nd = analyze_lazy(vs_get(base + 3), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "throw")) then
       nd = analyze_one(N_THROW, gcl_first(vs_get(base + 3)), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "try")) then
       nd = analyze_try(vs_get(base + 3), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "case*")) then
       nd = analyze_case(vs_get(base + 3), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "deftype*")) then
       nd = analyze_deftype(vs_get(base + 3), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "reify*")) then
       nd = analyze_reify(vs_get(base + 3), vs_get(base + 2), .false.)
    else if (gc_ref_is(head%ref, "proxy")) then
       nd = analyze_reify(vs_get(base + 3), vs_get(base + 2), .true.)
    else if (gc_ref_is(head%ref, "quasiquote")) then
       nd = analyze_quasiquote(vs_get(base + 3), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "monitor-enter") .or. gc_ref_is(head%ref, "monitor-exit")) then
       ! One thread: the lock expression is evaluated and that is all.
       nd = analyze_one(N_DO, gcl_first(vs_get(base + 3)), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "clojure.core/import*")) then
       ! Records the short name, at analysis like a def; see record_import.
       block
         type(gc_value) :: cn
         cn = strip_meta(gcl_first(vs_get(base + 3)))
         if (cn%tag == GCT_STR .or. cn%tag == GCT_SYM) call record_import(gc_ref_text(cn%ref))
       end block
       nd = const_node(gc_nil(), [vs_get(base + 1), vs_get(base + 2)])
    else if (gc_ref_is(head%ref, "set!")) then
       nd = analyze_setbang(vs_get(base + 3), vs_get(base + 2))
    else if (gc_ref_is(head%ref, "new")) then
       nd = analyze_new(vs_get(base + 1), vs_get(base + 2))
    else if (gc_ref_is(head%ref, ".")) then
       nd = analyze_dot(vs_get(base + 1), vs_get(base + 2))
    else
       call fail("unknown special form: " // gc_ref_text(head%ref))
    end if
    call vs_leave(base)
  end function analyze_special

  ! A node of `kind` with one child.
  recursive function analyze_one(kind, form, sc) result(nd)
    integer, intent(in) :: kind
    type(gc_value), intent(in) :: form, sc
    type(gc_value) :: nd, c, kids
    integer :: base
    nd = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, form)
    call vs_set(base + 2, sc)
    c = analyze(vs_get(base + 1), vs_get(base + 2))
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, c)
    kids = gcv_conj(gcv_empty([vs_get(base + 3)]), vs_get(base + 3), [vs_get(base + 3)])
    call vs_set(base + 3, kids)
    nd = mk_node(kind, vs_get(base + 3), gc_nil(), gc_nil(), 0, [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_one

  recursive function analyze_if(rest, sc) result(nd)
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, kids
    integer :: base
    nd = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    if (gcl_count(rest) < 2 .or. gcl_count(rest) > 3) then
       call fail("if takes two or three forms")
       call vs_leave(base)
       return
    end if
    kids = analyze_all(vs_get(base + 1), vs_get(base + 2), [vs_get(base + 1)])
    call vs_set(base + 3, kids)
    if (.not. has_error) nd = mk_node(N_IF, vs_get(base + 3), gc_nil(), gc_nil(), 0, &
         [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_if

  ! (def name init?) -- the Var is INTERNED NOW, unbound if new, so a
  ! recursive reference in the init resolves, as DefExpr does. Its
  ! metadata (evaluated, like Compiler does) and init are children.
  ! i2: bit 1 = has an init, bit 2 = defmacro*.
  recursive function analyze_def(rest, sc, is_macro) result(nd)
    type(gc_value), intent(in) :: rest, sc
    logical, intent(in) :: is_macro
    type(gc_value) :: nd, nm, md, var, kids, c
    integer :: base, flags

    nd = gc_nil()
    base = vs_enter(6)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    nm = gcl_first(rest)
    md = gc_nil()
    if (gc_kind(nm) == OBJ_META) then
       md = gc_slot(nm, 2)
       nm = strip_meta(nm)
    end if
    if (nm%tag /= GCT_SYM) then
       call fail("def needs a symbol")
       call vs_leave(base)
       return
    end if
    ! A qualified name -- (def ns/x ...) -- is allowed only for the
    ! current namespace, and defines the bare name: DefExpr's rule. A
    ! def inside a syntax-quote template arrives this way, as
    ! clojure.pprint's defdirectives does.
    call vs_set(base + 4, md)
    block
      character(len=:), allocatable :: t
      integer :: sl
      t = gc_ref_text(nm%ref)
      sl = index(t, "/")
      if (sl > 1 .and. sl < len(t)) then
         if (t(1:sl-1) /= gcn_name(gcn_current([vs_get(base + 1)]))) then
            call fail("Can't create defs outside of current ns: " // t)
            call vs_leave(base)
            return
         end if
         nm = gc_sym(t(sl+1:), [vs_get(base + 1), vs_get(base + 4)])
      end if
    end block
    call vs_set(base + 3, nm)
    var = gcn_lookup(gcn_current([vs_get(base + 1)]), vs_get(base + 3))
    if (.not. gcn_is_var(var)) then
       var = gcn_intern(gcn_current([vs_get(base + 1)]), vs_get(base + 3), gc_nil(), &
            [vs_get(base + 1), vs_get(base + 3)])
       call gc_set_i1(var, 0)
    end if
    call vs_set(base + 5, var)

    flags = 0
    if (is_macro) flags = 2
    kids = gcv_empty([vs_get(base + 1), vs_get(base + 5)])
    call vs_set(base + 6, kids)
    if (gcl_count(rest) > 1) then
       flags = flags + 1
       c = analyze(gcl_first(gcl_rest(vs_get(base + 1), [vs_get(base + 1)])), vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       kids = gcv_conj(vs_get(base + 6), c, [vs_get(base + 1), vs_get(base + 5), c])
       call vs_set(base + 6, kids)
    end if
    if (md%tag /= GCT_NIL) then
       c = analyze(vs_get(base + 4), vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
    else
       c = gc_nil()
    end if
    nd = mk_node(N_DEF, vs_get(base + 6), vs_get(base + 5), c, flags, [vs_get(base + 1), vs_get(base + 2), c])
    call vs_leave(base)
  end function analyze_def

  ! let* and loop*: a child block, n slots reserved together, each init
  ! analysed BEFORE its name is bound (sequential scope), then the body.
  ! Children: [init_0 .. init_{n-1}, body]; slot 3 = the first slot as
  ! an int; i2 = n. A loop is also a recur target for its body.
  recursive function analyze_let(rest, sc, is_loop) result(nd)
    type(gc_value), intent(in) :: rest, sc
    logical, intent(in) :: is_loop
    type(gc_value) :: nd, binds, blk, kids, c, k, rinfo
    integer :: base, i, n, start

    nd = gc_nil()
    base = vs_enter(6)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    binds = strip_meta(gcl_first(rest))
    if (.not. gcv_is(binds)) then
       call fail("let needs a vector of bindings")
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, binds)
    n = gcv_count(binds)
    if (mod(n, 2) /= 0) then
       call fail("let* needs an even number of binding forms")
       call vs_leave(base)
       return
    end if
    n = n / 2
    blk = child_scope(vs_get(base + 2), [vs_get(base + 1), vs_get(base + 3)])
    call vs_set(base + 4, blk)
    start = reserve_slots(vs_get(base + 4), n)
    if (is_loop) then
       rinfo = int_vec([0, start, n], [vs_get(base + 1), vs_get(base + 4)])
       call gc_set_slot(vs_get(base + 4), 4, rinfo)
    end if
    kids = gcv_empty([vs_get(base + 1), vs_get(base + 4)])
    call vs_set(base + 5, kids)
    do i = 0, n - 1
       c = analyze(gcv_nth(vs_get(base + 3), 2 * i + 1), vs_get(base + 4))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       kids = gcv_conj(vs_get(base + 5), c, [vs_get(base + 1), vs_get(base + 4), c])
       call vs_set(base + 5, kids)
       k = strip_meta(gcv_nth(vs_get(base + 3), 2 * i))
       if (k%tag /= GCT_SYM) then
          call fail("let* needs a symbol to bind")
          call vs_leave(base)
          return
       end if
       call bind_name(vs_get(base + 4), k, start + i, [vs_get(base + 1), vs_get(base + 5)])
    end do
    c = analyze_body(gcl_rest(vs_get(base + 1), [vs_get(base + 1)]), vs_get(base + 4), &
         [vs_get(base + 1), vs_get(base + 5)])
    if (has_error) then
       call vs_leave(base)
       return
    end if
    kids = gcv_conj(vs_get(base + 5), c, [vs_get(base + 1), vs_get(base + 4), c])
    call vs_set(base + 5, kids)
    nd = mk_node(merge(N_LOOP, N_LET, is_loop), vs_get(base + 5), gc_int(start), gc_nil(), n, &
         [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_let

  ! A persistent vector of ints.
  function int_vec(ints, roots) result(out)
    integer, intent(in) :: ints(:)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: out
    integer :: base, i
    base = vs_enter(1)
    out = gcv_empty(roots)
    call vs_set(base + 1, out)
    do i = 1, size(ints)
       out = gcv_conj(vs_get(base + 1), gc_int(ints(i)), roots)
       call vs_set(base + 1, out)
    end do
    out = vs_get(base + 1)
    call vs_leave(base)
  end function int_vec

  ! (letfn* [name (fn* ...) ...] body): every name in scope in every
  ! init. Children: [fn_0 .. fn_{n-1}, body]; slot 2 = first slot; i2 = n.
  recursive function analyze_letfn(rest, sc) result(nd)
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, binds, blk, kids, c, k
    integer :: base, i, n, start

    nd = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    binds = strip_meta(gcl_first(rest))
    if (.not. gcv_is(binds)) then
       call fail("letfn* needs a vector of bindings")
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, binds)
    n = gcv_count(binds)
    if (mod(n, 2) /= 0) then
       call fail("letfn* needs an even number of binding forms")
       call vs_leave(base)
       return
    end if
    n = n / 2
    blk = child_scope(vs_get(base + 2), [vs_get(base + 1), vs_get(base + 3)])
    call vs_set(base + 4, blk)
    start = reserve_slots(vs_get(base + 4), n)
    do i = 0, n - 1
       k = strip_meta(gcv_nth(vs_get(base + 3), 2 * i))
       if (k%tag /= GCT_SYM) then
          call fail("letfn* needs a symbol to bind")
          call vs_leave(base)
          return
       end if
       call bind_name(vs_get(base + 4), k, start + i, [vs_get(base + 1)])
    end do
    kids = gcv_empty([vs_get(base + 1), vs_get(base + 4)])
    call vs_set(base + 5, kids)
    do i = 0, n - 1
       c = analyze(gcv_nth(vs_get(base + 3), 2 * i + 1), vs_get(base + 4))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       kids = gcv_conj(vs_get(base + 5), c, [vs_get(base + 1), vs_get(base + 4), c])
       call vs_set(base + 5, kids)
    end do
    c = analyze_body(gcl_rest(vs_get(base + 1), [vs_get(base + 1)]), vs_get(base + 4), &
         [vs_get(base + 1), vs_get(base + 5)])
    if (has_error) then
       call vs_leave(base)
       return
    end if
    kids = gcv_conj(vs_get(base + 5), c, [vs_get(base + 1), vs_get(base + 4), c])
    call vs_set(base + 5, kids)
    nd = mk_node(N_LETFN, vs_get(base + 5), gc_int(start), gc_nil(), n, [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
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
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, head, name, fsc, arities, clauses, clause, ar, tmpl, walk
    integer :: base, self_slot, nfixed, i

    nd = gc_nil()
    base = vs_enter(8)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    head = strip_meta(gcl_first(rest))
    name = gc_nil()
    call vs_set(base + 3, rest)
    if (head%tag == GCT_SYM) then
       name = head
       call vs_set(base + 3, gcl_rest(vs_get(base + 1), [vs_get(base + 1)]))
    end if
    call vs_set(base + 4, name)
    fsc = new_fn_scope(vs_get(base + 2), [vs_get(base + 1), vs_get(base + 4)])
    call vs_set(base + 5, fsc)
    self_slot = -1
    if (name%tag == GCT_SYM) then
       self_slot = declare_local(vs_get(base + 5), vs_get(base + 4), [vs_get(base + 1)])
       call gc_set_i2(scope_info(vs_get(base + 5)), self_slot)
    end if

    ! One arity or several: (fn* [..] ..) versus (fn* ([..] ..) ...)
    head = strip_meta(gcl_first(vs_get(base + 3)))
    if (gcv_is(head)) then
       ! single arity: the whole rest is the one clause
       call vs_set(base + 6, gcl_cons(vs_get(base + 3), gcl_empty([vs_get(base + 3)]), [vs_get(base + 3)]))
    else
       call vs_set(base + 6, vs_get(base + 3))
    end if
    arities = gcv_empty([vs_get(base + 1), vs_get(base + 5), vs_get(base + 6)])
    call vs_set(base + 7, arities)
    walk = vs_get(base + 6)
    call vs_set(base + 8, walk)
    do while (gcl_count(vs_get(base + 8)) > 0)
       clause = norm_form(strip_meta(gcl_first(vs_get(base + 8))), [vs_get(base + 7), vs_get(base + 8)])
       ar = analyze_arity(clause, vs_get(base + 5))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       arities = gcv_conj(vs_get(base + 7), ar, [vs_get(base + 1), vs_get(base + 5), ar])
       call vs_set(base + 7, arities)
       walk = gcl_rest(vs_get(base + 8), [vs_get(base + 7)])
       call vs_set(base + 8, walk)
    end do

    ! locals clearing, per arity, now that the frame size is known
    do i = 0, gcv_count(vs_get(base + 7)) - 1
       call apply_clears(gcv_nth(gcv_nth(vs_get(base + 7), i), 3), gc_i1(scope_info(vs_get(base + 5))))
    end do

    ! [name arities captures nslots selfslot slotnames]
    tmpl = gcv_empty([vs_get(base + 1), vs_get(base + 5), vs_get(base + 7)])
    call vs_set(base + 8, tmpl)
    tmpl = gcv_conj(vs_get(base + 8), vs_get(base + 4), [vs_get(base + 5), vs_get(base + 7)])
    call vs_set(base + 8, tmpl)
    tmpl = gcv_conj(vs_get(base + 8), vs_get(base + 7), [vs_get(base + 5)])
    call vs_set(base + 8, tmpl)
    tmpl = gcv_conj(vs_get(base + 8), gc_slot(scope_info(vs_get(base + 5)), 1), [vs_get(base + 5)])
    call vs_set(base + 8, tmpl)
    tmpl = gcv_conj(vs_get(base + 8), gc_int(gc_i1(scope_info(vs_get(base + 5)))), [vs_get(base + 5)])
    call vs_set(base + 8, tmpl)
    tmpl = gcv_conj(vs_get(base + 8), gc_int(self_slot), [vs_get(base + 5)])
    call vs_set(base + 8, tmpl)
    ! slot -> name, for the debugger; an empty map when the fn has no
    ! named locals at all
    block
      type(gc_value) :: nm
      nm = gc_slot(scope_info(vs_get(base + 5)), 4)
      if (.not. gca_is(nm)) nm = gca_empty([vs_get(base + 5), vs_get(base + 8)])
      tmpl = gcv_conj(vs_get(base + 8), nm, [vs_get(base + 5)])
      call vs_set(base + 8, tmpl)
    end block
    nd = mk_node(N_FN, gc_nil(), vs_get(base + 8), gc_nil(), 0, [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_fn

  ! ([params] body...) -> [nfixed variadic? first-slot body]
  recursive function analyze_arity(clause, fsc) result(ar)
    type(gc_value), intent(in) :: clause, fsc
    type(gc_value) :: ar, params, blk, p, body, rinfo
    integer :: base, i, n, amp, start, nfixed
    logical :: variadic

    ar = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, clause)
    call vs_set(base + 2, fsc)
    params = strip_meta(gcl_first(clause))
    if (.not. gcv_is(params)) then
       call fail("fn* needs a parameter vector")
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, params)
    n = gcv_count(params)
    amp = -1
    do i = 0, n - 1
       p = strip_meta(gcv_nth(params, i))
       if (p%tag == GCT_SYM) then
          if (gc_ref_is(p%ref, "&")) then
             amp = i
             exit
          end if
       end if
    end do
    variadic = (amp >= 0)
    if (variadic) then
       if (amp + 2 /= n) then
          call fail("& must be followed by exactly one name")
          call vs_leave(base)
          return
       end if
       nfixed = amp
    else
       nfixed = n
    end if
    blk = child_scope(vs_get(base + 2), [vs_get(base + 1), vs_get(base + 3)])
    call vs_set(base + 4, blk)
    start = reserve_slots(vs_get(base + 4), merge(nfixed + 1, nfixed, variadic))
    do i = 0, nfixed - 1
       p = strip_meta(gcv_nth(vs_get(base + 3), i))
       if (p%tag /= GCT_SYM) then
          call fail("fn* parameter must be a symbol")
          call vs_leave(base)
          return
       end if
       call bind_name(vs_get(base + 4), p, start + i, [vs_get(base + 1)])
    end do
    if (variadic) then
       p = strip_meta(gcv_nth(vs_get(base + 3), amp + 1))
       call bind_name(vs_get(base + 4), p, start + nfixed, [vs_get(base + 1)])
    end if
    ! The body is a recur target: kind 1 fixed, 2 variadic.
    rinfo = int_vec([merge(2, 1, variadic), start, merge(nfixed + 1, nfixed, variadic)], &
         [vs_get(base + 1), vs_get(base + 4)])
    call gc_set_slot(vs_get(base + 4), 4, rinfo)
    body = analyze_body(gcl_rest(vs_get(base + 1), [vs_get(base + 1)]), vs_get(base + 4), &
         [vs_get(base + 1), vs_get(base + 2)])
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 5, body)
    ar = gcv_empty([vs_get(base + 5)])
    ar = gcv_conj(ar, gc_int(nfixed), [vs_get(base + 5), ar])
    ar = gcv_conj(ar, gc_bool(variadic), [vs_get(base + 5), ar])
    ar = gcv_conj(ar, gc_int(start), [vs_get(base + 5), ar])
    ar = gcv_conj(ar, vs_get(base + 5), [vs_get(base + 5), ar])
    call vs_leave(base)
  end function analyze_arity

  ! (recur args...) -> the nearest loop or fn. Slot 2 = [kind start n].
  recursive function analyze_recur(rest, sc) result(nd)
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, kids, rinfo
    integer :: base, n
    nd = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    rinfo = gc_slot(sc, 4)
    if (.not. gcv_is(rinfo)) then
       call fail("Can only recur from tail position of a loop or fn")
       call vs_leave(base)
       return
    end if
    n = int_of(gcv_nth(rinfo, 2))
    if (gcl_count(rest) /= n) then
       call fail("recur has the wrong number of arguments")
       call vs_leave(base)
       return
    end if
    kids = analyze_all(vs_get(base + 1), vs_get(base + 2), [vs_get(base + 1)])
    call vs_set(base + 3, kids)
    if (.not. has_error) nd = mk_node(N_RECUR, vs_get(base + 3), gc_slot(vs_get(base + 2), 4), gc_nil(), n, &
         [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_recur

  ! (var sym) -> the Var itself, resolved now.
  recursive function analyze_varq(rest, sc) result(nd)
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, sym, var
    integer :: base
    nd = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    sym = strip_meta(gcl_first(rest))
    if (sym%tag /= GCT_SYM) then
       call fail("var needs a symbol")
       call vs_leave(base)
       return
    end if
    var = resolve_var(sym, gc_nil())
    if (.not. gcn_is_var(var)) then
       call fail("Unable to resolve var: " // gc_ref_text(sym%ref))
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, var)
    nd = const_node(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_varq

  ! (lazy-seq* body...) -> a no-argument fn whose closure becomes the
  ! thunk of a pending lazy seq.
  recursive function analyze_lazy(rest, sc) result(nd)
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, fnform, fnode
    integer :: base
    nd = gc_nil()
    base = vs_enter(4)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    ! ([] body...) as the single clause of a fn*
    fnform = gcl_cons(gcv_empty([vs_get(base + 1)]), vs_get(base + 1), [vs_get(base + 1)])
    call vs_set(base + 3, fnform)
    fnode = analyze_fn(vs_get(base + 3), vs_get(base + 2))
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 4, fnode)
    nd = mk_node(N_LAZY, gc_nil(), gc_slot(vs_get(base + 4), 2), gc_nil(), 0, [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_lazy

  ! (try body* (catch Class name body*)* (finally body*)?)
  ! Children: [body, finally-or-nil]; slot 2 = catches, each
  ! [class-symbol, slot, body].
  recursive function analyze_try(rest, sc) result(nd)
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, body, fin, catches, item, cl, blk, cb, kids, cname
    integer :: base, i, n, slot

    nd = gc_nil()
    base = vs_enter(8)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    n = gcl_count(rest)
    body = gcl_empty([vs_get(base + 1)])
    call vs_set(base + 3, body)
    ! body forms, kept in order: collect then reverse via cons
    do i = n - 1, 0, -1
       item = norm_form(nth_of(vs_get(base + 1), i), [vs_get(base + 1), vs_get(base + 3)])
       if (is_clause(item, "catch") .or. is_clause(item, "finally")) cycle
       call vs_set(base + 4, item)
       body = gcl_cons(vs_get(base + 4), vs_get(base + 3), [vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
       call vs_set(base + 3, body)
    end do
    ! only the LEADING body forms are the body; a form after a catch is
    ! ignored by Clojure too (it is an error there). Simplification: all
    ! non-clause forms are body forms.
    body = analyze_body(vs_get(base + 3), vs_get(base + 2), [vs_get(base + 1)])
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, body)

    catches = gcv_empty([vs_get(base + 1), vs_get(base + 3)])
    call vs_set(base + 5, catches)
    fin = gc_nil()
    call vs_set(base + 6, fin)
    do i = 0, n - 1
       item = norm_form(nth_of(vs_get(base + 1), i), [vs_get(base + 1), vs_get(base + 5), vs_get(base + 6)])
       call vs_set(base + 4, item)
       if (is_clause(item, "catch")) then
          if (gcl_count(item) < 3) cycle
          cname = strip_meta(nth_of(vs_get(base + 4), 1))
          call vs_set(base + 7, cname)
          blk = child_scope(vs_get(base + 2), [vs_get(base + 1), vs_get(base + 5), vs_get(base + 7)])
          call vs_set(base + 8, blk)
          slot = declare_local(vs_get(base + 8), strip_meta(nth_of(vs_get(base + 4), 2)), [vs_get(base + 1)])
          cb = analyze_body(gcl_rest(gcl_rest(gcl_rest(vs_get(base + 4), [vs_get(base + 1)]), &
               [vs_get(base + 1)]), [vs_get(base + 1)]), vs_get(base + 8), [vs_get(base + 1), vs_get(base + 5)])
          if (has_error) then
             call vs_leave(base)
             return
          end if
          call vs_set(base + 8, cb)
          cl = gcv_empty([vs_get(base + 1), vs_get(base + 5), vs_get(base + 7), vs_get(base + 8)])
          cl = gcv_conj(cl, vs_get(base + 7), [vs_get(base + 5), vs_get(base + 8), cl])
          cl = gcv_conj(cl, gc_int(slot), [vs_get(base + 5), vs_get(base + 8), cl])
          cl = gcv_conj(cl, vs_get(base + 8), [vs_get(base + 5), cl])
          catches = gcv_conj(vs_get(base + 5), cl, [vs_get(base + 1), cl])
          call vs_set(base + 5, catches)
       else if (is_clause(item, "finally")) then
          fin = analyze_body(gcl_rest(vs_get(base + 4), [vs_get(base + 1)]), vs_get(base + 2), &
               [vs_get(base + 1), vs_get(base + 5)])
          if (has_error) then
             call vs_leave(base)
             return
          end if
          call vs_set(base + 6, fin)
       end if
    end do
    kids = gcv_empty([vs_get(base + 1), vs_get(base + 3), vs_get(base + 5), vs_get(base + 6)])
    kids = gcv_conj(kids, vs_get(base + 3), [vs_get(base + 5), vs_get(base + 6), kids])
    kids = gcv_conj(kids, vs_get(base + 6), [vs_get(base + 5), kids])
    call vs_set(base + 7, kids)
    nd = mk_node(N_TRY, vs_get(base + 7), vs_get(base + 5), gc_nil(), 0, [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_try

  ! (case* expr shift mask default map table-type test-type skip-check?)
  ! Children: [expr, default]; slot 2 = the map with each [test then]
  ! rebuilt as [test then-node]; slot 3 = [shift mask test-type skip].
  recursive function analyze_case(rest, sc) result(nd)
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, kids, c, tbl, entry, ent2, mp, tn, info, skip
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i, n

    nd = gc_nil()
    base = vs_enter(8)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    n = gcl_count(rest)
    if (n < 7) then
       call fail("case* needs 7 or 8 forms")
       call vs_leave(base)
       return
    end if
    kids = gcv_empty([vs_get(base + 1)])
    call vs_set(base + 3, kids)
    c = analyze(nth_of(vs_get(base + 1), 0), vs_get(base + 2))
    if (has_error) then
       call vs_leave(base)
       return
    end if
    kids = gcv_conj(vs_get(base + 3), c, [vs_get(base + 1), c])
    call vs_set(base + 3, kids)
    c = analyze(nth_of(vs_get(base + 1), 3), vs_get(base + 2))
    if (has_error) then
       call vs_leave(base)
       return
    end if
    kids = gcv_conj(vs_get(base + 3), c, [vs_get(base + 1), c])
    call vs_set(base + 3, kids)

    tbl = strip_meta(nth_of(vs_get(base + 1), 4))
    call vs_set(base + 4, tbl)
    mp = gca_empty([vs_get(base + 1), vs_get(base + 3), vs_get(base + 4)])
    call vs_set(base + 5, mp)
    call gca_entries(vs_get(base + 4), ks, vls)
    do i = 1, size(ks)
       entry = strip_meta(vls(i))
       call vs_set(base + 6, entry)
       if (.not. (gcv_is(entry) .and. gcv_count(entry) == 2)) cycle
       tn = analyze(gcv_nth(vs_get(base + 6), 1), vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       call vs_set(base + 7, tn)
       ent2 = gcv_empty([vs_get(base + 5), vs_get(base + 6), vs_get(base + 7)])
       ent2 = gcv_conj(ent2, gcv_nth(vs_get(base + 6), 0), [vs_get(base + 5), vs_get(base + 7), ent2])
       ent2 = gcv_conj(ent2, vs_get(base + 7), [vs_get(base + 5), ent2])
       call vs_set(base + 8, ent2)
       mp = gca_assoc(vs_get(base + 5), ks(i), vs_get(base + 8), [vs_get(base + 1), vs_get(base + 5), vs_get(base + 8)])
       call vs_set(base + 5, mp)
    end do
    skip = gc_nil()
    if (n >= 8) skip = strip_meta(nth_of(vs_get(base + 1), 7))
    call vs_set(base + 6, skip)
    info = gcv_empty([vs_get(base + 1), vs_get(base + 3), vs_get(base + 5), vs_get(base + 6)])
    info = gcv_conj(info, gc_int(ival_of(nth_of(vs_get(base + 1), 1))), [vs_get(base + 5), vs_get(base + 6), info])
    info = gcv_conj(info, gc_int(ival_of(nth_of(vs_get(base + 1), 2))), [vs_get(base + 5), vs_get(base + 6), info])
    info = gcv_conj(info, strip_meta(nth_of(vs_get(base + 1), 6)), [vs_get(base + 5), vs_get(base + 6), info])
    info = gcv_conj(info, vs_get(base + 6), [vs_get(base + 5), info])
    call vs_set(base + 7, info)
    nd = mk_node(N_CASE, vs_get(base + 3), vs_get(base + 5), vs_get(base + 7), 0, [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_case

  ! (deftype* tagname classname [fields] :implements [ifaces] opts (method [this args] body)*)
  ! Slot 2 = spec [class-text fields ifaces names fn-nodes]; i2 = 0.
  recursive function analyze_deftype(rest, sc) result(nd)
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, w, cname, k, fields, ifaces, spec
    integer :: base

    nd = gc_nil()
    base = vs_enter(6)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    w = gcl_rest(vs_get(base + 1), [vs_get(base + 1)])
    call vs_set(base + 3, w)
    cname = strip_meta(gcl_first(vs_get(base + 3)))
    if (cname%tag /= GCT_SYM) then
       call fail("deftype* needs a class name")
       call vs_leave(base)
       return
    end if
    call vs_set(base + 4, cname)
    w = gcl_rest(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 4)])
    call vs_set(base + 3, w)
    fields = strip_meta(gcl_first(vs_get(base + 3)))
    call vs_set(base + 5, fields)
    w = gcl_rest(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 4), vs_get(base + 5)])
    call vs_set(base + 3, w)
    ifaces = gcv_empty([vs_get(base + 1), vs_get(base + 5)])
    call vs_set(base + 6, ifaces)
    do while (gcl_count(vs_get(base + 3)) > 0)
       k = strip_meta(gcl_first(vs_get(base + 3)))
       if (k%tag /= GCT_KEY) exit
       w = gcl_rest(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 6)])
       call vs_set(base + 3, w)
       if (gc_ref_is(k%ref, "implements")) call vs_set(base + 6, strip_meta(gcl_first(vs_get(base + 3))))
       w = gcl_rest(vs_get(base + 3), [vs_get(base + 1), vs_get(base + 6)])
       call vs_set(base + 3, w)
    end do
    spec = type_spec(class_of_text(vs_get(base + 4)), vs_get(base + 5), vs_get(base + 6), &
         vs_get(base + 3), vs_get(base + 2))
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 6, spec)
    nd = mk_node(N_DEFTYPE, gc_nil(), vs_get(base + 6), gc_nil(), 0, [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_deftype

  ! (reify* [ifaces] (method [this args] body)*) and
  ! (proxy [supers] [ctor-args] (name [args] body)*): a nameless type,
  ! instantiated on the spot. i2 = 1.
  recursive function analyze_reify(rest, sc, is_proxy) result(nd)
    type(gc_value), intent(in) :: rest, sc
    logical, intent(in) :: is_proxy
    type(gc_value) :: nd, ifaces, methods, spec
    character(len=24) :: buf
    integer :: base

    nd = gc_nil()
    base = vs_enter(6)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    ifaces = strip_meta(gcl_first(rest))
    call vs_set(base + 3, ifaces)
    methods = gcl_rest(vs_get(base + 1), [vs_get(base + 1), vs_get(base + 3)])
    call vs_set(base + 4, methods)
    if (is_proxy) then
       if (.not. gcv_is(vs_get(base + 3))) then
          call fail("proxy needs a vector of superclasses")
          call vs_leave(base)
          return
       end if
       methods = gcl_rest(vs_get(base + 4), [vs_get(base + 3), vs_get(base + 4)])   ! past ctor args
       call vs_set(base + 4, methods)
       methods = proxy_methods(vs_get(base + 4), [vs_get(base + 3)])
       if (has_error) then
          call vs_leave(base)
          return
       end if
       call vs_set(base + 4, methods)
       proxy_id = proxy_id + 1
       write(buf, '(I0)') proxy_id
       buf = "clotran.proxy__" // trim(buf)
    else
       reify_id = reify_id + 1
       write(buf, '(I0)') reify_id
       buf = "clotran.reify__" // trim(buf)
    end if
    call vs_set(base + 5, gcv_empty([vs_get(base + 3), vs_get(base + 4)]))
    spec = type_spec(trim(buf), vs_get(base + 5), vs_get(base + 3), vs_get(base + 4), vs_get(base + 2))
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 6, spec)
    nd = mk_node(N_DEFTYPE, gc_nil(), vs_get(base + 6), gc_nil(), 1, [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_reify

  ! A type's spec: [class-text fields iface-keys names fn-nodes]. Method
  ! forms sharing a name become the clauses of ONE fn*, each with the
  ! type's fields bound around its body (method_clauses, bind_fields),
  ! and that fn* is analysed in the enclosing scope -- which is what
  ! lets a reify body close over its surroundings.
  recursive function type_spec(cname, fields, ifaces, methods, sc) result(spec)
    character(len=*), intent(in) :: cname
    type(gc_value), intent(in) :: fields, ifaces, methods, sc
    type(gc_value) :: spec, m, mname, names, fns, seen, clauses, fnform, fnode, tmp, keys
    integer :: base

    spec = gc_nil()
    base = vs_enter(10)
    call vs_set(base + 1, fields)
    call vs_set(base + 2, ifaces)
    call vs_set(base + 3, methods)
    call vs_set(base + 4, sc)
    names = gcv_empty([vs_get(base + 1), vs_get(base + 3)])
    call vs_set(base + 5, names)
    fns = gcv_empty([vs_get(base + 1), vs_get(base + 3), vs_get(base + 5)])
    call vs_set(base + 6, fns)
    seen = gca_empty([vs_get(base + 1), vs_get(base + 3), vs_get(base + 5), vs_get(base + 6)])
    call vs_set(base + 7, seen)
    call vs_set(base + 8, vs_get(base + 3))
    do while (gcl_count(vs_get(base + 8)) > 0)
       m = norm_form(strip_meta(gcl_first(vs_get(base + 8))), [vs_get(base + 5), vs_get(base + 6), vs_get(base + 7), vs_get(base + 8)])
       mname = strip_meta(gcl_first(m))
       if (mname%tag == GCT_SYM) then
          tmp = gc_key(bare_name(mname), [vs_get(base + 5), vs_get(base + 6), vs_get(base + 7), vs_get(base + 8)])
          call vs_set(base + 9, tmp)
          if (.not. gca_contains(vs_get(base + 7), vs_get(base + 9))) then
             clauses = method_clauses(bare_name(mname), vs_get(base + 3), vs_get(base + 1))
             call vs_set(base + 10, clauses)
             fnform = vs_get(base + 10)      ! the clause list IS fn*'s rest
             fnode = analyze_fn(fnform, vs_get(base + 4))
             if (has_error) then
                call vs_leave(base)
                return
             end if
             call vs_set(base + 10, fnode)
             names = gcv_conj(vs_get(base + 5), vs_get(base + 9), [vs_get(base + 6), vs_get(base + 7), vs_get(base + 10)])
             call vs_set(base + 5, names)
             fns = gcv_conj(vs_get(base + 6), vs_get(base + 10), [vs_get(base + 5), vs_get(base + 7)])
             call vs_set(base + 6, fns)
             seen = gca_assoc(vs_get(base + 7), vs_get(base + 9), gc_bool(.true.), &
                  [vs_get(base + 5), vs_get(base + 6), vs_get(base + 9)])
             call vs_set(base + 7, seen)
          end if
       end if
       tmp = gcl_rest(vs_get(base + 8), [vs_get(base + 5), vs_get(base + 6), vs_get(base + 7)])
       call vs_set(base + 8, tmp)
    end do
    keys = iface_keys(vs_get(base + 2))
    call vs_set(base + 8, keys)
    tmp = gc_str(cname, [vs_get(base + 1), vs_get(base + 5), vs_get(base + 6), vs_get(base + 8)])
    call vs_set(base + 9, tmp)
    spec = gcv_empty([vs_get(base + 1), vs_get(base + 5), vs_get(base + 6), vs_get(base + 8), vs_get(base + 9)])
    spec = gcv_conj(spec, vs_get(base + 9), [vs_get(base + 1), vs_get(base + 5), vs_get(base + 6), vs_get(base + 8), spec])
    spec = gcv_conj(spec, vs_get(base + 1), [vs_get(base + 5), vs_get(base + 6), vs_get(base + 8), spec])
    spec = gcv_conj(spec, vs_get(base + 8), [vs_get(base + 5), vs_get(base + 6), spec])
    spec = gcv_conj(spec, vs_get(base + 5), [vs_get(base + 6), spec])
    spec = gcv_conj(spec, vs_get(base + 6), [spec])
    call vs_leave(base)
  end function type_spec

  ! `x -> expanded to cons/concat calls, then analysed. Done here, once,
  ! rather than at every evaluation of the macro body that contains it
  ! (DEVIATIONS 6 moves from "at eval time" to "at analysis time").
  recursive function analyze_quasiquote(rest, sc) result(nd)
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, expanded
    integer :: base
    nd = gc_nil()
    base = vs_enter(3)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    if (qq_depth == 0) call gc_global_keep(gensym_root, gca_empty([vs_get(base + 1), vs_get(base + 2)]))
    qq_depth = qq_depth + 1
    expanded = qq_expand(gcl_first(vs_get(base + 1)), gc_nil())
    qq_depth = qq_depth - 1
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, expanded)
    nd = analyze(vs_get(base + 3), vs_get(base + 2))
    call vs_leave(base)
  end function analyze_quasiquote

  ! (set! target value). A symbol target is a Var (resolved now); a
  ! (.field obj) target is a host field write, which for the one field
  ! with storage -- a fn's __methodImplCache -- lands in the closure.
  ! i2: 0 = Var in slot 2, 1 = field; children [obj?, value].
  recursive function analyze_setbang(rest, sc) result(nd)
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, tgt, var, kids, c, objf
    integer :: base
    nd = gc_nil()
    base = vs_enter(5)
    call vs_set(base + 1, rest)
    call vs_set(base + 2, sc)
    tgt = strip_meta(gcl_first(rest))
    call vs_set(base + 3, tgt)
    kids = gcv_empty([vs_get(base + 1), vs_get(base + 3)])
    call vs_set(base + 4, kids)
    if (tgt%tag == GCT_SYM .and. is_static_call(tgt)) then
       ! Class/field: a host static field. There is no storage behind
       ! it; the value is evaluated and the write discarded, as for any
       ! other host field.
       c = analyze(gcl_first(gcl_rest(vs_get(base + 1), [vs_get(base + 1)])), vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       kids = gcv_conj(vs_get(base + 4), c, [vs_get(base + 1), vs_get(base + 3), c])
       call vs_set(base + 4, kids)
       kids = gcv_conj(vs_get(base + 4), vs_get(base + 4), [vs_get(base + 1), vs_get(base + 3)])   ! placeholder obj slot
       call vs_set(base + 4, kids)
       nd = mk_node(N_SETBANG, vs_get(base + 4), gc_nil(), vs_get(base + 3), 3, [vs_get(base + 1), vs_get(base + 2)])
    else if (tgt%tag == GCT_SYM) then
       if (lookup_local(vs_get(base + 2), tgt) >= 0) then
          ! A deftype's mutable field is a local here (bind_fields), and
          ! assigning one is refused -- at RUN time, as before, so that
          ! defrecord's hashCode, which does (set! __hash h), still
          ! defines. DEVIATIONS 20.
          nd = fail_node("Cannot assign to a local: " // gc_ref_text(tgt%ref) // &
               " (mutable deftype fields are not supported, DEVIATIONS 20)", &
               [vs_get(base + 1), vs_get(base + 2)])
          call vs_leave(base)
          return
       end if
       var = resolve_var(tgt, gc_nil())
       if (.not. gcn_is_var(var)) then
          call fail("set! needs a var: " // gc_ref_text(tgt%ref))
          call vs_leave(base)
          return
       end if
       call vs_set(base + 5, var)
       c = analyze(gcl_first(gcl_rest(vs_get(base + 1), [vs_get(base + 1)])), vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       kids = gcv_conj(vs_get(base + 4), c, [vs_get(base + 1), vs_get(base + 5), c])
       call vs_set(base + 4, kids)
       nd = mk_node(N_SETBANG, vs_get(base + 4), vs_get(base + 5), gc_nil(), 0, [vs_get(base + 1), vs_get(base + 2)])
    else if (gcl_is(tgt)) then
       ! (.field obj) -- the object, then the value
       objf = gcl_first(gcl_rest(vs_get(base + 3), [vs_get(base + 1)]))
       call vs_set(base + 5, objf)
       c = analyze(vs_get(base + 5), vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       kids = gcv_conj(vs_get(base + 4), c, [vs_get(base + 1), vs_get(base + 3), c])
       call vs_set(base + 4, kids)
       c = analyze(gcl_first(gcl_rest(vs_get(base + 1), [vs_get(base + 1)])), vs_get(base + 2))
       if (has_error) then
          call vs_leave(base)
          return
       end if
       kids = gcv_conj(vs_get(base + 4), c, [vs_get(base + 1), vs_get(base + 3), c])
       call vs_set(base + 4, kids)
       nd = mk_node(N_SETBANG, vs_get(base + 4), gc_nil(), strip_meta(gcl_first(vs_get(base + 3))), &
            merge(2, 1, is_cache_field(vs_get(base + 3))), [vs_get(base + 1), vs_get(base + 2)])
    else
       call fail("set! needs a var")
    end if
    call vs_leave(base)
  end function analyze_setbang

  ! --- locals clearing -----------------------------------------------
  !
  ! A local is nil-ed after its LAST read, as Clojure's compiler does
  ! ("locals clearing"), so a frame does not pin what it no longer
  ! needs: reduce's own `coll` parameter held the head of the whole
  ! realised range for the length of the reduce, 640 MB at 100000
  ! elements. Conservative rules, each a way a later read could exist:
  !
  !   - a read inside a loop body is never the clearing read, and it
  !     forbids clearing at any earlier read: the body runs again;
  !   - a fn body containing a `recur` to the fn re-runs too, so no
  !     clearing at all in such a body (its parameters are rewritten
  !     by the recur, but a capture is not);
  !   - a slot an inner fn captures is read when the closure is made,
  !     and letfn reads captures a second time, so those slots are
  !     left alone;
  !   - among alternatives (if branches, case branches, catch bodies)
  !     the textually last read wins and the others are not cleared,
  !     which leaks nothing across the whole form and never clears
  !     early on any path.
  !
  ! The pass records the last reading node per slot, then marks it
  ! (slot 3 = true on the N_LOCAL) for the executor to clear.

  ! Backwards liveness. `live(s)` on entry says slot s is read AFTER
  ! this node; on exit it says s is read after OR within it. A read of
  ! a slot that is not live afterwards is the clearing read -- on every
  ! path, since alternatives are processed against the same
  ! after-set and merged.
  recursive subroutine liveness(nd, live)
    type(gc_value), intent(in) :: nd
    logical, intent(inout) :: live(:)
    logical, allocatable :: l1(:), l2(:), reads(:)
    type(gc_value) :: kids, tmpl, caps, catches, cl, spec, fns, mp, entry
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: i, n, s, kind

    if (gc_kind(nd) /= OBJ_AST) return
    kind = gc_i1(nd)
    kids = gc_slot(nd, 1)
    select case (kind)
    case (N_LOCAL)
       s = gc_i2(nd) + 1
       if (s >= 1 .and. s <= size(live)) then
          if (.not. live(s)) call gc_set_slot(nd, 3, gc_bool(.true.))
          live(s) = .true.
       end if
    case (N_FN, N_LAZY)
       ! the closure reads its captures when it is made
       tmpl = gc_slot(nd, 2)
       caps = gcv_nth(tmpl, 2)
       do i = 0, gcv_count(caps) / 2 - 1
          s = int_of(gcv_nth(caps, 2 * i)) + 1
          if (s >= 1 .and. s <= size(live)) live(s) = .true.
       end do
    case (N_DEFTYPE)
       spec = gc_slot(nd, 2)
       fns = gcv_nth(spec, 4)
       do i = gcv_count(fns) - 1, 0, -1
          call liveness(gcv_nth(fns, i), live)
       end do
    case (N_IF)
       l1 = live
       l2 = live
       call liveness(gcv_nth(kids, 1), l1)
       if (gcv_count(kids) > 2) call liveness(gcv_nth(kids, 2), l2)
       live = l1 .or. l2
       call liveness(gcv_nth(kids, 0), live)
    case (N_CASE)
       l1 = live
       mp = gc_slot(nd, 2)
       call gca_entries(mp, ks, vls)
       do i = 1, size(ks)
          entry = strip_meta(vls(i))
          if (gcv_is(entry)) then
             l2 = live
             call liveness(gcv_nth(entry, 1), l2)
             l1 = l1 .or. l2
          end if
       end do
       l2 = live
       call liveness(gcv_nth(kids, 1), l2)
       live = l1 .or. l2
       call liveness(gcv_nth(kids, 0), live)
    case (N_TRY)
       ! finally runs after everything; a catch body can follow any
       ! point of the body
       if (gc_kind(gcv_nth(kids, 1)) == OBJ_AST) call liveness(gcv_nth(kids, 1), live)
       l1 = live
       catches = gc_slot(nd, 2)
       do i = 0, gcv_count(catches) - 1
          cl = gcv_nth(catches, i)
          l2 = live
          call liveness(gcv_nth(cl, 2), l2)
          l1 = l1 .or. l2
       end do
       live = l1
       call liveness(gcv_nth(kids, 0), live)
    case (N_LOOP)
       ! every slot read in the body is live throughout the body -- it
       ! is read again next iteration -- so no read inside is a last
       ! one, and none before the loop is either
       n = gc_i2(nd)
       allocate(reads(size(live)))
       reads = .false.
       call reads_in(gcv_nth(kids, n), reads)
       live = live .or. reads
       call liveness(gcv_nth(kids, n), live)
       do i = n - 1, 0, -1
          call liveness(gcv_nth(kids, i), live)
       end do
    case (N_LETFN)
       n = gc_i2(nd)
       call liveness(gcv_nth(kids, n), live)
       ! the second copy of the captures happens after every fn is made
       do i = 0, n - 1
          tmpl = gc_slot(gcv_nth(kids, i), 2)
          if (.not. gcv_is(tmpl)) cycle
          caps = gcv_nth(tmpl, 2)
          do s = 0, gcv_count(caps) / 2 - 1
             if (int_of(gcv_nth(caps, 2 * s)) + 1 <= size(live)) live(int_of(gcv_nth(caps, 2 * s)) + 1) = .true.
          end do
       end do
       do i = n - 1, 0, -1
          call liveness(gcv_nth(kids, i), live)
       end do
    case (N_DEF)
       if (gc_kind(gc_slot(nd, 3)) == OBJ_AST) call liveness(gc_slot(nd, 3), live)
       if (gcv_is(kids)) then
          do i = gcv_count(kids) - 1, 0, -1
             call liveness(gcv_nth(kids, i), live)
          end do
       end if
    case default
       ! children in evaluation order, so processed backwards
       if (gcv_is(kids)) then
          do i = gcv_count(kids) - 1, 0, -1
             call liveness(gcv_nth(kids, i), live)
          end do
       end if
    end select
  end subroutine liveness

  ! Every slot read anywhere under nd, nested fns excluded (they read
  ! only their captures, at creation, which N_FN accounts for).
  recursive subroutine reads_in(nd, reads)
    type(gc_value), intent(in) :: nd
    logical, intent(inout) :: reads(:)
    type(gc_value) :: kids, tmpl, caps, catches, cl, spec, fns, mp, entry
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: i, s
    if (gc_kind(nd) /= OBJ_AST) return
    kids = gc_slot(nd, 1)
    select case (gc_i1(nd))
    case (N_LOCAL)
       s = gc_i2(nd) + 1
       if (s >= 1 .and. s <= size(reads)) reads(s) = .true.
    case (N_FN, N_LAZY)
       tmpl = gc_slot(nd, 2)
       caps = gcv_nth(tmpl, 2)
       do i = 0, gcv_count(caps) / 2 - 1
          s = int_of(gcv_nth(caps, 2 * i)) + 1
          if (s >= 1 .and. s <= size(reads)) reads(s) = .true.
       end do
    case (N_DEFTYPE)
       spec = gc_slot(nd, 2)
       fns = gcv_nth(spec, 4)
       do i = 0, gcv_count(fns) - 1
          call reads_in(gcv_nth(fns, i), reads)
       end do
    case (N_TRY)
       call reads_in(gcv_nth(kids, 0), reads)
       catches = gc_slot(nd, 2)
       do i = 0, gcv_count(catches) - 1
          cl = gcv_nth(catches, i)
          call reads_in(gcv_nth(cl, 2), reads)
       end do
       if (gc_kind(gcv_nth(kids, 1)) == OBJ_AST) call reads_in(gcv_nth(kids, 1), reads)
    case (N_CASE)
       call reads_in(gcv_nth(kids, 0), reads)
       call reads_in(gcv_nth(kids, 1), reads)
       mp = gc_slot(nd, 2)
       call gca_entries(mp, ks, vls)
       do i = 1, size(ks)
          entry = strip_meta(vls(i))
          if (gcv_is(entry)) call reads_in(gcv_nth(entry, 1), reads)
       end do
    case (N_DEF)
       if (gc_kind(gc_slot(nd, 3)) == OBJ_AST) call reads_in(gc_slot(nd, 3), reads)
       if (gcv_is(kids)) then
          do i = 0, gcv_count(kids) - 1
             call reads_in(gcv_nth(kids, i), reads)
          end do
       end if
    case default
       if (gcv_is(kids)) then
          do i = 0, gcv_count(kids) - 1
             call reads_in(gcv_nth(kids, i), reads)
          end do
       end if
    end select
  end subroutine reads_in

  ! Whether a fn-level recur occurs under nd (nested fns excluded).
  recursive function has_fn_recur(nd) result(yes)
    type(gc_value), intent(in) :: nd
    logical :: yes
    type(gc_value) :: kids, catches, cl, mp, entry
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: i
    yes = .false.
    if (gc_kind(nd) /= OBJ_AST) return
    kids = gc_slot(nd, 1)
    select case (gc_i1(nd))
    case (N_FN, N_LAZY, N_LOCAL, N_CONST, N_VAR, N_DEFTYPE)
       return
    case (N_RECUR)
       yes = (int_of(gcv_nth(gc_slot(nd, 2), 0)) /= 0)
       return
    case (N_TRY)
       yes = has_fn_recur(gcv_nth(kids, 0))
       if (yes) return
       catches = gc_slot(nd, 2)
       do i = 0, gcv_count(catches) - 1
          cl = gcv_nth(catches, i)
          yes = has_fn_recur(gcv_nth(cl, 2))
          if (yes) return
       end do
       if (gc_kind(gcv_nth(kids, 1)) == OBJ_AST) yes = has_fn_recur(gcv_nth(kids, 1))
       return
    case (N_CASE)
       mp = gc_slot(nd, 2)
       call gca_entries(mp, ks, vls)
       do i = 1, size(ks)
          entry = strip_meta(vls(i))
          if (gcv_is(entry)) then
             yes = has_fn_recur(gcv_nth(entry, 1))
             if (yes) return
          end if
       end do
    case (N_DEF)
       if (gc_kind(gc_slot(nd, 3)) == OBJ_AST) then
          yes = has_fn_recur(gc_slot(nd, 3))
          if (yes) return
       end if
    end select
    if (gcv_is(kids)) then
       do i = 0, gcv_count(kids) - 1
          yes = has_fn_recur(gcv_nth(kids, i))
          if (yes) return
       end do
    end if
  end function has_fn_recur

  ! Runs the pass over one body with `nslots` slots and marks the reads.
  ! A body that recurs to its fn re-runs from the top with its captures
  ! unchanged, so it gets no clearing at all.
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

  subroutine apply_clears(body, nslots)
    type(gc_value), intent(in) :: body
    integer, intent(in) :: nslots
    logical, allocatable :: live(:)
    if (keep_locals()) return
    if (nslots <= 0) return
    if (has_fn_recur(body)) return
    allocate(live(nslots))
    live = .false.
    call liveness(body, live)
  end subroutine apply_clears

  ! --- the top level -------------------------------------------------

  ! A top-level form: analysed in a fresh fn scope (its lets need
  ! slots), wrapped as N_TOP with the frame size. A top-level `do` is
  ! NOT analysed as a unit: Compiler.eval evaluates its subforms one by
  ! one, each analysed after the previous has run, so an (ns ...) or a
  ! def earlier in the same do is visible to the rest.
  recursive function analyze_top(form0) result(nd)
    type(gc_value), intent(in) :: form0
    type(gc_value) :: nd, form, head, sc, body
    integer :: base

    nd = gc_nil()
    base = vs_enter(4)
    form = form0
    if (gc_kind(form) == OBJ_META) form = strip_meta(form)
    if (gc_kind(form) == OBJ_LAZY .or. gc_kind(form) == OBJ_SEQ) then
       call vs_set(base + 1, form)
       form = seq_to_list(vs_get(base + 1), [vs_get(base + 1)])
    end if
    call vs_set(base + 1, form)
    if (gcl_is(form)) then
       if (gcl_count(form) > 0) then
          head = strip_meta(gcl_first(form))
          if (head%tag == GCT_SYM) then
             if (gc_ref_is(head%ref, "do")) then
                nd = mk_node(N_TOPDO, gc_nil(), gcl_rest(vs_get(base + 1), [vs_get(base + 1)]), gc_nil(), 0, &
                     [vs_get(base + 1)])
                call vs_leave(base)
                return
             end if
          end if
       end if
    end if
    sc = new_fn_scope(gc_nil(), [vs_get(base + 1)])
    call vs_set(base + 2, sc)
    body = analyze(vs_get(base + 1), vs_get(base + 2))
    if (has_error) then
       call vs_leave(base)
       return
    end if
    call vs_set(base + 3, body)
    call apply_clears(vs_get(base + 3), gc_i1(scope_info(vs_get(base + 2))))
    nd = mk_node(N_TOP, gc_nil(), vs_get(base + 3), gc_nil(), gc_i1(scope_info(vs_get(base + 2))), &
         [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function analyze_top
