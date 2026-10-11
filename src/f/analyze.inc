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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: outer
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: sc, info, caps, cmap, names
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 4)
    call vs_set(vst, base + 1, outer)
    caps = gcv_empty([roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, caps)
    cmap = gca_empty([roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, cmap)
    info = gc_obj(OBJ_AST, [vs_get(vst, base + 2), vs_get(vst, base + 1), vs_get(vst, base + 3), gc_nil()], &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 3)])
    ! i1 is the SLOT COUNTER, from zero. It was set to K_FNINFO (101) as
    ! a kind tag nothing ever read, and reserve_slots counted on from
    ! there: every frame in the system had 101 slots nobody used, a
    ! 128-slot arena run per call, and memory to match.
    call gc_set_i1(info, 0)
    call gc_set_i2(info, -1)          ! self slot: none
    call vs_set(vst, base + 4, info)
    names = gca_empty([roots, vs_get(vst, base + 4)])
    call vs_set(vst, base + 3, names)
    sc = gc_obj(OBJ_AST, [vs_get(vst, base + 3), gc_nil(), vs_get(vst, base + 4), gc_nil()], &
         [roots, vs_get(vst, base + 3), vs_get(vst, base + 4)])
    call gc_set_i1(sc, K_SCOPE)
    call vs_leave(vst, base)
  end function new_fn_scope

  ! A nested block in the same fn: empty names, same fninfo, the
  ! parent's recur target unless the caller replaces it.
  function child_scope(parent, roots) result(sc)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: parent
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: sc, names
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, parent)
    names = gca_empty([roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, names)
    sc = gc_obj(OBJ_AST, [vs_get(vst, base + 2), vs_get(vst, base + 1), &
         gc_slot(vs_get(vst, base + 1), 3), gc_slot(vs_get(vst, base + 1), 4)], &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call gc_set_i1(sc, K_SCOPE)
    call vs_leave(vst, base)
  end function child_scope

  ! Every local visible in scope sc, name -> slot, the innermost binding
  ! of a name winning: this fn's blocks, what it captured, and the fns
  ! around it.
  recursive function locals_env(sc, roots) result(env)
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: sc
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: env, blk, info
    type(gc_value), allocatable :: ks(:), vls(:)
    integer :: base, i
    vst => gc_my_stack()
    base = vs_enter(vst, 2)
    call vs_set(vst, base + 1, sc)
    env = gca_empty([roots, vs_get(vst, base + 1)])
    call vs_set(vst, base + 2, env)
    blk = sc
    do while (gc_kind(blk) == OBJ_AST)
       call add_names(gc_slot(blk, 1))
       blk = gc_slot(blk, 2)
    end do
    if (gc_kind(sc) == OBJ_AST) then
       info = scope_info(sc)
       if (gc_kind(info) /= GCT_NIL .and. info%tag == GCT_OBJ) then
          call add_names(gc_slot(info, 3))
          if (gc_kind(gc_slot(info, 2)) == OBJ_AST) then
             blk = locals_env(gc_slot(info, 2), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
             call add_names(blk)
          end if
       end if
    end if
    env = vs_get(vst, base + 2)
    call vs_leave(vst, base)
  contains
    subroutine add_names(m)
      type(gc_value), intent(in) :: m
      type(gc_value) :: e
      if (.not. gca_is(m)) return
      call gca_entries(m, ks, vls)
      do i = 1, size(ks)
         if (gca_contains(vs_get(vst, base + 2), ks(i))) cycle
         e = gca_assoc(vs_get(vst, base + 2), ks(i), vls(i), [roots, vs_get(vst, base + 1), vs_get(vst, base + 2), m])
         call vs_set(vst, base + 2, e)
      end do
    end subroutine add_names
  end function locals_env

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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: sc, sym
    integer, intent(in) :: slot
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: names
    integer :: base
    vst => gc_my_stack()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, sc)
    call vs_set(vst, base + 2, sym)
    names = gca_assoc(gc_slot(vs_get(vst, base + 1), 1), vs_get(vst, base + 2), gc_int(slot), &
         [roots, vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call gc_set_slot(vs_get(vst, base + 1), 1, names)
    ! ...and the other way round, at the FN level.
    call vs_set(vst, base + 3, scope_info(vs_get(vst, base + 1)))
    call note_slot_name(vs_get(vst, base + 3), slot, vs_get(vst, base + 2), [roots, vs_get(vst, base + 1)])
    call vs_leave(vst, base)
  end subroutine bind_name

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

  ! The array hint of the local `sym` names here, or nil. The walk is
  ! name resolution's: the innermost scope that BINDS the name decides,
  ! so a rebinding with no hint hides an outer one that had it.
  function local_array_hint(sc0, sym) result(h)
    type(gc_value), intent(in) :: sc0, sym
    type(gc_value) :: h, sc, m
    h = gc_nil()
    sc = sc0
    do while (gc_kind(sc) == OBJ_AST)
       if (gca_is(gc_slot(sc, 1))) then
          if (gca_contains(gc_slot(sc, 1), sym)) then
             m = gc_slot(sc, 5)
             if (gca_is(m)) h = gca_get(m, sym)
             return
          end if
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

  ! slot -> name at the FN level, for every block of the fn and for its
  ! captures, so a paused frame can report its locals by name (the
  ! debugger, exec.inc break_frames). The scope maps are per block and
  ! gone after analysis; this one rides on the template.
  subroutine note_slot_name(info, slot, sym, roots)
    type(gc_value), intent(in) :: info, sym
    integer, intent(in) :: slot
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: names
    names = gc_slot(info, 4)
    if (.not. gca_is(names)) names = gca_empty([roots, info, sym])
    names = gca_assoc(names, gc_int(slot), sym, [roots, info, sym])
    call gc_set_slot(info, 4, names)
  end subroutine note_slot_name

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
    type(gc_stack), pointer :: vst
    type(gc_value), intent(in) :: sc, sym
    integer :: slot
    type(gc_value) :: blk, info, hit, caps, cmap
    integer :: outer, base

    vst => gc_my_stack()
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

    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, info)
    call vs_set(vst, base + 2, sym)
    slot = gc_i1(vs_get(vst, base + 1))
    call gc_set_i1(vs_get(vst, base + 1), slot + 1)
    caps = gcv_conj(gc_slot(vs_get(vst, base + 1), 1), gc_int(outer), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_set(vst, base + 3, caps)
    caps = gcv_conj(vs_get(vst, base + 3), gc_int(slot), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call gc_set_slot(vs_get(vst, base + 1), 1, caps)
    cmap = gca_assoc(gc_slot(vs_get(vst, base + 1), 3), vs_get(vst, base + 2), gc_int(slot), &
         [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call gc_set_slot(vs_get(vst, base + 1), 3, cmap)
    ! a captured value is a local of every arity's frame; name it too
    call note_slot_name(vs_get(vst, base + 1), slot, vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
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
                if (gc_i2(vs_get(vst, base + 1)) /= 0 .and. tag_of(gc_slot(nd, 4)) == GCT_NIL) &
                     call gc_set_slot(nd, 4, gc_int(gc_i2(vs_get(vst, base + 1))))
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
       sl = index(t, "/")
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
       if (index(dlt_1, "/") > 1) then
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
    if (index(dlt_1, "/") > 1) then
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
             slash = index(dlt_1, "/")
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
       ! A LOCAL shadows everything: a special form name, a macro, host
       ! sugar. (let [do 1] (do)) is a call of the local.
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
    slash = index(t, "/")
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
    if (member%tag /= GCT_SYM) then
       call fail(". needs a member name")
       call vs_leave(vst, base)
       return
    end if
    block
       call gc_ref_text(member%ref, s=dlt_1)
       mname = dlt_1
    end block
    ! A member name reached through syntax-quote arrives qualified --
    ! defmethod's template says addMethod and the reader makes it
    ! clojure.core/addMethod. HostExpr.Parser reads sym.name only, and
    ! so does this.
    if (index(mname, "/") > 1) then
       mname = mname(index(mname, "/") + 1:)
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
             ! (a class name nothing knows is NOT refused here: defrecord's
             ! expansion names its own class in a static call before its
             ! deftype* has run, and a top-level do is analysed whole -- the
             ! residual of DEVIATIONS 32)
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
    if (cls%tag /= GCT_SYM) then
       call fail("new needs a class name")
       call vs_leave(vst, base)
       return
    end if
    ! the class in full, once, here: a bare name through the imports
    block
      character(len=:), allocatable :: written, canonical
      call gc_ref_text(cls%ref, s=written)
      call canon_class(written, c=canonical)
      if (canonical /= written) cls = gc_sym(canonical, [vs_get(vst, base + 1), vs_get(vst, base + 3)])
      ! a name no import knows stays bare and fails when run (eval_new):
      ! a deftype's bare name means it only where imported (DEVIATIONS 17);
      ! not refused here, since a host class's short name is known to
      ! eval_new alone
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

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    vst => gc_my_stack()
    nd = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, form)
    call vs_set(vst, base + 2, sc)
    rest = gcl_rest(form, [vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, rest)

    if (gc_ref_is(head%ref, "quote")) then
       nd = const_node(gcl_first(vs_get(vst, base + 3)), [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    else if (gc_ref_is(head%ref, "if")) then
       nd = analyze_if(vs_get(vst, base + 3), vs_get(vst, base + 2))
    else if (gc_ref_is(head%ref, "do")) then
       nd = analyze_body(vs_get(vst, base + 3), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
    else if (gc_ref_is(head%ref, "def")) then
       nd = analyze_def(vs_get(vst, base + 3), vs_get(vst, base + 2), .false.)
    else if (gc_ref_is(head%ref, "defmacro*")) then
       nd = analyze_def(vs_get(vst, base + 3), vs_get(vst, base + 2), .true.)
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
       if (gcl_count(vs_get(vst, base + 3)) < 1) then
          call fail("Too few arguments to throw, expected: a single Throwable instance")
       else if (gcl_count(vs_get(vst, base + 3)) > 1) then
          call fail("Too many arguments to throw, expected: a single Throwable instance")
       else
          nd = analyze_one(N_THROW, gcl_first(vs_get(vst, base + 3)), vs_get(vst, base + 2))
       end if
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
    else if (gc_ref_is(head%ref, "quasiquote")) then
       nd = analyze_quasiquote(vs_get(vst, base + 3), vs_get(vst, base + 2))
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
    if (gcl_count(rest) < 2 .or. gcl_count(rest) > 3) then
       call fail("if takes two or three forms")
       call vs_leave(vst, base)
       return
    end if
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
  recursive function analyze_def(rest, sc, is_macro) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    logical, intent(in) :: is_macro
    type(gc_value) :: nd, nm, md, var, kids, c
    integer :: base, flags

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 7)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    nm = gcl_first(rest)
    md = gc_nil()
    if (gc_kind(nm) == OBJ_META) then
       md = gc_slot(nm, 2)
       nm = strip_meta(nm)
    end if
    if (nm%tag /= GCT_SYM) then
       call fail("def needs a symbol")
       call vs_leave(vst, base)
       return
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
      sl = index(t, "/")
      if (sl > 1 .and. sl < len(t)) then
         block
            call gcn_name(gcn_current([vs_get(vst, base + 1)]), s=dlt_1)
         if (t(1:sl-1) /= dlt_1) then
            call fail("Can't create defs outside of current ns: " // t)
            call vs_leave(vst, base)
            return
         end if
         end block
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
    call vs_set(vst, base + 7, gcl_rest(vs_get(vst, base + 1), [vs_get(vst, base + 1)]))
    if (gcl_count(vs_get(vst, base + 1)) == 3) then
       c = gcl_first(vs_get(vst, base + 7))
       if (c%tag == GCT_STR) then
          if (md%tag == GCT_NIL) md = gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 7)])
          call vs_set(vst, base + 4, md)
          md = gca_assoc(vs_get(vst, base + 4), gc_key("doc", [vs_get(vst, base + 1), vs_get(vst, base + 4), vs_get(vst, base + 7)]), &
               c, [vs_get(vst, base + 1), vs_get(vst, base + 4), vs_get(vst, base + 7)])
          call vs_set(vst, base + 4, md)
          call vs_set(vst, base + 7, gcl_rest(vs_get(vst, base + 7), [vs_get(vst, base + 1)]))
       end if
    end if

    flags = 0
    if (is_macro) flags = 2
    kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 5)])
    call vs_set(vst, base + 6, kids)
    if (gcl_count(vs_get(vst, base + 7)) > 0) then
       flags = flags + 1
       ! DefExpr.Parser: analyze(init, v.sym.name)
       call gc_ref_text(nm%ref, s=dlt_1)
       tctx%fn_hint = dlt_1(index(dlt_1, "/", back=.true.) + 1:)
       c = analyze(gcl_first(vs_get(vst, base + 7)), vs_get(vst, base + 2))
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
    integer :: base, i, n, start

    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 6)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    binds = strip_meta(gcl_first(rest))
    if (.not. gcv_is(binds)) then
       call fail("let needs a vector of bindings")
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 3, binds)
    n = gcv_count(binds)
    if (mod(n, 2) /= 0) then
       call fail("let* needs an even number of binding forms")
       call vs_leave(vst, base)
       return
    end if
    n = n / 2
    blk = child_scope(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, blk)
    start = reserve_slots(vs_get(vst, base + 4), n)
    if (is_loop) then
       rinfo = int_vec([0, start, n], [vs_get(vst, base + 1), vs_get(vst, base + 4)])
       call gc_set_slot(vs_get(vst, base + 4), 4, rinfo)
    end if
    kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 4)])
    call vs_set(vst, base + 5, kids)
    do i = 0, n - 1
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
       k = strip_meta(gcv_nth(vs_get(vst, base + 3), 2 * i))
       if (k%tag /= GCT_SYM) then
          call fail("let* needs a symbol to bind")
          call vs_leave(vst, base)
          return
       end if
       ! Compiler.LetExpr.Parser: a qualified symbol names a Var, not a
       ! local -- it was bound as written, and the body's x then
       ! resolved to nothing. (& is an ordinary local at 1.12.6.)
       block
         character(len=:), allocatable :: kt
         integer :: slash
         block
            call gc_ref_text(k%ref, s=dlt_1)
            kt = dlt_1
         end block
         slash = index(kt, "/")
         if (slash > 1 .and. slash < len(kt)) then
            call fail("Can't let qualified name: " // kt)
            call vs_leave(vst, base)
            return
         end if
       end block
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
    binds = strip_meta(gcl_first(rest))
    if (.not. gcv_is(binds)) then
       call fail("letfn* needs a vector of bindings")
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 3, binds)
    n = gcv_count(binds)
    if (mod(n, 2) /= 0) then
       call fail("letfn* needs an even number of binding forms")
       call vs_leave(vst, base)
       return
    end if
    n = n / 2
    blk = child_scope(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, blk)
    start = reserve_slots(vs_get(vst, base + 4), n)
    do i = 0, n - 1
       k = strip_meta(gcv_nth(vs_get(vst, base + 3), 2 * i))
       if (k%tag /= GCT_SYM) then
          call fail("letfn* needs a symbol to bind")
          call vs_leave(vst, base)
          return
       end if
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
    base = vs_enter(vst, 8)
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
       arities = gcv_conj(vs_get(vst, base + 7), ar, [vs_get(vst, base + 1), vs_get(vst, base + 5), ar])
       call vs_set(vst, base + 7, arities)
       walk = gcl_rest(vs_get(vst, base + 8), [vs_get(vst, base + 7)])
       call vs_set(vst, base + 8, walk)
    end do

    ! locals clearing, per arity, now that the frame size is known
    do i = 0, gcv_count(vs_get(vst, base + 7)) - 1
       call apply_clears(gcv_nth(gcv_nth(vs_get(vst, base + 7), i), 3), gc_i1(scope_info(vs_get(vst, base + 5))))
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
         vmfid = vm_compile_fn(vs_get(vst, base + 7), gc_i1(scope_info(vs_get(vst, base + 5))), &
              gc_slot(scope_info(vs_get(vst, base + 5)), 1), self_slot, vs_get(vst, base + 8), vmci, consts, &
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
         fl = flat_compile(gcv_nth(vs_get(vst, base + 7), i), gc_i1(scope_info(vs_get(vst, base + 5))), nt, &
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
    tmpl = gcv_conj(vs_get(vst, base + 8), gc_slot(scope_info(vs_get(vst, base + 5)), 1), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 8, tmpl)
    tmpl = gcv_conj(vs_get(vst, base + 8), gc_int(gc_i1(scope_info(vs_get(vst, base + 5))) + nflat), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 8, tmpl)
    tmpl = gcv_conj(vs_get(vst, base + 8), gc_int(self_slot), [vs_get(vst, base + 5)])
    call vs_set(vst, base + 8, tmpl)
    ! slot -> name, for the debugger; an empty map when the fn has no
    ! named locals at all
    block
      type(gc_value) :: nm
      nm = gc_slot(scope_info(vs_get(vst, base + 5)), 4)
      if (.not. gca_is(nm)) nm = gca_empty([vs_get(vst, base + 5), vs_get(vst, base + 8)])
      tmpl = gcv_conj(vs_get(vst, base + 8), nm, [vs_get(vst, base + 5)])
      call vs_set(vst, base + 8, tmpl)
    end block
    ! the builtin this fn only wraps, or nil (wrapper_builtin)
    block
      type(gc_value) :: wb
      wb = wrapper_builtin(vs_get(vst, base + 7), gc_slot(scope_info(vs_get(vst, base + 5)), 1))
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
    type(gc_value) :: f
    if (kind == 1) then
       f = native(B_NUMLONG, "long", roots)
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
          call vs_leave(vst, base)
          return
       end if
       nfixed = amp
    else
       nfixed = n
    end if
    blk = child_scope(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 4, blk)
    start = reserve_slots(vs_get(vst, base + 4), merge(nfixed + 1, nfixed, variadic))
    do i = 0, nfixed - 1
       p = strip_meta(gcv_nth(vs_get(vst, base + 3), i))
       if (p%tag /= GCT_SYM) then
          call fail("fn* parameter must be a symbol")
          call vs_leave(vst, base)
          return
       end if
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
    logical :: method
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
    if (gcl_count(rest) /= want) then
       write(wb, '(I0)') want
       write(gb, '(I0)') gcl_count(rest)
       call fail("Mismatched argument count to recur, expected: " // trim(wb) // " args, got: " // trim(gb))
       call vs_leave(vst, base)
       return
    end if
    kids = analyze_all(vs_get(vst, base + 1), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, kids)
    if (method .and. .not. tctx%has_error) then
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
    sl = index(t, "/")
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
          slash = index(dlt_1, "/")
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

  ! (try body* (catch Class name body*)* (finally body*)?)
  ! Children: [body, finally-or-nil]; slot 2 = catches, each
  ! [class-symbol, slot, body].
  recursive function analyze_try(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, body, fin, catches, item, cl, blk, cb, kids, cname
    integer :: base, i, n, slot

    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 8)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    n = gcl_count(rest)
    body = gcl_empty([vs_get(vst, base + 1)])
    call vs_set(vst, base + 3, body)
    ! body forms, kept in order: collect then reverse via cons
    do i = n - 1, 0, -1
       item = norm_form(nth_of(vs_get(vst, base + 1), i), [vs_get(vst, base + 1), vs_get(vst, base + 3)])
       if (is_clause(item, "catch") .or. is_clause(item, "finally")) cycle
       call vs_set(vst, base + 4, item)
       body = gcl_cons(vs_get(vst, base + 4), vs_get(vst, base + 3), [vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 4)])
       call vs_set(vst, base + 3, body)
    end do
    ! only the LEADING body forms are the body; a form after a catch is
    ! ignored by Clojure too (it is an error there). Simplification: all
    ! non-clause forms are body forms.
    body = analyze_body(vs_get(vst, base + 3), vs_get(vst, base + 2), [vs_get(vst, base + 1)])
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 3, body)

    catches = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 3)])
    call vs_set(vst, base + 5, catches)
    fin = gc_nil()
    call vs_set(vst, base + 6, fin)
    do i = 0, n - 1
       item = norm_form(nth_of(vs_get(vst, base + 1), i), [vs_get(vst, base + 1), vs_get(vst, base + 5), vs_get(vst, base + 6)])
       call vs_set(vst, base + 4, item)
       if (is_clause(item, "catch")) then
          if (gcl_count(item) < 3) cycle
          cname = strip_meta(nth_of(vs_get(vst, base + 4), 1))
          call vs_set(vst, base + 7, cname)
          ! the class must be one there is: a catch of an unknown class is
          ! Compiler's "Unable to resolve classname", not a clause that
          ! quietly never matches
          if (cname%tag == GCT_SYM) then
             block
               character(len=:), allocatable :: written, full
               call gc_ref_text(cname%ref, s=written)
               call class_key(written, k=full)
               if (.not. known_class_name(full)) then
                  call fail("Unable to resolve classname: " // written)
                  call vs_leave(vst, base)
                  return
               end if
             end block
          end if
          blk = child_scope(vs_get(vst, base + 2), [vs_get(vst, base + 1), vs_get(vst, base + 5), vs_get(vst, base + 7)])
          call vs_set(vst, base + 8, blk)
          slot = declare_local(vs_get(vst, base + 8), strip_meta(nth_of(vs_get(vst, base + 4), 2)), [vs_get(vst, base + 1)])
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
       else if (is_clause(item, "finally")) then
          fin = analyze_body(gcl_rest(vs_get(vst, base + 4), [vs_get(vst, base + 1)]), vs_get(vst, base + 2), &
               [vs_get(vst, base + 1), vs_get(vst, base + 5)])
          if (tctx%has_error) then
             call vs_leave(vst, base)
             return
          end if
          call vs_set(vst, base + 6, fin)
       end if
    end do
    kids = gcv_empty([vs_get(vst, base + 1), vs_get(vst, base + 3), vs_get(vst, base + 5), vs_get(vst, base + 6)])
    kids = gcv_conj(kids, vs_get(vst, base + 3), [vs_get(vst, base + 5), vs_get(vst, base + 6), kids])
    kids = gcv_conj(kids, vs_get(vst, base + 6), [vs_get(vst, base + 5), kids])
    call vs_set(vst, base + 7, kids)
    nd = mk_node(N_TRY, vs_get(vst, base + 7), vs_get(vst, base + 5), gc_nil(), 0, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
    call vs_leave(vst, base)
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
    ! after this deftype* in the same expansion name it
    block
       character(len=:), allocatable :: cn, nsn
       call gc_ref_text(cname%ref, s=cn)
       if (index(cn, ".") == 0) then
          call gcn_name(gcn_current([vs_get(vst, base + 1)]), s=nsn)
          cn = nsn // "." // cn
       end if
       call declare_type_name(cn)
       ! and by its short name inside its own methods, as clj's compile
       ! stub is (Compiler.COMPILE_STUB_SYM, HostExpr.maybeClass); the
       ! (import ...) deftype expands to after this records the same
       call record_import(cn)
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
    block
       call class_of_text(vs_get(vst, base + 4), s=dlt_1)
       spec = type_spec(dlt_1, vs_get(vst, base + 5), vs_get(vst, base + 6),  vs_get(vst, base + 3), vs_get(vst, base + 2))
    end block
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
    else
       write(buf, '(I0)') gc_next(reify_id)
       buf = "clotran.reify__" // trim(buf)
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
    spec = type_spec(trim(buf), vs_get(vst, base + 5), vs_get(vst, base + 3), vs_get(vst, base + 4), vs_get(vst, base + 2))
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
  recursive function analyze_quasiquote(rest, sc) result(nd)
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: rest, sc
    type(gc_value) :: nd, expanded
    integer :: base
    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 3)
    call vs_set(vst, base + 1, rest)
    call vs_set(vst, base + 2, sc)
    if (tctx%qq_depth == 0) call gc_global_keep(gensym_root, gca_empty([vs_get(vst, base + 1), vs_get(vst, base + 2)]))
    tctx%qq_depth = tctx%qq_depth + 1
    expanded = qq_expand(gcl_first(vs_get(vst, base + 1)), gc_nil())
    tctx%qq_depth = tctx%qq_depth - 1
    if (tctx%has_error) then
       call vs_leave(vst, base)
       return
    end if
    call vs_set(vst, base + 3, expanded)
    nd = analyze(vs_get(vst, base + 3), vs_get(vst, base + 2))
    call vs_leave(vst, base)
  end function analyze_quasiquote

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
             call fail("Cannot assign to non-mutable: " // dlt_1)
          end if
          call vs_leave(vst, base)
          return
       end if
       if (lookup_local(vs_get(vst, base + 2), tgt) >= 0) then
          ! A local -- a let binding, a parameter, or an immutable field
          ! bound as one (bind_fields) -- is not an assignable place:
          ! clj's AssignExpr refuses every local binding that is not a
          ! mutable field with this wording. At run time, as a method body
          ! is analysed when first run.
          block
             call gc_ref_text(tgt%ref, s=dlt_1)
             nd = fail_node("Cannot assign to non-mutable: " // dlt_1, [vs_get(vst, base + 1), vs_get(vst, base + 2)])
          end block
          call vs_leave(vst, base)
          return
       end if
       var = resolve_var(tgt, gc_nil())
       if (.not. gcn_is_var(var)) then
          block
             call gc_ref_text(tgt%ref, s=dlt_1)
             call fail("set! needs a var: " // dlt_1)
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
    type(gc_stack), pointer :: vst
    type(eval_ctx), pointer :: tctx
    type(gc_value), intent(in) :: form0
    type(gc_value) :: nd, form, head, sc, body
    integer :: base

    tctx => ctx_self()
    vst => tctx%stk
    nd = gc_nil()
    base = vs_enter(vst, 4)
    form = form0
    if (gc_kind(form) == OBJ_META) form = strip_meta(form)
    if (gc_kind(form) == OBJ_LAZY .or. gc_kind(form) == OBJ_SEQ) then
       call vs_set(vst, base + 1, form)
       form = seq_to_list(vs_get(vst, base + 1), [vs_get(vst, base + 1)])
    end if
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
    call apply_clears(vs_get(vst, base + 3), gc_i1(scope_info(vs_get(vst, base + 2))))
    ! the flat form beside the tree (flat.inc): a loop typed at the
    ! REPL runs as one in a fn does; its temporaries widen the frame
    block
      type(gc_value) :: fl
      integer :: nt
      fl = flat_compile_body(vs_get(vst, base + 3), gc_i1(scope_info(vs_get(vst, base + 2))), nt, &
           [vs_get(vst, base + 1), vs_get(vst, base + 2)])
      call vs_set(vst, base + 4, fl)
      nd = mk_node(N_TOP, gc_nil(), vs_get(vst, base + 3), vs_get(vst, base + 4), &
           gc_i1(scope_info(vs_get(vst, base + 2))) + nt, &
           [vs_get(vst, base + 1), vs_get(vst, base + 2), vs_get(vst, base + 4)])
    end block
    call vs_leave(vst, base)
  end function analyze_top
