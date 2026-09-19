! Exercises the mark-sweep heap on its own, before anything in clotran
! depends on it. The cases that matter are the ones refcounting could
! not do (cycles) and the ones that only fail intermittently in a real
! system (a missing root, growth during a live traversal) -- so those
! are tested deterministically here, under torture mode.
program gc_test
  use GC
  implicit none

  logical :: all_ok
  type(gc_value) :: no_roots(0)

  all_ok = .true.

  call check_immediates()
  call check_cons_roundtrip()
  call check_reachable_survives()
  call check_unreachable_freed()
  call check_free_list_reuse()
  call check_cycle_is_collected()
  call check_growth()
  call check_string_release()
  call check_torture_keeps_live_data()
  call check_argument_is_rooted()
  call check_object_shapes()
  call check_value_runs()
  call check_deep_structure()
  call check_heap_self_check()
  call check_namespaces()
  call check_grow_only()
  call check_value_stack()
  call check_global_root_growth()

  if (all_ok) then
     print *, ""
     print *, "ALL GC CHECKS PASSED"
  else
     print *, ""
     print *, "GC CHECKS FAILED"
     stop 1
  end if

contains

  subroutine ok(label, condition)
    character(len=*), intent(in) :: label
    logical, intent(in) :: condition
    if (condition) then
       print '(A,A)', "ok   - ", label
    else
       print '(A,A)', "FAIL - ", label
       all_ok = .false.
    end if
    flush(6)
  end subroutine ok

  subroutine ok_int(label, got, expected)
    character(len=*), intent(in) :: label
    integer, intent(in) :: got, expected
    if (got == expected) then
       print '(A,A,I0)', "ok   - ", label, got
    else
       print '(A,A,I0,A,I0,A)', "FAIL - ", label, got, "  (expected ", expected, ")"
       all_ok = .false.
    end if
    flush(6)
  end subroutine ok_int

  ! An immediate never touches the heap -- which is the point: most
  ! values in a running program are integers and nil, and they should
  ! cost nothing to allocate or collect.
  subroutine check_immediates()
    type(gc_value) :: i, n
    call gc_init(16)
    i = gc_int(42)
    n = gc_nil()
    call ok("1a. an integer holds no heap reference: ", i%ref == 0)
    call ok("1b. ...and neither does nil: ", n%ref == 0)
    call gc_collect(no_roots)
    call ok_int("1c. collecting with no roots frees nothing: ", gc_live_count(), 0)
  end subroutine check_immediates

  subroutine check_cons_roundtrip()
    type(gc_value) :: c, roots(0)
    call gc_init(16)
    c = gc_cons(gc_int(1), gc_int(2), roots)
    call ok_int("2a. car reads back: ", car_int(c), 1)
    call ok_int("2b. cdr reads back: ", cdr_int(c), 2)
    call ok_int("2c. one cell is live: ", gc_live_count(), 1)
  end subroutine check_cons_roundtrip

  ! A chain of 500 cells, held only by its head.
  subroutine check_reachable_survives()
    type(gc_value) :: head, roots(1)
    integer :: i
    call gc_init(16)
    head = gc_nil()
    do i = 1, 500
       roots(1) = head
       head = gc_cons(gc_int(i), head, roots)
    end do
    roots(1) = head
    call gc_collect(roots)
    call ok_int("3a. a 500-cell chain survives, held by its head: ", gc_live_count(), 500)
    call ok_int("3b. ...and is still intact: ", chain_length(head), 500)
    call ok_int("3c. ...with its contents unchanged: ", car_int(head), 500)
  end subroutine check_reachable_survives

  subroutine check_unreachable_freed()
    type(gc_value) :: head, roots(1)
    integer :: i
    call gc_init(16)
    head = gc_nil()
    do i = 1, 100
       roots(1) = head
       head = gc_cons(gc_int(i), head, roots)
    end do
    call gc_collect(no_roots) ! nothing is a root: all of it is garbage
    call ok_int("4a. an unreachable chain is collected entirely: ", gc_live_count(), 0)
  end subroutine check_unreachable_freed

  subroutine check_free_list_reuse()
    type(gc_value) :: c, roots(0)
    integer :: cap_before, i
    call gc_init(64)
    do i = 1, 50
       c = gc_cons(gc_int(i), gc_nil(), roots)
    end do
    call gc_collect(no_roots)
    cap_before = gc_obj_capacity()
    do i = 1, 50
       c = gc_cons(gc_int(i), gc_nil(), roots)
    end do
    call ok_int("5a. freed slots are reused, not grown past: ", gc_obj_capacity(), cap_before)
    call ok_int("5b. ...and the live count is right again: ", gc_live_count(), 50)
  end subroutine check_free_list_reuse

  ! The case refcounting structurally cannot reclaim, and the reason
  ! clotran leaks today: a closure bound into its own environment for
  ! `recur` is exactly this shape.
  subroutine check_cycle_is_collected()
    type(gc_value) :: a, b, roots(1)
    call gc_init(16)
    a = gc_cons(gc_int(1), gc_nil(), no_roots)
    roots(1) = a
    b = gc_cons(gc_int(2), a, roots)
    call gc_set_cdr(a, b) ! a -> b -> a
    roots(1) = a
    call gc_collect(roots)
    call ok_int("6a. a cycle held by a root survives: ", gc_live_count(), 2)
    call gc_collect(no_roots)
    call ok_int("6b. ...and is collected once unreachable: ", gc_live_count(), 0)
  end subroutine check_cycle_is_collected

  ! Growth has to happen mid-traversal without losing the live chain --
  ! the pool is reallocated underneath values that already point into it.
  subroutine check_growth()
    type(gc_value) :: head, roots(1)
    integer :: i
    call gc_init(8)
    head = gc_nil()
    do i = 1, 300
       roots(1) = head
       head = gc_cons(gc_int(i), head, roots)
    end do
    roots(1) = head
    call ok("7a. the pool grew past its initial size: ", gc_obj_capacity() >= 300)
    call ok_int("7b. ...and the chain survived growth intact: ", chain_length(head), 300)
    call gc_collect(roots)
    call ok_int("7c. ...and still does after a collection: ", chain_length(head), 300)
  end subroutine check_growth

  subroutine check_string_release()
    type(gc_value) :: s, roots(1)
    call gc_init(16)
    s = gc_str("a string on the heap", no_roots)
    roots(1) = s
    call gc_collect(roots)
    call ok("8a. a rooted string survives: ", gc_text(s) == "a string on the heap")
    call gc_collect(no_roots)
    call ok_int("8b. ...and is released when unreachable: ", gc_live_count(), 0)
  end subroutine check_string_release

  ! Torture mode collects at EVERY allocation, so anything not passed
  ! as a root is destroyed immediately. A missing root then fails here
  ! and now, deterministically, instead of corrupting memory later.
  subroutine check_torture_keeps_live_data()
    type(gc_value) :: head, roots(1)
    integer :: i
    call gc_init(8)
    gc_torture = .true.
    head = gc_nil()
    do i = 1, 200
       roots(1) = head
       head = gc_cons(gc_int(i), head, roots)
    end do
    call ok_int("9a. under torture, a properly rooted chain is intact: ", &
         chain_length(head), 200)
    call ok_int("9b. ...its contents are correct: ", car_int(head), 200)
    call ok("9c. ...and it really did collect every allocation: ", gc_collections >= 200)
    gc_torture = .false.
  end subroutine check_torture_keeps_live_data

  ! A freshly built value passed as an ARGUMENT is live, but the caller
  ! cannot have listed it as a root -- nothing references it yet. If
  ! allocation does not root its own arguments, (cons (str ...) ...)
  ! frees the string between the two calls: only under torture or at an
  ! unlucky heap size, which is the worst way to find a bug.
  subroutine check_argument_is_rooted()
    type(gc_value) :: c, roots(0)
    call gc_init(8)
    gc_torture = .true.
    c = gc_cons(gc_str("inner", roots), gc_int(7), roots)
    call ok("10a. an argument built at the call site survives: ", &
         gc_text(gc_car(c)) == "inner")
    call ok_int("10b. ...and the cell around it is intact: ", cdr_int(c), 7)
    gc_torture = .false.
  end subroutine check_argument_is_rooted

  ! The object pool is general: a cons cell, a closure, a lazy seq and
  ! an environment are all "some slots plus a couple of integers", so
  ! they share one pool, one allocator and one trace routine. `kind`
  ! is what distinguishes them.
  subroutine check_object_shapes()
    type(gc_value) :: clo, roots(1), body
    call gc_init(32)
    body = gc_sym("body", no_roots)
    roots(1) = body
    clo = gc_obj(OBJ_CLOSURE, [gc_sym("params", roots), body, gc_nil(), gc_nil()], roots)
    call gc_set_i1(clo, 1) ! is-a-macro
    roots(1) = clo
    call gc_collect(roots)
    call ok_int("11a. an object reports its kind: ", gc_kind(clo), OBJ_CLOSURE)
    call ok("11b. ...its slots survive collection: ", gc_text(gc_slot(clo, 1)) == "params")
    call ok("11c. ...all of them: ", gc_text(gc_slot(clo, 2)) == "body")
    call ok_int("11d. ...and its inline integer: ", gc_i1(clo), 1)
    call ok_int("11e. an unset slot is nil: ", slot_tag(clo, 4), GCT_NIL)
  end subroutine check_object_shapes

  ! The other shape: a variable-length run of values, which is what
  ! backs a vector's trie node, a map's keys and vals, and a Var's
  ! dynamic binding stack.
  subroutine check_value_runs()
    type(gc_value) :: keys, vals, m, roots(1)
    integer :: i
    call gc_init(32)
    keys = gc_vec(3, no_roots)
    roots(1) = keys
    vals = gc_vec(3, roots)
    do i = 1, 3
       call gc_vec_set(keys, i, gc_key("k", roots))
       call gc_vec_set(vals, i, gc_int(i * 10))
    end do
    m = gc_obj(OBJ_MAP, [keys, vals], roots)
    call gc_set_i1(m, 3)
    roots(1) = m
    call gc_collect(roots)
    call ok_int("12a. a value run keeps its length: ", gc_vec_len(gc_slot(m, 1)), 3)
    call ok_int("12b. ...and its contents: ", vec_int(gc_slot(m, 2), 2), 20)
    call ok("12c. ...including heap values inside it: ", &
         gc_text(gc_vec_get(gc_slot(m, 1), 1)) == "k")
    call gc_collect(no_roots)
    call ok_int("12d. the whole map is collected when unreachable: ", gc_live_count(), 0)
  end subroutine check_value_runs

  ! Tracing has to reach through BOTH shapes to find everything: an
  ! object holding a run holding objects holding text.
  subroutine check_deep_structure()
    type(gc_value) :: run, outer, roots(1)
    integer :: i
    call gc_init(16)
    run = gc_vec(20, no_roots)
    roots(1) = run
    do i = 1, 20
       call gc_vec_set(run, i, gc_cons(gc_str("deep", roots), gc_int(i), roots))
    end do
    outer = gc_obj(OBJ_VECTOR, [run], roots)
    roots(1) = outer
    call gc_collect(roots)
    ! 1 run + 20 cons cells + 20 strings + 1 outer object.
    call ok_int("13a. object -> run -> object -> text all survive: ", gc_live_count(), 42)
    call ok("13b. ...and the text is intact: ", &
         gc_text(gc_car(gc_vec_get(gc_slot(outer, 1), 7))) == "deep")
    call ok_int("13c. ...as are the immediates beside it: ", &
         cdr_int(gc_vec_get(gc_slot(outer, 1), 7)), 7)
  end subroutine check_deep_structure

  ! The payoff of handles over pointers: the heap can audit itself.
  ! Under torture, every allocation collects, so this is the strongest
  ! statement available -- no live object ever points at a freed slot.
  subroutine check_heap_self_check()
    type(gc_value) :: head, roots(1)
    integer :: i
    call gc_init(8)
    gc_torture = .true.
    head = gc_nil()
    do i = 1, 100
       roots(1) = head
       head = gc_cons(gc_str("x", roots), head, roots)
    end do
    call ok("14a. the heap passes its own audit under torture: ", gc_check_heap() == "")
    call ok_int("14b. ...with the structure still whole: ", chain_length(head), 100)
    gc_torture = .false.
  end subroutine check_heap_self_check

  ! Namespaces are the first thing that is a root because of WHERE IT
  ! LIVES rather than because some caller happened to pass it: the
  ! registry is process-wide and outlives every call. So every check
  ! below collects with NO local roots -- if the global root does not
  ! hold, all of it is swept.
  subroutine check_namespaces()
    type(gc_value) :: reg, bigger, ns, var, binds, roots(2)
    integer :: g, i, var_ref

    call gc_init(64)

    reg = gc_vec(4, no_roots)
    g = gc_global_new(reg)

    ! (in-ns 'user) (def x 41), with the Var as the namespace's binding
    ns = gc_obj(OBJ_NS, [gc_str("user", no_roots), gc_nil(), gc_nil()], no_roots)
    roots(1) = ns
    var = gc_obj(OBJ_VAR, [gc_int(41), gc_nil(), gc_nil(), gc_sym("x", roots)], roots)
    call gc_set_slot(ns, 2, var)
    call gc_vec_set(reg, 1, ns)

    call gc_collect(no_roots)
    reg = gc_global_get(g)
    ns = gc_vec_get(reg, 1)
    var = gc_slot(ns, 2)
    call ok("15a. a namespace survives on the global root alone: ", &
         gc_text(gc_slot(ns, 1)) == "user")
    call ok_int("15b. ...with its Var still reachable through it: ", gc_kind(var), OBJ_VAR)
    call ok_int("15c. ...and the Var's root binding intact: ", slot_int(var, 1), 41)

    ! (def x 42) mutates the SAME Var rather than replacing it. That is
    ! what makes a closure built before a later def see the new value,
    ! so the handle must not change.
    var_ref = var%ref
    call gc_set_slot(var, 1, gc_int(42))
    call gc_collect(no_roots)
    ns = gc_vec_get(gc_global_get(g), 1)
    var = gc_slot(ns, 2)
    call ok("15d. redefinition keeps Var identity: ", var%ref == var_ref)
    call ok_int("15e. ...with the new value: ", slot_int(var, 1), 42)

    ! The registry grows, so the global is a SLOT, not a handle handed
    ! over once: the old run becomes garbage and the new one must root.
    bigger = gc_vec(8, no_roots)
    do i = 1, 4
       call gc_vec_set(bigger, i, gc_vec_get(gc_global_get(g), i))
    end do
    call gc_global_set(g, bigger)
    call gc_collect(no_roots)
    ns = gc_vec_get(gc_global_get(g), 1)
    call ok("15f. a grown registry still roots its namespaces: ", &
         gc_text(gc_slot(ns, 1)) == "user")

    ! And it is a root, not a leak: drop the namespace and it goes.
    call gc_vec_set(gc_global_get(g), 1, gc_nil())
    call gc_collect(no_roots)
    call ok_int("15g. ...and drops them when unbound: ", gc_live_count(), 1)

    ! Under torture every allocation collects, so the only thing
    ! keeping 50 Vars alive across 50 collections is the chain
    ! registry -> namespace -> bindings, with nothing on the stack.
    gc_torture = .true.
    ns = gc_obj(OBJ_NS, [gc_str("user", no_roots), gc_nil(), gc_nil()], no_roots)
    call gc_vec_set(gc_global_get(g), 1, ns)
    binds = gc_vec(50, no_roots)
    call gc_set_slot(ns, 2, binds)
    do i = 1, 50
       call gc_vec_set(binds, i, &
            gc_obj(OBJ_VAR, [gc_int(i), gc_nil(), gc_nil(), gc_sym("v", no_roots)], no_roots))
    end do
    call ok("15h. the heap audits clean rooted only by a global: ", gc_check_heap() == "")
    call ok_int("15i. ...and every Var survived every collection: ", var_sum(binds), 1275)
    gc_torture = .false.
  end subroutine check_namespaces

  ! Grow-only mode, left over from the migration into this heap, when
  ! nothing rooted the payloads yet and the pools had to only grow. Nothing here is rooted at all -- under the normal
  ! policy the first collection would sweep every one of these.
  subroutine check_grow_only()
    type(gc_value) :: kept(200)
    integer :: i, bad
    call gc_init(8)
    gc_no_collect = .true.
    do i = 1, 200
       kept(i) = gc_cons(gc_str("keep", no_roots), gc_int(i), no_roots)
    end do
    bad = 0
    do i = 1, 200
       if (gc_text(gc_car(kept(i))) /= "keep") bad = bad + 1
       if (cdr_int(kept(i)) /= i) bad = bad + 1
    end do
    call ok_int("16a. grow-only keeps every unrooted allocation: ", bad, 0)
    call ok_int("16b. ...and never collected: ", gc_collections, 0)
    call ok("16c. ...with the heap still sound: ", gc_check_heap() == "")
    gc_no_collect = .false.
  end subroutine check_grow_only

  ! The value stack. These are the checks that
  ! decide whether rooting-by-construction actually holds: every one
  ! collects with NO argument roots at all, so if the stack is not
  ! scanned, the data is gone.
  subroutine check_value_stack()
    type(gc_value) :: v
    integer :: base, b2, i, bad

    call gc_init(8)

    ! A frame's slots are roots.
    base = vs_enter(3)
    call vs_set(base + 1, gc_str("alpha", no_roots))
    call vs_set(base + 2, gc_cons(gc_int(1), gc_int(2), no_roots))
    call gc_collect(no_roots)
    call ok("17a. a frame's slots survive collection: ", &
         gc_text(vs_get(base + 1)) == "alpha")
    call ok_int("17b. ...including structure: ", car_int(vs_get(base + 2)), 1)
    call ok_int("17c. an unset slot is nil: ", vs_tag(base + 3), GCT_NIL)

    ! Leaving releases them -- the part a stack collector gets wrong by
    ! leaving stale values above the top, which keeps dead data alive.
    call vs_leave(base)
    call gc_collect(no_roots)
    call ok_int("17d. leaving a frame makes its values collectable: ", gc_live_count(), 0)
    call ok_int("17e. ...and the stack is back to empty: ", vs_depth(), 0)

    ! Nesting, and growth past the initial stack size.
    base = vs_enter(2)
    call vs_set(base + 1, gc_str("outer", no_roots))
    b2 = vs_enter(300)
    do i = 1, 300
       call vs_set(b2 + i, gc_cons(gc_str("deep", no_roots), gc_int(i), no_roots))
    end do
    call gc_collect(no_roots)
    bad = 0
    do i = 1, 300
       if (cdr_int(vs_get(b2 + i)) /= i) bad = bad + 1
    end do
    call ok_int("17f. the stack grows and keeps every slot: ", bad, 0)
    call ok("17g. ...and the outer frame is untouched: ", &
         gc_text(vs_get(base + 1)) == "outer")

    ! Torture: collect at every allocation, rooted only by the stack.
    gc_torture = .true.
    do i = 1, 100
       call vs_set(b2 + i, gc_cons(gc_str("x", no_roots), gc_int(i * 2), no_roots))
    end do
    call ok("17h. rooted only by the stack, under torture: ", gc_check_heap() == "")
    call ok_int("17i. ...with values intact: ", cdr_int(vs_get(b2 + 50)), 100)
    gc_torture = .false.

    call vs_leave(b2)
    call vs_leave(base)
    call gc_collect(no_roots)
    call ok_int("17j. unwinding everything collects everything: ", gc_live_count(), 0)
  end subroutine check_value_stack

  function vs_tag(slot) result(t)
    integer, intent(in) :: slot
    type(gc_value) :: x
    integer :: t
    x = vs_get(slot)
    t = x%tag
  end function vs_tag

  ! --- helpers ---

  function car_int(c) result(i)
    type(gc_value), intent(in) :: c
    type(gc_value) :: v
    integer :: i
    v = gc_car(c)
    i = v%ival
  end function car_int

  function cdr_int(c) result(i)
    type(gc_value), intent(in) :: c
    type(gc_value) :: v
    integer :: i
    v = gc_cdr(c)
    i = v%ival
  end function cdr_int

  ! Not gc_slot(v, i)%tag -- flang cannot take a component off a
  ! function result. See NOTES.md's gotchas catalog.
  function slot_tag(v, i) result(t)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: x
    integer :: t
    x = gc_slot(v, i)
    t = x%tag
  end function slot_tag

  function slot_int(v, i) result(n)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: x
    integer :: n
    x = gc_slot(v, i)
    n = x%ival
  end function slot_int

  function var_sum(run) result(s)
    type(gc_value), intent(in) :: run
    type(gc_value) :: v
    integer :: i, s
    s = 0
    do i = 1, gc_vec_len(run)
       v = gc_vec_get(run, i)
       s = s + slot_int(v, 1)
    end do
  end function var_sum

  function vec_int(v, i) result(n)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: x
    integer :: n
    x = gc_vec_get(v, i)
    n = x%ival
  end function vec_int

  function chain_length(head) result(n)
    type(gc_value), intent(in) :: head
    type(gc_value) :: p
    integer :: n
    n = 0
    p = head
    do while (gc_kind(p) == OBJ_CONS)
       n = n + 1
       p = gc_cdr(p)
    end do
  end function chain_length

  ! The global root table GROWS rather than capping. It started
  ! life as a fixed eight, which was exactly the number of roots
  ! the tree claimed, so the ninth was dropped silently and swept
  ! on the next collection. Nine against an initial eight only
  ! exercises one doubling, so this claims far more than that and
  ! checks two things the grow path could get wrong: that every
  ! slot INDEX still names the value it was given (modules hold
  ! those indices, so a copy landing at a different offset would
  ! silently swap two modules roots), and that a collection after
  ! the move keeps all of them alive.
  subroutine check_global_root_growth()
    integer, parameter :: many = 200
    integer :: handle(many), i
    logical :: indices_ok, values_ok

    call gc_init(64)
    do i = 1, many
       handle(i) = gc_global_new(gc_obj(OBJ_CONS, [gc_int(i), gc_nil()], no_roots))
    end do

    indices_ok = .true.
    do i = 1, many
       if (handle(i) /= i) indices_ok = .false.
    end do
    call ok("18a. every claim gets its own slot, in order: ", indices_ok)
    call ok_int("18b. ...and the count is all of them: ", gc_global_count(), many)

    call gc_collect(no_roots)

    values_ok = .true.
    do i = 1, many
       if (slot_int(gc_global_get(handle(i)), 1) /= i) values_ok = .false.
    end do
    call ok("18c. a root survives the table growing under it: ", values_ok)
    call ok("18d. ...and the heap is still sound: ", gc_check_heap() == "")
  end subroutine check_global_root_growth

end program gc_test
