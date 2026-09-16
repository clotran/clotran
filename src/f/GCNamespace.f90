! GCNamespace: namespaces and Vars, over the GC heap.
!
! Standalone like the rest of the new layer; GCEval uses it. See
! PLAN.md 3c-2/3d.
!
! Shape, matching GC.f90's comments on OBJ_NS and OBJ_VAR:
!
!   namespace  an object: slot 1 = name, slot 2 = bindings map
!   var        an object: slot 1 = root value, slot 4 = name
!
! WHY VARS EXIST AT ALL, rather than a namespace just mapping a name
! to a value. A Var is a stable box with IDENTITY: `(def x 1)` then
! `(def x 2)` mutates the same Var rather than replacing it, so
! anything holding a reference to it -- a closure created before the
! second def -- sees the new value. That is what makes redefining a
! function at the REPL work while everything that already called it
! keeps working. gc_test check 15d pins the same property one layer
! down.
!
! The registry and the current namespace are GC GLOBAL ROOTS. They
! have to be: they are reachable from nothing else, and everything a
! program has defined hangs off them. That is also the semantics --
! Clojure's namespaces live as long as the process and are dropped
! only by remove-ns.
module GCNamespace
  use GC
  use GCAssoc
  implicit none
  private

  type(gc_root), save :: registry_root   ! a map of name -> namespace
  ! THE current namespace is the Var, not this. current_root is the
  ! bootstrap value only -- what gcn_current answers before
  ! clojure.core and #'*ns* exist. Once the Var is interned it is the
  ! single source of truth, and this stops being read.
  type(gc_root), save :: current_root    ! bootstrap only
  type(gc_root), save :: ns_var_root     ! #'clojure.core/*ns*

  public :: gcn_reset, gcn_current, gcn_set_current, gcn_find_or_create
  public :: gcn_intern, gcn_lookup, gcn_var_value, gcn_set_var, gcn_is_var
  public :: gcn_name

contains

  ! Re-checks the slot rather than trusting the cached index: gc_init
  ! clears the global-root registry but these module variables survive
  ! it, which is the stale-singleton bug GCList's check 4c caught.
  logical function roots_live()
    roots_live = .false.
    if (.not. gc_root_live(registry_root)) return
    roots_live = gca_is(gc_root_get(registry_root))
  end function roots_live

  ! Starts (or restarts) with a single namespace, `user`, current.
  subroutine gcn_reset(roots)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: reg, ns
    integer :: base

    base = vs_enter(2)
    reg = gca_empty(roots)
    call vs_set(base + 1, reg)
    call gc_global_keep(registry_root, vs_get(base + 1))
    ns = make_ns("user", [vs_get(base + 1)])
    call vs_set(base + 2, ns)
    call register(ns)
    call gc_global_keep(current_root, vs_get(base + 2))
    call vs_leave(base)
  end subroutine gcn_reset

  function make_ns(name, roots) result(ns)
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: ns, nm, binds
    integer :: base
    base = vs_enter(2)
    nm = gc_str(name, roots)
    call vs_set(base + 1, nm)
    binds = gca_empty([vs_get(base + 1)])
    call vs_set(base + 2, binds)
    ns = gc_obj(OBJ_NS, [vs_get(base + 1), vs_get(base + 2), gc_nil()], &
         [vs_get(base + 1), vs_get(base + 2)])
    call vs_leave(base)
  end function make_ns

  subroutine register(ns)
    type(gc_value), intent(in) :: ns
    type(gc_value) :: reg
    integer :: base
    base = vs_enter(1)
    call vs_set(base + 1, ns)
    reg = gc_root_get(registry_root)
    reg = gca_assoc(reg, gc_slot(vs_get(base + 1), 1), vs_get(base + 1), &
         [vs_get(base + 1), reg])
    call gc_global_keep(registry_root, reg)
    call vs_leave(base)
  end subroutine register

  function gcn_current(roots) result(ns)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: ns
    if (.not. roots_live()) call gcn_reset(roots)
    ! Deref the Var. Compiler.CURRENT_NS IS #'clojure.core/*ns* and
    ! in-ns sets it, so the current namespace is a Var value and
    ! nothing else. That is what makes (binding [*ns* *ns*] (in-ns
    ! ...)) restore on the way out for free: binding swaps the Var,
    ! and there is no second copy to fall out of step with it.
    !
    ! There used to be a second copy. It drifted exactly once and
    ! exactly as predicted -- the REPL prompt said G__2281 while *ns*
    ! said user, because binding writes the Var and knows nothing
    ! about namespaces.
    if (gc_root_live(ns_var_root)) then
       ns = gcn_var_value(gc_root_get(ns_var_root))
       if (gc_kind(ns) == OBJ_NS) return
    end if
    ns = gc_root_get(current_root)
  end function gcn_current

  ! Sets the Var, which IS the current namespace. The bootstrap copy
  ! is written too, for the window before clojure.core exists.
  subroutine gcn_set_current(ns)
    type(gc_value), intent(in) :: ns
    type(gc_value) :: core, sym
    integer :: base
    call gc_global_keep(current_root, ns)
    ! Only once the registry exists: gcn_reset calls this on its way up,
    ! and find-or-create would call gcn_reset straight back.
    if (.not. roots_live()) return
    base = vs_enter(2)
    call vs_set(base + 1, ns)
    core = gcn_find_or_create("clojure.core", [vs_get(base + 1)])
    call vs_set(base + 2, core)
    sym = gc_sym("*ns*", [vs_get(base + 1), vs_get(base + 2)])
    core = gcn_intern(vs_get(base + 2), sym, vs_get(base + 1), &
         [vs_get(base + 1), vs_get(base + 2), sym])
    ! Cache the VAR, not its value: gcn_current then derefs it with no
    ! lookup and no allocation, on a path that runs constantly.
    call gc_global_keep(ns_var_root, core)
    call vs_leave(base)
  end subroutine gcn_set_current

  function gcn_name(ns) result(s)
    type(gc_value), intent(in) :: ns
    character(len=:), allocatable :: s
    type(gc_value) :: nm
    s = ""
    if (gc_kind(ns) /= OBJ_NS) return
    nm = gc_slot(ns, 1)
    s = gc_ref_text(nm%ref)
  end function gcn_name

  function gcn_find_or_create(name, roots) result(ns)
    character(len=*), intent(in) :: name
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: ns, key, reg
    integer :: base

    base = vs_enter(2)
    if (.not. roots_live()) call gcn_reset(roots)
    key = gc_str(name, roots)
    call vs_set(base + 1, key)
    reg = gc_root_get(registry_root)
    call vs_set(base + 2, reg)
    ns = gca_get(vs_get(base + 2), vs_get(base + 1))
    if (gc_kind(ns) /= OBJ_NS) then
       ns = make_ns(name, [vs_get(base + 1), vs_get(base + 2)])
       call register(ns)
    end if
    call vs_leave(base)
  end function gcn_find_or_create

  function gcn_is_var(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    yes = (gc_kind(v) == OBJ_VAR)
  end function gcn_is_var

  function gcn_var_value(v) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value) :: out
    out = gc_nil()
    if (gcn_is_var(v)) out = gc_slot(v, 1)
  end function gcn_var_value

  subroutine gcn_set_var(v, val)
    type(gc_value), intent(in) :: v, val
    if (gcn_is_var(v)) call gc_set_slot(v, 1, val)
  end subroutine gcn_set_var

  ! Interns `sym` in `ns`. An existing Var is MUTATED rather than
  ! replaced -- that is the whole reason Vars exist, and it is what
  ! lets a closure built before a redefinition see the new value.
  function gcn_intern(ns, sym, val, roots) result(var)
    type(gc_value), intent(in) :: ns, sym, val
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: var, binds
    integer :: base

    var = gc_nil()
    if (gc_kind(ns) /= OBJ_NS) return
    base = vs_enter(4)
    call vs_set(base + 1, ns)
    call vs_set(base + 2, sym)
    call vs_set(base + 3, val)

    binds = gc_slot(vs_get(base + 1), 2)
    var = gca_get(binds, sym)
    if (gcn_is_var(var)) then
       ! Mutate it only if THIS namespace owns it. Redefining a Var in
       ! place is deliberate -- it is what lets a REPL redefinition
       ! reach closures that already captured it -- but a namespace's
       ! bindings map holds the Vars it REFERS as well as the ones it
       ! interned, so finding the name here is not proof of ownership.
       !
       ! Without the check, (defn first [x] :s) in any namespace found
       ! clojure.core's referred first and mutated THAT, redefining
       ! clojure.core/first for the whole program. Shadowing `next`
       ! did not shadow it, it destroyed it, and core's own loops --
       ! sigs, last, butlast -- then spun forever. clojure.zip hung on
       ! exactly this. Clojure interns a NEW Var in the current
       ! namespace and leaves the referred one alone.
       block
         type(gc_value) :: owner
         logical :: ours
         owner = gc_slot(var, 3)
         if (gc_kind(owner) == OBJ_NS) then
            ours = (gcn_name(owner) == gcn_name(vs_get(base + 1)))
         else
            ! No owner recorded: a Var from before namespaces carried
            ! one. Treat it as ours, which is what it always was.
            ours = .true.
         end if
         if (ours) then
            call gc_set_slot(var, 1, vs_get(base + 3))
            call vs_leave(base)
            return
         end if
         ! Replacing a name this namespace only REFERRED is legal and
         ! occasionally meant, but it is worth saying out loud --
         ! Namespace.checkReplacement prints exactly this, to stderr,
         ! and it is how you find out you have shadowed something you
         ! did not mean to. A namespace that declares the shadowing up
         ! front, (:refer-clojure :exclude (next)), has nothing left to
         ! replace and so says nothing.
         write(0, '(A)') "WARNING: " // gc_ref_text(sym%ref) // &
              " already refers to: #'" // gcn_name(owner) // "/" // &
              gc_ref_text(sym%ref) // " in namespace: " // &
              gcn_name(vs_get(base + 1)) // ", being replaced by: #'" // &
              gcn_name(vs_get(base + 1)) // "/" // gc_ref_text(sym%ref)
       end block
    end if

    var = gc_obj(OBJ_VAR, [vs_get(base + 3), gc_nil(), vs_get(base + 1), &
         vs_get(base + 2)], &
         [vs_get(base + 1), vs_get(base + 2), vs_get(base + 3)])
    call vs_set(base + 4, var)
    binds = gca_assoc(gc_slot(vs_get(base + 1), 2), vs_get(base + 2), &
         vs_get(base + 4), [vs_get(base + 1), vs_get(base + 2), vs_get(base + 4)])
    call gc_set_slot(vs_get(base + 1), 2, binds)
    var = vs_get(base + 4)
    call vs_leave(base)
  end function gcn_intern

  ! The Var `sym` names in `ns`, or nil. Returns the VAR, not its
  ! value, because a caller that wants the var itself (#'x) and one
  ! that wants the value need different things from the same lookup.
  function gcn_lookup(ns, sym) result(var)
    type(gc_value), intent(in) :: ns, sym
    type(gc_value) :: var
    var = gc_nil()
    if (gc_kind(ns) /= OBJ_NS) return
    var = gca_get(gc_slot(ns, 2), sym)
  end function gcn_lookup

end module GCNamespace
