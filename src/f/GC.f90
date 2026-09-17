! GC: a non-moving mark-sweep heap, built standalone.
!
! Nothing in clotran uses this yet. It exists so the collector can be
! written and tested on its own before the value representation is
! committed to it -- see PLAN.md step 3.
!
! WHY THIS EXISTS AT ALL. Measured: one `cons_value` copy costs 497 ns,
! and 94.7% of clotran's runtime is flang's generic derived-type
! machinery. That is a per-COPY cost, not allocation and not freeing,
! and it is there because `cons_value` has a FINAL binding and nine
! allocatable components. The same data in a type with no FINAL copies
! in 4 ns. So the value type has to lose FINAL, which means its
! components can no longer free themselves, which means something else
! has to reclaim them. Hence a tracing collector.
!
! THE SHAPE, and why each choice:
!
!   non-moving   A compacting collector relocates objects, which
!                invalidates any pointer a Fortran library is holding.
!                Handing array buffers to dgemm or ChemSol is the point
!                of the project, so addresses stay put. It also keeps
!                rooting simple: a root is a value, not the ADDRESS of
!                a local that the collector would have to rewrite.
!
!   handles      A reference is an INDEX into a pool, not a pointer. It
!                can be bounds-checked, dumped and printed -- see
!                gc_check_heap, which walks the whole heap asserting no
!                live object points at a freed slot. A corrupt
!                reference is a bad index rather than a wild pointer,
!                and we will be debugging this collector.
!
!   roots passed A thread's root set is an ARGUMENT, never a module
!                global. Per PLAN.md, concurrency comes after this, and
!                a thread is then just another context with its own
!                roots. Making the whole root set global here would
!                mean rewriting the collector later.
!
!                The exception is a genuinely PROCESS-wide root, and
!                the namespace registry is one: it is shared by every
!                thread, so there is no context to pass it through, and
!                it lives until exit. Those register once via
!                gc_global_new and the collector scans them alongside
!                the caller's. The split is the point -- global means
!                shared by all threads, argument means owned by one.
!
! THREE POOLS, NOT FIFTEEN. Fortran cannot cast, so each node kind
! needs its own typed array -- and clotran has about fifteen of them
! (cons cells, trie nodes, array maps, HAMT nodes, closures, atoms,
! lazy seqs, metadata boxes, arity clauses, environments, namespaces,
! ...). One pool per kind is fifteen near-identical allocators, free
! lists, mark arrays and trace routines.
!
! Underneath, nearly all of them are one of two shapes:
!
!   obj   a FIXED, small number of value slots plus a couple of small
!         integers. A cons cell is two slots; a closure is params,
!         body, env, clauses; a lazy seq is a state integer plus thunk,
!         head and tail; an environment is bindings plus outer.
!   vec   a VARIABLE-length run of values. A vector trie node's
!         children, an array map's keys and vals, a multi-arity fn's
!         clauses, a Var's dynamic binding stack.
!
! plus raw character data for text. So: three pools, three trace
! routines, and an object's own `kind` says which shape it means.
! Adding a clotran type is then a new OBJ_ constant, not a new pool.
!
! `gc_value` deliberately has no allocatable components and no FINAL,
! which is the entire point: copying one is a flat move.
module GC
  implicit none
  private

  integer, parameter, public :: gc_dp = kind(1.0d0)

  ! Tags say what a value IS, and which pool `ref` indexes into.
  !
  ! GCT_, not GC_: Fortran is case-insensitive, so a parameter GC_CONS
  ! and a function gc_cons are the SAME name and collide. Same trap as
  ! LAZY_CONS/lazy_cons in the gotchas catalog.
  !
  ! An immediate holds its whole value inline and never touches the
  ! heap, which matters because most values in a running program are
  ! one of these. A character is its code point, not a one-char string.
  integer, parameter, public :: GCT_NIL  = 0
  integer, parameter, public :: GCT_BOOL = 1
  integer, parameter, public :: GCT_INT  = 2
  integer, parameter, public :: GCT_REAL = 3
  integer, parameter, public :: GCT_CHAR = 4
  ! Text in the string pool. Three tags because a string, a symbol and
  ! a keyword differ in behaviour, not in storage.
  integer, parameter, public :: GCT_STR  = 5
  integer, parameter, public :: GCT_SYM  = 6
  integer, parameter, public :: GCT_KEY  = 7
  ! Anything in the object pool. What it MEANS is the object's own kind
  ! (OBJ_* below); the tag only says "this lives in the object pool".
  integer, parameter, public :: GCT_OBJ  = 8
  ! A run of values. Internal -- reached from objects, not normally
  ! held by user code directly.
  integer, parameter, public :: GCT_VEC  = 9

  ! Object kinds. Each comment says what that kind's slots hold.
  integer, parameter, public :: OBJ_CONS    = 1  ! 1=car 2=cdr
  integer, parameter, public :: OBJ_VECTOR  = 2  ! 1=root vec; i1=count i2=shift
  integer, parameter, public :: OBJ_MAP     = 3  ! 1=keys vec 2=vals vec; i1=count
  integer, parameter, public :: OBJ_CLOSURE = 4  ! 1=params 2=body 3=env 4=clauses; i1=macro?
  integer, parameter, public :: OBJ_ATOM    = 5  ! 1=value 2=meta 3=dynamic stack
  integer, parameter, public :: OBJ_LAZY    = 6  ! 1=thunk 2=head 3=tail; i1=state
  ! A lazy seq's three states. PENDING means the thunk has not run;
  ! the other two are what it turned out to be, cached on the node so
  ! walking a seq costs O(1) per cell rather than re-running the thunk.
  integer, parameter, public :: LAZY_PENDING = 0
  integer, parameter, public :: LAZY_CONS    = 1
  integer, parameter, public :: LAZY_EMPTY   = 2
  integer, parameter, public :: OBJ_ENV     = 7  ! 1=bindings 2=outer; i1=defining ns
  ! A value CARRYING metadata: slot 1 = the value, slot 2 = the
  ! metadata map. A wrapper rather than a field, because gc_value
  ! has no spare component -- that is the point of it -- and
  ! because symbol text is INTERNED, so metadata hung off a
  ! string-pool slot would apply to every `foo` in the program.
  !
  ! Everything that consumes a value must see through this, which
  ! is the cost. It is contained by unwrapping in one place:
  ! gce_eval evaluates the value inside, so metadata is invisible
  ! to every form that does not specifically ask for it.
  integer, parameter, public :: OBJ_META    = 8  ! 1=value 2=meta
  ! A namespace is an ordinary object, not a pool of its own: name plus
  ! two maps. Reached only from the registry (a global root), so a
  ! namespace is never collected -- which is the semantics anyway,
  ! Clojure drops one only on remove-ns.
  integer, parameter, public :: OBJ_NS      = 9  ! 1=name 2=bindings 3=aliases
  ! Same shape as OBJ_ATOM plus a name, and deliberately a distinct
  ! kind: the box is identical, the behaviour is not (a Var derefs
  ! through its dynamic stack and prints as #'ns/name).
  ! HAMT (GCHamt.f90): a node is a VEC run of 32 slots, each holding
  ! nil (empty), an OBJ_HAMT_LEAF, another run (a child node), or an
  ! OBJ_MAP (a hash-collision bucket -- a collision set IS a small
  ! linear map, so it reuses the one that already exists).
  ! A primitive implemented in Fortran: slot 1 = its name (for
  ! printing and errors), i1 = which one. Distinct from OBJ_CLOSURE so
  ! that "is this callable" and "does this have a body to evaluate"
  ! stay separate questions.
  integer, parameter, public :: OBJ_BUILTIN   = 13 ! 1=name; i1=id
  ! What `recur` evaluates to: slot 1 = a vector of its arguments.
  ! A VALUE rather than a control-flow mechanism in the host, because
  ! the recur point (a loop* or a fn* body) is the only thing that
  ! knows how to rebind, and it is the one that catches this.
  integer, parameter, public :: OBJ_RECUR     = 14 ! 1=args vector
  ! A SEQ VIEW over an indexable collection: slot 1 = the source,
  ! i1 = the current index. Vectors, strings and maps become seqable
  ! through this without being copied, so `rest` is O(1) -- it is a
  ! new view, not a new collection.
  !
  ! Lists and lazy seqs need no view: they ARE seqs already, which is
  ! the same split real Clojure makes (PersistentList implements ISeq;
  ! PersistentVector does not, and hands out a ChunkedSeq).
  integer, parameter, public :: OBJ_SEQ       = 15 ! 1=source; i1=index
  ! A set, backed by a map from each element to itself -- which is
  ! how real Clojure does it (PersistentHashSet wraps a map). A
  ! distinct kind rather than a bare map so that it prints as #{...}
  ! and answers set? rather than map?.
  integer, parameter, public :: OBJ_SET       = 16 ! 1=backing map
  ! A multimethod: a dispatch function plus a table from dispatch value
  ! to method. MUTABLE, as MultiFn is in Clojure -- addMethod alters the
  ! object rather than returning a new one, which is what lets defmethod
  ! extend a multimethod defined in another file.
  integer, parameter, public :: OBJ_MULTIFN   = 17 ! 1=name 2=dispatch 3=default 4=methods
  ! A StringBuilder: slot 1 holds the text so far. The one MUTABLE
  ! sequence-ish object here, and it exists because core.clj's own `str`
  ! is written around one.
  !
  ! Appending rebuilds the string, so building a string of length n out
  ! of n pieces is O(n^2) -- a real StringBuilder amortises it. Fine for
  ! (str a b c); a growable text buffer in GC.f90 is what to write if
  ! anything ever appends in a loop.
  integer, parameter, public :: OBJ_SB        = 18 ! 1=text
  ! A THROWN THING: slot 1 = the class name it was constructed with,
  ! slot 2 = its message, slot 3 = its data (what ex-info carries).
  !
  ! Clojure throws Java objects and clotran has none, so this is what
  ! (IllegalArgumentException. "...") and (ex-info msg m) both build.
  ! A real kind rather than a map with a :type key, so that
  ! (instance? Throwable x) is an exact answer and not a guess about
  ! what a map might mean.
  integer, parameter, public :: OBJ_ERR       = 19 ! 1=class 2=message 3=data
  ! A compiled regex (Regex.f90). Slot 1 = the original source text (so
  ! it prints back as #"..." and (str pattern) round-trips), i1 = a
  ! handle index into Regex.f90's own registry -- a handle is an opaque
  ! C pointer, and gc_value keeps no pointer fields, so it is looked up
  ! by index exactly the way a namespace or a Var is.
  integer, parameter, public :: OBJ_REGEX     = 20 ! 1=source text; i1=handle
  ! (.matcher) on a Pattern: slot 1 = the Pattern object (keeps it, and
  ! the ICU handle beneath it, alive), slot 2 = the subject text (for
  ! Fortran to slice group spans out of), i1 = this matcher's OWN
  ! cloned handle -- independent of the Pattern's, so two matchers over
  ! one Pattern never share search position (see Regex.f90).
  integer, parameter, public :: OBJ_MATCHER   = 21 ! 1=pattern 2=subject; i1=handle
  integer, parameter, public :: OBJ_WRITER    = 22 ! i1=Fortran unit
  ! What `deftype*` and `reify*` create, and what an instance of one
  ! is. A TYPE is a name, the field names in declaration order, a map
  ! from method-name keyword to the closure implementing it, and the
  ! class keywords it claims to implement -- which is all `instance?`
  ! has to consult, since there is no class hierarchy to walk.
  !
  ! A real kind rather than a map with a hidden key (the trick
  ! (reduced x) uses), because an instance that answered `map?` and
  ! seq'd like a map would be a SILENT wrong answer everywhere a
  ! deftype is not map-like -- which, for deftype as opposed to
  ! defrecord, is everywhere.
  integer, parameter, public :: OBJ_TYPE      = 23 ! 1=name 2=fields 3=methods 4=implements
  integer, parameter, public :: OBJ_INST      = 24 ! 1=type 2=field values 3=meta
  ! A DELAY: slot 1 = the no-argument thunk, slot 2 = what it
  ! produced, i1 = whether it has run. `delay` is literally
  ! (new clojure.lang.Delay (fn [] ...)) in core.clj, and deref runs
  ! it ONCE and caches -- which is the whole contract.
  !
  ! Distinct from OBJ_LAZY, which caches a first and a rest and whose
  ! forcing expects a seq. A delay holds one value of any kind.
  integer, parameter, public :: OBJ_DELAY     = 25 ! 1=thunk 2=value; i1=forced?
  integer, parameter, public :: OBJ_HAMT      = 11 ! 1=root run; i1=count
  integer, parameter, public :: OBJ_HAMT_LEAF = 12 ! 1=key 2=val
  ! Slot 3 was reserved for a per-Var dynamic stack; the dynamic
  ! bindings ended up in one global frame stack instead (GCEval), so the
  ! slot holds the Var's OWN NAMESPACE -- which Var.ns is in Clojure, and
  ! which ns-publics needs to tell a Var defined here from one referred
  ! in from somewhere else.
  integer, parameter, public :: OBJ_VAR     = 10 ! 1=root 2=meta 3=ns 4=name

  ! FIVE, not four. A protocol function carries its dispatch cache
  ! on itself -- (set! (.__methodImplCache f) cache) in
  ! emit-method-builder, read back on every call -- and a closure's
  ! four slots are all spoken for: params, body, env, clauses. The
  ! clause slot looked free for single-arity fns, but a protocol
  ! method has one arity per signature, so it is not.
  !
  ! The fifth slot costs one gc_value on every object in the heap,
  ! which is the honest price of not having a place to put it.
  integer, parameter, public :: OBJ_SLOTS = 5

  ! A claim on a global root slot. Two fields rather than one integer
  ! because an index alone is ambiguous across a gc_init -- see
  ! global_gen. Modules keep one of these instead of a bare index.
  type, public :: gc_root
     integer :: idx = 0
     integer :: gen = -1
  end type gc_root

  type, public :: gc_value
     integer :: tag = GCT_NIL
     integer :: ival = 0
     real(gc_dp) :: rval = 0.0_gc_dp
     integer :: ref = 0 ! index into this tag's pool; 0 for immediates
  end type gc_value

  ! --- object pool -----------------------------------------------
  type :: obj_node
     integer :: kind = 0
     integer :: i1 = 0, i2 = 0 ! inline payload (count, shift, state, ...)
     type(gc_value) :: slot(OBJ_SLOTS)
  end type obj_node

  type(obj_node), allocatable :: obj_pool(:)
  logical, allocatable :: obj_mark(:), obj_free(:)
  integer, allocatable :: obj_free_next(:)
  integer :: obj_free_head = 0, obj_used = 0

  ! --- value-run pool --------------------------------------------
  type :: vec_node
     type(gc_value), allocatable :: items(:)
  end type vec_node

  type(vec_node), allocatable :: vec_pool(:)
  logical, allocatable :: vec_mark(:), vec_free(:)
  integer, allocatable :: vec_free_next(:)
  integer :: vec_free_head = 0, vec_used = 0

  ! --- string pool -----------------------------------------------
  ! Text is a heap object too: a value stays copyable by a flat move,
  ! so it cannot own a deferred-length character of its own.
  type :: str_node
     character(len=:), allocatable :: text
  end type str_node

  type(str_node), allocatable :: str_pool(:)
  logical, allocatable :: str_mark(:), str_free(:)
  integer, allocatable :: str_free_next(:)
  integer :: str_free_head = 0, str_used = 0

  ! --- global roots ----------------------------------------------
  ! Process-wide and mutable: the registry handle changes whenever the
  ! registry grows, so a global is a SLOT, not a value handed over once.
  ! GROWABLE, and with no maximum to maintain. It was a fixed array of
  ! eight, which was exactly the number claimed, so the ninth (GCEval's
  ! type table) was dropped SILENTLY -- registered nowhere, collected
  ! on the next sweep, and visible only as "no such class" for a type
  ! that had just been defined.
  !
  ! Raising the constant would have fixed that instance and kept the
  ! shape that caused it: a limit in THIS file that has to be
  ! maintained in step with `type(gc_root), save ::` declarations in
  ! other ones. There is no number here now, so there is nothing to
  ! keep in step and nothing to exhaust.
  !
  ! It does not grow large. Every root is a module-level singleton --
  ! nine today -- and nothing claims one per object: a million deftypes
  ! live inside the one types_root map, a million namespaces inside
  ! registry_root. So this doubles once, at startup, and never again.
  type(gc_value), allocatable :: global_root(:)
  integer :: global_count = 0
  ! Bumped by gc_init. A module holding a slot index across a reset
  ! cannot tell "my slot" from "someone else's slot that now has my
  ! number" -- and a stale index that lands back IN range silently
  ! overwrites another module's root. The generation is what makes
  ! that distinguishable; see gc_root and gc_global_keep.
  integer :: global_gen = 0

  ! --- the value stack (PLAN.md 3d, Design B) ----------------------
  !
  ! The evaluator's roots, and the reason rooting is by CONSTRUCTION
  ! rather than by discipline: a value the evaluator is working on
  ! lives in a stack slot, and the collector scans every live slot. A
  ! missed root is not a bug you can write, because there is nowhere
  ! else to put the value.
  !
  ! Frames are a base index, not a linked structure: vs_enter reserves
  ! n slots and returns the base, vs_leave pops back to it. Leaving is
  ! what makes a frame's values collectable, so it must be paired --
  ! and because the base is returned and passed back, an unbalanced
  ! leave is visible rather than silent.
  !
  ! Lives in this module, not beside the evaluator, because the
  ! collector has to scan it directly and nothing else may.
  type(gc_value), allocatable :: vstack(:)
  integer :: vs_top = 0

  ! --- marking work list -----------------------------------------
  ! An explicit stack, not recursion: a list is a chain thousands of
  ! nodes deep, and recursive marking would overflow the real stack on
  ! exactly the structure this language builds most.
  type(gc_value), allocatable :: mark_stack(:)
  integer :: mark_sp = 0

  integer, public :: gc_allocs = 0
  integer, public :: gc_frees = 0
  integer, public :: gc_collections = 0

  ! Collect at EVERY allocation. Turns a missing root from a rare,
  ! timing-dependent corruption into an immediate, deterministic
  ! failure; the test suite runs under it.
  logical, public :: gc_torture = .false.

  ! MIGRATION SCAFFOLDING -- PLAN.md 3c-2. Payloads move into this heap
  ! one at a time, and until 3d makes the evaluator root properly there
  ! is nothing to trace from: a collection would sweep everything that
  ! is actually live. In this mode the pools only ever grow, never
  ! collect. It is a leak by construction, and temporary; 3d turns it
  ! off, and gc_check_heap plus torture mode are what replace it.
  logical, public :: gc_no_collect = .false.

  public :: gc_init, gc_collect
  public :: gc_nil, gc_bool, gc_int, gc_real, gc_char, gc_str, gc_sym, gc_key
  public :: gc_obj, gc_vec, gc_cons
  public :: gc_text, gc_slot, gc_set_slot, gc_kind
  public :: gc_i1, gc_i2, gc_set_i1, gc_set_i2
  public :: gc_vec_len, gc_vec_get, gc_vec_set
  public :: gc_car, gc_cdr, gc_set_car, gc_set_cdr
  public :: gc_live_count, gc_obj_capacity, gc_check_heap
  public :: gc_global_new, gc_global_set, gc_global_get, gc_global_count
  public :: gc_global_keep, gc_root_get, gc_root_live
  public :: gc_ensure_init, gc_str_ref, gc_ref_text, gc_ref_is, gc_ref_len
  public :: vs_enter, vs_leave, vs_set, vs_get, vs_depth
  public :: gc_equal, gc_hash

contains

  ! Self-initialising, so the nine test drivers and main.f90 do not
  ! each need a gc_init call while payloads are being migrated. Starts
  ! in grow-only mode deliberately -- see gc_no_collect.
  subroutine gc_ensure_init()
    if (allocated(obj_pool)) return
    call gc_init()
    gc_no_collect = .true.
  end subroutine gc_ensure_init

  ! ---- ref-level text API (PLAN.md 3c-2) --------------------------
  !
  ! A migrating cons_value holds a bare handle, not a gc_value, so text
  ! is reached by ref. Split the same way Values' own accessors are:
  ! gc_ref_is and gc_ref_len touch the pool WITHOUT copying, because
  ! comparing a symbol against a literal is the hottest read in the
  ! interpreter. gc_ref_text is the one that copies.

  function gc_str_ref(text) result(ref)
    character(len=*), intent(in) :: text
    integer :: ref
    type(gc_value) :: v
    type(gc_value) :: none(0)
    call gc_ensure_init()
    v = new_text(text, none, GCT_STR)
    ref = v%ref
  end function gc_str_ref

  logical function ref_ok(ref)
    integer, intent(in) :: ref
    ref_ok = .false.
    if (ref <= 0) return
    if (.not. allocated(str_pool)) return
    if (ref > str_used) return
    ref_ok = allocated(str_pool(ref)%text)
  end function ref_ok

  function gc_ref_text(ref) result(s)
    integer, intent(in) :: ref
    character(len=:), allocatable :: s
    s = ""
    if (ref_ok(ref)) s = str_pool(ref)%text
  end function gc_ref_text

  function gc_ref_is(ref, s) result(yes)
    integer, intent(in) :: ref
    character(len=*), intent(in) :: s
    logical :: yes
    yes = .false.
    if (ref_ok(ref)) yes = (str_pool(ref)%text == s)
  end function gc_ref_is

  function gc_ref_len(ref) result(n)
    integer, intent(in) :: ref
    integer :: n
    n = 0
    if (ref_ok(ref)) n = len(str_pool(ref)%text)
  end function gc_ref_len

  subroutine gc_init(initial)
    integer, intent(in), optional :: initial
    integer :: n
    n = 256
    if (present(initial)) n = max(initial, 8)

    if (allocated(obj_pool)) deallocate(obj_pool, obj_mark, obj_free, obj_free_next)
    allocate(obj_pool(n), obj_mark(n), obj_free(n), obj_free_next(n))
    obj_mark = .false.; obj_free = .false.; obj_free_next = 0
    obj_free_head = 0; obj_used = 0

    if (allocated(vec_pool)) deallocate(vec_pool, vec_mark, vec_free, vec_free_next)
    allocate(vec_pool(n), vec_mark(n), vec_free(n), vec_free_next(n))
    vec_mark = .false.; vec_free = .false.; vec_free_next = 0
    vec_free_head = 0; vec_used = 0

    if (allocated(str_pool)) deallocate(str_pool, str_mark, str_free, str_free_next)
    allocate(str_pool(n), str_mark(n), str_free(n), str_free_next(n))
    str_mark = .false.; str_free = .false.; str_free_next = 0
    str_free_head = 0; str_used = 0

    if (allocated(vstack)) deallocate(vstack)
    allocate(vstack(max(n, 64)))
    vstack = gc_nil()
    vs_top = 0

    if (allocated(mark_stack)) deallocate(mark_stack)
    allocate(mark_stack(n))
    mark_sp = 0

    if (allocated(global_root)) deallocate(global_root)
    allocate(global_root(8))
    global_root = gc_nil()
    global_count = 0
    global_gen = global_gen + 1
    gc_allocs = 0; gc_frees = 0; gc_collections = 0
    gc_no_collect = .false.
  end subroutine gc_init

  ! --- immediates: no heap involved at all -----------------------

  function gc_nil() result(v)
    type(gc_value) :: v
    v%tag = GCT_NIL
  end function gc_nil

  function gc_bool(b) result(v)
    logical, intent(in) :: b
    type(gc_value) :: v
    v%tag = GCT_BOOL
    if (b) v%ival = 1
  end function gc_bool

  function gc_int(i) result(v)
    integer, intent(in) :: i
    type(gc_value) :: v
    v%tag = GCT_INT
    v%ival = i
  end function gc_int

  function gc_real(r) result(v)
    real(gc_dp), intent(in) :: r
    type(gc_value) :: v
    v%tag = GCT_REAL
    v%rval = r
  end function gc_real

  function gc_char(c) result(v)
    character, intent(in) :: c
    type(gc_value) :: v
    v%tag = GCT_CHAR
    v%ival = iachar(c)
  end function gc_char

  ! --- allocation ------------------------------------------------
  !
  ! Every allocator takes the caller's roots AND roots whatever it was
  ! handed. A freshly built value passed as an ARGUMENT is live but
  ! cannot be in the caller's root list, because nothing references it
  ! yet -- see gc_test check 10a, which fails without this.

  function gc_str(text, roots) result(v)
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    v = new_text(text, roots, GCT_STR)
  end function gc_str

  function gc_sym(text, roots) result(v)
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    v = new_text(text, roots, GCT_SYM)
  end function gc_sym

  function gc_key(text, roots) result(v)
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    v = new_text(text, roots, GCT_KEY)
  end function gc_key

  function new_text(text, roots, tag) result(v)
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    integer, intent(in) :: tag
    type(gc_value) :: v
    integer :: idx
    if (gc_no_collect) then
       if (str_free_head == 0 .and. str_used >= size(str_pool)) call grow_str()
    else if (gc_torture .or. (str_free_head == 0 .and. str_used >= size(str_pool))) then
       call gc_collect(roots)
       if (str_free_head == 0 .and. str_used >= size(str_pool)) call grow_str()
    end if
    if (str_free_head /= 0) then
       idx = str_free_head
       str_free_head = str_free_next(idx)
    else
       str_used = str_used + 1
       idx = str_used
    end if
    str_free(idx) = .false.
    str_pool(idx)%text = text
    v%tag = tag
    v%ref = idx
    gc_allocs = gc_allocs + 1
  end function new_text

  ! An object of the given kind, with up to OBJ_SLOTS initial slots.
  function gc_obj(kind, slots, roots) result(v)
    integer, intent(in) :: kind
    type(gc_value), intent(in) :: slots(:), roots(:)
    type(gc_value) :: v
    type(gc_value), allocatable :: all_roots(:)
    integer :: idx, i

    if (gc_no_collect) then
       if (obj_free_head == 0 .and. obj_used >= size(obj_pool)) call grow_obj()
    else if (gc_torture .or. (obj_free_head == 0 .and. obj_used >= size(obj_pool))) then
       allocate(all_roots(size(roots) + size(slots)))
       all_roots(1:size(roots)) = roots
       all_roots(size(roots) + 1:) = slots
       call gc_collect(all_roots)
       if (obj_free_head == 0 .and. obj_used >= size(obj_pool)) call grow_obj()
    end if
    if (obj_free_head /= 0) then
       idx = obj_free_head
       obj_free_head = obj_free_next(idx)
    else
       obj_used = obj_used + 1
       idx = obj_used
    end if
    obj_free(idx) = .false.
    obj_pool(idx)%kind = kind
    obj_pool(idx)%i1 = 0
    obj_pool(idx)%i2 = 0
    do i = 1, OBJ_SLOTS
       obj_pool(idx)%slot(i) = gc_nil()
    end do
    do i = 1, min(size(slots), OBJ_SLOTS)
       obj_pool(idx)%slot(i) = slots(i)
    end do
    v%tag = GCT_OBJ
    v%ref = idx
    gc_allocs = gc_allocs + 1
  end function gc_obj

  ! A run of n values, all nil.
  function gc_vec(n, roots) result(v)
    integer, intent(in) :: n
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: idx, i

    if (gc_no_collect) then
       if (vec_free_head == 0 .and. vec_used >= size(vec_pool)) call grow_vec()
    else if (gc_torture .or. (vec_free_head == 0 .and. vec_used >= size(vec_pool))) then
       call gc_collect(roots)
       if (vec_free_head == 0 .and. vec_used >= size(vec_pool)) call grow_vec()
    end if
    if (vec_free_head /= 0) then
       idx = vec_free_head
       vec_free_head = vec_free_next(idx)
    else
       vec_used = vec_used + 1
       idx = vec_used
    end if
    vec_free(idx) = .false.
    if (allocated(vec_pool(idx)%items)) deallocate(vec_pool(idx)%items)
    allocate(vec_pool(idx)%items(max(n, 0)))
    do i = 1, n
       vec_pool(idx)%items(i) = gc_nil()
    end do
    v%tag = GCT_VEC
    v%ref = idx
    gc_allocs = gc_allocs + 1
  end function gc_vec

  ! A cons cell is an object of two slots, allocated often enough to
  ! deserve its own name.
  function gc_cons(car, cdr, roots) result(v)
    type(gc_value), intent(in) :: car, cdr, roots(:)
    type(gc_value) :: v
    type(gc_value) :: pair(2)
    pair(1) = car
    pair(2) = cdr
    v = gc_obj(OBJ_CONS, pair, roots)
  end function gc_cons

  ! --- growth ----------------------------------------------------
  ! Doubling, with move_alloc rather than array assignment -- see the
  ! reallocating-assignment entries in NOTES.md's gotchas catalog.

  subroutine grow_obj()
    type(obj_node), allocatable :: bigger(:)
    logical, allocatable :: bmark(:), bfree(:)
    integer, allocatable :: bnext(:)
    integer :: n, i
    n = size(obj_pool)
    allocate(bigger(2 * n), bmark(2 * n), bfree(2 * n), bnext(2 * n))
    do i = 1, n
       bigger(i) = obj_pool(i)
    end do
    bmark = .false.; bfree = .false.; bnext = 0
    bfree(1:n) = obj_free(1:n)
    bnext(1:n) = obj_free_next(1:n)
    call move_alloc(bigger, obj_pool)
    call move_alloc(bmark, obj_mark)
    call move_alloc(bfree, obj_free)
    call move_alloc(bnext, obj_free_next)
  end subroutine grow_obj

  subroutine grow_vec()
    type(vec_node), allocatable :: bigger(:)
    logical, allocatable :: bmark(:), bfree(:)
    integer, allocatable :: bnext(:)
    integer :: n, i
    n = size(vec_pool)
    allocate(bigger(2 * n), bmark(2 * n), bfree(2 * n), bnext(2 * n))
    do i = 1, n
       if (allocated(vec_pool(i)%items)) bigger(i)%items = vec_pool(i)%items
    end do
    bmark = .false.; bfree = .false.; bnext = 0
    bfree(1:n) = vec_free(1:n)
    bnext(1:n) = vec_free_next(1:n)
    call move_alloc(bigger, vec_pool)
    call move_alloc(bmark, vec_mark)
    call move_alloc(bfree, vec_free)
    call move_alloc(bnext, vec_free_next)
  end subroutine grow_vec

  subroutine grow_str()
    type(str_node), allocatable :: bigger(:)
    logical, allocatable :: bmark(:), bfree(:)
    integer, allocatable :: bnext(:)
    integer :: n, i
    n = size(str_pool)
    allocate(bigger(2 * n), bmark(2 * n), bfree(2 * n), bnext(2 * n))
    do i = 1, n
       if (allocated(str_pool(i)%text)) bigger(i)%text = str_pool(i)%text
    end do
    bmark = .false.; bfree = .false.; bnext = 0
    bfree(1:n) = str_free(1:n)
    bnext(1:n) = str_free_next(1:n)
    call move_alloc(bigger, str_pool)
    call move_alloc(bmark, str_mark)
    call move_alloc(bfree, str_free)
    call move_alloc(bnext, str_free_next)
  end subroutine grow_str

  ! --- accessors -------------------------------------------------

  function gc_text(v) result(s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: s
    s = ""
    if (v%tag /= GCT_STR .and. v%tag /= GCT_SYM .and. v%tag /= GCT_KEY) return
    if (allocated(str_pool(v%ref)%text)) s = str_pool(v%ref)%text
  end function gc_text

  function gc_kind(v) result(k)
    type(gc_value), intent(in) :: v
    integer :: k
    k = 0
    if (v%tag == GCT_OBJ) k = obj_pool(v%ref)%kind
  end function gc_kind

  function gc_slot(v, i) result(out)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: out
    if (v%tag == GCT_OBJ .and. i >= 1 .and. i <= OBJ_SLOTS) out = obj_pool(v%ref)%slot(i)
  end function gc_slot

  ! Mutation is what makes CYCLES possible, which is the case
  ! refcounting structurally cannot reclaim and this collector can.
  subroutine gc_set_slot(v, i, x)
    type(gc_value), intent(in) :: v, x
    integer, intent(in) :: i
    if (v%tag == GCT_OBJ .and. i >= 1 .and. i <= OBJ_SLOTS) obj_pool(v%ref)%slot(i) = x
  end subroutine gc_set_slot

  function gc_i1(v) result(i)
    type(gc_value), intent(in) :: v
    integer :: i
    i = 0
    if (v%tag == GCT_OBJ) i = obj_pool(v%ref)%i1
  end function gc_i1

  function gc_i2(v) result(i)
    type(gc_value), intent(in) :: v
    integer :: i
    i = 0
    if (v%tag == GCT_OBJ) i = obj_pool(v%ref)%i2
  end function gc_i2

  subroutine gc_set_i1(v, i)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    if (v%tag == GCT_OBJ) obj_pool(v%ref)%i1 = i
  end subroutine gc_set_i1

  subroutine gc_set_i2(v, i)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    if (v%tag == GCT_OBJ) obj_pool(v%ref)%i2 = i
  end subroutine gc_set_i2

  function gc_vec_len(v) result(n)
    type(gc_value), intent(in) :: v
    integer :: n
    n = 0
    if (v%tag /= GCT_VEC) return
    if (allocated(vec_pool(v%ref)%items)) n = size(vec_pool(v%ref)%items)
  end function gc_vec_len

  function gc_vec_get(v, i) result(out)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: out
    if (v%tag /= GCT_VEC) return
    if (i < 1 .or. i > gc_vec_len(v)) return
    out = vec_pool(v%ref)%items(i)
  end function gc_vec_get

  subroutine gc_vec_set(v, i, x)
    type(gc_value), intent(in) :: v, x
    integer, intent(in) :: i
    if (v%tag /= GCT_VEC) return
    if (i < 1 .or. i > gc_vec_len(v)) return
    vec_pool(v%ref)%items(i) = x
  end subroutine gc_vec_set

  function gc_car(v) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value) :: out
    out = gc_slot(v, 1)
  end function gc_car

  function gc_cdr(v) result(out)
    type(gc_value), intent(in) :: v
    type(gc_value) :: out
    out = gc_slot(v, 2)
  end function gc_cdr

  subroutine gc_set_car(v, x)
    type(gc_value), intent(in) :: v, x
    call gc_set_slot(v, 1, x)
  end subroutine gc_set_car

  subroutine gc_set_cdr(v, x)
    type(gc_value), intent(in) :: v, x
    call gc_set_slot(v, 2, x)
  end subroutine gc_set_cdr

  ! --- collection ------------------------------------------------

  subroutine gc_collect(roots)
    type(gc_value), intent(in) :: roots(:)
    integer :: i

    gc_collections = gc_collections + 1
    obj_mark = .false.
    vec_mark = .false.
    str_mark = .false.
    mark_sp = 0

    do i = 1, global_count
       call push_mark(global_root(i))
    end do
    do i = 1, vs_top
       call push_mark(vstack(i))
    end do
    do i = 1, size(roots)
       call push_mark(roots(i))
    end do
    call drain_mark_stack()
    call sweep()
  end subroutine gc_collect

  ! Value equality, mirroring Values.f90's value_equal so the two
  ! representations agree during the migration: same tag, and same
  ! scalar or text content. Collections compare by IDENTITY, not
  ! deeply -- which is what value_equal does today too, and what map
  ! keys currently rely on. Deep equality for collection keys is a
  ! separate decision, not one to make silently here.
  ! METADATA IS INVISIBLE TO EQUALITY, as it is in Clojure:
  ! (= (with-meta 'a {:m 1}) 'a) is true, and so a hinted symbol has to
  ! find the same entry in a map that a bare one does. core.clj leans on
  ! it -- destructuring looks its :or defaults up by a local name that
  ! carries a hint. DEVIATIONS.md 5.
  recursive function gc_equal(a0, b0) result(eq)
    type(gc_value), intent(in) :: a0, b0
    type(gc_value) :: a, b
    logical :: eq
    a = a0
    b = b0
    do while (gc_kind(a) == OBJ_META)
       a = gc_slot(a, 1)
    end do
    do while (gc_kind(b) == OBJ_META)
       b = gc_slot(b, 1)
    end do
    eq = .false.
    if (a%tag /= b%tag) return
    select case (a%tag)
    case (GCT_NIL)
       eq = .true.
    case (GCT_BOOL, GCT_INT, GCT_CHAR)
       eq = (a%ival == b%ival)
    case (GCT_REAL)
       eq = (a%rval == b%rval)
    case (GCT_STR, GCT_SYM, GCT_KEY)
       ! Compared by CONTENT, not by pool slot: the same text
       ! allocated twice is two slots but one value.
       eq = (gc_ref_len(a%ref) == gc_ref_len(b%ref))
       if (eq) eq = gc_ref_is(a%ref, gc_ref_text(b%ref))
    case default
       eq = (a%ref == b%ref)
    end select
  end function gc_equal

  ! Hash, mirroring PersistentHashMap's hash_of so the two
  ! representations agree during the migration -- same mix32, same
  ! FNV-1a over the text, same tag mixed in so "a" the string and \a
  ! the character do not collide.
  !
  ! It MUST agree with gc_equal: two values that compare equal have to
  ! hash equal, or a trie will store the same key twice and lookups
  ! will find whichever arm they walk into. That is why text hashes
  ! over its CONTENT here, exactly as gc_equal compares content.
  ! Metadata is invisible here for the same reason it is in gc_equal:
  ! two values that are equal must hash equal, or a map loses entries.
  recursive function gc_hash(v0) result(h)
    type(gc_value), intent(in) :: v0
    type(gc_value) :: v
    integer :: h
    integer(kind=8) :: bits8
    v = v0
    do while (gc_kind(v) == OBJ_META)
       v = gc_slot(v, 1)
    end do
    select case (v%tag)
    case (GCT_NIL)
       h = 0
    case (GCT_BOOL)
       if (v%ival /= 0) then
          h = 1231
       else
          h = 1237
       end if
    case (GCT_INT, GCT_CHAR)
       h = mix32(ieor(v%ival, v%tag))
    case (GCT_REAL)
       bits8 = transfer(v%rval, bits8)
       h = mix32(int(ieor(bits8, ishft(bits8, -32)), kind=4))
    case (GCT_STR, GCT_SYM, GCT_KEY)
       h = mix32(ieor(fnv1a(gc_ref_text(v%ref)), v%tag))
    case default
       ! Collections hash by identity, matching gc_equal's default.
       h = mix32(ieor(v%ref, v%tag))
    end select
  end function gc_hash

  function mix32(x) result(h)
    integer, intent(in) :: x
    integer :: h
    h = x
    h = ieor(h, ishft(h, -16))
    h = h * (-2048144789) ! 0x85ebca6b as signed 32-bit
    h = ieor(h, ishft(h, -13))
    h = h * (-1028477387) ! 0xc2b2ae35 as signed 32-bit
    h = ieor(h, ishft(h, -16))
  end function mix32

  function fnv1a(s) result(h)
    character(len=*), intent(in) :: s
    integer :: h, i
    h = -2128831035 ! FNV offset basis, 0x811c9dc5, as signed 32-bit
    do i = 1, len(s)
       h = ieor(h, iachar(s(i:i)))
       h = h * 16777619 ! FNV prime
    end do
  end function fnv1a

  ! --- the value stack -------------------------------------------

  ! Reserves n slots, cleared to nil, and returns the frame's base.
  ! Pass that base back to vs_leave; slots are addressed base+1 .. base+n.
  function vs_enter(n) result(base)
    integer, intent(in) :: n
    integer :: base, i
    type(gc_value), allocatable :: bigger(:)
    call gc_ensure_init()
    do while (vs_top + n > size(vstack))
       allocate(bigger(2 * size(vstack)))
       bigger = gc_nil()
       bigger(1:vs_top) = vstack(1:vs_top)
       call move_alloc(bigger, vstack)
    end do
    base = vs_top
    do i = base + 1, base + n
       vstack(i) = gc_nil()
    end do
    vs_top = base + n
  end function vs_enter

  ! Pops back to base. Clearing on the way out is not tidiness: a stale
  ! value above the top would be traced on the next collection and keep
  ! dead data alive, which is the leak a stack collector is prone to.
  subroutine vs_leave(base)
    integer, intent(in) :: base
    integer :: i
    if (base < 0 .or. base > vs_top) return
    do i = base + 1, vs_top
       vstack(i) = gc_nil()
    end do
    vs_top = base
  end subroutine vs_leave

  subroutine vs_set(slot, v)
    integer, intent(in) :: slot
    type(gc_value), intent(in) :: v
    if (slot >= 1 .and. slot <= vs_top) vstack(slot) = v
  end subroutine vs_set

  function vs_get(slot) result(v)
    integer, intent(in) :: slot
    type(gc_value) :: v
    v = gc_nil()
    if (slot >= 1 .and. slot <= vs_top) v = vstack(slot)
  end function vs_get

  function vs_depth() result(n)
    integer :: n
    n = vs_top
  end function vs_depth

  ! --- global roots ----------------------------------------------

  ! Claims a slot and returns its index. Registration is permanent:
  ! there is no unregister, because the only things that belong here
  ! live until the process exits.
  function gc_global_new(v) result(idx)
    type(gc_value), intent(in) :: v
    integer :: idx
    ! Grows rather than refusing. Returning 0 here used to leave the
    ! caller holding an UNREGISTERED root: everything worked until the
    ! first collection, which then swept something genuinely live.
    ! There was never a recovery a caller could write.
    if (.not. allocated(global_root)) then
       allocate(global_root(8))
       global_root = gc_nil()
    end if
    if (global_count >= size(global_root)) call grow_global_roots()
    global_count = global_count + 1
    global_root(global_count) = v
    idx = global_count
  end function gc_global_new

  ! Doubles the root table, preserving every claimed slot INDEX --
  ! modules hold those indices across calls, so the copy has to land
  ! at the same positions or every held handle would point at someone
  ! else's root. Growing is what makes that safe; the addresses do not
  ! matter, only the indices, and nothing outside this module ever
  ! sees a pointer to the array.
  subroutine grow_global_roots()
    type(gc_value), allocatable :: bigger(:)
    allocate(bigger(max(8, 2 * size(global_root))))
    bigger = gc_nil()
    bigger(1:global_count) = global_root(1:global_count)
    call move_alloc(bigger, global_root)
  end subroutine grow_global_roots

  ! Register-or-update, for a caller holding its slot index in a
  ! module variable across a gc_init.
  !
  ! This exists because getting it wrong is silent and has now bitten
  ! three separate modules. gc_init clears the global-root table, but a
  ! module's saved index survives it -- so gc_global_set on that stale
  ! index does NOTHING (it is out of range), and the root is quietly
  ! never registered again. Everything then works until the first
  ! collection, which sweeps data that is genuinely live.
  !
  ! Callers should use this rather than new/set, and keep the index it
  ! returns.
  subroutine gc_global_keep(h, v)
    type(gc_root), intent(inout) :: h
    type(gc_value), intent(in) :: v
    if (h%gen == global_gen .and. h%idx >= 1 .and. h%idx <= global_count) then
       global_root(h%idx) = v
    else
       h%idx = gc_global_new(v)
       h%gen = global_gen
    end if
  end subroutine gc_global_keep

  ! The value in a claimed slot, or nil if the claim is stale.
  function gc_root_get(h) result(v)
    type(gc_root), intent(in) :: h
    type(gc_value) :: v
    v = gc_nil()
    if (h%gen /= global_gen) return
    v = gc_global_get(h%idx)
  end function gc_root_get

  function gc_root_live(h) result(yes)
    type(gc_root), intent(in) :: h
    logical :: yes
    yes = (h%gen == global_gen .and. h%idx >= 1 .and. h%idx <= global_count)
  end function gc_root_live

  subroutine gc_global_set(idx, v)
    integer, intent(in) :: idx
    type(gc_value), intent(in) :: v
    if (idx >= 1 .and. idx <= global_count) global_root(idx) = v
  end subroutine gc_global_set

  function gc_global_get(idx) result(v)
    integer, intent(in) :: idx
    type(gc_value) :: v
    v = gc_nil()
    if (idx >= 1 .and. idx <= global_count) v = global_root(idx)
  end function gc_global_get

  function gc_global_count() result(n)
    integer :: n
    n = global_count
  end function gc_global_count

  subroutine push_mark(v)
    type(gc_value), intent(in) :: v
    type(gc_value), allocatable :: bigger(:)
    integer :: n
    if (v%ref == 0) return
    select case (v%tag)
    case (GCT_OBJ, GCT_VEC, GCT_STR, GCT_SYM, GCT_KEY)
       continue
    case default
       return ! an immediate holds nothing
    end select
    if (mark_sp >= size(mark_stack)) then
       n = size(mark_stack)
       allocate(bigger(2 * n))
       bigger(1:n) = mark_stack(1:n)
       call move_alloc(bigger, mark_stack)
    end if
    mark_sp = mark_sp + 1
    mark_stack(mark_sp) = v
  end subroutine push_mark

  subroutine drain_mark_stack()
    type(gc_value) :: v
    integer :: i, n
    do while (mark_sp > 0)
       v = mark_stack(mark_sp)
       mark_sp = mark_sp - 1
       select case (v%tag)
       case (GCT_OBJ)
          ! Already-marked stops the walk, which is what makes a cycle
          ! terminate instead of looping forever.
          if (obj_mark(v%ref)) cycle
          obj_mark(v%ref) = .true.
          do i = 1, OBJ_SLOTS
             call push_mark(obj_pool(v%ref)%slot(i))
          end do
       case (GCT_VEC)
          if (vec_mark(v%ref)) cycle
          vec_mark(v%ref) = .true.
          n = 0
          if (allocated(vec_pool(v%ref)%items)) n = size(vec_pool(v%ref)%items)
          do i = 1, n
             call push_mark(vec_pool(v%ref)%items(i))
          end do
       case (GCT_STR, GCT_SYM, GCT_KEY)
          str_mark(v%ref) = .true. ! a leaf: holds no references
       end select
    end do
  end subroutine drain_mark_stack

  ! A per-slot free FLAG, not a scan of the free list: scanning made
  ! sweep O(free^2), quadratic in exactly the case that matters -- a
  ! heap that is mostly garbage.
  subroutine sweep()
    integer :: i, j
    do i = 1, obj_used
       if (obj_mark(i) .or. obj_free(i)) cycle
       do j = 1, OBJ_SLOTS
          obj_pool(i)%slot(j) = gc_nil()
       end do
       obj_pool(i)%kind = 0
       obj_free(i) = .true.
       obj_free_next(i) = obj_free_head
       obj_free_head = i
       gc_frees = gc_frees + 1
    end do
    do i = 1, vec_used
       if (vec_mark(i) .or. vec_free(i)) cycle
       if (allocated(vec_pool(i)%items)) deallocate(vec_pool(i)%items)
       vec_free(i) = .true.
       vec_free_next(i) = vec_free_head
       vec_free_head = i
       gc_frees = gc_frees + 1
    end do
    do i = 1, str_used
       if (str_mark(i) .or. str_free(i)) cycle
       ! Released here rather than at process exit: this is the one
       ! place a finalizer genuinely belongs, run once per object by
       ! sweep instead of once per copy.
       if (allocated(str_pool(i)%text)) deallocate(str_pool(i)%text)
       str_free(i) = .true.
       str_free_next(i) = str_free_head
       str_free_head = i
       gc_frees = gc_frees + 1
    end do
  end subroutine sweep

  function gc_live_count() result(n)
    integer :: n
    integer :: i
    n = 0
    do i = 1, obj_used
       if (.not. obj_free(i)) n = n + 1
    end do
    do i = 1, vec_used
       if (.not. vec_free(i)) n = n + 1
    end do
    do i = 1, str_used
       if (.not. str_free(i)) n = n + 1
    end do
  end function gc_live_count

  function gc_obj_capacity() result(n)
    integer :: n
    n = size(obj_pool)
  end function gc_obj_capacity

  ! Walks the whole heap asserting its invariants: every reference in
  ! every live object is in range and points at something still live.
  ! This is the payoff of handles over pointers -- the heap can check
  ! itself, and a corruption is caught where it happened rather than
  ! whenever the wild pointer is next dereferenced. "" means healthy.
  function gc_check_heap() result(problem)
    character(len=:), allocatable :: problem
    integer :: i, j, n
    problem = ""
    do i = 1, obj_used
       if (obj_free(i)) cycle
       do j = 1, OBJ_SLOTS
          problem = bad_ref(obj_pool(i)%slot(j))
          if (len(problem) > 0) return
       end do
    end do
    do i = 1, vec_used
       if (vec_free(i)) cycle
       n = 0
       if (allocated(vec_pool(i)%items)) n = size(vec_pool(i)%items)
       do j = 1, n
          problem = bad_ref(vec_pool(i)%items(j))
          if (len(problem) > 0) return
       end do
    end do
  end function gc_check_heap

  function bad_ref(v) result(problem)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable :: problem
    problem = ""
    select case (v%tag)
    case (GCT_OBJ)
       if (v%ref < 1 .or. v%ref > obj_used) then
          problem = "object reference out of range"
       else if (obj_free(v%ref)) then
          problem = "live object references a freed object"
       end if
    case (GCT_VEC)
       if (v%ref < 1 .or. v%ref > vec_used) then
          problem = "vec reference out of range"
       else if (vec_free(v%ref)) then
          problem = "live object references a freed vec"
       end if
    case (GCT_STR, GCT_SYM, GCT_KEY)
       if (v%ref < 1 .or. v%ref > str_used) then
          problem = "text reference out of range"
       else if (str_free(v%ref)) then
          problem = "live object references freed text"
       end if
    end select
  end function bad_ref

end module GC
