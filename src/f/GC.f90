! GC: a non-moving mark-sweep heap.
!
! Built standalone and tested on its own before anything used it.
!
! WHY THIS EXISTS AT ALL. Measured: one copy of the previous value type
! (`cons_value`, nine allocatable components and a FINAL) cost 497 ns,
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
  use Threads, only: th_key, th_key_create, th_key_set, th_key_get, th_lock, th_cond, &
       th_lock_init, th_lock_acquire, th_lock_release, th_cond_init, th_cond_wait, th_cond_broadcast, &
       th_cond_timedwait
  use iso_c_binding, only: c_ptr, c_loc, c_f_pointer, c_associated, c_size_t, c_int64_t, c_int, c_int32_t
  use BigInt
  use BigDec
  use iso_fortran_env, only: int64
  implicit none
  private

  integer, parameter, public :: gc_dp = kind(1.0d0)
  ! The integer kind, and it is 8 for the same reason gc_dp is double:
  ! Clojure's default integer is `long`, and a narrower one here
  ! truncates a perfectly ordinary literal without saying so --
  ! 9999999999 read back as 1410065407. The real was widened early on
  ! with exactly this argument and the integer beside it was left at
  ! the default kind; this is the other half of that change.
  integer, parameter, public :: gc_ip = 8

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
  ! An exact rational. Numerator in ival, denominator in REF -- ref is
  ! otherwise "index into this tag's pool", and a ratio has no pool
  ! entry, so the field is free. That keeps a ratio an immediate, like
  ! the int and the real it sits between, with no allocation and
  ! nothing for the collector to trace: push_mark switches on the tag
  ! and treats anything that is not a heap kind as holding nothing.
  !
  ! ALWAYS NORMALIZED by gc_ratio -- reduced by their gcd, sign on the
  ! numerator, and never with a denominator of 1, because Clojure
  ! collapses that to an integer: (/ 4 2) is 2, not 2/1, and
  ! (= 2/1 2) is true only because 2/1 never exists. Nothing else
  ! should construct one.
  integer, parameter, public :: GCT_RATIO = 10

  ! An arbitrary-precision integer: clotran.host.bigint, which `1N`
  ! reads as and `+'` promotes into. The VALUE is its decimal text,
  ! canonical (BigInt.f90), in the string pool -- ref is the pool
  ! index, exactly as for a string, so the collector marks it with the
  ! same case and nothing else here changes.
  !
  ! A BigInt is never collapsed to an integer, however small: `1N` is
  ! a BigInt in Clojure and stays one through (+ 1N 1). Equality and
  ! hashing cross the two tags instead -- (= 1N 1) is true and the
  ! hashes match, so a map keyed by one finds the other.
  integer, parameter, public :: GCT_BIG = 11

  ! A CLASS. Its name is the value -- the canonical spelling, in
  ! full -- in the string pool, so ref means what it
  ! means for a string and the collector needs no new case. A class
  ! was a KEYWORD until 2026-09-21 (DEVIATIONS 34), which made
  ! (= (class x) String) work and (pr-str (class 1)) answer :Long.
  ! Equality and hashing are by NAME, so two classes of the same name
  ! are one value however they were built -- a literal, (class x), or
  ! a deftype's :implements list.
  integer, parameter, public :: GCT_CLASS = 12

  ! An arbitrary-precision DECIMAL: clotran.host.decimal, which `1.0M`
  ! reads as. The value is BigDec's "unscaled|scale" text in the string
  ! pool, so the collector marks it as it marks a string.
  !
  ! Unlike every other text-backed tag, two decimals are equal when
  ! their VALUES are, not their texts: 1M and 1.0M are equal and hash
  ! alike, as Clojure says they do, while printing differently.
  integer, parameter, public :: GCT_DEC = 13

  ! A run of values. Internal -- reached from objects, not normally
  ! held by user code directly.
  integer, parameter, public :: GCT_VEC  = 9
  ! A FRAME ON THE STACK: a flat body's registers in the value stack of the
  ! context running it, slots ref+1 .. ref+ival (exec.inc frame_get). An
  ! immediate to the collector -- the stack is scanned as roots already --
  ! and never stored anywhere that outlives its call.
  integer, parameter, public :: GCT_SFRAME = 14
  ! A RATIO TOO BIG TO BE IMMEDIATE: its "n/d" text in the string pool,
  ! in lowest terms (Eval.f90 rational.inc, rat_make)
  integer, parameter, public :: GCT_BIGRATIO = 15

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
  ! DELEGATING: the thunk returned a seq that must stay itself -- a
  ! ChunkedCons, whose chunk is lost if it is split into a head and a
  ! tail. Slot 2 holds that seq and `seq` answers it, which is what
  ! LazySeq.seq does in clj (it returns `s`, it does not wrap it).
  integer, parameter, public :: LAZY_DELEG   = 3
  ! being realized by the thread whose context id is in slot 4 (Eval's
  ! gce_force): the others wait for it, so a thunk runs once
  integer, parameter, public :: LAZY_RUNNING = 4
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
  ! HAMT (PersistentHashMap.f90): a node is a VEC run of 32 slots, each holding
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
  integer, parameter, public :: OBJ_SB        = 18 ! 1=text 2=pieces appended since; i1=how many (gc_sb_append)
  ! A THROWN THING: slot 1 = the class name it was constructed with,
  ! slot 2 = its message, slot 3 = its data (what ex-info carries).
  !
  ! Clojure throws host exception objects and clotran has none, so this is what
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
  ! (new clotran.host.delay (fn [] ...)) in core.clj, and deref runs
  ! it ONCE and caches -- which is the whole contract.
  !
  ! Distinct from OBJ_LAZY, which caches a first and a rest and whose
  ! forcing expects a seq. A delay holds one value of any kind.
  integer, parameter, public :: OBJ_DELAY     = 25 ! 1=thunk 2=value; i1=forced?
  ! A REAL FORTRAN ARRAY. i1 = a handle into NativeArray's registry,
  ! which owns the buffer; slot 1 is a GC run for the `value` element
  ! kind and nil for every numeric one.
  !
  ! The buffer CANNOT live in a pool. The whole point of a native
  ! array is that its bytes are a contiguous, column-major Fortran
  ! array at a stable address, so dgemm can be handed a pointer to
  ! them -- which is also why the collector is non-moving (PLAN.md).
  ! A pool of gc_value could not hold real(8) anyway.
  !
  ! Values are the exception and go in a RUN, in slot 1, because the
  ! collector must trace them: an array of clotran values holding heap
  ! references outside the heap is how those references become
  ! dangling. push_mark already traces GCT_VEC, so this costs nothing.
  integer, parameter, public :: OBJ_ARRAY     = 26 ! 1=value run; i1=buffer handle
  ! An analysed form (Eval.f90's analyze.inc): 1=children 2,3=payloads;
  ! i1=node kind, i2=an integer operand. Also the analyser's scopes.
  ! Not OBJ_NODE: Fortran is case-insensitive and obj_node is the pool's
  ! derived type.
  integer, parameter, public :: OBJ_AST       = 30
  ! Chunked seqs (Eval.f90, chunks): a window onto a backing run or
  ! vector; a buffer being filled; a ChunkedCons of a chunk and a rest.
  integer, parameter, public :: OBJ_CHUNK     = 31 ! 1=backing; i1=offset i2=end
  integer, parameter, public :: OBJ_CHUNKBUF  = 32 ! 1=run; i1=count
  integer, parameter, public :: OBJ_CHUNKSEQ  = 33 ! 1=chunk 2=more 3=meta
  ! A task: a closure run in a context of its own, the thread primitive
  ! (Eval's tasks.inc). i1 is its state, i2 the context it runs in -- 0
  ! before it starts and once it has finished.
  integer, parameter, public :: OBJ_TASK      = 34 ! 1=thunk 2=value or failure 3=awaited 4=deadline 5=mailbox
  integer, parameter, public :: OBJ_VOLATILE  = 35 ! 1=value; clotran.host.volatile, a box with no validator or watches
  ! A COMPILED function: slot 1 = its name (for printing and traces),
  ! i1 = its handle in CompiledFn's table, i2 = its arity, or -1 for
  ! any. The procedure pointer is NOT here, because a gc_value has no
  ! pointer component and that is what keeps a copy at 4 ns.
  integer, parameter, public :: OBJ_COMPILED = 36 ! 1=name; i1=handle i2=arity
  integer, parameter, public :: OBJ_TVECTOR  = 37 ! 1=vector it came from 2=append buffer; i1=buffered i2=1 editable
  integer, parameter, public :: OBJ_TMAP     = 38 ! a transient map or set: 1=the persistent value; i1=1 map 2 set, i2=1 editable
  integer, parameter, public :: OBJ_HAMT      = 11 ! 1=root run; i1=count
  integer, parameter, public :: OBJ_HAMT_LEAF = 12 ! 1=key 2=val
  ! Slot 3 was reserved for a per-Var dynamic stack; the dynamic
  ! bindings ended up in one global frame stack instead (Eval), so the
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

  ! SIXTEEN BYTES (the calling convention's step 3, PLAN.md): a tag, a
  ! pool index, and one 64-bit payload -- an integer, a character's code
  ! point, a boolean, or a real's BITS (gc_rval/gc_real). It was 32: a
  ! separate real beside the integer, never both used, doubled every
  ! slot, stack entry and vector element in the heap.
  type, public :: gc_value
     integer :: tag = GCT_NIL
     integer :: ref = 0 ! index into this tag's pool; 0 for immediates
     integer(gc_ip) :: ival = 0
  end type gc_value
  ! nil, as a constant: every slot the pools and stacks clear is set
  ! to this rather than through a call.
  type(gc_value), parameter :: nilv = gc_value()

  ! --- object pool -----------------------------------------------
  type :: obj_node
     integer :: kind = 0
     integer :: i1 = 0, i2 = 0 ! inline payload (count, shift, state, ...)
     type(gc_value) :: slot(OBJ_SLOTS)
  end type obj_node

  type(obj_node), allocatable, target :: obj_pool(:)
  logical, allocatable :: obj_mark(:), obj_free(:)
  integer, allocatable :: obj_free_next(:)
  integer :: obj_free_head = 0, obj_used = 0

  ! --- value-run pool --------------------------------------------
  !
  ! A run's storage is a slice of ONE arena, vec_store, not its own
  ! allocatable: every frame and every vector node used to be a
  ! malloc/free pair, and the profile said so. Runs are handed out in
  ! power-of-two size classes, each class with a free list threaded
  ! through the first slot of its free runs (a free run is never
  ! marked, so the slot is ours). The arena grows by doubling and is
  ! never returned; offsets stay valid across growth, which pointers
  ! would not.
  type :: vec_node
     integer :: off = 0, len = 0   ! slice vec_store(off : off+len-1); len 0 = empty
  end type vec_node

  type(vec_node), allocatable :: vec_pool(:)
  type(gc_value), allocatable :: vec_store(:)
  integer :: store_used = 0
  integer :: arena_alloc_since = 0   ! slots handed out since the last collection
  integer :: arena_live = 0          ! slots the last collection found live
  integer(8) :: arena_reused = 0, arena_fresh = 0   ! runs served from a free list / from fresh arena
  integer, parameter :: VCLASSES = 30
  integer :: class_head(VCLASSES) = 0
  logical, allocatable :: vec_mark(:), vec_free(:)
  integer, allocatable :: vec_free_next(:)
  integer :: vec_free_head = 0, vec_used = 0

  ! --- string pool -----------------------------------------------
  ! Text is a heap object too: a value stays copyable by a flat move,
  ! so it cannot own a deferred-length character of its own.
  type :: str_node
     character(len=:), allocatable :: text
     ! THE TEXT'S INDEX (model/string.lisp), made with it by str_index:
     ! how many code points it holds, and for text that is not all ASCII
     ! the byte where every 32nd starts -- so count is O(1) and the
     ! character at i, or a slice, is found in at most 31 steps, where
     ! each walked the bytes from the start (and copied them first)
     integer :: ncp = 0
     integer, allocatable :: ck(:)
  end type str_node

  type(str_node), allocatable :: str_pool(:)
  logical, allocatable :: str_mark(:), str_free(:)
  integer, allocatable :: str_free_next(:)
  integer :: str_free_head = 0, str_used = 0

  ! --- generations ----------------------------------------------
  !
  ! Non-moving and generational by STICKY MARK BITS: a full collection
  ! leaves every survivor marked, and marked MEANS old. A new object
  ! starts unmarked and goes on its pool's young list. A young collection
  ! marks from the roots and from the REMEMBERED objects -- old ones a
  ! young value was stored into since -- and stops at anything already
  ! marked, so it traces only the young; it sweeps only the young lists,
  ! and a survivor is old from then on. The write barrier is in the two
  ! setters that store into an existing object (gc_set_slot, gc_vec_set):
  ! everything else writes into a new, young, object. A full collection
  ! runs when the old generation has doubled since the last one.
  ! CLOTRAN_GC_FULL=1 makes every collection full (to bisect a wrong
  ! answer to the collector); CLOTRAN_GC_VERIFY=1 checks the whole heap
  ! after each young collection (gc_check_heap) and stops on a dangling
  ! reference, which is what a missing barrier or root looks like.
  logical :: gen_mode = .true., gen_verify = .false., gen_env_read = .false.
  integer, allocatable :: obj_young(:), vec_young(:), str_young(:)
  integer :: n_obj_young = 0, n_vec_young = 0, n_str_young = 0
  logical, allocatable :: obj_rem(:), vec_rem(:)
  ! AGING (PLAN.md step 16). A young object that survives one collection
  ! is not promoted: it stays young -- unmarked, so the barrier and the
  ! marking treat it as young -- on the aged list for one more round,
  ! and is old only after surviving twice. Without this the cell a walk
  ! had just passed was promoted, died at once, and as an unswept old
  ! object kept every later cell alive until a full collection:
  ! (dorun (range 10^6)) held 780 MB. The remembered set keeps, across
  ! a collection, the old objects that still point at an aged one.
  ! Strings hold no references and are promoted as before.
  integer, allocatable :: obj_aged_list(:), vec_aged_list(:)
  integer :: n_obj_aged = 0, n_vec_aged = 0
  logical, allocatable :: obj_aged(:), vec_aged(:)
  type(gc_value), allocatable :: rem_set(:)
  integer :: n_rem = 0
  ! live objects per pool and live arena slots, kept as allocation and
  ! sweep go: the growth rules read these, not what one sweep freed --
  ! a young sweep frees little of a pool and must not grow it for that
  integer :: obj_live = 0, vec_live = 0, str_live = 0, arena_live_now = 0
  ! of the live counts, how much is dead and waiting in pending lists --
  ! set by a young collection's handoff, spent by the next collection
  integer :: obj_pend_dead = 0, vec_pend_dead = 0, str_pend_dead = 0
  ! gc_check_heap's view of the pending dead while it runs (bad_ref)
  logical, allocatable :: chk_dead_o(:), chk_dead_v(:), chk_dead_s(:)
  integer :: old_at_full = 0, promoted_since_full = 0
  integer, public :: gc_young_collections = 0
  ! pause times, for CLOTRAN_STATS: total and longest, young and full, ms
  real(8), public :: gc_young_ms = 0, gc_full_ms = 0, gc_young_max_ms = 0, gc_full_max_ms = 0
  ! where a pause goes: waiting for the other threads to reach a
  ! safepoint, and a young collection's mark and sweep
  real(8), public :: gc_safepoint_ms = 0, gc_ymark_ms = 0, gc_ysweep_ms = 0, gc_finish_ms = 0

  ! --- global roots ----------------------------------------------
  ! Process-wide and mutable: the registry handle changes whenever the
  ! registry grows, so a global is a SLOT, not a value handed over once.
  ! GROWABLE, and with no maximum to maintain. It was a fixed array of
  ! eight, which was exactly the number claimed, so the ninth (Eval's
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

  ! --- finalizers for storage the heap does not own ----------------
  !
  ! Almost every object here holds only gc_values, and sweeping one is
  ! just returning its slot. Two kinds do not: a native array owns a
  ! real Fortran buffer, and a regex owns an ICU handle. Neither can
  ! live in a pool -- that is the POINT of a native array, whose bytes
  ! have to be a contiguous Fortran array at a stable address so a
  ! Fortran library can be handed a pointer to them.
  !
  ! So the owning module keeps a registry, the object holds an integer
  ! handle, and the sweep tells that module when a handle dies. Without
  ! this, collecting an array leaks its buffer -- which is what
  ! DEVIATIONS 14 already records for Matcher, discovered the same way.
  !
  ! A procedure POINTER rather than a call, because GC.f90 sits at the
  ! bottom: NativeArray uses GC, so GC cannot use NativeArray. Same
  ! dependency inversion gcp_set_forcer already uses for lazy seqs, and
  ! a MODULE procedure for the same reason -- flang segfaults passing a
  ! host-associated internal procedure as a callback on macOS/ARM64.
  abstract interface
     subroutine finalizer_i(kind, handle, extra)
       integer, intent(in) :: kind, handle, extra
     end subroutine finalizer_i
  end interface
  procedure(finalizer_i), pointer, save :: obj_finalizer => null()
  ! the kinds it is called for: a sweep frees hundreds of thousands of
  ! objects and nearly none of them hold anything outside the heap
  logical, save :: finalized_kind(0:63) = .false.

  ! Hashing and comparing a COLLECTION means walking it, and a
  ! persistent vector is a 32-way trie whose walking logic lives in a
  ! module above this one. Same dependency inversion as the finalizer:
  ! this module declares the hook, the module that can walk installs
  ! it, and gc_hash/gc_equal call it for the kinds that need it.
  !
  ! The two MUST agree. A structural hash with an identity equality
  ! (or the reverse) puts the same key in a trie twice and loses
  ! lookups down whichever arm they walk into, so they are installed
  ! together and neither is used without the other.
  abstract interface
     recursive function coll_hash_i(v) result(h)
       import :: gc_value
       type(gc_value), intent(in) :: v
       integer :: h
     end function coll_hash_i

     recursive function coll_equal_i(a, b) result(eq)
       import :: gc_value
       type(gc_value), intent(in) :: a, b
       logical :: eq
     end function coll_equal_i
  end interface
  procedure(coll_hash_i), pointer, save :: obj_coll_hash => null()
  procedure(coll_equal_i), pointer, save :: obj_coll_equal => null()

  ! --- the value stack ----------------------------------------------
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
  !
  ! One stack per evaluation context, and each thread runs on its own
  ! context's (PLAN.md step 14b): the stack this module's key names on
  ! that thread. Each is allocated on its own and never moves, so growing
  ! the table copies pointers; the collector scans every one, so a parked
  ! context keeps what it was holding. Stack 1 is the main thread's, made
  ! and bound by gc_init.
  integer, parameter, public :: SPARE_SIZES = 32, SPARE_DEPTH = 8
  ! allocation batches (PLAN.md step 14d): slots per pool, and runs per
  ! size class for the classes up to 2**(RUN_CLASSES-1) slots
  integer, parameter :: ALLOC_BATCH = 256, RUN_BATCH = 64, RUN_CLASSES = 8
  ! spare ARGUMENT VECTORS of 1..ARG_SPARE_MAX elements (Eval, args_take)
  integer, parameter, public :: ARG_SPARE_MAX = 8
  type :: gc_stack
     ! FIXED, never moved: compiled code holds a view of it across calls
     ! (ClotranABI, clotran_slots). calloc'd, so its pages are real only
     ! once touched; vstack_make.
     type(gc_value), pointer, contiguous :: vstack(:) => null()
     integer :: vs_hi = 0   ! the highest top reached; above it, untouched
     integer :: vs_top = 0
     logical :: holds_heap = .false.   ! this thread is inside heap_enter/heap_leave
     integer :: state_depth = 0        ! how deep this thread holds the state lock
     logical :: grow_entered = .false., grow_stopped = .false.   ! gc_grow_begin's, for gc_grow_end
     ! the generated VM's running body: its entry values are vstack(vm_args_rb + i + 1)
     ! (src/f/VmRuntime.f90, vm.inc) -- per thread, as two threads run VM code at once
     integer :: vm_args_rb = 0
     ! its control records, (record, field): a run takes them from vm_ctl_top up
     integer(8), pointer, contiguous :: vm_ctl(:, :) => null()
     integer :: vm_ctl_top = 0
     ! SPARE FRAMES: a compiled procedure's frame, cleared, once its call
     ! has returned (gc_frame_give) -- nothing keeps a frame after its
     ! call -- by size, a few of each. Not roots: every collection empties
     ! them (forget_spares), so a spare is never one the sweep freed.
     type(gc_value) :: spare(SPARE_DEPTH, SPARE_SIZES)
     integer :: nspare(SPARE_SIZES) = 0
     ! SPARE ARGUMENT VECTORS: a builtin that touches its arguments only
     ! by element (argsafe.inc) is handed one of these and it comes back
     ! after the call, so a call allocates none. Forgotten at every
     ! collection, as the spare frames are: they are not roots.
     type(gc_value) :: aspare(SPARE_DEPTH, ARG_SPARE_MAX)
     integer :: naspare(ARG_SPARE_MAX) = 0
     ! THIS THREAD'S DYNAMIC BINDINGS (Var.dvals): nil, or the top Frame
     ! as a vector [bindings prev] -- bindings a map of Var to box, the
     ! frame below's merged in -- as Var.pushThreadBindings builds it
     type(gc_root) :: bindings
     ! THIS THREAD'S ALLOCATION BATCHES (PLAN.md step 14d): free slots of
     ! each pool, and free arena runs of the small size classes, taken
     ! under the heap lock a batch at a time and handed out here without
     ! it. A batched slot stays flagged FREE -- the sweep skips it and
     ! nothing else can hand it out -- until this thread allocates it.
     ! What this thread allocated since the last collection, and what that
     ! did to the live counts, is kept here and merged at the collection
     ! (merge_batches), with the world stopped.
     integer :: obj_b(ALLOC_BATCH), n_obj_b = 0
     integer :: vec_b(ALLOC_BATCH), n_vec_b = 0
     integer :: str_b(ALLOC_BATCH), n_str_b = 0
     integer :: run_b(RUN_BATCH, RUN_CLASSES), n_run_b(RUN_CLASSES) = 0
     integer, allocatable :: y_obj(:), y_vec(:), y_str(:)
     integer :: n_y_obj = 0, n_y_vec = 0, n_y_str = 0
     integer :: d_obj_live = 0, d_vec_live = 0, d_str_live = 0, d_arena_live = 0
     integer(8) :: d_allocs = 0
     ! PENDING: what this thread allocated in the cycle before the last
     ! young collection, handed back to it unswept. After that collection
     ! a survivor is marked and anything else in the list is dead; the
     ! thread frees the dead into its own batches as it needs slots
     ! (pend_refill_*), p_*(1:c_*) done, the rest not yet. Whatever is
     ! left is freed at the next collection's start (finish_pending), so
     ! between collections nothing else can free, or hand out, a slot here.
     integer, allocatable :: p_obj(:), p_vec(:), p_str(:)
     integer :: np_obj = 0, np_vec = 0, np_str = 0, cp_obj = 0, cp_vec = 0, cp_str = 0
     ! dead objects with a finalizer, freed at the collection instead
     integer, allocatable :: defer_obj(:)
     integer :: n_defer = 0
     ! arena runs of lazily freed vectors that did not fit the run batch
     integer, allocatable :: loose_off(:), loose_len(:)
     integer :: n_loose = 0
  end type gc_stack
  type :: gc_stack_ref
     type(gc_stack), pointer :: s => null()
  end type gc_stack_ref
  type(gc_stack_ref), allocatable :: stacks(:)
  integer :: n_stacks = 0
  type(th_key) :: stack_key
  logical :: stack_key_made = .false.

  ! --- several mutators (PLAN.md step 14c) ---------------------------
  !
  ! Every allocation holds heap_lock. One that must collect, or grow a
  ! pool or the arena -- growth MOVES the pool, and other threads read
  ! pools outside allocation -- first stops the world: raises stop_world
  ! and waits until every other RUNNING mutator is parked at a safepoint.
  ! A safepoint is an allocation's entry: a thread arriving while the
  ! world is stopped pushes that call's roots and slots onto its own
  ! value stack, where the collector sees them, and waits. A thread
  ! counts as running between gc_mutator_enter and gc_mutator_leave;
  ! the main thread is one from gc_init, and while clotran's baton is on
  ! nothing else registers, so a stop never waits (step 14f changes that).
  ! THE STATE LOCK (PLAN.md step 14e): every read and write of a cell
  ! Clojure code mutates after other threads can see it -- a Var's root,
  ! an atom's value, a registry -- goes through it, because a gc_value is
  ! four words and a reader racing a writer would see half of each.
  ! Re-entrant per thread. NEVER held across an allocation (a thread
  ! parked at a safepoint holding it could deadlock the collector's
  ! finalizers) nor across Clojure code (swap! calls f outside it).
  ! the remembered set's own lock: the write barrier runs in any thread's
  ! store, holding no other lock, and two appending at once lost one
  ! (PLAN.md step 14f) -- a young value only an old object held was then
  ! swept and its slot handed out again
  type(th_lock) :: rem_lk
  type(th_lock) :: state_lk
  type(th_cond) :: state_cv
  integer :: notify_gen = 0   ! bumped by every gc_state_notify, under the state lock
  type(th_lock) :: heap_lock
  type(th_cond) :: heap_cond
  logical :: heap_sync_up = .false.
  logical, volatile :: stop_world = .false.
  integer :: n_running = 1, n_parked = 0

  ! --- marking work list -----------------------------------------
  ! An explicit stack, not recursion: a list is a chain thousands of
  ! nodes deep, and recursive marking would overflow the real stack on
  ! exactly the structure this language builds most.
  ! THE MARKER (PLAN step 33, stage 1a): generated from model/heapg.lisp
  ! (src/f/gen/heap_gen.inc, included below), proved in heapg-proof.lisp to
  ! leave the mark set closed. Its stack and counts; the pools it reads
  ! through the hp_* accessors. A reference is marked when it is pushed, so
  ! each object and run is pushed at most once and the stack, sized to
  ! them at each collection's start (mark_begin), cannot overflow.
  type :: heap_state
     integer(int64) :: err = 0, msp = 0, nobj = 0, nvec = 0, nstr = 0, alive = 0
     ! the sweep's (stage 1b, model/heapsw.lisp): slots freed by pool, and
     ! arena words freed
     integer(int64) :: nswo = 0, nswv = 0, nsws = 0, afree = 0
     integer(int64), allocatable :: mtag(:), mref(:)
  end type heap_state
  type(heap_state) :: hstate

  integer, public :: gc_allocs = 0
  ! objects allocated, by kind (CLOTRAN_STATS)
  integer(8), public :: gc_kind_n(0:63) = 0
  integer, public :: gc_frees = 0
  integer, public :: gc_collections = 0
  ! Objects marked, summed over every collection: the collector's
  ! total work, which is what a growing live set inflates.
  integer(8), public :: gc_marked = 0
  ! Slots the LAST sweep freed, per pool. The growth policy reads them:
  ! a collection that frees less than half a pool means the pool is
  ! mostly live, and collecting again as soon as that sliver is used
  ! up would mark the same live set again. Without this the heap was
  ! quadratic under (reduce + (range n)) -- the realized range is held
  ! by reduce's own argument, so the live set grows with n, and a
  ! full-pool-only trigger collected every few hundred allocations,
  ! each time marking everything: 8000 elements, 2344 collections,
  ! 535 million marks. Growing on a mostly-live pool is what every
  ! collector does; this one had only grown when a sweep freed NOTHING.
  integer :: obj_swept = 0, vec_swept = 0, str_swept = 0
  ! Objects marked by the LAST collection: the live set, heap-wide.
  ! Every collection costs this much, whichever pool triggered it, so
  ! the pool that triggered it grows until it can absorb that many
  ! allocations before filling again. That makes collections
  ! proportional to allocation / live, and total marking proportional
  ! to allocation -- the amortised bound a tracing collector is meant
  ! to have. Half-live alone was not enough: a garbage-churning pool
  ! (argument vectors, frames) kept filling every few thousand
  ! allocations while a different pool held a live set of hundreds of
  ! thousands, and each of its collections marked all of them.
  integer(8) :: last_marked = 0
  ! ...and per pool, so each pool grows to twice ITS OWN live count
  ! rather than to the heap-wide total, which sized every pool to the
  ! largest and cost 1.4 GB for a 100000-element into.
  integer :: obj_marked = 0, vec_marked = 0, str_marked = 0

  ! Collect at EVERY allocation. Turns a missing root from a rare,
  ! timing-dependent corruption into an immediate, deterministic
  ! failure; the test suite runs under it.
  logical, public :: gc_torture = .false.
  ! Collect at every Nth object allocation (CLOTRAN_GC_EVERY=N): the
  ! collection points then depend on the allocation count alone, so a
  ! failure that moves with timing is pinned to one place. 0 is off.
  integer, public :: gc_every = 0
  integer :: every_count = 0

  ! Grow-only mode: the pools never collect. Left over from the
  ! migration, when payloads moved into this heap before anything
  ! rooted them; kept because gc_test still exercises it.
  logical, public :: gc_no_collect = .false.

  public :: gc_init, gc_collect, gc_hold_begin, gc_hold_end
  public :: gc_image_write, gc_image_read, gc_obj_kind_at
  integer, parameter, public :: GC_IMAGE_VERSION = 1
  public :: gc_nil, gc_bool, gc_int, gc_real, gc_char, gc_str, gc_sym, gc_key
  public :: gc_char_cp, u8_count, u8_off, u8_cpidx, u8_slice, u8_dec, u8_at, u8_enc
  public :: gc_str_count, gc_str_at, gc_str_slice

  interface gc_int
     module procedure gc_int4, gc_int8
  end interface gc_int
  public :: gc_ratio, gc_numerator, gc_denominator, gc_gcd
  public :: gc_big, gc_big_text, gc_is_big, gc_bigratio, gc_bigratio_text, gc_rat_make, big_gcd
  public :: gc_class, gc_class_text
  public :: gc_dec, gc_dec_text
  public :: gc_set_coll_ops
  ! The hash mixer, so the collection walkers installed through
  ! gc_set_coll_ops finish with the same one every other hash uses.
  public :: mix32, m3_mix_coll, m3_ordered_step, m3_add, gc_utf16, gc_text_hasheq
  public :: gc_obj, gc_vec, gc_cons
  public :: gc_text, gc_slot, gc_set_slot, gc_kind
  public :: gc_i1, gc_i2, gc_set_i1, gc_set_i2, gc_seq_fast
  public :: gc_vec_len, gc_vec_get, gc_vec_set, gc_vec_word, gc_reg, gc_reg_set, gc_vec_clone
  ! the vector store itself, for the executor's register reads and writes
  ! inline (flat.inc reg_get, reg_set): a call each was a tenth of a call
  public :: vec_pool, vec_store, vec_mark, vec_rem, gc_reg_barrier
  public :: gc_car, gc_cdr, gc_set_car, gc_set_cdr
  public :: gc_live_count, gc_obj_capacity, gc_check_heap
  public :: gc_global_new, gc_global_set, gc_global_get, gc_global_count
  public :: gc_global_keep, gc_root_get, gc_root_live
  public :: gc_set_finalizer
  public :: gc_ensure_init, gc_str_ref, gc_ref_text, gc_ref_is, gc_ref_len, gc_ref_same
  public :: gc_sb_append, gc_sb_flush, gc_ref_slice, gc_ref_ascii
  public :: vs_enter, vs_leave, vs_set, vs_get, vs_depth, gc_stack, gc_my_stack
  public :: gc_bindings_get, gc_bindings_set, gc_int_text, gc_rval
  interface vs_enter
     module procedure vs_enter_self, vs_enter_on
  end interface vs_enter
  interface vs_leave
     module procedure vs_leave_self, vs_leave_on
  end interface vs_leave
  interface vs_set
     module procedure vs_set_self, vs_set_on
  end interface vs_set
  interface vs_get
     module procedure vs_get_self, vs_get_on
  end interface vs_get
  interface vs_depth
     module procedure vs_depth_self, vs_depth_on
  end interface vs_depth
  public :: gc_stack_new, gc_stack_bind, gc_stacks_reset, gc_stack_of, gc_generation
  public :: gc_frame_take, gc_frame_give
  public :: gc_state_lock, gc_state_unlock, gc_cell_get, gc_cell_set, gc_cell_cas, gc_identical
  public :: gc_grow_begin, gc_grow_end, gc_next, gc_root_cas
  public :: gc_poll, gc_state_wait, gc_state_notify, gc_notify_gen, gc_stop_pending
  public :: gc_cas_i1, gc_lazy_wait_add, gc_lazy_wake

  interface
     subroutine clotran_seq_begin() bind(C, name="clotran_seq_begin")
     end subroutine clotran_seq_begin
     subroutine clotran_gc_hold(delta) bind(C, name="clotran_gc_hold")
       import :: c_int64_t
       integer(c_int64_t), value :: delta
     end subroutine clotran_gc_hold
     function clotran_gc_holding() bind(C, name="clotran_gc_holding") result(n)
       import :: c_int64_t
       integer(c_int64_t) :: n
     end function clotran_gc_holding
     subroutine clotran_seq_end() bind(C, name="clotran_seq_end")
     end subroutine clotran_seq_end
     function clotran_cas_i32(p, e, d) bind(C, name="clotran_cas_i32") result(ok)
       import :: c_ptr, c_int, c_int32_t
       type(c_ptr), value :: p
       integer(c_int32_t), value :: e, d
       integer(c_int) :: ok
     end function clotran_cas_i32
     subroutine clotran_lazy_waiters_add(d) bind(C, name="clotran_lazy_waiters_add")
       import :: c_int64_t
       integer(c_int64_t), value :: d
     end subroutine clotran_lazy_waiters_add
     function clotran_lazy_waiters_fenced() bind(C, name="clotran_lazy_waiters_fenced") result(n)
       import :: c_int64_t
       integer(c_int64_t) :: n
     end function clotran_lazy_waiters_fenced
     subroutine clotran_seq_read16(src, dst) bind(C, name="clotran_seq_read16")
       import :: c_ptr
       type(c_ptr), value :: src, dst
     end subroutine clotran_seq_read16
  end interface
  public :: gc_mutator_enter, gc_mutator_leave
  public :: gc_arena_stats
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

  ! ---- ref-level text API ------------------------------------------
  !
  ! Text is reached by ref, not by value, so the evaluator can compare
  ! a symbol without copying its text:
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

  subroutine gc_ref_text(ref, s)
    integer, intent(in) :: ref
    character(len=:), allocatable, intent(out) :: s
    s = ""
    if (ref_ok(ref)) then
       s = str_pool(ref)%text
    else if (ref > 0) then
       write(0, '(A,I0)') "TRAP: read of a freed string, ref ", ref
       call abort()
    end if
  end subroutine gc_ref_text

  function gc_ref_is(ref, s) result(yes)
    integer, intent(in) :: ref
    character(len=*), intent(in) :: s
    logical :: yes
    yes = .false.
    if (ref_ok(ref)) yes = (str_pool(ref)%text == s)
  end function gc_ref_is

  ! Whether two texts are the same text, compared in place: a symbol's
  ! name against a keyword's, with no copy. Lengths first: Fortran's ==
  ! pads the shorter with blanks.
  function gc_ref_same(r1, r2) result(yes)
    integer, intent(in) :: r1, r2
    logical :: yes
    yes = .false.
    if (.not. (ref_ok(r1) .and. ref_ok(r2))) return
    if (len(str_pool(r1)%text) /= len(str_pool(r2)%text)) return
    yes = str_pool(r1)%text == str_pool(r2)%text
  end function gc_ref_same

  ! --- StringBuilder text, appended in amortised O(1) ------------------
  !
  ! An OBJ_SB's slot 1 is its text so far, slot 2 a buffer of pieces
  ! appended since, i1 how many. An append copied the whole text out and
  ! back with the piece on the end, so building a string of n pieces was
  ! O(n^2): clojure.string/join and pr-str of 2 x 10^4 elements cost 28
  ! and 30 us an element, 6 and 9 at 2 x 10^3. Now an append puts the
  ! piece in the buffer (doubling it when full) and a READ -- anything
  ! that looks at slot 1, through gc_sb_flush -- joins the pieces once.
  subroutine gc_sb_append(sb, piece, roots)
    type(gc_value), intent(in) :: sb
    character(len=*), intent(in) :: piece
    type(gc_value), intent(in) :: roots(:)
    type(gc_stack), pointer :: s
    type(gc_value) :: p, buf, nb
    integer :: n, cap, i, base
    if (len(piece) == 0) return
    s => my_stack()
    base = vs_enter_on(s, 2)
    s%vstack(base + 1) = sb
    p = gc_str(piece, roots)
    s%vstack(base + 2) = p
    buf = gc_slot(sb, 2)
    n = gc_i1(sb)
    cap = gc_vec_len(buf)
    if (n >= cap) then
       nb = gc_vec(max(16, 2 * cap), roots)
       do i = 1, n
          call gc_vec_set(nb, i, gc_vec_get(buf, i))
       end do
       call gc_set_slot(sb, 2, nb)
       buf = nb
    end if
    call gc_vec_set(buf, n + 1, s%vstack(base + 2))
    call gc_set_i1(sb, n + 1)
    call vs_leave_on(s, base)
  end subroutine gc_sb_append

  ! The pieces appended since the last read, joined onto slot 1.
  subroutine gc_sb_flush(sb, roots)
    type(gc_value), intent(in) :: sb
    type(gc_value), intent(in) :: roots(:)
    type(gc_stack), pointer :: s
    type(gc_value) :: t, buf, p
    character(len=:), allocatable :: all
    integer :: n, i, total, at, base, l
    n = gc_i1(sb)
    if (n <= 0) return
    buf = gc_slot(sb, 2)
    t = gc_slot(sb, 1)
    total = 0
    if (t%tag == GCT_STR) total = gc_ref_len(t%ref)
    do i = 1, n
       p = gc_vec_get(buf, i)
       total = total + gc_ref_len(p%ref)
    end do
    allocate(character(len=total) :: all)
    at = 0
    if (t%tag == GCT_STR) then
       l = gc_ref_len(t%ref)
       if (l > 0) all(1:l) = str_pool(t%ref)%text
       at = l
    end if
    do i = 1, n
       p = gc_vec_get(buf, i)
       l = gc_ref_len(p%ref)
       if (l > 0) all(at + 1:at + l) = str_pool(p%ref)%text
       at = at + l
       call gc_vec_set(buf, i, nilv)
    end do
    s => my_stack()
    base = vs_enter_on(s, 1)
    s%vstack(base + 1) = sb
    t = gc_str(all, roots)
    call gc_set_slot(sb, 1, t)
    call gc_set_i1(sb, 0)
    call vs_leave_on(s, base)
  end subroutine gc_sb_flush

  ! Bytes from+1 .. to of a text, cut in place rather than after
  ! copying the whole text out.
  subroutine gc_ref_slice(ref, from, to, s)
    integer, intent(in) :: ref, from, to
    character(len=:), allocatable, intent(out) :: s
    s = ""
    if (.not. ref_ok(ref)) return
    if (from < 0 .or. to > len(str_pool(ref)%text) .or. to < from) return
    s = str_pool(ref)%text(from + 1:to)
  end subroutine gc_ref_slice

  ! Whether a text is all ASCII: a byte is then a character.
  logical function gc_ref_ascii(ref) result(yes)
    integer, intent(in) :: ref
    integer :: i
    yes = .false.
    if (.not. ref_ok(ref)) return
    do i = 1, len(str_pool(ref)%text)
       if (ichar(str_pool(ref)%text(i:i)) > 127) return
    end do
    yes = .true.
  end function gc_ref_ascii

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
    if (allocated(vec_store)) deallocate(vec_store)
    allocate(vec_store(max(8 * n, 4096)))
    vec_store = nilv
    store_used = 0
    class_head = 0
    arena_alloc_since = 0
    arena_live = 0

    if (allocated(str_pool)) deallocate(str_pool, str_mark, str_free, str_free_next)
    allocate(str_pool(n), str_mark(n), str_free(n), str_free_next(n))
    str_mark = .false.; str_free = .false.; str_free_next = 0
    str_free_head = 0; str_used = 0


    if (allocated(obj_young)) deallocate(obj_young, vec_young, str_young, obj_rem, vec_rem, rem_set)
    allocate(obj_young(1024), vec_young(1024), str_young(1024), rem_set(1024))
    allocate(obj_rem(n), vec_rem(n))
    obj_rem = .false.; vec_rem = .false.
    if (allocated(obj_aged)) deallocate(obj_aged, vec_aged, obj_aged_list, vec_aged_list)
    allocate(obj_aged(n), vec_aged(n), obj_aged_list(1024), vec_aged_list(1024))
    obj_aged = .false.; vec_aged = .false.; n_obj_aged = 0; n_vec_aged = 0
    n_obj_young = 0; n_vec_young = 0; n_str_young = 0; n_rem = 0
    obj_live = 0; vec_live = 0; str_live = 0; arena_live_now = 0
    old_at_full = 0; promoted_since_full = 0; gc_young_collections = 0

    if (allocated(global_root)) deallocate(global_root)
    allocate(global_root(8))
    global_root = nilv
    global_count = 0
    global_gen = global_gen + 1
    gc_allocs = 0; gc_frees = 0; gc_collections = 0
    gc_no_collect = .false.
    call heap_sync_init()
    n_running = 1
    n_parked = 0
    call gc_stacks_reset()
    call gc_stack_new(1)   ! a fresh heap: stack 1 starts empty
    call clear_batches(stacks(1)%s)   ! and its batches name slots of the old heap
  end subroutine gc_init

  ! Context `id`'s stack, empty -- made, or emptied for reuse.
  ! --- the heap image -------------------------------------------------
  !
  ! The heap as it stands, written to a stream and read back. A handle
  ! is an index and a value carries no pointer (gc_value), so the pools
  ! go out as the arrays they are and come back the same. The image is
  ! taken after a full collection with one thread: the sticky marks say
  ! which objects are old, the young, remembered and aged sets are
  ! empty, and no stack holds pending work. What is not in these arrays
  ! -- a native array's buffer, a regex's ICU object, a compiled
  ! procedure -- each module writes after this or rebuilds on the way in
  ! (main.f90, image_save and image_load).
  subroutine gc_image_write(u)
    integer, intent(in) :: u
    integer :: i
    call gc_collect([gc_value ::])
    if (n_stacks > 1) error stop "clotran: an image is taken with one thread"
    write(u) GC_IMAGE_VERSION
    write(u) size(obj_pool), obj_free_head, obj_used
    write(u) obj_pool, obj_mark, obj_free, obj_free_next
    write(u) size(vec_pool), vec_free_head, vec_used
    write(u) vec_pool, vec_mark, vec_free, vec_free_next
    write(u) size(vec_store), store_used, arena_alloc_since, arena_live, arena_reused, arena_fresh
    write(u) vec_store(1:store_used), class_head
    write(u) size(str_pool), str_free_head, str_used
    write(u) str_mark, str_free, str_free_next
    do i = 1, size(str_pool)
       if (allocated(str_pool(i)%text)) then
          write(u) len(str_pool(i)%text)
          if (len(str_pool(i)%text) > 0) write(u) str_pool(i)%text
       else
          write(u) -1
       end if
    end do
    write(u) size(global_root), global_count, global_gen
    write(u) global_root
    write(u) obj_live, vec_live, str_live, arena_live_now, old_at_full, promoted_since_full
    write(u) gc_root_get(stacks(1)%s%bindings)
  end subroutine gc_image_write

  ! The pools replaced by the image's; the young, remembered and aged
  ! sets sized to them and empty; stack 1 fresh and bound to this
  ! thread, holding the binding frame the image was taken with.
  subroutine gc_image_read(u, ok)
    integer, intent(in) :: u
    logical, intent(out) :: ok
    integer :: ver, n, i, k, st
    type(gc_value) :: b
    ok = .false.
    read(u, iostat=st) ver
    if (st /= 0 .or. ver /= GC_IMAGE_VERSION) return
    read(u) n, obj_free_head, obj_used
    if (allocated(obj_pool)) deallocate(obj_pool, obj_mark, obj_free, obj_free_next)
    allocate(obj_pool(n), obj_mark(n), obj_free(n), obj_free_next(n))
    read(u) obj_pool, obj_mark, obj_free, obj_free_next
    read(u) n, vec_free_head, vec_used
    if (allocated(vec_pool)) deallocate(vec_pool, vec_mark, vec_free, vec_free_next)
    allocate(vec_pool(n), vec_mark(n), vec_free(n), vec_free_next(n))
    read(u) vec_pool, vec_mark, vec_free, vec_free_next
    read(u) n, store_used, arena_alloc_since, arena_live, arena_reused, arena_fresh
    if (allocated(vec_store)) deallocate(vec_store)
    allocate(vec_store(n))
    read(u) vec_store(1:store_used), class_head
    if (store_used < n) vec_store(store_used + 1:n) = nilv
    read(u) n, str_free_head, str_used
    if (allocated(str_pool)) deallocate(str_pool, str_mark, str_free, str_free_next)
    allocate(str_pool(n), str_mark(n), str_free(n), str_free_next(n))
    read(u) str_mark, str_free, str_free_next
    do i = 1, n
       read(u) k
       if (k >= 0) then
          allocate(character(len=k) :: str_pool(i)%text)
          if (k > 0) read(u) str_pool(i)%text
          call str_index(i)
       end if
    end do
    read(u) n, global_count, global_gen
    if (allocated(global_root)) deallocate(global_root)
    allocate(global_root(n))
    read(u) global_root
    read(u) obj_live, vec_live, str_live, arena_live_now, old_at_full, promoted_since_full
    if (allocated(obj_young)) deallocate(obj_young, vec_young, str_young, obj_rem, vec_rem, rem_set)
    allocate(obj_young(1024), vec_young(1024), str_young(1024), rem_set(1024))
    allocate(obj_rem(size(obj_pool)), vec_rem(size(vec_pool)))
    obj_rem = .false.; vec_rem = .false.
    if (allocated(obj_aged)) deallocate(obj_aged, vec_aged, obj_aged_list, vec_aged_list)
    allocate(obj_aged(size(obj_pool)), vec_aged(size(vec_pool)), obj_aged_list(1024), vec_aged_list(1024))
    obj_aged = .false.; vec_aged = .false.
    n_obj_young = 0; n_vec_young = 0; n_str_young = 0; n_rem = 0; n_obj_aged = 0; n_vec_aged = 0
    obj_pend_dead = 0; vec_pend_dead = 0; str_pend_dead = 0
    gc_allocs = 0; gc_frees = 0; gc_collections = 0; gc_young_collections = 0
    gc_no_collect = .false.
    call heap_sync_init()
    n_running = 1
    n_parked = 0
    call gc_stacks_reset()
    call gc_stack_new(1)
    call clear_batches(stacks(1)%s)
    read(u) b
    call gc_global_keep(stacks(1)%s%bindings, b)
    ok = .true.
  end subroutine gc_image_read

  ! The kind of the object at a pool index, 0 when the slot is free:
  ! how the image loader finds the objects whose native resource it
  ! must rebuild (a regex's ICU object).
  function gc_obj_kind_at(i) result(k)
    integer, intent(in) :: i
    integer :: k
    k = 0
    if (i < 1 .or. i > size(obj_pool)) return
    if (obj_free(i)) return
    k = obj_pool(i)%kind
  end function gc_obj_kind_at

  subroutine gc_stack_new(id)
    integer, intent(in) :: id
    type(gc_stack_ref), allocatable :: bigger(:)
    integer :: n
    logical :: stop
    if (.not. allocated(stacks)) allocate(stacks(8))
    if (id > size(stacks)) then
       ! the collector and gc_stack_of read it: it moves with the world
       ! stopped -- once a thread has a stack; before, there is one thread
       stop = stack_key_made .and. heap_sync_up
       if (stop) stop = c_associated(th_key_get(stack_key))
       if (stop) call gc_grow_begin()
       n = size(stacks)
       allocate(bigger(max(2 * n, id)))
       bigger(1:n) = stacks(1:n)
       call move_alloc(bigger, stacks)
       if (stop) call gc_grow_end()
    end if
    n_stacks = max(n_stacks, id)
    if (.not. associated(stacks(id)%s)) allocate(stacks(id)%s)
    if (associated(stacks(id)%s%vstack)) then
       stacks(id)%s%vstack(1:stacks(id)%s%vs_hi) = nilv
    else
       call vstack_make(stacks(id)%s)
    end if
    stacks(id)%s%vs_top = 0
    stacks(id)%s%vs_hi = 0
    ! NOT the batches: Eval empties a reused context's stack here, and its
    ! batches and young list must survive -- dropping the young list lost
    ! live young objects from the next young collection's view
  end subroutine gc_stack_new

  ! The calling thread runs on context `id`'s stack from now on: at a
  ! thread's start, and for the debugger's same-thread switch.
  ! A stack's slots: CLOTRAN_STACK_SLOTS of them, 4,194,304 (64 MB of
  ! address space) unless set. calloc hands back zeroes, which is nil, and
  ! maps a page only when it is first written, so a thread pays for the
  ! depth it reaches. The interpreter's deepest -- CLOTRAN_MAX_FRAMES of
  ! a one-line fn -- reached 1,400,000.
  subroutine vstack_make(s)
    type(gc_stack), intent(inout) :: s
    interface
       function calloc(n, sz) bind(C, name="calloc") result(p)
         import :: c_size_t, c_ptr
         integer(c_size_t), value :: n, sz
         type(c_ptr) :: p
       end function calloc
    end interface
    integer, save :: slots = 0
    character(len=24) :: buf
    integer :: st, n
    type(c_ptr) :: p
    if (slots == 0) then
       n = 4194304
       call get_environment_variable("CLOTRAN_STACK_SLOTS", buf)
       if (len_trim(buf) > 0) then
          read(buf, *, iostat=st) n
          if (st /= 0 .or. n < 1024) n = 4194304
       end if
       slots = n
    end if
    p = calloc(int(slots, c_size_t), int(storage_size(nilv) / 8, c_size_t))
    if (.not. c_associated(p)) error stop "clotran: no memory for a value stack"
    call c_f_pointer(p, s%vstack, [slots])
  end subroutine vstack_make

  subroutine vstack_free(s)
    type(gc_stack), intent(inout) :: s
    interface
       subroutine free(p) bind(C, name="free")
         import :: c_ptr
         type(c_ptr), value :: p
       end subroutine free
    end interface
    if (.not. associated(s%vstack)) return
    call free(c_loc(s%vstack(1)))
    nullify(s%vstack)
  end subroutine vstack_free

  subroutine gc_stack_bind(id)
    integer, intent(in) :: id
    logical :: ok
    if (id > n_stacks) call gc_stack_new(id)
    if (.not. associated(stacks(id)%s)) call gc_stack_new(id)
    ok = th_key_set(stack_key, c_loc(stacks(id)%s))
  end subroutine gc_stack_bind

  ! Which heap this is: gc_init starts a new one. A cache of heap values
  ! outside the heap (CompiledFn's flat pools) is good for one generation.
  integer function gc_generation()
    gc_generation = global_gen
  end function gc_generation

  ! Context `id`'s stack, made if need be. Stacks never move, so a
  ! context may keep this pointer and skip the key (Eval's eval_ctx%stk).
  function gc_stack_of(id) result(s)
    integer, intent(in) :: id
    type(gc_stack), pointer :: s
    if (id > n_stacks) call gc_stack_new(id)
    if (.not. associated(stacks(id)%s)) call gc_stack_new(id)
    s => stacks(id)%s
  end function gc_stack_of

  ! This thread's stack.
  function my_stack() result(s)
    type(gc_stack), pointer :: s
    type(c_ptr) :: p
    p = th_key_get(stack_key)
    if (.not. c_associated(p)) error stop "clotran: a value stack used on a thread with none"
    call c_f_pointer(p, s)
  end function my_stack

  subroutine heap_sync_init()
    if (heap_sync_up) return
    if (.not. (th_lock_init(heap_lock) .and. th_cond_init(heap_cond))) &
         error stop "clotran: no lock for the heap"
    if (.not. th_lock_init(rem_lk)) error stop "clotran: no lock for the remembered set"
    if (.not. (th_lock_init(state_lk) .and. th_cond_init(state_cv))) &
         error stop "clotran: no lock for shared state"
    heap_sync_up = .true.
  end subroutine heap_sync_init

  ! Into the heap: take its lock, and if the world is stopped, park here
  ! -- a safepoint -- with a and b on this thread's stack until it goes
  ! on. `entered` says whether this call took the lock: a finalizer that
  ! allocates, run by a collection this thread started, already holds it.
  subroutine heap_enter(a, b, entered)
    type(gc_value), intent(in) :: a(:), b(:)
    logical, intent(out) :: entered
    type(gc_stack), pointer :: s
    integer :: base, i
    logical :: ok
    call gc_ensure_init()
    s => my_stack()
    entered = .not. s%holds_heap
    if (.not. entered) return
    ok = th_lock_acquire(heap_lock)
    s%holds_heap = .true.
    if (stop_world) then
       base = vs_enter_on(s, size(a) + size(b))
       do i = 1, size(a)
          s%vstack(base + i) = a(i)
       end do
       do i = 1, size(b)
          s%vstack(base + size(a) + i) = b(i)
       end do
       n_parked = n_parked + 1
       ok = th_cond_broadcast(heap_cond)
       do while (stop_world)
          ok = th_cond_wait(heap_cond, heap_lock)
       end do
       n_parked = n_parked - 1
       call vs_leave_on(s, base)
    end if
  end subroutine heap_enter

  subroutine heap_leave(entered)
    logical, intent(in) :: entered
    type(gc_stack), pointer :: s
    logical :: ok
    if (.not. entered) return
    s => my_stack()
    s%holds_heap = .false.
    ok = th_lock_release(heap_lock)
  end subroutine heap_leave

  ! Every other running mutator parked (heap_lock held throughout, except
  ! while waiting). `stopped` says whether this call stopped it, so a
  ! nested stop -- a growth inside a collection's allocation -- is one.
  subroutine world_stop(stopped)
    logical, intent(out) :: stopped
    logical :: ok
    stopped = .not. stop_world
    if (.not. stopped) return
    if (n_running <= 1) then
       stopped = .false.   ! no one to stop: the common case, the baton on
       return
    end if
    stop_world = .true.
    block
      integer(8) :: t0, t1, rate
      call system_clock(t0, rate)
      do while (n_parked < n_running - 1)
         ok = th_cond_wait(heap_cond, heap_lock)
      end do
      call system_clock(t1)
      gc_safepoint_ms = gc_safepoint_ms + real(t1 - t0, 8) * 1000d0 / real(rate, 8)
    end block
  end subroutine world_stop

  subroutine world_start(stopped)
    logical, intent(in) :: stopped
    logical :: ok
    if (.not. stopped) return
    stop_world = .false.
    ok = th_cond_broadcast(heap_cond)
  end subroutine world_start

  ! This thread runs heap code from now on: it allocates, and a stop
  ! waits for it. Not while the world is stopped.
  subroutine gc_mutator_enter()
    logical :: ok
    call gc_ensure_init()
    ok = th_lock_acquire(heap_lock)
    do while (stop_world)
       ok = th_cond_wait(heap_cond, heap_lock)
    end do
    n_running = n_running + 1
    ok = th_lock_release(heap_lock)
  end subroutine gc_mutator_enter

  ! ... and no longer: a stop stops waiting for it. It holds nothing the
  ! collector must see but its value stack, which is scanned regardless.
  subroutine gc_mutator_leave()
    logical :: ok
    ok = th_lock_acquire(heap_lock)
    n_running = n_running - 1
    ok = th_cond_broadcast(heap_cond)
    ok = th_lock_release(heap_lock)
  end subroutine gc_mutator_leave

  ! Every stack but 1 gone, and the calling thread on stack 1 -- kept as
  ! it is: Eval starts its contexts over (ctx_reset) with frames of its
  ! own on it. gc_init empties it.
  subroutine gc_stacks_reset()
    integer :: i
    if (.not. stack_key_made) then
       if (.not. th_key_create(stack_key)) error stop "clotran: no thread key for the value stacks"
       stack_key_made = .true.
    end if
    do i = 2, n_stacks
       if (associated(stacks(i)%s)) then
          call vstack_free(stacks(i)%s)
          deallocate(stacks(i)%s)
       end if
    end do
    n_stacks = min(n_stacks, 1)
    call gc_stack_bind(1)
  end subroutine gc_stacks_reset

  ! --- immediates: no heap involved at all -----------------------

  function gc_nil() result(v)
    type(gc_value) :: v
    v = nilv
  end function gc_nil

  function gc_bool(b) result(v)
    logical, intent(in) :: b
    type(gc_value) :: v
    v%tag = GCT_BOOL
    if (b) v%ival = 1
  end function gc_bool

  ! Two specifics behind one name. Most callers hand this a plain
  ! `integer` -- a count, an index, a character code -- and widening
  ! the dummy instead would have broken every one of them, because
  ! Fortran matches arguments by KIND and will not promote silently.
  function gc_int4(i) result(v)
    integer(kind=4), intent(in) :: i
    type(gc_value) :: v
    v%tag = GCT_INT
    v%ival = int(i, gc_ip)
  end function gc_int4

  function gc_int8(i) result(v)
    integer(kind=8), intent(in) :: i
    type(gc_value) :: v
    v%tag = GCT_INT
    v%ival = i
  end function gc_int8

  ! The greatest common divisor, by Euclid. Both arguments are taken
  ! as magnitudes; sign is the caller's business.
  ! in 128 bits: abs(Long/MIN_VALUE) overflows a long, and (/ MIN 5)
  ! answered -9223372036854775808/-5
  pure function gc_gcd(a0, b0) result(g)
    integer(gc_ip), intent(in) :: a0, b0
    integer(gc_ip) :: g
    integer, parameter :: w = selected_int_kind(30)
    integer(w) :: a, b, t
    a = abs(int(a0, w))
    b = abs(int(b0, w))
    do while (b /= 0)
       t = b
       b = mod(a, b)
       a = t
    end do
    if (a == 0) a = 1
    ! a gcd of 2^63 (both parts MIN) cannot be a long; 1 leaves them as
    ! they are, which rat_make never asks of it
    if (a > int(huge(0_gc_ip), w)) a = 1
    g = int(a, gc_ip)
  end function gc_gcd

  ! The ONLY way to make a ratio, because a ratio that is not in
  ! normal form breaks equality: 2/4 and 1/2 must be the same value,
  ! and gc_equal compares the two fields directly rather than
  ! cross-multiplying.
  !
  ! Returns an INTEGER, not a ratio, when the denominator reduces to
  ! 1 -- that is Clojure's rule, verified: (/ 4 2) is 2 and
  ! (/ 0 5) is 0. A zero denominator is the caller's to reject; this
  ! returns nil rather than dividing.
  ! The NUMERATOR is 64-bit, like any other integer here. The
  ! DENOMINATOR lives in `ref`, which is 32-bit, so a denominator
  ! past 2^31 wraps -- the same overflow every other integer
  ! operation has, reached sooner. DEVIATIONS 26.
  ! A BigInt from canonical decimal text. Nothing else builds one:
  ! the text is normalized here so every later comparison is exact.
  ! A class from its canonical name. class_key in Eval.f90 decides
  ! the spelling; this only stores it.
  ! A decimal from BigDec's internal pair text. The reader and the
  ! arithmetic build that; nothing else should.
  function gc_dec(text, roots) result(v)
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    v = new_text(text, roots, GCT_DEC)
  end function gc_dec

  subroutine gc_dec_text(v, s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable, intent(out) :: s
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    block
       call dec_make("0", 0, o=dlt_1)
       s = dlt_1
    end block
    if (v%tag == GCT_DEC) then
       block
          call gc_ref_text(v%ref, s=dlt_1)
          s = dlt_1
       end block
    end if
  end subroutine gc_dec_text

  function gc_class(text, roots) result(v)
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    v = new_text(text, roots, GCT_CLASS)
  end function gc_class

  subroutine gc_class_text(v, s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable, intent(out) :: s
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    s = ""
    if (v%tag == GCT_CLASS) then
       block
          call gc_ref_text(v%ref, s=dlt_1)
          s = dlt_1
       end block
    end if
  end subroutine gc_class_text

  function gc_big(text, roots) result(v)
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    block
       call big_norm(text, o=dlt_1)
       v = new_text(dlt_1, roots, GCT_BIG)
    end block
  end function gc_big

  pure function gc_is_big(v) result(yes)
    type(gc_value), intent(in) :: v
    logical :: yes
    yes = (v%tag == GCT_BIG)
  end function gc_is_big

  subroutine gc_big_text(v, s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable, intent(out) :: s
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    s = "0"
    if (v%tag == GCT_BIG) then
       block
          call gc_ref_text(v%ref, s=dlt_1)
          s = dlt_1
       end block
    end if
  end subroutine gc_big_text

  ! a ratio's "n/d" text, already in lowest terms (rat_make makes it)
  function gc_bigratio(text, roots) result(v)
    character(len=*), intent(in) :: text
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    v = new_text(text, roots, GCT_BIGRATIO)
  end function gc_bigratio

  subroutine gc_bigratio_text(v, s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable, intent(out) :: s
    s = "0/1"
    if (v%tag == GCT_BIGRATIO) call gc_ref_text(v%ref, s=s)
  end subroutine gc_bigratio_text

  ! gcd of two non-negative integers, as text: Euclid
  subroutine big_gcd(a0, b0, g)
    character(len=*), intent(in) :: a0, b0
    character(len=:), allocatable, intent(out) :: g
    character(len=:), allocatable :: a, b, q, r
    a = a0
    b = b0
    do while (b /= "0")
       call big_divmod(a, b, q, r)
       a = b
       b = r
    end do
    g = a
  end subroutine big_gcd

  ! n/d in its one form; d is not zero. An integral result is a BigInt
  ! when int_big -- a Ratio's arithmetic answers 4N, not 4 -- and the
  ! smallest integer that holds it otherwise.
  function gc_rat_make(n0, d0, int_big, roots) result(v)
    character(len=*), intent(in) :: n0, d0
    logical, intent(in) :: int_big
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    character(len=:), allocatable :: n, d, g, an, q, r
    n = n0
    d = d0
    if (big_is_neg(d)) then
       call big_neg(n, o=an); n = an
       call big_neg(d, o=an); d = an
    end if
    call big_abs(n, o=an)
    call big_gcd(an, d, g)
    if (g /= "1" .and. g /= "0") then
       call big_divmod(n, g, q, r); n = q
       call big_divmod(d, g, q, r); d = q
    end if
    if (d == "1") then
       if (.not. int_big .and. big_fits_i64(n)) then
          v = gc_int(big_to_i64(n))
       else
          v = gc_big(n, roots)
       end if
    else if (big_fits_i64(n) .and. big_fits_i64(d)) then
       if (big_to_i64(d) <= 2147483647_gc_ip) then
          v = gc_ratio(big_to_i64(n), big_to_i64(d))
       else
          v = gc_bigratio(n // "/" // d, roots)
       end if
    else
       v = gc_bigratio(n // "/" // d, roots)
    end if
  end function gc_rat_make

  function gc_ratio(num0, den0) result(v)
    integer(gc_ip), intent(in) :: num0, den0
    type(gc_value) :: v
    integer(gc_ip) :: num, den, g
    if (den0 == 0) then
       v = nilv
       return
    end if
    num = num0
    den = den0
    ! The sign lives on the numerator: (/ 1 -3) is -1/3, never 1/-3.
    if (den < 0) then
       num = -num
       den = -den
    end if
    g = gc_gcd(num, den)
    num = num / g
    den = den / g
    if (den == 1) then
       v = gc_int(num)
    else
       v%tag = GCT_RATIO
       v%ival = num
       v%ref = int(den, kind=4)
    end if
  end function gc_ratio

  pure function gc_numerator(v) result(n)
    type(gc_value), intent(in) :: v
    integer(gc_ip) :: n
    n = v%ival
  end function gc_numerator

  pure function gc_denominator(v) result(d)
    type(gc_value), intent(in) :: v
    integer(gc_ip) :: d
    if (v%tag == GCT_RATIO) then
       d = int(v%ref, gc_ip)
    else
       d = 1
    end if
  end function gc_denominator

  function gc_real(r) result(v)
    real(gc_dp), intent(in) :: r
    type(gc_value) :: v
    v%tag = GCT_REAL
    v%ival = transfer(r, v%ival)
  end function gc_real

  ! A real value's double: its bits are the payload.
  elemental function gc_rval(v) result(r)
    type(gc_value), intent(in) :: v
    real(gc_dp) :: r
    r = transfer(v%ival, r)
  end function gc_rval

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
    logical :: entered, stopped
    type(gc_value) :: none(0)
    type(gc_stack), pointer :: s
    if (gc_every > 0 .and. .not. gc_no_collect) call every_tick(roots, none)
    if (batching()) then
       s => my_stack()
       if (fast_ok(s) .and. s%n_str_b == 0 .and. s%cp_str < s%np_str) call pend_refill_str(s)
       if (fast_ok(s) .and. s%n_str_b > 0) then
          idx = s%str_b(s%n_str_b)
          s%n_str_b = s%n_str_b - 1
          str_free(idx) = .false.
          str_mark(idx) = .false.
          s%d_str_live = s%d_str_live + 1
          s%d_allocs = s%d_allocs + 1
          call y_add(s%y_str, s%n_y_str, idx)
          str_pool(idx)%text = text
          call str_index(idx)
          v%tag = tag
          v%ref = idx
          return
       end if
    end if
    call heap_enter(roots, none, entered)
    ! ponytail: the world stops for every allocation that may collect or
    ! grow -- rare outside torture; the fast path below never stops it
    stopped = .false.
    if (gc_torture .or. (str_free_head == 0 .and. str_used >= size(str_pool))) call world_stop(stopped)
    if (gc_no_collect) then
       if (str_free_head == 0 .and. str_used >= size(str_pool)) call grow_str()
    else if (gc_torture .or. (str_free_head == 0 .and. str_used >= size(str_pool))) then
       call collect_auto(roots)
       if (str_free_head == 0 .and. str_used >= size(str_pool)) call grow_str()
       ! Not under torture: it collects at EVERY allocation, so almost
       ! nothing is garbage per collection and the half-live rule
       ! would double the pool on every allocation until the process
       ! was killed. Torture tests rooting, not the growth policy.
       if (.not. gc_torture) then
          do while (size(str_pool) < 2 * (str_live - str_pend_dead))
             call grow_str()
          end do
       end if
    end if
    call world_start(stopped)
    idx = str_take()
    str_free(idx) = .false.
    str_mark(idx) = .false.
    str_live = str_live + 1
    call young_add(str_young, n_str_young, idx)
    str_pool(idx)%text = text
    call str_index(idx)
    v%tag = tag
    v%ref = idx
    gc_allocs = gc_allocs + 1   ! statistics: shared, and counted under the lock
    call heap_leave(entered)
  end function new_text

  ! CLOTRAN_GC_EVERY=N: a collection at every Nth allocation of ANY kind
  ! -- an object, a vector or a text. Objects alone left a value held
  ! across a string's allocation unseen: swap! kept f's answer in a local
  ! while the validator's key was made, and a collection there freed it
  ! (spec's registry atom then held whatever reused the slot), and every
  ! torture run passed. `held` are the caller's roots and `extra` what it
  ! is about to store.
  subroutine every_tick(held, extra)
    type(gc_value), intent(in) :: held(:), extra(:)
    logical :: entered, stopped
    every_count = every_count + 1
    if (mod(every_count, gc_every) /= 0) return
    call heap_enter(held, extra, entered)
    call world_stop(stopped)
    call collect_auto(held)
    call world_start(stopped)
    call heap_leave(entered)
  end subroutine every_tick

  ! An object of the given kind, with up to OBJ_SLOTS initial slots.
  function gc_obj(kind, slots, roots) result(v)
    integer, intent(in) :: kind
    type(gc_value), intent(in) :: slots(:), roots(:)
    type(gc_value) :: v
    type(gc_value), allocatable :: all_roots(:)
    integer :: idx, i
    logical :: entered, stopped
    type(gc_stack), pointer :: s

    if (kind >= 0 .and. kind <= 63) gc_kind_n(kind) = gc_kind_n(kind) + 1
    if (gc_every > 0 .and. .not. gc_no_collect) then
       allocate(all_roots(size(roots) + size(slots)))
       all_roots(1:size(roots)) = roots
       all_roots(size(roots) + 1:) = slots
       call every_tick(all_roots, slots)
       deallocate(all_roots)
    end if
    if (batching()) then
       s => my_stack()
       if (fast_ok(s) .and. s%n_obj_b == 0 .and. s%cp_obj < s%np_obj) call pend_refill_obj(s)
       if (fast_ok(s) .and. s%n_obj_b > 0) then
          idx = s%obj_b(s%n_obj_b)
          s%n_obj_b = s%n_obj_b - 1
          obj_free(idx) = .false.
          obj_mark(idx) = .false.
          s%d_obj_live = s%d_obj_live + 1
          s%d_allocs = s%d_allocs + 1
          call y_add(s%y_obj, s%n_y_obj, idx)
          obj_pool(idx)%kind = kind
          obj_pool(idx)%i1 = 0
          obj_pool(idx)%i2 = 0
          do i = 1, OBJ_SLOTS
             obj_pool(idx)%slot(i) = nilv
          end do
          do i = 1, min(size(slots), OBJ_SLOTS)
             obj_pool(idx)%slot(i) = slots(i)
          end do
          v%tag = GCT_OBJ
          v%ref = idx
          return
       end if
    end if

    call heap_enter(roots, slots, entered)
    stopped = .false.
    if (gc_torture .or. (obj_free_head == 0 .and. obj_used >= size(obj_pool))) call world_stop(stopped)
    if (gc_no_collect) then
       if (obj_free_head == 0 .and. obj_used >= size(obj_pool)) call grow_obj()
    else if (gc_torture .or. (obj_free_head == 0 .and. obj_used >= size(obj_pool))) then
       allocate(all_roots(size(roots) + size(slots)))
       all_roots(1:size(roots)) = roots
       all_roots(size(roots) + 1:) = slots
       call collect_auto(all_roots)
       if (obj_free_head == 0 .and. obj_used >= size(obj_pool)) call grow_obj()
       ! Not under torture: it collects at EVERY allocation, so almost
       ! nothing is garbage per collection and the half-live rule
       ! would double the pool on every allocation until the process
       ! was killed. Torture tests rooting, not the growth policy.
       if (.not. gc_torture) then
          do while (size(obj_pool) < 2 * (obj_live - obj_pend_dead))
             call grow_obj()
          end do
       end if
    end if
    call world_start(stopped)
    idx = obj_take()
    obj_free(idx) = .false.
    obj_mark(idx) = .false.
    obj_live = obj_live + 1
    call young_add(obj_young, n_obj_young, idx)
    obj_pool(idx)%kind = kind
    obj_pool(idx)%i1 = 0
    obj_pool(idx)%i2 = 0
    do i = 1, OBJ_SLOTS
       obj_pool(idx)%slot(i) = nilv
    end do
    do i = 1, min(size(slots), OBJ_SLOTS)
       obj_pool(idx)%slot(i) = slots(i)
    end do
    v%tag = GCT_OBJ
    v%ref = idx
    gc_allocs = gc_allocs + 1
    call heap_leave(entered)
  end function gc_obj

  ! A run of n values, all nil.
  function gc_vec(n, roots) result(v)
    integer, intent(in) :: n
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: idx, i, c
    logical :: entered, stopped
    type(gc_value) :: none(0)
    type(gc_stack), pointer :: s
    if (gc_every > 0 .and. .not. gc_no_collect) call every_tick(roots, none)

    if (batching()) then
       s => my_stack()
       c = 0
       if (n > 0) c = size_class(n)
       if (fast_ok(s) .and. s%cp_vec < s%np_vec) then
          if (s%n_vec_b == 0) then
             call pend_refill_vec(s)
          else if (c > 0 .and. c <= RUN_CLASSES) then
             if (s%n_run_b(c) == 0) call pend_refill_vec(s)
          end if
       end if
       if (fast_ok(s) .and. s%n_vec_b > 0 .and. c <= RUN_CLASSES) then
          if (c == 0) then
             ok_fast: block
               idx = s%vec_b(s%n_vec_b)
               s%n_vec_b = s%n_vec_b - 1
               vec_pool(idx)%off = 0
             end block ok_fast
          else if (s%n_run_b(c) > 0) then
             idx = s%vec_b(s%n_vec_b)
             s%n_vec_b = s%n_vec_b - 1
             vec_pool(idx)%off = s%run_b(s%n_run_b(c), c)
             s%n_run_b(c) = s%n_run_b(c) - 1
          else
             idx = 0
          end if
          if (idx /= 0) then
             vec_free(idx) = .false.
             vec_mark(idx) = .false.
             s%d_vec_live = s%d_vec_live + 1
             s%d_arena_live = s%d_arena_live + max(n, 0)
             s%d_allocs = s%d_allocs + 1
             call y_add(s%y_vec, s%n_y_vec, idx)
             vec_pool(idx)%len = max(n, 0)
             do i = 1, n
                vec_store(vec_pool(idx)%off + i - 1) = nilv
             end do
             v%tag = GCT_VEC
             v%ref = idx
             return
          end if
       end if
    end if

    call heap_enter(roots, none, entered)
    stopped = .false.
    if (gc_torture .or. (vec_free_head == 0 .and. vec_used >= size(vec_pool)) &
         .or. arena_alloc_since >= max(2 * arena_live, 262144)) call world_stop(stopped)
    ! Growing the ARENA is a reason to collect first, like filling the
    ! node pool: otherwise every run between two collections comes from
    ! fresh arena and it ends four times the live size (measured: 4.2M
    ! slots for 1.0M live after core.clj). One collection per doubling
    ! is the amortised bound either way.
    if (gc_no_collect) then
       if (vec_free_head == 0 .and. vec_used >= size(vec_pool)) call grow_vec()
    else if (.not. gc_torture .and. .not. (vec_free_head == 0 .and. vec_used >= size(vec_pool)) &
         .and. arena_alloc_since >= max(2 * arena_live, 262144)) then
       ! As many SLOTS have been handed out since the last collection as
       ! twice what that collection found live: collect, whether or not
       ! the arena is full, because a 128-slot frame is 128 slots of
       ! garbage and the node count does not see that. Otherwise
       ! slab_alloc simply grows the arena. That is the amortised bound -- arena about
       ! three times live in the worst case -- and it does not depend on
       ! how much one sweep freed, which fragmentation across size
       ! classes makes meaningless. ("Freed less than half" doubled the
       ! arena to 67M slots for 4.6M live.) The node pool's own growth
       ! rule must NOT run here: it doubled the pool on every one of these.
       call collect_auto(roots)
    else if (gc_torture .or. (vec_free_head == 0 .and. vec_used >= size(vec_pool))) then
       call collect_auto(roots)
       if (vec_free_head == 0 .and. vec_used >= size(vec_pool)) call grow_vec()
       ! Not under torture: it collects at EVERY allocation, so almost
       ! nothing is garbage per collection and the half-live rule
       ! would double the pool on every allocation until the process
       ! was killed. Torture tests rooting, not the growth policy.
       if (.not. gc_torture) then
          do while (size(vec_pool) < 2 * (vec_live - vec_pend_dead))
             call grow_vec()
          end do
       end if
    end if
    call world_start(stopped)
    idx = vec_take()
    vec_free(idx) = .false.
    vec_mark(idx) = .false.
    vec_live = vec_live + 1
    arena_live_now = arena_live_now + max(n, 0)
    call young_add(vec_young, n_vec_young, idx)
    call run_take(max(n, 0), vec_pool(idx)%off)
    vec_pool(idx)%len = max(n, 0)
    do i = 1, n
       vec_store(vec_pool(idx)%off + i - 1) = nilv
    end do
    v%tag = GCT_VEC
    v%ref = idx
    gc_allocs = gc_allocs + 1
    call heap_leave(entered)
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
    bmark(1:n) = obj_mark(1:n)   ! marked is old: growth must not make it young
    bfree(1:n) = obj_free(1:n)
    bnext(1:n) = obj_free_next(1:n)
    call grow_flags(obj_rem, 2 * n)
    call grow_flags(obj_aged, 2 * n)
    call move_alloc(bigger, obj_pool)
    call move_alloc(bmark, obj_mark)
    call move_alloc(bfree, obj_free)
    call move_alloc(bnext, obj_free_next)
  end subroutine grow_obj

  subroutine grow_flags(f, n)
    logical, allocatable, intent(inout) :: f(:)
    integer, intent(in) :: n
    logical, allocatable :: b(:)
    allocate(b(n))
    b = .false.
    b(1:size(f)) = f
    call move_alloc(b, f)
  end subroutine grow_flags

  ! Appends idx to a young list, growing it.
  ! ---- per-thread allocation (PLAN.md step 14d) ------------------------
  !
  ! One heap lock serialised every allocation; eight threads allocating
  ! spent their time waiting for it (sampled: 10,673 of ~17,000 samples
  ! in the mutex, all under gc_obj, gc_vec and new_text) and ran 2.5x
  ! slower than one. So with more than one mutator running, a thread
  ! takes free slots a batch at a time and allocates from its batch
  ! without the lock. With one mutator -- every test, torture, the REPL
  ! alone -- nothing changes: batching() is false and the one slot comes
  ! off the free list as always.
  !
  ! The fast path runs outside heap_enter, so it is not a safepoint; it
  ! only writes slots it owns, and a stop (collection, growth) waits for a
  ! running thread to reach its next one. It is not taken when a stop is
  ! already asked for, nor from inside the heap.

  logical function batching()
    batching = n_running > 1 .and. .not. gc_torture .and. .not. gc_no_collect
  end function batching

  ! Whether this thread may allocate from its batches right now.
  logical function fast_ok(s)
    type(gc_stack), pointer, intent(in) :: s
    fast_ok = batching() .and. .not. stop_world .and. .not. s%holds_heap
  end function fast_ok

  subroutine y_add(list, n, idx)
    integer, allocatable, intent(inout) :: list(:)
    integer, intent(inout) :: n
    integer, intent(in) :: idx
    if (.not. allocated(list)) allocate(list(256))
    call young_add(list, n, idx)
  end subroutine y_add

  ! At a collection, the world stopped: every thread's young and counts
  ! join the heap's, so the young collection sees every young object.
  subroutine merge_batches(lists)
    logical, intent(in) :: lists
    integer :: i, k
    type(gc_stack), pointer :: s
    do i = 1, n_stacks
       if (.not. associated(stacks(i)%s)) cycle
       s => stacks(i)%s
       if (.not. lists) then
          obj_live = obj_live + s%d_obj_live
          vec_live = vec_live + s%d_vec_live
          str_live = str_live + s%d_str_live
          arena_live_now = arena_live_now + s%d_arena_live
          gc_allocs = gc_allocs + s%d_allocs
          s%d_obj_live = 0; s%d_vec_live = 0; s%d_str_live = 0; s%d_arena_live = 0; s%d_allocs = 0
          cycle
       end if
       do k = 1, s%n_y_obj
          call young_add(obj_young, n_obj_young, s%y_obj(k))
       end do
       do k = 1, s%n_y_vec
          call young_add(vec_young, n_vec_young, s%y_vec(k))
       end do
       do k = 1, s%n_y_str
          call young_add(str_young, n_str_young, s%y_str(k))
       end do
       s%n_y_obj = 0; s%n_y_vec = 0; s%n_y_str = 0
       obj_live = obj_live + s%d_obj_live
       vec_live = vec_live + s%d_vec_live
       str_live = str_live + s%d_str_live
       arena_live_now = arena_live_now + s%d_arena_live
       gc_allocs = gc_allocs + s%d_allocs
       s%d_obj_live = 0; s%d_vec_live = 0; s%d_str_live = 0; s%d_arena_live = 0; s%d_allocs = 0
    end do
  end subroutine merge_batches

  ! At a collection's start, the world stopped: every thread's pending
  ! dead not yet reused is freed as a sweep frees -- finalizers run here,
  ! on the collector -- and loose runs go back to their class lists. After
  ! this no pending list exists, so the collection's marks mean what they
  ! always meant.
  subroutine finish_pending()
    integer :: i, k, j
    type(gc_stack), pointer :: s
    do i = 1, n_stacks
       if (.not. associated(stacks(i)%s)) cycle
       s => stacks(i)%s
       do k = s%cp_obj + 1, s%np_obj
          j = s%p_obj(k)
          if (.not. (obj_mark(j) .or. obj_free(j) .or. obj_aged(j))) call free_obj(j)
       end do
       do k = s%cp_vec + 1, s%np_vec
          j = s%p_vec(k)
          if (.not. (vec_mark(j) .or. vec_free(j) .or. vec_aged(j))) call free_vec(j)
       end do
       do k = s%cp_str + 1, s%np_str
          j = s%p_str(k)
          if (.not. (str_mark(j) .or. str_free(j))) call free_str(j)
       end do
       do k = 1, s%n_defer
          if (.not. obj_free(s%defer_obj(k))) call free_obj(s%defer_obj(k))
       end do
       do k = 1, s%n_loose
          call slab_push(s%loose_off(k), s%loose_len(k))
       end do
       s%np_obj = 0; s%np_vec = 0; s%np_str = 0; s%cp_obj = 0; s%cp_vec = 0; s%cp_str = 0
       s%n_defer = 0; s%n_loose = 0
    end do
    obj_pend_dead = 0; vec_pend_dead = 0; str_pend_dead = 0
    call sweep_counts_take()
  end subroutine finish_pending

  ! After a young collection's marking, the world stopped: each thread's
  ! young list becomes its pending list, to be swept by the thread
  ! itself. The dead in them are counted, for the growth rules: the
  ! young marked in this collection are the survivors, those of the
  ! heap's own young list (swept here) are known, and the rest of the
  ! marked are the pending lists' survivors.
  subroutine hand_off_young(sa_obj, sa_vec, sa_str)
    integer, intent(in) :: sa_obj, sa_vec, sa_str   ! survivors on the threads' lists
    integer :: i, t_obj, t_vec, t_str
    integer, allocatable :: tmp(:)
    type(gc_stack), pointer :: s
    t_obj = 0; t_vec = 0; t_str = 0
    do i = 1, n_stacks
       if (.not. associated(stacks(i)%s)) cycle
       s => stacks(i)%s
       call move_alloc(s%p_obj, tmp); call move_alloc(s%y_obj, s%p_obj); call move_alloc(tmp, s%y_obj)
       s%np_obj = s%n_y_obj; s%cp_obj = 0; s%n_y_obj = 0
       call move_alloc(s%p_vec, tmp); call move_alloc(s%y_vec, s%p_vec); call move_alloc(tmp, s%y_vec)
       s%np_vec = s%n_y_vec; s%cp_vec = 0; s%n_y_vec = 0
       call move_alloc(s%p_str, tmp); call move_alloc(s%y_str, s%p_str); call move_alloc(tmp, s%y_str)
       s%np_str = s%n_y_str; s%cp_str = 0; s%n_y_str = 0
       t_obj = t_obj + s%np_obj; t_vec = t_vec + s%np_vec; t_str = t_str + s%np_str
    end do
    obj_pend_dead = max(0, t_obj - sa_obj)
    vec_pend_dead = max(0, t_vec - sa_vec)
    str_pend_dead = max(0, t_str - sa_str)
  end subroutine hand_off_young

  ! This thread's batch topped up from its pending list: each dead object
  ! is freed into the batch -- flagged free, as a batched slot is -- and
  ! a survivor (marked) is passed over. No lock: only this thread reads
  ! or writes these entries until the next collection, and a collection
  ! waits for this thread to reach a safepoint.
  subroutine pend_refill_obj(s)
    type(gc_stack), pointer, intent(in) :: s
    integer :: j
    do while (s%n_obj_b < ALLOC_BATCH .and. s%cp_obj < s%np_obj)
       s%cp_obj = s%cp_obj + 1
       j = s%p_obj(s%cp_obj)
       if (obj_mark(j) .or. obj_free(j) .or. obj_aged(j)) cycle
       if (finalized_kind(obj_pool(j)%kind)) then
          ! its finalizer runs on the collector, not here
          if (.not. allocated(s%defer_obj)) allocate(s%defer_obj(64))
          call young_add(s%defer_obj, s%n_defer, j)
          cycle
       end if
       obj_pool(j)%kind = 0
       obj_free(j) = .true.
       s%d_obj_live = s%d_obj_live - 1
       s%n_obj_b = s%n_obj_b + 1
       s%obj_b(s%n_obj_b) = j
    end do
  end subroutine pend_refill_obj

  subroutine pend_refill_str(s)
    type(gc_stack), pointer, intent(in) :: s
    integer :: j
    do while (s%n_str_b < ALLOC_BATCH .and. s%cp_str < s%np_str)
       s%cp_str = s%cp_str + 1
       j = s%p_str(s%cp_str)
       if (str_mark(j) .or. str_free(j)) cycle
       ! the text stays allocated: the next assignment reuses or resizes it
       str_free(j) = .true.
       s%d_str_live = s%d_str_live - 1
       s%n_str_b = s%n_str_b + 1
       s%str_b(s%n_str_b) = j
    end do
  end subroutine pend_refill_str

  ! A dead vector's run goes to this thread's run batch of its class if
  ! there is room, else aside until the collection returns it.
  subroutine pend_refill_vec(s)
    type(gc_stack), pointer, intent(in) :: s
    integer :: j, c, n
    do while (s%n_vec_b < ALLOC_BATCH .and. s%cp_vec < s%np_vec)
       s%cp_vec = s%cp_vec + 1
       j = s%p_vec(s%cp_vec)
       if (vec_mark(j) .or. vec_free(j) .or. vec_aged(j)) cycle
       n = vec_pool(j)%len
       if (n > 0) then
          c = size_class(n)
          if (c <= RUN_CLASSES) then
             if (s%n_run_b(c) < RUN_BATCH) then
                s%n_run_b(c) = s%n_run_b(c) + 1
                s%run_b(s%n_run_b(c), c) = vec_pool(j)%off
                n = -n
             end if
          end if
          if (n > 0) then
             if (.not. allocated(s%loose_off)) allocate(s%loose_off(64), s%loose_len(64))
             call young_add(s%loose_off, s%n_loose, vec_pool(j)%off)
             s%n_loose = s%n_loose - 1
             call young_add(s%loose_len, s%n_loose, n)
          end if
          s%d_arena_live = s%d_arena_live - abs(n)
       end if
       vec_pool(j)%off = 0
       vec_pool(j)%len = 0
       vec_free(j) = .true.
       s%d_vec_live = s%d_vec_live - 1
       s%n_vec_b = s%n_vec_b + 1
       s%vec_b(s%n_vec_b) = j
    end do
  end subroutine pend_refill_vec

  ! A new heap (gc_init): batches name slots of the old one.
  subroutine clear_batches(s)
    type(gc_stack), pointer, intent(in) :: s
    s%n_obj_b = 0; s%n_vec_b = 0; s%n_str_b = 0; s%n_run_b = 0
    s%naspare = 0
    s%np_obj = 0; s%np_vec = 0; s%np_str = 0; s%cp_obj = 0; s%cp_vec = 0; s%cp_str = 0
    s%n_defer = 0; s%n_loose = 0
    s%n_y_obj = 0; s%n_y_vec = 0; s%n_y_str = 0
    s%d_obj_live = 0; s%d_vec_live = 0; s%d_str_live = 0; s%d_arena_live = 0; s%d_allocs = 0
  end subroutine clear_batches

  ! Under the heap lock, a slot for the caller -- obj_take, vec_take and
  ! str_take alike (generated: model/heapal.lisp; heapal-proof's
  ! theorems: never one in use, on the free list or in a batch). With
  ! batching, this thread's own dead first (pend_refill_*), then its
  ! batch filled from the free list and the pool's unused end, and the
  ! batch's last taken; else the free list's head or the unused end.
  integer function obj_take()
    type(gc_stack), pointer :: s
    integer(int64) :: r
    if (batching()) then
       s => my_stack()
       call pend_refill_obj(s)
       call hpg_obj_fill(hstate, int(ALLOC_BATCH, int64))
       call hpg_obj_pop(hstate, r)
       if (r > 0) then
          obj_take = int(r)
          return
       end if
    end if
    call hpg_obj_take(hstate, r)
    if (r <= 0) error stop "clotran: obj_take with the pool full"
    obj_take = int(r)
  end function obj_take

  integer function vec_take()
    type(gc_stack), pointer :: s
    integer(int64) :: r
    if (batching()) then
       s => my_stack()
       call pend_refill_vec(s)
       call hpg_vec_fill(hstate, int(ALLOC_BATCH, int64))
       call hpg_vec_pop(hstate, r)
       if (r > 0) then
          vec_take = int(r)
          return
       end if
    end if
    call hpg_vec_take(hstate, r)
    if (r <= 0) error stop "clotran: vec_take with the pool full"
    vec_take = int(r)
  end function vec_take

  integer function str_take()
    type(gc_stack), pointer :: s
    integer(int64) :: r
    if (batching()) then
       s => my_stack()
       call pend_refill_str(s)
       call hpg_str_fill(hstate, int(ALLOC_BATCH, int64))
       call hpg_str_pop(hstate, r)
       if (r > 0) then
          str_take = int(r)
          return
       end if
    end if
    call hpg_str_take(hstate, r)
    if (r <= 0) error stop "clotran: str_take with the pool full"
    str_take = int(r)
  end function str_take

  ! A run of n for a vector, under the heap lock (generated:
  ! model/heaprn.lisp; heaprn-proof's theorems: the run is inside the
  ! arena and apart from every run still free or batched, in any class).
  ! With batching and a small class, from this thread's batch of its class,
  ! filled from the class's free list and fresh arena WITHOUT growing when
  ! empty; else from the class's list or fresh arena. A run that does not
  ! fit grows the arena, with the world stopped, and is asked for again.
  subroutine run_take(n, off)
    integer, intent(in) :: n
    integer, intent(out) :: off
    integer(int64) :: r, c, l
    off = 0
    if (n <= 0) return
    call hpg_run_take(hstate, int(n, int64), merge(1_int64, 0_int64, batching()), r)
    if (r == 0) then
       c = hpg_size_class(int(n, int64), 1_int64, 1_int64)
       l = hpg_class_len(c, 1_int64, 1_int64)
       call arena_grow(int(l))
       call hpg_run_new(hstate, c, l, r)
       if (r <= 0) error stop "clotran: run_take with the arena full"
    end if
    off = int(r)
  end subroutine run_take

  subroutine young_add(list, n, idx)
    integer, allocatable, intent(inout) :: list(:)
    integer, intent(inout) :: n
    integer, intent(in) :: idx
    integer, allocatable :: b(:)
    if (n >= size(list)) then
       allocate(b(2 * size(list)))
       b(1:n) = list(1:n)
       call move_alloc(b, list)
    end if
    n = n + 1
    list(n) = idx
  end subroutine young_add

  ! The size class of a run of n: the smallest power of two that holds it.
  integer function size_class(n)
    integer, intent(in) :: n
    integer :: c
    c = 1
    do while (ishft(1, c - 1) < n)
       c = c + 1
    end do
    size_class = c
  end function size_class

  ! Whether a run of n would have to extend the arena: no free run of
  ! its class and no room at the end.
  logical function arena_would_grow(n)
    integer, intent(in) :: n
    integer :: c
    arena_would_grow = .false.
    if (n <= 0) return
    c = size_class(n)
    if (class_head(c) /= 0) return
    arena_would_grow = (store_used + ishft(1, c - 1) > size(vec_store))
  end function arena_would_grow

  ! The arena grown, with the world stopped, until l more words fit past
  ! its used end.
  subroutine arena_grow(l)
    integer, intent(in) :: l
    type(gc_value), allocatable :: bigger(:)
    integer :: sz
    logical :: stopped
    if (store_used + l <= size(vec_store)) return
    call world_stop(stopped)
    sz = size(vec_store)
    do while (store_used + l > sz)
       sz = 2 * sz
    end do
    allocate(bigger(sz))
    bigger(1:store_used) = vec_store(1:store_used)
    bigger(store_used + 1:) = nilv
    call move_alloc(bigger, vec_store)
    call world_start(stopped)
  end subroutine arena_grow

  ! A dead run goes back to its class's free list; its first slot
  ! carries the link.
  subroutine slab_free(idx)
    integer, intent(in) :: idx
    if (vec_pool(idx)%len <= 0) return
    call slab_push(vec_pool(idx)%off, vec_pool(idx)%len)
    vec_pool(idx)%off = 0
    vec_pool(idx)%len = 0
  end subroutine slab_free

  ! The run at off, of a vector of len, onto its class's free list.
  subroutine slab_push(off, len)
    integer, intent(in) :: off, len
    integer :: c
    if (len <= 0) return
    c = size_class(len)
    vec_store(off) = nilv
    vec_store(off)%ival = class_head(c)
    class_head(c) = off
  end subroutine slab_push

  ! Arena accounting for CLOTRAN_STATS: capacity, handed out, and the
  ! slots live runs actually use.
  subroutine gc_arena_stats(cap, used, live)
    integer, intent(out) :: cap, used, live
    integer :: i
    cap = 0
    if (allocated(vec_store)) cap = size(vec_store)
    used = store_used
    live = 0
    do i = 1, vec_used
       if (.not. vec_free(i)) live = live + vec_pool(i)%len
    end do
    write(0, '(A,I0,A,I0)') "arena: reused=", arena_reused, " fresh=", arena_fresh
    block
      integer :: c, off, cnt
      do c = 1, 12
         cnt = 0
         off = class_head(c)
         do while (off /= 0)
            cnt = cnt + 1
            off = int(vec_store(off)%ival)
         end do
         if (cnt > 0) write(0, '(A,I0,A,I0,A,I0)') "arena: class ", ishft(1, c - 1), " free runs=", cnt, " slots=", cnt * ishft(1, c - 1)
      end do
    end block
  end subroutine gc_arena_stats

  subroutine grow_vec()
    type(vec_node), allocatable :: bigger(:)
    logical, allocatable :: bmark(:), bfree(:)
    integer, allocatable :: bnext(:)
    integer :: n, i
    n = size(vec_pool)
    allocate(bigger(2 * n), bmark(2 * n), bfree(2 * n), bnext(2 * n))
    bigger(1:n) = vec_pool(1:n)
    bmark = .false.; bfree = .false.; bnext = 0
    bmark(1:n) = vec_mark(1:n)
    bfree(1:n) = vec_free(1:n)
    bnext(1:n) = vec_free_next(1:n)
    call grow_flags(vec_rem, 2 * n)
    call grow_flags(vec_aged, 2 * n)
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
       if (allocated(str_pool(i)%text)) call move_alloc(str_pool(i)%text, bigger(i)%text)
       bigger(i)%ncp = str_pool(i)%ncp
       if (allocated(str_pool(i)%ck)) call move_alloc(str_pool(i)%ck, bigger(i)%ck)
    end do
    bmark = .false.; bfree = .false.; bnext = 0
    bmark(1:n) = str_mark(1:n)
    bfree(1:n) = str_free(1:n)
    bnext(1:n) = str_free_next(1:n)
    call move_alloc(bigger, str_pool)
    call move_alloc(bmark, str_mark)
    call move_alloc(bfree, str_free)
    call move_alloc(bnext, str_free_next)
  end subroutine grow_str

  ! --- accessors -------------------------------------------------

  subroutine gc_text(v, s)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable, intent(out) :: s
    s = ""
    if (v%tag /= GCT_STR .and. v%tag /= GCT_SYM .and. v%tag /= GCT_KEY) return
    if (allocated(str_pool(v%ref)%text)) s = str_pool(v%ref)%text
  end subroutine gc_text

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
    if (v%tag == GCT_OBJ .and. i >= 1 .and. i <= OBJ_SLOTS) then
       obj_pool(v%ref)%slot(i) = x
       ! the write barrier: a young value into an old object
       if (obj_mark(v%ref) .and. .not. obj_rem(v%ref)) then
          if (is_young(x)) call remember_obj(v)
       end if
    end if
  end subroutine gc_set_slot

  ! Whether x is a heap object allocated since the last collection: the
  ! write barrier's test, generated (model/heapgn.lisp's hpg-young-ref --
  ! heapgn-proof's barrier-keeps: with it every old object stays black or
  ! remembered, which makes the young collection sound, young-closed)
  logical function is_young(x)
    type(gc_value), intent(in) :: x
    is_young = hpg_young_ref(hstate, int(x%tag, int64), int(x%ref, int64))
  end function is_young

  ! The flag is checked again under the lock: another thread may have
  ! remembered this object between the barrier's check and here.
  subroutine remember_obj(v)
    type(gc_value), intent(in) :: v
    logical :: ok
    ok = th_lock_acquire(rem_lk)
    if (.not. obj_rem(v%ref)) then
       obj_rem(v%ref) = .true.
       call remember(v)
    end if
    ok = th_lock_release(rem_lk)
  end subroutine remember_obj

  subroutine remember_vec(v)
    type(gc_value), intent(in) :: v
    logical :: ok
    ok = th_lock_acquire(rem_lk)
    if (.not. vec_rem(v%ref)) then
       vec_rem(v%ref) = .true.
       call remember(v)
    end if
    ok = th_lock_release(rem_lk)
  end subroutine remember_vec

  subroutine remember(v)
    type(gc_value), intent(in) :: v
    type(gc_value), allocatable :: b(:)
    if (n_rem >= size(rem_set)) then
       allocate(b(2 * size(rem_set)))
       b(1:n_rem) = rem_set(1:n_rem)
       call move_alloc(b, rem_set)
    end if
    n_rem = n_rem + 1
    rem_set(n_rem) = v
  end subroutine remember

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
    n = vec_pool(v%ref)%len
  end function gc_vec_len

  function gc_vec_get(v, i) result(out)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: out
    if (v%tag /= GCT_VEC) return
    if (i < 1 .or. i > gc_vec_len(v)) return
    out = vec_store(vec_pool(v%ref)%off + i - 1)
  end function gc_vec_get

  ! size(w) integer elements from i on, as one instruction of a flat
  ! body (Eval flat.inc): one call and one offset lookup per
  ! instruction. The caller guarantees v is a vector of integers long
  ! enough -- the code the flat compiler wrote.
  subroutine gc_vec_word(v, i, w)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    integer, intent(out) :: w(:)
    integer :: o, k
    o = vec_pool(v%ref)%off + i - 1
    do k = 1, size(w)
       w(k) = int(vec_store(o + k - 1)%ival)
    end do
  end subroutine gc_vec_word

  ! A new vector holding what src holds, copied as one block: the node
  ! a persistent trie path-copies on every assoc, 32 slots through a
  ! checked accessor and a barrier test each. The copy is young -- made
  ! just now, nothing allocated since -- so no write barrier is owed.
  function gc_vec_clone(src, roots) result(v)
    type(gc_value), intent(in) :: src
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: n, o1, o2, k
    n = gc_vec_len(src)
    v = gc_vec(n, [roots, src])
    if (n == 0) return
    o1 = vec_pool(src%ref)%off
    o2 = vec_pool(v%ref)%off
    ! element by element: two sections of one array are a possible
    ! overlap to the compiler, and it copied through a temporary
    do k = 0, n - 1
       vec_store(o2 + k) = vec_store(o1 + k)
    end do
  end function gc_vec_clone

  ! Element i of a raw vector with no checks: a flat body's registers,
  ! every index fixed when it was compiled against the frame's size.
  function gc_reg(v, i) result(out)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value) :: out
    out = vec_store(vec_pool(v%ref)%off + i - 1)
  end function gc_reg

  ! The same, stored; the write barrier only for a reference, since an
  ! immediate (a number, a boolean, nil) is never young
  subroutine gc_reg_set(v, i, x)
    type(gc_value), intent(in) :: v, x
    integer, intent(in) :: i
    vec_store(vec_pool(v%ref)%off + i - 1) = x
    if (x%ref /= 0) then
       if (vec_mark(v%ref) .and. .not. vec_rem(v%ref)) then
          if (is_young(x)) call remember_vec(v)
       end if
    end if
  end subroutine gc_reg_set

  ! the barrier's slow half: a register write that stored a young value
  ! into a vector the collector has marked old
  subroutine gc_reg_barrier(v, x)
    type(gc_value), intent(in) :: v, x
    if (is_young(x)) call remember_vec(v)
  end subroutine gc_reg_barrier

  subroutine gc_vec_set(v, i, x)
    type(gc_value), intent(in) :: v, x
    integer, intent(in) :: i
    if (v%tag /= GCT_VEC) return
    if (i < 1 .or. i > gc_vec_len(v)) return
    vec_store(vec_pool(v%ref)%off + i - 1) = x
    if (vec_mark(v%ref) .and. .not. vec_rem(v%ref)) then
       if (is_young(x)) call remember_vec(v)
    end if
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

  ! An explicit collection -- System/gc, a test -- frees everything
  ! unreachable, old included: a full one.
  subroutine gc_collect(roots)
    type(gc_value), intent(in) :: roots(:)
    gc_collections = gc_collections + 1
    call collect_full(roots, .false.)
    arena_alloc_since = 0
    arena_live = arena_live_now
  end subroutine gc_collect

  ! A collection an allocation asked for: young, or full when the old
  ! generation has doubled since the last full one.
  subroutine collect_auto(roots)
    type(gc_value), intent(in) :: roots(:)
    logical :: full
    integer(8) :: t0, t1, rate
    real(8) :: dt
    character(len=8) :: e
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1
    if (.not. gen_env_read) then
       call get_environment_variable("CLOTRAN_GC_FULL", e)
       gen_mode = trim(e) /= "1"
       call get_environment_variable("CLOTRAN_GC_VERIFY", e)
       gen_verify = trim(e) == "1"
       gen_env_read = .true.
    end if
    ! held: some thread is in data-structure code that called back into
    ! the evaluator (gc_hold_begin); the allocation goes on, the pools
    ! growing, and the next one after the hold collects
    if (clotran_gc_holding() > 0) return
    gc_collections = gc_collections + 1
    full = .not. gen_mode .or. promoted_since_full > max(old_at_full, 65536)
    ! torture: every allocation collects; alternate, so both kinds are
    ! exercised at every allocation site
    if (gc_torture) full = .not. gen_mode .or. mod(gc_collections, 2) == 0
    call system_clock(t0, rate)
    if (full) then
       call collect_full(roots, .true.)
       call system_clock(t1)
       dt = real(t1 - t0, 8) * 1000d0 / real(rate, 8)
       gc_full_ms = gc_full_ms + dt
       gc_full_max_ms = max(gc_full_max_ms, dt)
    else
       call collect_young(roots)
       call system_clock(t1)
       dt = real(t1 - t0, 8) * 1000d0 / real(rate, 8)
       gc_young_ms = gc_young_ms + dt
       gc_young_max_ms = max(gc_young_max_ms, dt)
       if (gen_verify) then
          block
            character(len=:), allocatable :: p
            block
               call gc_check_heap(problem=dlt_1)
               p = dlt_1
            end block
            if (len(p) > 0) then
               write(0, '(A)') "clotran: a young collection left a dangling reference: " // p
               error stop 1
            end if
          end block
       end if
    end if
    arena_alloc_since = 0
    arena_live = arena_live_now
  end subroutine collect_auto

  ! Every root: the global ones, every thread's value stack, and the
  ! allocation's own.
  subroutine push_roots(roots)
    type(gc_value), intent(in) :: roots(:)
    integer :: i, k
    do i = 1, global_count
       call push_mark(global_root(i))
    end do
    do i = 1, n_stacks
       if (.not. associated(stacks(i)%s)) cycle
       if (associated(stacks(i)%s%vstack)) then
          do k = 1, stacks(i)%s%vs_top
             call push_mark(stacks(i)%s%vstack(k))
          end do
       end if
    end do
    do i = 1, size(roots)
       call push_mark(roots(i))
    end do
  end subroutine push_roots

  ! `age`: the young survivors stay young (age_full_survivors) -- only an
  ! automatic collection; an explicit one (gc_collect: the heap image,
  ! a regex handle wanted back) leaves every survivor old and no set aged
  subroutine collect_full(roots, age)
    type(gc_value), intent(in) :: roots(:)
    logical, intent(in) :: age
    call finish_pending()
    call merge_batches(.true.)
    last_marked = gc_marked
    obj_marked = 0; vec_marked = 0; str_marked = 0
    obj_mark = .false.
    vec_mark = .false.
    str_mark = .false.
    call mark_begin()
    call push_roots(roots)
    call drain_mark_stack()
    last_marked = gc_marked - last_marked
    call census()
    call sweep()
    call unage_all()
    if (age) call age_full_survivors()
    call forget_young()
    old_at_full = obj_live + vec_live + str_live
    promoted_since_full = 0
  end subroutine collect_full

  ! CLOTRAN_STATS=2: after a full collection's marking, what is live, by
  ! object kind and by run length -- the instrument for "what is holding
  ! this seq" (a walk over (range 10^6) retained 3 objects an element).
  subroutine census()
    integer :: i, k, b, n
    integer :: kinds(0:40), runs(8)
    character(len=8), parameter :: kname(38) = [character(len=8) :: &
         "cons", "vector", "map", "closure", "atom", "lazy", "env", "meta", "ns", "var", &
         "hamt", "hamtleaf", "builtin", "recur", "seq", "set", "multifn", "sb", "err", "regex", &
         "matcher", "writer", "type", "inst", "delay", "array", "?27", "?28", "?29", "ast", &
         "chunk", "chunkbuf", "chunkseq", "task", "volatile", "compiled", "tvector", "tmap"]
    character(len=8), parameter :: rname(8) = [character(len=8) :: &
         "0-1", "2", "3", "4", "5-8", "9-16", "17-32", "33+"]
    character(len=8) :: e
    logical, save :: on = .false., read = .false.
    if (.not. read) then
       call get_environment_variable("CLOTRAN_STATS", e)
       on = trim(e) == "2"
       read = .true.
    end if
    if (.not. on) return
    kinds = 0; runs = 0
    do i = 1, obj_used
       if (.not. obj_mark(i) .or. obj_free(i)) cycle
       k = obj_pool(i)%kind
       if (k < 0 .or. k > 40) k = 0
       kinds(k) = kinds(k) + 1
    end do
    do i = 1, vec_used
       if (.not. vec_mark(i) .or. vec_free(i)) cycle
       n = vec_pool(i)%len
       if (n <= 1) then; b = 1
       else if (n <= 4) then; b = n
       else if (n <= 8) then; b = 5
       else if (n <= 16) then; b = 6
       else if (n <= 32) then; b = 7
       else; b = 8
       end if
       runs(b) = runs(b) + 1
    end do
    write(0, '(A)', advance="no") "census objs:"
    do k = 1, 38
       if (kinds(k) > 0) write(0, '(A,A,A,I0)', advance="no") " ", trim(kname(k)), "=", kinds(k)
    end do
    write(0, '(A,I0)') " other=", kinds(0) + sum(kinds(39:40))
    write(0, '(A)', advance="no") "census runs:"
    do b = 1, 8
       if (runs(b) > 0) write(0, '(A,A,A,I0)', advance="no") " ", trim(rname(b)), "=", runs(b)
    end do
    write(0, '(A)') ""
  end subroutine census

  ! The young only: marking stops at the old (already marked), and the
  ! remembered old objects stand in for the old ones that reach the
  ! young. Survivors are left marked -- old -- by the marking itself.
  subroutine collect_young(roots)
    type(gc_value), intent(in) :: roots(:)
    type(gc_value) :: v
    integer :: i, j, k, a_obj, a_vec, ta_obj, ta_vec, n
    type(gc_stack), pointer :: s
    type(gc_value) :: pv
    integer, allocatable :: prom_obj(:), prom_vec(:)
    integer(8) :: tm0, tm1, rate
    gc_young_collections = gc_young_collections + 1
    call system_clock(tm1, rate)
    call finish_pending()
    call system_clock(tm0)
    gc_finish_ms = gc_finish_ms + real(tm0 - tm1, 8) * 1000d0 / real(rate, 8)
    call merge_batches(.false.)
    last_marked = gc_marked
    obj_marked = 0; vec_marked = 0; str_marked = 0
    call mark_begin()
    call push_roots(roots)
    ! the remembered set's slots and words pushed (heapgn-proof's
    ! young-mark: roots, then scan-objs and scan-vecs of the remembered)
    do i = 1, n_rem
       v = rem_set(i)
       if (v%tag == GCT_OBJ) then
          call hpg_scan_obj(hstate, int(v%ref, int64), 0_int64)
       else if (v%tag == GCT_VEC) then
          call hpg_scan_vec(hstate, int(v%ref, int64))
       end if
    end do
    call drain_mark_stack()
    call system_clock(tm1)
    gc_ymark_ms = gc_ymark_ms + real(tm1 - tm0, 8) * 1000d0 / real(rate, 8)
    last_marked = gc_marked - last_marked
    obj_swept = 0; vec_swept = 0; str_swept = 0
    ! the aged: marked has survived twice and is old from here; unmarked
    ! is dead, and nothing else will sweep it
    ! the promoted are kept aside for a moment: once the young
    ! survivors below are aged, a promoted object that points at one of
    ! them is an old object pointing at a young one, and must be
    ! remembered -- no barrier saw that write, since it was made into
    ! an object that was young at the time
    a_obj = 0; a_vec = 0
    allocate(prom_obj(max(1, n_obj_aged)), prom_vec(max(1, n_vec_aged)))
    do i = 1, n_obj_aged
       j = obj_aged_list(i)
       obj_aged(j) = .false.
       if (obj_mark(j)) then
          a_obj = a_obj + 1
          prom_obj(a_obj) = j
       else if (.not. obj_free(j)) then
          call free_obj(j)
       end if
    end do
    do i = 1, n_vec_aged
       j = vec_aged_list(i)
       vec_aged(j) = .false.
       if (vec_mark(j)) then
          a_vec = a_vec + 1
          prom_vec(a_vec) = j
       else if (.not. vec_free(j)) then
          call free_vec(j)
       end if
    end do
    n_obj_aged = 0; n_vec_aged = 0
    ! the heap's own young: a survivor is aged, not promoted
    do i = 1, n_obj_young
       j = obj_young(i)
       if (obj_free(j)) cycle
       if (obj_mark(j)) then
          call age_obj(j)
       else
          call free_obj(j)
       end if
    end do
    do i = 1, n_vec_young
       j = vec_young(i)
       if (vec_free(j)) cycle
       if (vec_mark(j)) then
          call age_vec(j)
       else
          call free_vec(j)
       end if
    end do
    do i = 1, n_str_young
       j = str_young(i)
       if (.not. (str_mark(j) .or. str_free(j))) call free_str(j)
    end do
    ! the threads' young: survivors aged here; the dead stay on the
    ! lists, which become the threads' pending lists, swept by each
    ! thread as it allocates (pend_refill_*), not here
    ta_obj = 0; ta_vec = 0
    do i = 1, n_stacks
       if (.not. associated(stacks(i)%s)) cycle
       s => stacks(i)%s
       do k = 1, s%n_y_obj
          j = s%y_obj(k)
          if (obj_mark(j) .and. .not. obj_free(j)) then
             call age_obj(j)
             ta_obj = ta_obj + 1
          end if
       end do
       do k = 1, s%n_y_vec
          j = s%y_vec(k)
          if (vec_mark(j) .and. .not. vec_free(j)) then
             call age_vec(j)
             ta_vec = ta_vec + 1
          end if
       end do
    end do
    ! the promoted that point at an aged object are remembered now
    do i = 1, a_obj
       j = prom_obj(i)
       if (any_aged_slot(j)) then
          pv%tag = GCT_OBJ; pv%ref = j
          if (.not. obj_rem(j)) call remember_obj(pv)
       end if
    end do
    do i = 1, a_vec
       j = prom_vec(i)
       if (any_aged_run(j)) then
          pv%tag = GCT_VEC; pv%ref = j
          if (.not. vec_rem(j)) call remember_vec(pv)
       end if
    end do
    call sweep_counts_take()
    call hand_off_young(ta_obj, ta_vec, str_marked - (n_str_young - str_swept))
    call system_clock(tm0)
    gc_ysweep_ms = gc_ysweep_ms + real(tm0 - tm1, 8) * 1000d0 / real(rate, 8)
    ! promoted: what survived its second collection, and every string
    promoted_since_full = promoted_since_full + a_obj + a_vec + str_marked
    call forget_young()
  end subroutine collect_young

  subroutine age_obj(j)
    integer, intent(in) :: j
    obj_mark(j) = .false.
    obj_aged(j) = .true.
    call young_add(obj_aged_list, n_obj_aged, j)
  end subroutine age_obj

  subroutine age_vec(j)
    integer, intent(in) :: j
    vec_mark(j) = .false.
    vec_aged(j) = .true.
    call young_add(vec_aged_list, n_vec_aged, j)
  end subroutine age_vec

  logical function any_aged_slot(j)
    integer, intent(in) :: j
    integer :: k
    any_aged_slot = .false.
    do k = 1, OBJ_SLOTS
       if (aged_ref(obj_pool(j)%slot(k))) any_aged_slot = .true.
    end do
  end function any_aged_slot

  logical function any_aged_run(j)
    integer, intent(in) :: j
    integer :: k
    any_aged_run = .false.
    do k = 1, vec_pool(j)%len
       if (aged_ref(vec_store(vec_pool(j)%off + k - 1))) any_aged_run = .true.
    end do
  end function any_aged_run

  logical function aged_ref(x)
    type(gc_value), intent(in) :: x
    aged_ref = .false.
    if (x%ref == 0) return
    if (x%tag == GCT_OBJ) aged_ref = obj_aged(x%ref)
    if (x%tag == GCT_VEC) aged_ref = vec_aged(x%ref)
  end function aged_ref

  ! A full collection ages the young it finds alive rather than promoting
  ! them, as a young collection does. Promoted, the cell a lazy walk was
  ! on became old, its realisation put the next cell in the remembered
  ! set, and from then each young collection kept the whole window behind
  ! the walk alive through the dead old cell -- a chain no young
  ! collection breaks, which made full collections that started it again:
  ! compiled core's (dorun (range n)) marked 5*10^4 objects a young
  ! collection, an interpreted one 7. The old that point at an aged object
  ! are remembered, from one pass over the old.
  subroutine age_full_survivors()
    integer :: i, j, na
    type(gc_value) :: pv
    na = 0
    do i = 1, n_obj_young
       j = obj_young(i)
       if (obj_free(j) .or. .not. obj_mark(j)) cycle
       call age_obj(j)
       na = na + 1
    end do
    do i = 1, n_vec_young
       j = vec_young(i)
       if (vec_free(j) .or. .not. vec_mark(j)) cycle
       call age_vec(j)
       na = na + 1
    end do
    do i = 1, n_rem
       if (rem_set(i)%tag == GCT_OBJ) obj_rem(rem_set(i)%ref) = .false.
       if (rem_set(i)%tag == GCT_VEC) vec_rem(rem_set(i)%ref) = .false.
    end do
    n_rem = 0
    if (na == 0) return
    do j = 1, obj_used
       if (.not. obj_mark(j) .or. obj_free(j)) cycle
       if (any_aged_slot(j)) then
          pv%tag = GCT_OBJ; pv%ref = j
          call remember_obj(pv)
       end if
    end do
    do j = 1, vec_used
       if (.not. vec_mark(j) .or. vec_free(j)) cycle
       if (any_aged_run(j)) then
          pv%tag = GCT_VEC; pv%ref = j
          call remember_vec(pv)
       end if
    end do
  end subroutine age_full_survivors

  ! After a full collection every survivor is marked, so nothing is aged.
  subroutine unage_all()
    integer :: i
    do i = 1, n_obj_aged
       obj_aged(obj_aged_list(i)) = .false.
    end do
    do i = 1, n_vec_aged
       vec_aged(vec_aged_list(i)) = .false.
    end do
    n_obj_aged = 0; n_vec_aged = 0
  end subroutine unage_all

  ! After any collection: nothing is young, and only the old that point
  ! at an aged object stay remembered.
  subroutine forget_young()
    integer :: i, j, m
    logical :: keep
    do i = 1, n_stacks
       if (associated(stacks(i)%s)) stacks(i)%s%nspare = 0
       if (associated(stacks(i)%s)) stacks(i)%s%naspare = 0
    end do
    ! an old object still pointing at an aged one stays remembered:
    ! the aged object is unmarked and must be re-proven next time, and
    ! this edge is the only way the marking reaches it
    m = 0
    do i = 1, n_rem
       keep = .false.
       if (rem_set(i)%tag == GCT_OBJ) then
          do j = 1, OBJ_SLOTS
             if (aged_ref(obj_pool(rem_set(i)%ref)%slot(j))) keep = .true.
          end do
          if (.not. keep) obj_rem(rem_set(i)%ref) = .false.
       else if (rem_set(i)%tag == GCT_VEC) then
          do j = 1, vec_pool(rem_set(i)%ref)%len
             if (aged_ref(vec_store(vec_pool(rem_set(i)%ref)%off + j - 1))) keep = .true.
          end do
          if (.not. keep) vec_rem(rem_set(i)%ref) = .false.
       end if
       if (keep) then
          m = m + 1
          rem_set(m) = rem_set(i)
       end if
    end do
    n_rem = m
    n_obj_young = 0; n_vec_young = 0; n_str_young = 0
  end subroutine forget_young

  ! Value equality: same tag, and same
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
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
    a = a0
    b = b0
    do while (gc_kind(a) == OBJ_META)
       a = gc_slot(a, 1)
    end do
    do while (gc_kind(b) == OBJ_META)
       b = gc_slot(b, 1)
    end do
    eq = .false.
    ! An integer and a BigInt of the same value ARE equal: Clojure's
    ! equiv puts Long and BigInt in one category, so (= 1N 1) is true
    ! (and (= 1N 1.0) is not -- a double is its own category).
    if (a%tag == GCT_BIG .neqv. b%tag == GCT_BIG) then
       if (a%tag == GCT_BIG .and. b%tag == GCT_INT) then
          block
             call gc_ref_text(a%ref, s=dlt_1)
             eq = big_fits_i64(dlt_1)
          end block
          if (eq) then
             block
                call gc_ref_text(a%ref, s=dlt_1)
                eq = (big_to_i64(dlt_1) == b%ival)
             end block
          end if
       else if (b%tag == GCT_BIG .and. a%tag == GCT_INT) then
          block
             call gc_ref_text(b%ref, s=dlt_1)
             eq = big_fits_i64(dlt_1)
          end block
          if (eq) then
             block
                call gc_ref_text(b%ref, s=dlt_1)
                eq = (big_to_i64(dlt_1) == a%ival)
             end block
          end if
       end if
       return
    end if
    if (a%tag /= b%tag) return
    select case (a%tag)
    case (GCT_NIL)
       eq = .true.
    case (GCT_BOOL, GCT_INT, GCT_CHAR)
       eq = (a%ival == b%ival)
    case (GCT_REAL)
       eq = (gc_rval(a) == gc_rval(b))
    case (GCT_RATIO)
       ! Both fields. Normal form is what makes this correct without
       ! cross-multiplying, and the default branch below would have
       ! compared the denominators alone.
       eq = (a%ival == b%ival .and. a%ref == b%ref)
    case (GCT_BIG, GCT_CLASS, GCT_BIGRATIO)
       ! Canonical text, so this is exact.
       block
          call gc_ref_text(b%ref, s=dlt_1)
          eq = gc_ref_is(a%ref, dlt_1)
       end block
    case (GCT_DEC)
       ! By VALUE: (= 1M 1.0M) is true although the two print apart.
       block
          call gc_ref_text(a%ref, s=dlt_1)
          call gc_ref_text(b%ref, s=dlt_2)
          eq = (dec_cmp(dlt_1, dlt_2) == 0)
       end block
    case (GCT_STR, GCT_SYM, GCT_KEY)
       ! Compared by CONTENT, not by pool slot: the same text
       ! allocated twice is two slots but one value.
       eq = (gc_ref_len(a%ref) == gc_ref_len(b%ref))
       if (eq) then
          block
             call gc_ref_text(b%ref, s=dlt_1)
             eq = gc_ref_is(a%ref, dlt_1)
          end block
       end if
    case default
       ! A collection is its CONTENTS, when something above this
       ! module has said how to walk one. Identity was the old answer
       ! and it made (get {[1] 2} [1]) nil: the lookup key is a
       ! different object from the stored one, however equal.
       if (associated(obj_coll_equal) .and. &
            (((is_structural_kind(gc_kind(a)) .or. gc_kind(a) == OBJ_LAZY) .and. &
              (is_structural_kind(gc_kind(b)) .or. gc_kind(b) == OBJ_LAZY)) .or. &
             (gc_kind(a) == OBJ_INST .and. gc_kind(b) == OBJ_INST))) then
          call gc_hold_begin()
          eq = obj_coll_equal(a, b)
          call gc_hold_end()
       else
          eq = (a%ref == b%ref)
       end if
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
    ! temporaries for the deferred-length calls below (share.clj)
    character(len=:), allocatable :: dlt_1, dlt_2
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
    ! Clojure's hasheq for each (Util.hasheq, Numbers.hasheq, Symbol,
    ! Keyword, Ratio, BigInt, BigDecimal): see "Clojure's hashes" below.
    case (GCT_INT)
       h = m3_hash_long(v%ival)
    case (GCT_CHAR)
       h = int(v%ival)                  ! Character.hashCode
    case (GCT_REAL)
       h = double_hasheq(gc_rval(v))
    case (GCT_RATIO)
       h = ieor(big_hash_i64(gc_numerator(v)), big_hash_i64(gc_denominator(v)))
    case (GCT_BIGRATIO)
       ! one form per value (rat_make), so its text decides
       block
          call gc_ref_text(v%ref, s=dlt_1)
          h = big_hash_text(dlt_1)
       end block
    case (GCT_BIG)
       ! the value it equals when it fits a long, as BigInt.hasheq
       block
          call gc_ref_text(v%ref, s=dlt_1)
          if (big_fits_i64(dlt_1)) then
             h = m3_hash_long(big_to_i64(dlt_1))
          else
             h = big_hash_text(dlt_1)
          end if
       end block
    case (GCT_DEC)
       block
          call gc_ref_text(v%ref, s=dlt_1)
          h = dec_hasheq(dlt_1)   ! stripped inside
       end block
    case (GCT_STR)
       block
          call gc_ref_text(v%ref, s=dlt_1)
          h = m3_hash_int(string_hash_code(dlt_1))
       end block
    case (GCT_SYM)
       block
          call gc_ref_text(v%ref, s=dlt_1)
          h = sym_hasheq(dlt_1)
       end block
    case (GCT_KEY)
       block
          call gc_ref_text(v%ref, s=dlt_1)
          h = wrap32(int(sym_hasheq(dlt_1), 8) - 1640531527_8)   ! + 0x9e3779b9
       end block
    case (GCT_CLASS)
       block
          call gc_ref_text(v%ref, s=dlt_1)
          h = mix32(ieor(mix32(fnv1a(dlt_1)), tag_salt(v%tag)))
       end block
    case default
       ! ...and hashing has to follow equality exactly, or a trie
       ! stores the same key twice and loses lookups.
       ! an instance too: a RECORD hashes by value (Eval's gce_coll_hash),
       ! anything else by identity there
       ! a lazy seq too, realised (Eval's gce_coll_hash, under the hold)
       if (associated(obj_coll_hash) .and. (is_structural_kind(gc_kind(v)) .or. gc_kind(v) == OBJ_INST &
            .or. gc_kind(v) == OBJ_LAZY)) then
          call gc_hold_begin()
          h = obj_coll_hash(v)
          call gc_hold_end()
       else
          h = mix32(ieor(mix32(v%ref), tag_salt(v%tag)))
       end if
    end select
  end function gc_hash

  ! A tag, spread across the word before it is mixed in. The
  ! tags are 0..10; XORing one straight onto a value disturbs
  ! only its bottom four bits, which is not enough to separate
  ! two kinds holding the same bits.
  ! A 32-bit multiply WRAPS here, and saying so is not pedantry: a
  ! signed overflow is undefined in Fortran, and gfortran folded
  ! (tag + 1) * C at compile time for a constant tag and computed it
  ! at run time for a variable one -- with different results. The
  ! symptom was (hash 1N) /= (hash 1) from two calls running the same
  ! formula. Every mixing step below goes through here instead.
  pure function wrap32(p) result(s)
    integer(kind=8), intent(in) :: p
    integer :: s
    integer(kind=8) :: low
    low = iand(p, 4294967295_8)
    if (low >= 2147483648_8) low = low - 4294967296_8
    s = int(low, kind=4)
  end function wrap32

  pure function tag_salt(tag) result(s)
    integer, intent(in) :: tag
    integer :: s
    s = wrap32(int(tag + 1, 8) * (-1640531527_8))   ! the golden-ratio constant
  end function tag_salt

  pure function mix32(x) result(h)
    integer, intent(in) :: x
    integer :: h
    h = x
    h = ieor(h, ishft(h, -16))
    h = wrap32(int(h, 8) * (-2048144789_8)) ! 0x85ebca6b as signed 32-bit
    h = ieor(h, ishft(h, -13))
    h = wrap32(int(h, 8) * (-1028477387_8)) ! 0xc2b2ae35 as signed 32-bit
    h = ieor(h, ishft(h, -16))
  end function mix32


  ! ---- Clojure's hashes: Murmur3.clj and Util.hasheq -----------------
  !
  ! (hash x) and every hash map's iteration order come from these, so
  ! they are Clojure's own, bit for bit, where they were a mix of our
  ! own before: a set or a map past 8 entries iterated in another
  ! order than clj's, and (hash "a") answered another number. clj's
  ! int arithmetic wraps; every step here goes through wrap32 because
  ! a signed overflow in Fortran is undefined.

  pure function m3_mixk1(k0) result(k)
    integer, intent(in) :: k0
    integer :: k
    k = wrap32(int(k0, 8) * (-862048943_8))    ! 0xcc9e2d51
    k = ishftc(k, 15)
    k = wrap32(int(k, 8) * 461845907_8)        ! 0x1b873593
  end function m3_mixk1

  pure function m3_mixh1(h0, k1) result(h)
    integer, intent(in) :: h0, k1
    integer :: h
    h = ieor(h0, k1)
    h = ishftc(h, 13)
    h = wrap32(int(h, 8) * 5_8 - 430675100_8)  ! + 0xe6546b64
  end function m3_mixh1

  pure function m3_fmix(h0, length) result(h)
    integer, intent(in) :: h0, length
    integer :: h
    h = ieor(h0, length)
    h = ieor(h, ishft(h, -16))
    h = wrap32(int(h, 8) * (-2048144789_8))    ! 0x85ebca6b
    h = ieor(h, ishft(h, -13))
    h = wrap32(int(h, 8) * (-1028477387_8))    ! 0xc2b2ae35
    h = ieor(h, ishft(h, -16))
  end function m3_fmix

  pure function m3_hash_int(i) result(h)
    integer, intent(in) :: i
    integer :: h
    h = 0
    if (i /= 0) h = m3_fmix(m3_mixh1(0, m3_mixk1(i)), 4)
  end function m3_hash_int

  pure function m3_hash_long(x) result(h)
    integer(kind=8), intent(in) :: x
    integer :: h
    h = 0
    if (x == 0) return
    h = m3_mixh1(0, m3_mixk1(wrap32(x)))
    h = m3_mixh1(h, m3_mixk1(wrap32(ishft(x, -32))))
    h = m3_fmix(h, 8)
  end function m3_hash_long

  ! Murmur3.mixCollHash: the fold of an ordered or unordered collection
  ! and its count, finished
  pure function m3_mix_coll(hash, count) result(h)
    integer, intent(in) :: hash, count
    integer :: h
    h = m3_fmix(m3_mixh1(0, m3_mixk1(hash)), count)
  end function m3_mix_coll

  ! One step of hashOrdered's fold, 31 * h + x, wrapped
  pure function m3_ordered_step(h, x) result(r)
    integer, intent(in) :: h, x
    integer :: r
    r = wrap32(31_8 * int(h, 8) + int(x, 8))
  end function m3_ordered_step

  pure function m3_add(h, x) result(r)
    integer, intent(in) :: h, x
    integer :: r
    r = wrap32(int(h, 8) + int(x, 8))
  end function m3_add

  ! A string as clj holds it: UTF-16 code units
  subroutine gc_utf16(t, u, n)
    character(len=*), intent(in) :: t
    integer, allocatable, intent(out) :: u(:)
    integer, intent(out) :: n
    integer :: p, cp, nb
    allocate(u(2 * len(t) + 1))
    n = 0
    p = 1
    do while (p <= len(t))
       if (ichar(t(p:p)) >= 128 .and. ichar(t(p:p)) < 192) then
          p = p + 1
          cycle
       end if
       call u8_dec(t, p, cp, nb)
       if (cp >= 65536) then
          u(n + 1) = 55296 + (cp - 65536) / 1024
          u(n + 2) = 56320 + mod(cp - 65536, 1024)
          n = n + 2
       else
          n = n + 1
          u(n) = cp
       end if
       p = p + 1
    end do
  end subroutine gc_utf16

  ! String.hashCode
  function string_hash_code(t) result(h)
    character(len=*), intent(in) :: t
    integer :: h, n, i
    integer, allocatable :: u(:)
    call gc_utf16(t, u, n)
    h = 0
    do i = 1, n
       h = m3_ordered_step(h, u(i))
    end do
  end function string_hash_code

  ! Murmur3.hashUnencodedChars
  function m3_hash_chars(t) result(h)
    character(len=*), intent(in) :: t
    integer :: h, n, i
    integer, allocatable :: u(:)
    call gc_utf16(t, u, n)
    h = 0
    do i = 2, n, 2
       h = m3_mixh1(h, m3_mixk1(wrap32(int(u(i - 1), 8) + int(u(i), 8) * 65536_8)))
    end do
    if (mod(n, 2) == 1) h = ieor(h, m3_mixk1(u(n)))
    h = m3_fmix(h, 2 * n)
  end function m3_hash_chars

  ! Util.hashCombine
  pure function hash_combine(seed, hash) result(s)
    integer, intent(in) :: seed, hash
    integer :: s
    s = ieor(seed, wrap32(int(hash, 8) - 1640531527_8 + int(wrap32(int(seed, 8) * 64_8), 8) &
         + int(shifta(seed, 2), 8)))
  end function hash_combine

  ! Symbol.hasheq over its text: the name by Murmur3, the namespace by
  ! String.hashCode
  ! The hash of the symbol -- or, keyword true, the keyword -- whose
  ! name is t, computed from the text with nothing allocated: a
  ! record's field names hashed as the keys (:a) of its map view.
  function gc_text_hasheq(t, keyword) result(h)
    character(len=*), intent(in) :: t
    logical, intent(in) :: keyword
    integer :: h
    h = sym_hasheq(t)
    if (keyword) h = wrap32(int(h, 8) - 1640531527_8)   ! + 0x9e3779b9, as gc_hash
  end function gc_text_hasheq

  function sym_hasheq(t) result(h)
    character(len=*), intent(in) :: t
    integer :: h, sl
    sl = index(t, "/")
    if (len(t) > 1 .and. sl > 1) then
       h = hash_combine(m3_hash_chars(t(sl + 1:)), string_hash_code(t(1:sl - 1)))
    else
       h = hash_combine(m3_hash_chars(t), 0)
    end if
  end function sym_hasheq

  ! BigInteger.hashCode of a 64-bit value: its magnitude's 32-bit words,
  ! high first, times its sign
  pure function big_hash_i64(v) result(h)
    integer(kind=8), intent(in) :: v
    integer :: h
    integer(kind=8) :: hi, lo
    if (v == 0) then
       h = 0
       return
    end if
    if (v == -huge(v) - 1) then
       hi = 2147483648_8; lo = 0     ! 2^63: its magnitude overflows a long
    else
       hi = ishft(abs(v), -32); lo = iand(abs(v), 4294967295_8)
    end if
    h = 0
    if (hi /= 0) h = wrap32(31_8 * int(h, 8) + hi)
    h = wrap32(31_8 * int(h, 8) + lo)
    if (v < 0) h = wrap32(-int(h, 8))
  end function big_hash_i64

  ! BigInteger.hashCode of a decimal integer of any size
  function big_hash_text(t0) result(h)
    character(len=*), intent(in) :: t0
    integer :: h, nw, i
    character(len=:), allocatable :: t, q, r
    integer(kind=8) :: w(64)
    logical :: neg
    neg = (len(t0) > 0 .and. t0(1:1) == "-")
    if (neg) then
       t = t0(2:)
    else
       t = t0
    end if
    nw = 0
    do while (t /= "0" .and. len(t) > 0 .and. nw < 64)
       call big_divmod(t, "4294967296", q, r)
       nw = nw + 1
       w(nw) = big_to_i64(r)
       t = q
    end do
    h = 0
    do i = nw, 1, -1
       h = wrap32(31_8 * int(h, 8) + w(i))
    end do
    if (neg) h = wrap32(-int(h, 8))
  end function big_hash_text

  ! BigDecimal.hashCode after stripTrailingZeros: 31 * the unscaled
  ! value's hash + the scale, over BigDec's "unscaled|scale"; zero is 0
  function dec_hasheq(t0) result(h)
    character(len=*), intent(in) :: t0
    integer :: h, bar, scale, i
    logical :: neg
    character(len=:), allocatable :: t
    call dec_strip(t0, o=t)
    bar = index(t, "|")
    h = 0
    if (bar < 2) return
    if (t(1:bar - 1) == "0" .or. t(1:bar - 1) == "-0") return
    ! the scale by hand: an internal read takes libgfortran's unit lock
    scale = 0
    neg = .false.
    do i = bar + 1, len(t)
       if (t(i:i) == "-") then
          neg = .true.
       else if (t(i:i) >= "0" .and. t(i:i) <= "9") then
          scale = scale * 10 + (ichar(t(i:i)) - ichar("0"))
       end if
    end do
    if (neg) scale = -scale
    ! and past the point, as stripTrailingZeros goes: 100 is 1E+2
    t = t(1:bar - 1)
    do while (len(t) > 1 .and. t(len(t):len(t)) == "0")
       t = t(1:len(t) - 1)
       scale = scale - 1
    end do
    bar = len(t) + 1
    h = wrap32(31_8 * int(big_hash_text(t(1:bar - 1)), 8) + int(scale, 8))
  end function dec_hasheq

  ! Double.hashCode, with -0.0 as 0.0 (Numbers.hasheq)
  pure function double_hasheq(d) result(h)
    real(kind=8), intent(in) :: d
    integer :: h
    integer(kind=8) :: bits
    if (d == 0.0d0) then
       h = 0
       return
    end if
    if (d /= d) then
       bits = 9221120237041090560_8   ! doubleToLongBits' one NaN
    else
       bits = transfer(d, bits)
    end if
    h = wrap32(ieor(bits, ishft(bits, -32)))
  end function double_hasheq

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
  ! Each has two forms: on this thread's stack, found through the key,
  ! and on a stack the caller already holds -- the evaluator fetches its
  ! own once per procedure (gc_my_stack) rather than once per slot.
  function vs_enter_self(n) result(base)
    integer, intent(in) :: n
    integer :: base
    call gc_ensure_init()
    base = vs_enter_on(my_stack(), n)
  end function vs_enter_self

  function vs_enter_on(s, n) result(base)
    type(gc_stack), pointer, intent(in) :: s
    integer, intent(in) :: n
    integer :: base
    if (s%vs_top + n > size(s%vstack)) &
         error stop "clotran: the value stack is full; CLOTRAN_STACK_SLOTS raises it"
    ! Not cleared here: every slot above the top is already nil -- a new
    ! stack starts nil, growing fills with nil, and vs_leave clears what
    ! it pops. Clearing twice was a fifth of a compiled call (dtrace).
    base = s%vs_top
    s%vs_top = base + n
    if (s%vs_top > s%vs_hi) s%vs_hi = s%vs_top
  end function vs_enter_on

  ! Pops back to base. Clearing on the way out is not tidiness: a stale
  ! value above the top would be traced on the next collection and keep
  ! dead data alive, which is the leak a stack collector is prone to.
  subroutine vs_leave_self(base)
    integer, intent(in) :: base
    call vs_leave_on(my_stack(), base)
  end subroutine vs_leave_self

  subroutine vs_leave_on(s, base)
    type(gc_stack), pointer, intent(in) :: s
    integer, intent(in) :: base
    type(gc_value), pointer, contiguous :: v(:)
    integer :: i
    if (base < 0 .or. base > s%vs_top) return
    ! through a local contiguous pointer: on the component itself every
    ! slot reloaded the stride from the descriptor and multiplied (lldb),
    ! and this is a sixth of a compiled call
    v => s%vstack
    do i = base + 1, s%vs_top
       v(i) = nilv
    end do
    s%vs_top = base
  end subroutine vs_leave_on

  subroutine vs_set_self(slot, v)
    integer, intent(in) :: slot
    type(gc_value), intent(in) :: v
    call vs_set_on(my_stack(), slot, v)
  end subroutine vs_set_self

  subroutine vs_set_on(s, slot, v)
    type(gc_stack), pointer, intent(in) :: s
    integer, intent(in) :: slot
    type(gc_value), intent(in) :: v
    if (slot >= 1 .and. slot <= s%vs_top) s%vstack(slot) = v
  end subroutine vs_set_on

  function vs_get_self(slot) result(v)
    integer, intent(in) :: slot
    type(gc_value) :: v
    v = vs_get_on(my_stack(), slot)
  end function vs_get_self

  function vs_get_on(s, slot) result(v)
    type(gc_stack), pointer, intent(in) :: s
    integer, intent(in) :: slot
    type(gc_value) :: v
    v = nilv
    if (slot >= 1 .and. slot <= s%vs_top) v = s%vstack(slot)
  end function vs_get_on

  function vs_depth_self() result(n)
    integer :: n
    type(gc_stack), pointer :: s
    s => my_stack()
    n = s%vs_top
  end function vs_depth_self

  function vs_depth_on(s) result(n)
    type(gc_stack), pointer, intent(in) :: s
    integer :: n
    n = s%vs_top
  end function vs_depth_on

  ! An integer's decimal text WITHOUT Fortran I/O: an internal write takes
  ! libgfortran's unit-table lock, and every thread formatting a number
  ! queued on it (PLAN.md step 14d: sampled, the lock behind the heap's).
  ! Digits are taken from the value made non-positive, so -huge-1 works.
  pure subroutine gc_int_text(i, s)
    integer(gc_ip), intent(in) :: i
    character(len=:), allocatable, intent(out) :: s
    character(len=20) :: buf
    integer(gc_ip) :: m
    integer :: p
    p = 21
    m = i
    if (m > 0) m = -m
    do
       p = p - 1
       buf(p:p) = achar(iachar('0') - int(mod(m, 10_gc_ip)))
       m = m / 10_gc_ip
       if (m == 0) exit
    end do
    if (i < 0) then
       p = p - 1
       buf(p:p) = '-'
    end if
    s = buf(p:20)
  end subroutine gc_int_text

  ! This thread's binding frame (gc_stack%bindings), and replacing it.
  function gc_bindings_get() result(v)
    type(gc_stack), pointer :: s
    type(gc_value) :: v
    s => my_stack()
    v = gc_root_get(s%bindings)
  end function gc_bindings_get

  subroutine gc_bindings_set(v)
    type(gc_value), intent(in) :: v
    type(gc_stack), pointer :: s
    s => my_stack()
    call gc_global_keep(s%bindings, v)
  end subroutine gc_bindings_set

  ! How many notifies there have been -- read under the state lock, to
  ! tell whether anything was announced between two looks.
  integer function gc_notify_gen()
    gc_notify_gen = notify_gen
  end function gc_notify_gen

  ! THE HOLD. Data-structure code -- an array map's index_of, a trie's
  ! insert, a sorted map's search -- keeps the map it is in, and the key,
  ! in Fortran locals, and roots only what it passes to its own
  ! allocations. When it asks the evaluator about a key -- equality of
  ! two vectors (obj_coll_equal), a key's hash (obj_coll_hash), a
  ! comparator fn -- the evaluator allocates with roots of its own, and a
  ! collection there freed the map being searched: (destructure) read a
  ! nil key out of a map literal under torture, one read in two
  ! (scripts/fuzz-gc). No collection runs while any thread holds;
  ! allocation still does, the pools growing until the hold ends.
  subroutine gc_hold_begin()
    call clotran_gc_hold(1_c_int64_t)
  end subroutine gc_hold_begin

  subroutine gc_hold_end()
    call clotran_gc_hold(-1_c_int64_t)
  end subroutine gc_hold_end

  subroutine gc_state_lock()
    type(gc_stack), pointer :: s
    logical :: ok
    ! before any thread has a stack the process is one thread: no lock
    if (.not. stack_key_made) return
    if (.not. c_associated(th_key_get(stack_key))) return
    s => my_stack()
    if (s%state_depth == 0) then
       ok = th_lock_acquire(state_lk)
       call clotran_seq_begin()   ! lock-free readers retry while it is held
    end if
    s%state_depth = s%state_depth + 1
  end subroutine gc_state_lock

  subroutine gc_state_unlock()
    type(gc_stack), pointer :: s
    logical :: ok
    if (.not. stack_key_made) return
    if (.not. c_associated(th_key_get(stack_key))) return
    s => my_stack()
    s%state_depth = s%state_depth - 1
    if (s%state_depth == 0) then
       call clotran_seq_end()
       ok = th_lock_release(state_lk)
    end if
  end subroutine gc_state_unlock

  ! GROWTH OF A TABLE READ WITHOUT A LOCK -- CompiledFn's procedures,
  ! read on every compiled call; the context table: with every other
  ! running thread parked at a safepoint, so none is mid-read when the
  ! table moves. NEVER under the state lock: a thread blocked on it is
  ! not parked, and the stop would wait for it forever.
  subroutine gc_grow_begin()
    type(gc_stack), pointer :: s
    type(gc_value) :: none(0)
    logical :: e, st
    call heap_enter(none, none, e)
    call world_stop(st)
    s => my_stack()
    s%grow_entered = e
    s%grow_stopped = st
  end subroutine gc_grow_begin

  subroutine gc_grow_end()
    type(gc_stack), pointer :: s
    s => my_stack()
    call world_start(s%grow_stopped)
    call heap_leave(s%grow_entered)
  end subroutine gc_grow_end

  ! A lazy cell's state word (i1) from `from` to `to` in one atomic
  ! step, true when it was `from` (model/lazy-cell.lisp's claim). The
  ! pool does not move under it: it grows only with the world stopped.
  logical function gc_cas_i1(v, from, to)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: from, to
    gc_cas_i1 = .false.
    if (v%tag /= GCT_OBJ) return
    gc_cas_i1 = clotran_cas_i32(c_loc(obj_pool(v%ref)%i1), int(from, c_int32_t), int(to, c_int32_t)) /= 0
  end function gc_cas_i1

  ! a thread waits for a cell another is realising (d 1), or stops (d -1)
  subroutine gc_lazy_wait_add(d)
    integer, intent(in) :: d
    call clotran_lazy_waiters_add(int(d, c_int64_t))
  end subroutine gc_lazy_wait_add

  ! a cell settled or given back: its waiters woken, when there are any
  subroutine gc_lazy_wake()
    if (clotran_lazy_waiters_fenced() > 0) call gc_state_notify()
  end subroutine gc_lazy_wake

  ! A SAFEPOINT that allocates nothing: the interpreter's loop and a
  ! compiled loop's back-edge call it, so a thread computing without
  ! allocating still stops when another must collect. One read of a
  ! volatile flag when nothing is stopping.
  ! Whether a stop is asked for: a caller holding a value outside the
  ! stack roots it before gc_poll only then (exec.inc's run_loop).
  logical function gc_stop_pending()
    gc_stop_pending = stop_world
  end function gc_stop_pending

  subroutine gc_poll()
    type(gc_value) :: none(0)
    logical :: e
    if (.not. stop_world) return
    call heap_enter(none, none, e)
    call heap_leave(e)
  end subroutine gc_poll

  ! WAITING (PLAN.md step 14f). Called holding the state lock once (not
  ! nested): lets it go, steps out of the running mutators -- a stop
  ! must not wait for a thread that is waiting -- and sleeps until a
  ! gc_state_notify, or ms milliseconds (negative: no limit). Holds the
  ! lock again on return. A notify between the caller's last check and
  ! the sleep is not lost: notify_gen, read before letting go, says so.
  ! Callers re-check what they wait for: wake-ups can be spurious.
  subroutine gc_state_wait(ms)
    integer(8), intent(in) :: ms
    type(gc_stack), pointer :: s
    integer :: gen
    logical :: ok
    s => my_stack()
    if (s%state_depth /= 1) error stop "clotran: a wait under a nested state lock"
    gen = notify_gen
    s%state_depth = 0
    ! the sequence counter is even whenever the lock is not held -- a
    ! condition wait lets it go too -- or lock-free readers would spin
    call clotran_seq_end()
    ok = th_lock_release(state_lk)
    call gc_mutator_leave()
    ok = th_lock_acquire(state_lk)
    if (notify_gen == gen) then
       if (ms < 0) then
          ok = th_cond_wait(state_cv, state_lk)
       else
          ok = th_cond_timedwait(state_cv, state_lk, int(ms, kind(0_8)))
       end if
    end if
    ok = th_lock_release(state_lk)
    call gc_mutator_enter()
    ok = th_lock_acquire(state_lk)
    call clotran_seq_begin()
    s%state_depth = 1
  end subroutine gc_state_wait

  ! Something a waiter may be waiting for has happened: wake them all.
  subroutine gc_state_notify()
    logical :: ok
    call gc_state_lock()
    notify_gen = notify_gen + 1
    ok = th_cond_broadcast(state_cv)
    call gc_state_unlock()
  end subroutine gc_state_notify

  ! The next number from a counter other threads also count with.
  integer function gc_next(counter)
    integer, intent(inout) :: counter
    call gc_state_lock()
    counter = counter + 1
    gc_next = counter
    call gc_state_unlock()
  end function gc_next

  ! A root replaced only if it still holds `old` (nil for one never
  ! set): a read-modify-write of a shared table -- the type registry --
  ! that another thread's own may have overtaken.
  logical function gc_root_cas(h, old, x)
    type(gc_root), intent(inout) :: h
    type(gc_value), intent(in) :: old, x
    call gc_state_lock()
    gc_root_cas = gc_identical(gc_root_get(h), old)
    if (gc_root_cas) call gc_global_keep(h, x)
    call gc_state_unlock()
  end function gc_root_cas

  ! Identity, as Eval's same_object: the same object, or the same
  ! immediate (a NaN is itself).
  logical function gc_identical(a, b)
    type(gc_value), intent(in) :: a, b
    gc_identical = a%tag == b%tag .and. a%ref == b%ref
    if (.not. gc_identical) return
    if (a%tag == GCT_REAL) then
       ! by value, as before: 0.0 and -0.0 are one, and a NaN is itself
       gc_identical = gc_rval(a) == gc_rval(b) .or. (gc_rval(a) /= gc_rval(a) .and. gc_rval(b) /= gc_rval(b))
    else
       gc_identical = a%ival == b%ival
    end if
  end function gc_identical

  ! Slot i of a shared mutable object, read whole -- WITHOUT the lock:
  ! a consistent copy under the state lock's sequence counter
  ! (src/c/seqlock.c). The pool it reads moves only with the world
  ! stopped, never under a running reader.
  function gc_cell_get(v, i) result(x)
    type(gc_value), intent(in) :: v
    integer, intent(in) :: i
    type(gc_value), target :: x
    x = nilv
    if (v%tag /= GCT_OBJ .or. i < 1 .or. i > OBJ_SLOTS) return
    if (v%ref < 1 .or. v%ref > size(obj_pool)) return
    if (.not. stack_key_made) then
       x = obj_pool(v%ref)%slot(i)
       return
    end if
    call clotran_seq_read16(c_loc(obj_pool(v%ref)%slot(i)), c_loc(x))
  end function gc_cell_get

  subroutine gc_cell_set(v, i, x)
    type(gc_value), intent(in) :: v, x
    integer, intent(in) :: i
    call gc_state_lock()
    call gc_set_slot(v, i, x)
    call gc_state_unlock()
  end subroutine gc_cell_set

  ! Compare-and-set: x goes in only if slot i still holds `old`.
  logical function gc_cell_cas(v, i, old, x)
    type(gc_value), intent(in) :: v, old, x
    integer, intent(in) :: i
    call gc_state_lock()
    gc_cell_cas = gc_identical(gc_slot(v, i), old)
    if (gc_cell_cas) call gc_set_slot(v, i, x)
    call gc_state_unlock()
  end function gc_cell_cas

  ! A spare frame of n slots, all nil, or nil if there is none.
  function gc_frame_take(s, n) result(v)
    type(gc_stack), pointer, intent(in) :: s
    integer, intent(in) :: n
    type(gc_value) :: v
    v = nilv
    if (n < 1 .or. n > SPARE_SIZES) return
    if (s%nspare(n) == 0) return
    v = s%spare(s%nspare(n), n)
    s%nspare(n) = s%nspare(n) - 1
  end function gc_frame_take

  ! A frame whose call has returned: cleared -- a stale slot would keep
  ! its value alive -- and kept for the next call of its size.
  subroutine gc_frame_give(s, v)
    type(gc_stack), pointer, intent(in) :: s
    type(gc_value), intent(in) :: v
    integer :: n, i
    if (v%tag /= GCT_VEC) return
    n = vec_pool(v%ref)%len
    if (n < 1 .or. n > SPARE_SIZES) return
    if (s%nspare(n) >= SPARE_DEPTH) return
    do i = 0, n - 1
       vec_store(vec_pool(v%ref)%off + i) = nilv
    end do
    s%nspare(n) = s%nspare(n) + 1
    s%spare(s%nspare(n), n) = v
  end subroutine gc_frame_give

  ! This thread's stack, for vs_*_on.
  function gc_my_stack() result(s)
    type(gc_stack), pointer :: s
    call gc_ensure_init()
    s => my_stack()
  end function gc_my_stack

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
    ! under the state lock, as every read is: a root is rewritten while
    ! other threads read it (types_root, tasks_root), and the table
    ! grows with no reader able to be inside it
    call gc_state_lock()
    if (.not. allocated(global_root)) then
       allocate(global_root(8))
       global_root = nilv
    end if
    if (global_count >= size(global_root)) call grow_global_roots()
    global_count = global_count + 1
    global_root(global_count) = v
    idx = global_count
    call gc_state_unlock()
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
    bigger = nilv
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
  ! Registered once at startup by the module that owns out-of-heap
  ! storage. See the finalizer_i interface above.
  subroutine gc_set_finalizer(f, kinds)
    procedure(finalizer_i) :: f
    integer, intent(in) :: kinds(:)
    obj_finalizer => f
    finalized_kind = .false.
    finalized_kind(kinds) = .true.
  end subroutine gc_set_finalizer

  ! Both at once, deliberately: see the note on the interfaces.
  subroutine gc_set_coll_ops(h, e)
    procedure(coll_hash_i) :: h
    procedure(coll_equal_i) :: e
    obj_coll_hash => h
    obj_coll_equal => e
  end subroutine gc_set_coll_ops

  ! Whether a kind is one the hooks handle -- the collections whose
  ! identity is their CONTENTS.
  pure logical function is_structural_kind(k)
    integer, intent(in) :: k
    ! OBJ_LAZY is not here but beside it, in gc_hash and gc_equal: a
    ! lazy seq is REALISED to hash or compare it, which the GC hold makes
    ! safe inside a map insert (DEVIATIONS 35, resolved).
    ! A ChunkedCons IS here: its own chunk is already realised, and the
    ! hook checks whether the rest is before folding (DEVIATIONS 35).
    ! OBJ_HAMT too: a map past 8 entries is one, and hashing it by
    ! identity gave two equal maps two hashes -- a set held both
    is_structural_kind = (k == OBJ_CONS .or. k == OBJ_VECTOR .or. &
         k == OBJ_MAP .or. k == OBJ_HAMT .or. k == OBJ_SET .or. k == OBJ_SEQ .or. k == OBJ_CHUNKSEQ)
  end function is_structural_kind

  subroutine gc_global_keep(h, v)
    type(gc_root), intent(inout) :: h
    type(gc_value), intent(in) :: v
    call gc_state_lock()
    if (h%gen == global_gen .and. h%idx >= 1 .and. h%idx <= global_count) then
       global_root(h%idx) = v
    else
       h%idx = gc_global_new(v)
       h%gen = global_gen
    end if
    call gc_state_unlock()
  end subroutine gc_global_keep

  ! The value in a claimed slot, or nil if the claim is stale.
  function gc_root_get(h) result(v)
    type(gc_root), intent(in) :: h
    type(gc_value) :: v
    v = nilv
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
    call gc_state_lock()
    if (idx >= 1 .and. idx <= global_count) global_root(idx) = v
    call gc_state_unlock()
  end subroutine gc_global_set

  function gc_global_get(idx) result(v)
    integer, intent(in) :: idx
    type(gc_value) :: v
    v = nilv
    call gc_state_lock()
    if (idx >= 1 .and. idx <= global_count) v = global_root(idx)
    call gc_state_unlock()
  end function gc_global_get

  function gc_global_count() result(n)
    integer :: n
    n = global_count
  end function gc_global_count

  ! A collection's marking begins: the stack empty and big enough for every
  ! object and run, the counts zero
  subroutine mark_begin()
    integer(int64) :: n
    n = int(obj_used, int64) + int(vec_used, int64) + 2
    if (allocated(hstate%mtag)) then
       if (size(hstate%mtag, kind=int64) < n) deallocate(hstate%mtag, hstate%mref)
    end if
    if (.not. allocated(hstate%mtag)) allocate(hstate%mtag(0:2 * n - 1), hstate%mref(0:2 * n - 1))
    hstate%err = 0; hstate%msp = 0
    hstate%nobj = 0; hstate%nvec = 0; hstate%nstr = 0; hstate%alive = 0
  end subroutine mark_begin

  ! a reference met: marked, and an object or a run pushed to be scanned
  subroutine push_mark(v)
    type(gc_value), intent(in) :: v
    call hpg_push(hstate, int(v%tag, int64), int(v%ref, int64))
  end subroutine push_mark

  ! everything reachable from what was pushed, marked; the counts added
  subroutine drain_mark_stack()
    call hpg_drain(hstate, huge(0_int64))
    if (hstate%err /= 0) error stop "clotran: the collector's mark stack overflowed"
    gc_marked = gc_marked + hstate%nobj + hstate%nvec + hstate%nstr
    obj_marked = obj_marked + int(hstate%nobj)
    vec_marked = vec_marked + int(hstate%nvec)
    str_marked = str_marked + int(hstate%nstr)
    arena_live = arena_live + int(hstate%alive)
    hstate%nobj = 0; hstate%nvec = 0; hstate%nstr = 0; hstate%alive = 0
  end subroutine drain_mark_stack

  ! ---- the marker's view of the pools (heap_gen.inc's externs) ----
  ! object i's slot k is word 5i+k; a mark is 1 or 0
  pure integer(int64) function hp_otag(j)
    integer(int64), intent(in) :: j
    hp_otag = obj_pool(j / 5)%slot(mod(j, 5_int64) + 1)%tag
  end function hp_otag
  pure integer(int64) function hp_oref(j)
    integer(int64), intent(in) :: j
    hp_oref = obj_pool(j / 5)%slot(mod(j, 5_int64) + 1)%ref
  end function hp_oref
  pure integer(int64) function hp_n_oslot()
    hp_n_oslot = 5_int64 * (size(obj_pool, kind=int64) + 1)
  end function hp_n_oslot
  pure integer(int64) function hp_omark(i)
    integer(int64), intent(in) :: i
    hp_omark = merge(1_int64, 0_int64, obj_mark(i))
  end function hp_omark
  subroutine hp_set_omark(i, x)
    integer(int64), intent(in) :: i, x
    obj_mark(i) = x /= 0
  end subroutine hp_set_omark
  ! the pool's slots and slot 0, as every array the model reads of it
  pure integer(int64) function hp_n_obj()
    hp_n_obj = size(obj_pool, kind=int64) + 1
  end function hp_n_obj
  integer(int64) function hp_voff(i)
    integer(int64), intent(in) :: i
    hp_voff = vec_pool(i)%off
  end function hp_voff
  pure integer(int64) function hp_vlen(i)
    integer(int64), intent(in) :: i
    hp_vlen = vec_pool(i)%len
  end function hp_vlen
  pure integer(int64) function hp_vmark(i)
    integer(int64), intent(in) :: i
    hp_vmark = merge(1_int64, 0_int64, vec_mark(i))
  end function hp_vmark
  subroutine hp_set_vmark(i, x)
    integer(int64), intent(in) :: i, x
    vec_mark(i) = x /= 0
  end subroutine hp_set_vmark
  pure integer(int64) function hp_n_vec()
    hp_n_vec = size(vec_pool, kind=int64) + 1
  end function hp_n_vec
  integer(int64) function hp_atag(j)
    integer(int64), intent(in) :: j
    hp_atag = vec_store(j)%tag
  end function hp_atag
  integer(int64) function hp_aref(j)
    integer(int64), intent(in) :: j
    hp_aref = vec_store(j)%ref
  end function hp_aref
  integer(int64) function hp_n_arena()
    hp_n_arena = size(vec_store, kind=int64) + 1
  end function hp_n_arena
  pure integer(int64) function hp_smark(i)
    integer(int64), intent(in) :: i
    hp_smark = merge(1_int64, 0_int64, str_mark(i))
  end function hp_smark
  subroutine hp_set_smark(i, x)
    integer(int64), intent(in) :: i, x
    str_mark(i) = x /= 0
  end subroutine hp_set_smark
  pure integer(int64) function hp_n_str()
    hp_n_str = size(str_pool, kind=int64) + 1
  end function hp_n_str

  ! the sweep's view (stage 1b)
  pure integer(int64) function hp_okind(i)
    integer(int64), intent(in) :: i
    hp_okind = obj_pool(i)%kind
  end function hp_okind
  ! THE SEQ OPERATIONS on what is already there (stage 2): first, next,
  ! rest or seq -- builtin id bid -- of nil, a list or a realised lazy cell,
  ! answered by the generated hpg_seq_op (model/heapsq.lisp) as a place:
  ! nil, x itself, or the slot it names, copied whole. False when it needs
  ! the runtime's full way (a cell to force, a seq view, a chunk).
  logical function gc_seq_fast(bid, x, out) result(done)
    integer, intent(in) :: bid
    type(gc_value), intent(in) :: x
    type(gc_value), intent(inout) :: out
    integer(int64) :: a
    a = hpg_seq_op(hstate, int(bid, int64), int(x%tag, int64), int(x%ref, int64))
    done = a /= 0
    select case (a)
    case (0)
    case (1); out = gc_nil()
    case (2); out = x
    case default; out = obj_pool(a / 5)%slot(mod(a, 5_int64) + 1)
    end select
  end function gc_seq_fast

  ! the seq operations' view (stage 2): a list's count, a lazy cell's state
  pure integer(int64) function hp_oi1(i)
    integer(int64), intent(in) :: i
    hp_oi1 = obj_pool(i)%i1
  end function hp_oi1
  subroutine hp_set_okind(i, x)
    integer(int64), intent(in) :: i, x
    obj_pool(i)%kind = int(x)
  end subroutine hp_set_okind
  integer(int64) function hp_ofree(i)
    integer(int64), intent(in) :: i
    hp_ofree = merge(1_int64, 0_int64, obj_free(i))
  end function hp_ofree
  subroutine hp_set_ofree(i, x)
    integer(int64), intent(in) :: i, x
    obj_free(i) = x /= 0
  end subroutine hp_set_ofree
  integer(int64) function hp_onext(i)
    integer(int64), intent(in) :: i
    hp_onext = obj_free_next(i)
  end function hp_onext
  subroutine hp_set_onext(i, x)
    integer(int64), intent(in) :: i, x
    obj_free_next(i) = int(x)
  end subroutine hp_set_onext
  ! the owner told before the slot is reused: a native array's buffer, a
  ! host handle, released exactly once (i2 tells an owner from a slice)
  subroutine hp_finalize(i, x)
    integer(int64), intent(in) :: i, x
    if (x == 0) return
    if (finalized_kind(obj_pool(i)%kind)) then
       if (associated(obj_finalizer)) &
            call obj_finalizer(obj_pool(i)%kind, obj_pool(i)%i1, obj_pool(i)%i2)
    end if
  end subroutine hp_finalize
  integer(int64) function hp_ohead()
    hp_ohead = obj_free_head
  end function hp_ohead
  subroutine hp_set_ohead(x)
    integer(int64), intent(in) :: x
    obj_free_head = int(x)
  end subroutine hp_set_ohead
  subroutine hp_set_voff(i, x)
    integer(int64), intent(in) :: i, x
    vec_pool(i)%off = int(x)
  end subroutine hp_set_voff
  subroutine hp_set_vlen(i, x)
    integer(int64), intent(in) :: i, x
    vec_pool(i)%len = int(x)
  end subroutine hp_set_vlen
  integer(int64) function hp_vfree(i)
    integer(int64), intent(in) :: i
    hp_vfree = merge(1_int64, 0_int64, vec_free(i))
  end function hp_vfree
  subroutine hp_set_vfree(i, x)
    integer(int64), intent(in) :: i, x
    vec_free(i) = x /= 0
  end subroutine hp_set_vfree
  integer(int64) function hp_vnext(i)
    integer(int64), intent(in) :: i
    hp_vnext = vec_free_next(i)
  end function hp_vnext
  subroutine hp_set_vnext(i, x)
    integer(int64), intent(in) :: i, x
    vec_free_next(i) = int(x)
  end subroutine hp_set_vnext
  integer(int64) function hp_vhead()
    hp_vhead = vec_free_head
  end function hp_vhead
  subroutine hp_set_vhead(x)
    integer(int64), intent(in) :: x
    vec_free_head = int(x)
  end subroutine hp_set_vhead
  subroutine hp_set_atag(j, x)
    integer(int64), intent(in) :: j, x
    vec_store(j)%tag = int(x)
  end subroutine hp_set_atag
  subroutine hp_set_aref(j, x)
    integer(int64), intent(in) :: j, x
    vec_store(j)%ref = int(x)
  end subroutine hp_set_aref
  integer(int64) function hp_aival(j)
    integer(int64), intent(in) :: j
    hp_aival = vec_store(j)%ival
  end function hp_aival
  subroutine hp_set_aival(j, x)
    integer(int64), intent(in) :: j, x
    vec_store(j)%ival = x
  end subroutine hp_set_aival
  integer(int64) function hp_chead(c)
    integer(int64), intent(in) :: c
    hp_chead = class_head(c)
  end function hp_chead
  subroutine hp_set_chead(c, x)
    integer(int64), intent(in) :: c, x
    class_head(c) = int(x)
  end subroutine hp_set_chead
  integer(int64) function hp_n_chead()
    hp_n_chead = VCLASSES + 1
  end function hp_n_chead
  integer(int64) function hp_sfree(i)
    integer(int64), intent(in) :: i
    hp_sfree = merge(1_int64, 0_int64, str_free(i))
  end function hp_sfree
  subroutine hp_set_sfree(i, x)
    integer(int64), intent(in) :: i, x
    str_free(i) = x /= 0
  end subroutine hp_set_sfree
  integer(int64) function hp_snext(i)
    integer(int64), intent(in) :: i
    hp_snext = str_free_next(i)
  end function hp_snext
  subroutine hp_set_snext(i, x)
    integer(int64), intent(in) :: i, x
    str_free_next(i) = int(x)
  end subroutine hp_set_snext
  integer(int64) function hp_shead()
    hp_shead = str_free_head
  end function hp_shead
  subroutine hp_set_shead(x)
    integer(int64), intent(in) :: x
    str_free_head = int(x)
  end subroutine hp_set_shead
  ! allocation's view (stage 1b): the pool's used end and size, and the
  ! calling thread's batch
  integer(int64) function hp_oused()
    hp_oused = obj_used
  end function hp_oused
  subroutine hp_set_oused(x)
    integer(int64), intent(in) :: x
    obj_used = int(x)
  end subroutine hp_set_oused
  integer(int64) function hp_ocap()
    hp_ocap = size(obj_pool, kind=int64)
  end function hp_ocap
  integer(int64) function hp_nob()
    type(gc_stack), pointer :: s
    s => my_stack()
    hp_nob = s%n_obj_b
  end function hp_nob
  subroutine hp_set_nob(x)
    integer(int64), intent(in) :: x
    type(gc_stack), pointer :: s
    s => my_stack()
    s%n_obj_b = int(x)
  end subroutine hp_set_nob
  integer(int64) function hp_ob(k)
    integer(int64), intent(in) :: k
    type(gc_stack), pointer :: s
    s => my_stack()
    hp_ob = s%obj_b(k)
  end function hp_ob
  subroutine hp_set_ob(k, x)
    integer(int64), intent(in) :: k, x
    type(gc_stack), pointer :: s
    s => my_stack()
    s%obj_b(k) = int(x)
  end subroutine hp_set_ob
  integer(int64) function hp_n_ob()
    hp_n_ob = ALLOC_BATCH + 1
  end function hp_n_ob
  ! the arena's allocation (stage 1b): its used end and size, its counts,
  ! and the calling thread's batches of runs, class c's k-th at (c-1)*64 + k
  integer(int64) function hp_aused()
    hp_aused = store_used
  end function hp_aused
  subroutine hp_set_aused(x)
    integer(int64), intent(in) :: x
    store_used = int(x)
  end subroutine hp_set_aused
  integer(int64) function hp_acap()
    hp_acap = size(vec_store, kind=int64)
  end function hp_acap
  integer(int64) function hp_areu()
    hp_areu = arena_reused
  end function hp_areu
  subroutine hp_set_areu(x)
    integer(int64), intent(in) :: x
    arena_reused = x
  end subroutine hp_set_areu
  integer(int64) function hp_afre()
    hp_afre = arena_fresh
  end function hp_afre
  subroutine hp_set_afre(x)
    integer(int64), intent(in) :: x
    arena_fresh = x
  end subroutine hp_set_afre
  integer(int64) function hp_asince()
    hp_asince = arena_alloc_since
  end function hp_asince
  subroutine hp_set_asince(x)
    integer(int64), intent(in) :: x
    arena_alloc_since = int(x)
  end subroutine hp_set_asince
  integer(int64) function hp_rb(j)
    integer(int64), intent(in) :: j
    type(gc_stack), pointer :: s
    s => my_stack()
    hp_rb = s%run_b(int(mod(j - 1, int(RUN_BATCH, int64))) + 1, int((j - 1) / RUN_BATCH) + 1)
  end function hp_rb
  subroutine hp_set_rb(j, x)
    integer(int64), intent(in) :: j, x
    type(gc_stack), pointer :: s
    s => my_stack()
    s%run_b(int(mod(j - 1, int(RUN_BATCH, int64))) + 1, int((j - 1) / RUN_BATCH) + 1) = int(x)
  end subroutine hp_set_rb
  integer(int64) function hp_n_rb()
    hp_n_rb = int(RUN_BATCH, int64) * RUN_CLASSES + 1
  end function hp_n_rb
  integer(int64) function hp_nrb(c)
    integer(int64), intent(in) :: c
    type(gc_stack), pointer :: s
    s => my_stack()
    hp_nrb = s%n_run_b(c)
  end function hp_nrb
  subroutine hp_set_nrb(c, x)
    integer(int64), intent(in) :: c, x
    type(gc_stack), pointer :: s
    s => my_stack()
    s%n_run_b(c) = int(x)
  end subroutine hp_set_nrb
  integer(int64) function hp_n_nrb()
    hp_n_nrb = RUN_CLASSES + 1
  end function hp_n_nrb
  integer(int64) function hp_vused()
    hp_vused = vec_used
  end function hp_vused
  subroutine hp_set_vused(x)
    integer(int64), intent(in) :: x
    vec_used = int(x)
  end subroutine hp_set_vused
  integer(int64) function hp_vcap()
    hp_vcap = size(vec_pool, kind=int64)
  end function hp_vcap
  integer(int64) function hp_nvb()
    type(gc_stack), pointer :: s
    s => my_stack()
    hp_nvb = s%n_vec_b
  end function hp_nvb
  subroutine hp_set_nvb(x)
    integer(int64), intent(in) :: x
    type(gc_stack), pointer :: s
    s => my_stack()
    s%n_vec_b = int(x)
  end subroutine hp_set_nvb
  integer(int64) function hp_vb(k)
    integer(int64), intent(in) :: k
    type(gc_stack), pointer :: s
    s => my_stack()
    hp_vb = s%vec_b(k)
  end function hp_vb
  subroutine hp_set_vb(k, x)
    integer(int64), intent(in) :: k, x
    type(gc_stack), pointer :: s
    s => my_stack()
    s%vec_b(k) = int(x)
  end subroutine hp_set_vb
  integer(int64) function hp_sused()
    hp_sused = str_used
  end function hp_sused
  subroutine hp_set_sused(x)
    integer(int64), intent(in) :: x
    str_used = int(x)
  end subroutine hp_set_sused
  integer(int64) function hp_scap()
    hp_scap = size(str_pool, kind=int64)
  end function hp_scap
  integer(int64) function hp_nsb()
    type(gc_stack), pointer :: s
    s => my_stack()
    hp_nsb = s%n_str_b
  end function hp_nsb
  subroutine hp_set_nsb(x)
    integer(int64), intent(in) :: x
    type(gc_stack), pointer :: s
    s => my_stack()
    s%n_str_b = int(x)
  end subroutine hp_set_nsb
  integer(int64) function hp_sb(k)
    integer(int64), intent(in) :: k
    type(gc_stack), pointer :: s
    s => my_stack()
    hp_sb = s%str_b(k)
  end function hp_sb
  subroutine hp_set_sb(k, x)
    integer(int64), intent(in) :: k, x
    type(gc_stack), pointer :: s
    s => my_stack()
    s%str_b(k) = int(x)
  end subroutine hp_set_sb

  ! a text's storage released: the one place it belongs, run once per slot
  subroutine hp_release_str(i, x)
    integer(int64), intent(in) :: i, x
    if (x == 0) return
    if (allocated(str_pool(i)%text)) deallocate(str_pool(i)%text)
    if (allocated(str_pool(i)%ck)) deallocate(str_pool(i)%ck)
  end subroutine hp_release_str

  include "gen/heap_gen.inc"

  ! A per-slot free FLAG, not a scan of the free list: scanning made
  ! sweep O(free^2), quadratic in exactly the case that matters -- a
  ! heap that is mostly garbage.
  ! THE SWEEP (generated: model/heapsw.lisp, heapsw-proof's theorems): every
  ! slot neither marked nor free, freed
  subroutine sweep()
    call sweep_counts_take()
    call hpg_sweep_objs(hstate, 1_int64, int(obj_used, int64))
    call hpg_sweep_vecs(hstate, 1_int64, int(vec_used, int64))
    call hpg_sweep_strs(hstate, 1_int64, int(str_used, int64))
    obj_swept = 0; vec_swept = 0; str_swept = 0
    call sweep_counts_take()
  end subroutine sweep

  subroutine sweep_counts_zero()
    hstate%nswo = 0; hstate%nswv = 0; hstate%nsws = 0; hstate%afree = 0
  end subroutine sweep_counts_zero

  ! the generated frees' counts into GC's
  subroutine sweep_counts_take()
    obj_swept = obj_swept + int(hstate%nswo)
    vec_swept = vec_swept + int(hstate%nswv)
    str_swept = str_swept + int(hstate%nsws)
    obj_live = obj_live - int(hstate%nswo)
    vec_live = vec_live - int(hstate%nswv)
    str_live = str_live - int(hstate%nsws)
    arena_live_now = arena_live_now - int(hstate%afree)
    gc_frees = gc_frees + int(hstate%nswo + hstate%nswv + hstate%nsws)
    call sweep_counts_zero()
  end subroutine sweep_counts_take

  ! one slot freed, as a young collection frees its dead; the counts are
  ! taken where they are read (sweep_counts_take): the end of
  ! finish_pending, before hand_off_young, the end of the sweep
  subroutine free_obj(i)
    integer, intent(in) :: i
    call hpg_free_obj(hstate, int(i, int64))
  end subroutine free_obj

  subroutine free_vec(i)
    integer, intent(in) :: i
    call hpg_free_vec(hstate, int(i, int64))
  end subroutine free_vec

  subroutine free_str(i)
    integer, intent(in) :: i
    call hpg_free_str(hstate, int(i, int64))
  end subroutine free_str

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
  subroutine gc_check_heap(problem)
    character(len=:), allocatable, intent(out) :: problem
    integer :: i, j, n, k
    type(gc_stack), pointer :: s
    character(len=:), allocatable :: p
    problem = ""
    ! vs_enter hands slots out without clearing them, trusting that
    ! everything above a stack's top is nil
    do i = 1, n_stacks
       if (.not. associated(stacks(i)%s)) cycle
       s => stacks(i)%s
       if (any(s%vstack(s%vs_top + 1:s%vs_hi)%tag /= GCT_NIL)) then
          problem = "a value above a stack's top, which vs_enter would hand out as nil"
          return
       end if
    end do
    ! The dead waiting in pending lists are unswept on purpose: what THEY
    ! point at may already be freed, so they are not checked. But a live
    ! object pointing AT one is as wrong as pointing at a freed one --
    ! the owning thread will free it under it (pend_refill) -- and
    ! bad_ref reports that too, through these masks.
    allocate(chk_dead_o(obj_used), chk_dead_v(vec_used), chk_dead_s(str_used))
    chk_dead_o = .false.; chk_dead_v = .false.; chk_dead_s = .false.
    do i = 1, n_stacks
       if (.not. associated(stacks(i)%s)) cycle
       s => stacks(i)%s
       do k = s%cp_obj + 1, s%np_obj
          if (.not. (obj_mark(s%p_obj(k)) .or. obj_free(s%p_obj(k)) .or. obj_aged(s%p_obj(k)))) chk_dead_o(s%p_obj(k)) = .true.
       end do
       do k = 1, s%n_defer
          chk_dead_o(s%defer_obj(k)) = .true.
       end do
       do k = s%cp_vec + 1, s%np_vec
          if (.not. (vec_mark(s%p_vec(k)) .or. vec_free(s%p_vec(k)) .or. vec_aged(s%p_vec(k)))) chk_dead_v(s%p_vec(k)) = .true.
       end do
       do k = s%cp_str + 1, s%np_str
          if (.not. (str_mark(s%p_str(k)) .or. str_free(s%p_str(k)))) chk_dead_s(s%p_str(k)) = .true.
       end do
    end do
    outer: block
      do i = 1, obj_used
         if (obj_free(i) .or. chk_dead_o(i)) cycle
         do j = 1, OBJ_SLOTS
            call bad_ref(obj_pool(i)%slot(j), p)
            if (len(p) > 0) then
               block
                 character(len=160) :: w
                 write(w, '(A,I0,A,I0,A,L1,A,I0,A,I0,A,I0,A,L1)') " (object #", i, " kind ", obj_pool(i)%kind, &
                      " marked ", obj_mark(i), " slot ", j, " -> tag ", obj_pool(i)%slot(j)%tag, " #", &
                      obj_pool(i)%slot(j)%ref, " rem ", obj_rem(i)
                 problem = p // trim(w)
               end block
               exit outer
            end if
         end do
      end do
      do i = 1, vec_used
         if (vec_free(i) .or. chk_dead_v(i)) cycle
         n = vec_pool(i)%len
         do j = 1, n
            call bad_ref(vec_store(vec_pool(i)%off + j - 1), p)
            if (len(p) > 0) then
               block
                 character(len=160) :: w
                 write(w, '(A,I0,A,I0,A,L1,A,I0,A,I0,A,I0,A,L1)') " (vec #", i, " len ", n, &
                      " marked ", vec_mark(i), " at ", j, " -> tag ", vec_store(vec_pool(i)%off + j - 1)%tag, " #", &
                      vec_store(vec_pool(i)%off + j - 1)%ref, " rem ", vec_rem(i)
                 problem = p // trim(w)
               end block
               exit outer
            end if
         end do
      end do
    end block outer
    deallocate(chk_dead_o, chk_dead_v, chk_dead_s)
  end subroutine gc_check_heap

  subroutine bad_ref(v, problem)
    type(gc_value), intent(in) :: v
    character(len=:), allocatable, intent(out) :: problem
    problem = ""
    select case (v%tag)
    case (GCT_OBJ)
       if (v%ref < 1 .or. v%ref > obj_used) then
          problem = "object reference out of range"
       else if (obj_free(v%ref)) then
          problem = "live object references a freed object"
       else if (allocated(chk_dead_o)) then
          if (chk_dead_o(v%ref)) problem = "live object references an object a young collection found dead"
       end if
    case (GCT_VEC)
       if (v%ref < 1 .or. v%ref > vec_used) then
          problem = "vec reference out of range"
       else if (vec_free(v%ref)) then
          problem = "live object references a freed vec"
       else if (allocated(chk_dead_v)) then
          if (chk_dead_v(v%ref)) problem = "live object references a vec a young collection found dead"
       end if
    case (GCT_STR, GCT_SYM, GCT_KEY)
       if (v%ref < 1 .or. v%ref > str_used) then
          problem = "text reference out of range"
       else if (str_free(v%ref)) then
          problem = "live object references freed text"
       else if (allocated(chk_dead_s)) then
          if (chk_dead_s(v%ref)) problem = "live object references text a young collection found dead"
       end if
    end select
  end subroutine bad_ref

  ! --- UTF-8 -----------------------------------------------------
  !
  ! A string is UTF-8 bytes; the language indexes it by CHARACTER
  ! (clj: by UTF-16 unit, the same thing off the astral plane). These
  ! are the two conversions and nothing else: a continuation byte is
  ! 10xxxxxx, so a character starts at every byte that is not one.
  ! Each walk is linear from the front -- ponytail: an index into a
  ! long non-ASCII string is O(n), a table of offsets if that shows.

  pure function u8_lead(c) result(yes)
    character, intent(in) :: c
    logical :: yes
    yes = iand(ichar(c), 192) /= 128
  end function u8_lead

  pure function u8_count(t) result(n)
    character(len=*), intent(in) :: t
    integer :: n, i
    n = 0
    do i = 1, len(t)
       if (u8_lead(t(i:i))) n = n + 1
    end do
  end function u8_count

  ! The 1-based byte position where character i (0-based) starts;
  ! len(t)+1 for i at or past the count.
  pure function u8_off(t, i) result(p)
    character(len=*), intent(in) :: t
    integer, intent(in) :: i
    integer :: p, seen
    seen = -1
    do p = 1, len(t)
       if (u8_lead(t(p:p))) then
          seen = seen + 1
          if (seen == i) return
       end if
    end do
    p = len(t) + 1
  end function u8_off

  ! The index of pool text idx, as it is made (str_node): one pass to
  ! count, and one more to mark every 32nd character when any is not
  ! ASCII. Made with the text, never on first use, so no two threads
  ! ever fill it at once.
  subroutine str_index(idx)
    integer, intent(in) :: idx
    integer :: p, n
    n = u8_count(str_pool(idx)%text)
    str_pool(idx)%ncp = n
    if (allocated(str_pool(idx)%ck)) deallocate(str_pool(idx)%ck)
    if (n == len(str_pool(idx)%text)) return
    allocate(str_pool(idx)%ck(0:(n - 1) / 32))
    n = 0
    do p = 1, len(str_pool(idx)%text)
       if (u8_lead(str_pool(idx)%text(p:p))) then
          if (mod(n, 32) == 0) str_pool(idx)%ck(n / 32) = p
          n = n + 1
       end if
    end do
  end subroutine str_index

  ! The 1-based byte where character i (0-based) of pool text ref
  ! starts, len+1 at or past the end: direct for ASCII, else the mark at
  ! or before it and at most 31 lead bytes on
  function str_byte(ref, i) result(p)
    integer, intent(in) :: ref, i
    integer :: p, k, nb
    nb = len(str_pool(ref)%text)
    if (i >= str_pool(ref)%ncp) then
       p = nb + 1
    else if (str_pool(ref)%ncp == nb) then
       p = i + 1
    else
       p = str_pool(ref)%ck(i / 32)
       k = mod(i, 32)
       do while (k > 0)
          p = p + 1
          if (u8_lead(str_pool(ref)%text(p:p))) k = k - 1
       end do
    end if
  end function str_byte

  ! how many characters pool text ref holds, O(1)
  integer function gc_str_count(ref)
    integer, intent(in) :: ref
    gc_str_count = 0
    if (ref_ok(ref)) gc_str_count = str_pool(ref)%ncp
  end function gc_str_count

  ! the code point of character i (0-based), -1 out of range; read in place
  integer function gc_str_at(ref, i) result(cp)
    integer, intent(in) :: ref, i
    integer :: p, nb
    cp = -1
    if (.not. ref_ok(ref) .or. i < 0) return
    p = str_byte(ref, i)
    if (p <= len(str_pool(ref)%text)) call u8_dec(str_pool(ref)%text, p, cp, nb)
  end function gc_str_at

  ! characters cs (inclusive) to ce (exclusive) as their bytes: only
  ! those bytes copied, the caller checking 0 <= cs <= ce <= count
  subroutine gc_str_slice(ref, cs, ce, s)
    integer, intent(in) :: ref, cs, ce
    character(len=:), allocatable, intent(out) :: s
    s = ""
    if (.not. ref_ok(ref)) return
    s = str_pool(ref)%text(str_byte(ref, cs):str_byte(ref, ce) - 1)
  end subroutine gc_str_slice

  ! The character index (0-based) of byte position p (1-based).
  pure function u8_cpidx(t, p) result(i)
    character(len=*), intent(in) :: t
    integer, intent(in) :: p
    integer :: i
    i = u8_count(t(1:min(p, len(t) + 1) - 1))
  end function u8_cpidx

  ! Characters cs (inclusive) to ce (exclusive), as their bytes.
  pure subroutine u8_slice(t, cs, ce, s)
    character(len=*), intent(in) :: t
    integer, intent(in) :: cs, ce
    character(len=:), allocatable, intent(out) :: s
    s = t(u8_off(t, cs):u8_off(t, ce) - 1)
  end subroutine u8_slice

  ! The code point starting at byte p and how many bytes it took. A
  ! byte that is not valid UTF-8 is its own code point, one byte, so
  ! Latin-1 text read from a file still round-trips.
  pure subroutine u8_dec(t, p, cp, nb)
    character(len=*), intent(in) :: t
    integer, intent(in) :: p
    integer, intent(out) :: cp, nb
    integer :: b, k, c
    b = ichar(t(p:p))
    cp = b
    nb = 1
    if (b < 192) return
    if (b < 224) then
       nb = 2; cp = b - 192
    else if (b < 240) then
       nb = 3; cp = b - 224
    else
       nb = 4; cp = b - 240
    end if
    if (p + nb - 1 > len(t)) then
       cp = b; nb = 1
       return
    end if
    do k = 1, nb - 1
       c = ichar(t(p+k:p+k))
       if (iand(c, 192) /= 128) then
          cp = b; nb = 1
          return
       end if
       cp = cp * 64 + iand(c, 63)
    end do
  end subroutine u8_dec

  ! The code point of character i, or -1 past the end.
  pure function u8_at(t, i) result(cp)
    character(len=*), intent(in) :: t
    integer, intent(in) :: i
    integer :: cp, p, nb
    p = u8_off(t, i)
    cp = -1
    if (p <= len(t)) call u8_dec(t, p, cp, nb)
  end function u8_at

  ! A code point as UTF-8, one to four bytes.
  pure subroutine u8_enc(cp, s)
    integer, intent(in) :: cp
    character(len=:), allocatable, intent(out) :: s
    if (cp < 0) then
       s = "?"
    else if (cp < 128) then
       s = achar(cp)
    else if (cp < 2048) then
       s = achar(192 + cp / 64) // achar(128 + mod(cp, 64))
    else if (cp < 65536) then
       s = achar(224 + cp / 4096) // achar(128 + mod(cp / 64, 64)) // achar(128 + mod(cp, 64))
    else
       s = achar(240 + cp / 262144) // achar(128 + mod(cp / 4096, 64)) // &
            achar(128 + mod(cp / 64, 64)) // achar(128 + mod(cp, 64))
    end if
  end subroutine u8_enc

  ! A character from its code point; gc_char takes one byte.
  function gc_char_cp(cp) result(v)
    integer, intent(in) :: cp
    type(gc_value) :: v
    v%tag = GCT_CHAR
    v%ival = int(cp, gc_ip)
  end function gc_char_cp

end module GC
