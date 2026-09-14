! Core, mutually-recursive type definitions: cons_value (the tagged-union
! value every operation passes around) needs to hold a list/vector, and a
! list cell / vector-trie node needs to hold a cons_value. Fortran can
! only forward-reference a not-yet-defined type within the same module
! (and only via an allocatable/pointer component), so all of it lives
! here together. Operations live in their own files: PersistentList.f90,
! PersistentVector.f90, RT.f90.
module values
  implicit none

  ! Double precision, not the bare default `real`: every real scientific
  ! Fortran library (ChemSol included) works in real(8)/double precision
  ! throughout. A value type built for native interop has to match that
  ! from the start, not bolt it on after silently losing precision.
  integer, parameter :: dp = kind(1.0d0)

  integer, parameter :: TAG_NIL = 0
  integer, parameter :: TAG_BOOL = 1
  integer, parameter :: TAG_INT = 2
  integer, parameter :: TAG_REAL = 3
  integer, parameter :: TAG_STRING = 4
  integer, parameter :: TAG_SYMBOL = 5
  integer, parameter :: TAG_KEYWORD = 6
  integer, parameter :: TAG_LIST = 7
  integer, parameter :: TAG_VECTOR = 8
  integer, parameter :: TAG_HASHMAP = 9
  integer, parameter :: TAG_BUILTIN = 10 ! str_val holds the builtin's name; dispatched by Eval
  integer, parameter :: TAG_FN = 11 ! fn_val holds params/body/captured env; a real closure
  integer, parameter :: TAG_ATOM = 12 ! atom_val is a genuinely mutable box, shared by reference
  integer, parameter :: TAG_SET = 13 ! map_val backs it too -- every element mapped to itself,
                                      ! exactly like real Clojure's PersistentHashSet wraps a map
  integer, parameter :: TAG_VAR = 14 ! clojure.lang.Var -- a mutable, identity-preserving box a
                                      ! namespace interns a name to (see Namespace.f90). Reuses
                                      ! atom_val for the root binding (a Var's root IS "one
                                      ! genuinely mutable slot, shared by reference," exactly
                                      ! atom_ref's own shape) rather than a parallel type; str_val
                                      ! holds the qualified "ns/name" for printing (#'ns/name).
                                      ! Differs from TAG_ATOM only in behavior, not storage: a
                                      ! symbol resolving to a Var auto-derefs transparently
                                      ! (ns_get_own/ns_resolve do this); an atom never does.
  integer, parameter :: TAG_STRING_BUILDER = 15 ! java.lang.StringBuilder -- real core.clj's own
                                      ! multi-arg `str` builds one (`.append`s each arg's own str
                                      ! form, then `.toString`s it). Same "reuse atom_val"
                                      ! pattern as TAG_VAR: the mutable payload is a TAG_STRING
                                      ! cons_value, mutated in place by .append; .toString reads
                                      ! it back out directly (see eval_new/eval_instance_call).
  integer, parameter :: TAG_REDUCED = 17 ! clojure.lang.Reduced -- reduce's early-exit wrapper
                                      ! ((reduced x) says "stop, the answer is x"). Same
                                      ! "reuse atom_val as the box" pattern as TAG_VAR; its
                                      ! whole job is to be distinguishable from a plain
                                      ! value, which is exactly what a tag gives us.
  integer, parameter :: TAG_LAZYSEQ = 16 ! clojure.lang.LazySeq -- a seq whose rest isn't computed
                                      ! until asked for. lazy_val holds the node; see
                                      ! RT.f90's force-then-delegate seq/first/rest and
                                      ! Eval.f90's force_lazy (the thunk has to be CALLED,
                                      ! which only Eval can do -- RT reaches it through a
                                      ! procedure pointer, see rt_set_lazy_forcer).
  integer, parameter :: TAG_CHAR = 18 ! java.lang.Character -- its own type in Clojure, so
                                      ! (= \a "a") is false. The character itself lives in
                                      ! str_val (length 1), so equality and hashing fall out
                                      ! of the existing string handling for free.
  integer, parameter :: TAG_ARRAY = 20 ! a REAL Fortran array -- see native_array_node. Not
                                      ! java.lang.Object[]: emulating the JVM's array here
                                      ! would throw away the one thing this host has that
                                      ! the JVM doesn't, which is that the bytes can be
                                      ! handed straight to a Fortran library.
  integer, parameter :: TAG_MULTIFN = 19 ! clojure.lang.MultiFn -- what defmulti constructs and
                                      ! defmethod mutates. Same "reuse atom_val as the mutable
                                      ! box" pattern as TAG_VAR; the box holds a map of
                                      ! {:dispatch fn :default dv :methods {dv -> fn}}, since a
                                      ! multimethod IS a value plus one genuinely mutable table.

  integer, parameter :: BITS = 5
  integer, parameter :: BRANCH = 32
  integer, parameter :: MASK = 31

  ! Every value in the language. Only the field matching %tag is meaningful.
  type, public :: cons_value
     integer :: tag = TAG_NIL
     integer :: int_val = 0
     real(dp) :: real_val = 0.0_dp
     logical :: bool_val = .false.
     character(len=:), allocatable :: str_val   ! string/symbol/keyword text
     type(cons_ref), allocatable :: list_val
     type(vec_t), allocatable :: vector_val
     type(array_map_t), allocatable :: map_val
     type(closure_t), allocatable :: fn_val
     type(atom_ref), allocatable :: atom_val
     type(lazy_ref), allocatable :: lazy_val
     type(native_array_ref), allocatable :: array_val
     type(meta_ref), allocatable :: meta_val ! (with-meta x m)/(meta x) -- any value, any type
   contains
     final :: cons_value_finalize
  end type cons_value

  ! --- PersistentList backing: a real, refcounted cons cell ---
  type, public :: cons_cell
     integer :: refcount = 0
     type(cons_value) :: car
     type(cons_ref), allocatable :: cdr
     integer :: count = 0
     ! Where this form was READ from: line and column of its opening
     ! paren, plus an index into the reader's file-name table (0 = no
     ! position, e.g. a form built by a macro rather than read).
     !
     ! Three integers on the CELL, deliberately, rather than a metadata
     ! map on every value the way real Clojure does it: a map per form
     ! is an allocation per form across ~11k lines of bootstrap, and
     ! only list forms are ever what an error or a stack frame points
     ! at. (meta form) can synthesise {:line :column :file} from these
     ! on demand, so core.clj's own (meta &form) still works.
     integer :: src_line = 0
     integer :: src_col = 0
     integer :: src_file = 0
     ! Where the form ENDS, so an editor can highlight the exact sexp
     ! rather than a whole line. Line-level positions give a gdb-style
     ! debugger; start+end give a CIDER-style one, and this is far
     ! cheaper to record now than to retrofit.
     integer :: src_end_line = 0
     integer :: src_end_col = 0
  end type cons_cell

  type, public :: cons_ref
     type(cons_cell), pointer :: ptr => null()
   contains
     final :: cons_ref_finalize
  end type cons_ref

  ! --- PersistentVector backing: a 32-way branching trie ---
  type, public :: vec_node
     integer :: refcount = 0
     type(node_ref), allocatable :: children(:)
     type(cons_value), allocatable :: items(:)
  end type vec_node

  type, public :: node_ref
     type(vec_node), pointer :: ptr => null()
   contains
     final :: node_ref_finalize
  end type node_ref

  type, public :: vec_t
     integer :: count = 0
     integer :: shift = 0
     type(node_ref) :: root
  end type vec_t

  ! --- PersistentArrayMap backing: a flat, linear-scan k/v array. Real
  ! Clojure uses this same representation for maps up to 8 entries,
  ! promoting to a real hash trie (PersistentHashMap, see hamt_node
  ! below) beyond that -- confirmed via the real `clojure` CLI: 8
  ! entries stays a PersistentArrayMap, 9 becomes a PersistentHashMap.
  type, public :: array_map_node
     integer :: refcount = 0
     type(cons_value), allocatable :: keys(:)
     type(cons_value), allocatable :: vals(:)
  end type array_map_node

  type, public :: array_map_ref
     type(array_map_node), pointer :: ptr => null()
   contains
     final :: array_map_ref_finalize
  end type array_map_ref

  ! big: unallocated for a small (<=8 entry) map/set, using root above.
  ! Once promoted (see PersistentArrayMap.f90's array_map_assoc), big
  ! holds the real hash trie instead and root goes unused -- one-way,
  ! same as real Clojure (a HashMap never demotes back to an ArrayMap).
  ! Allocatable (not a plain component, unlike root above) only because
  ! hamt_ref is defined below and Fortran can only forward-reference a
  ! not-yet-defined same-module type through an allocatable/pointer
  ! component (see this file's header) -- same reason meta_val/extra
  ! are allocatable elsewhere here.
  ! big_count: only meaningful once big is allocated -- a HAMT has no
  ! O(1) way to report its own size (unlike the array tier's size(keys)
  ! above), so PersistentArrayMap.f90 maintains this directly from
  ! hamt_assoc/hamt_dissoc's is_new/removed flags instead of walking
  ! the whole trie on every count.
  type, public :: array_map_t
     type(array_map_ref) :: root
     type(hamt_ref), allocatable :: big
     integer :: big_count = 0
   contains
     final :: array_map_t_finalize
  end type array_map_t

  ! --- PersistentHashMap backing: a real hash-array-mapped trie (HAMT),
  ! same algorithm as PersistentVector above but branching on hash bits
  ! instead of a sequential index, and each node uses a full 32-slot
  ! array rather than real Clojure's bitmap-compressed sparse array --
  ! same O(log32 n) (effectively O(1), depth <=7 for a 32-bit hash)
  ! asymptotic behavior, just a higher constant memory factor per node.
  ! kind: 0 empty, 1 leaf (key/val meaningful), 2 child (a deeper node,
  ! for keys whose hash bits collided this far down), 3 bucket (a
  ! small linear key/val array, for the rare case of two DIFFERENT
  ! keys sharing every hash bit all the way to depth 7 -- true hash
  ! collision, not just a shared prefix). See PersistentHashMap.f90.
  integer, parameter :: HAMT_EMPTY = 0
  integer, parameter :: HAMT_LEAF = 1
  integer, parameter :: HAMT_CHILD = 2
  integer, parameter :: HAMT_BUCKET = 3

  ! hamt_ref defined first (forward-referencing hamt_node, below, via
  ! its pointer component -- allowed) so hamt_slot can hold a plain,
  ! already-defined hamt_ref for `child` rather than needing another
  ! allocatable-for-forward-reference workaround.
  type, public :: hamt_ref
     type(hamt_node), pointer :: ptr => null()
   contains
     final :: hamt_ref_finalize
  end type hamt_ref

  type, public :: hamt_slot
     integer :: kind = HAMT_EMPTY
     type(cons_value) :: key, val
     type(hamt_ref) :: child
     type(cons_value), allocatable :: bucket_keys(:), bucket_vals(:)
  end type hamt_slot

  ! slots is allocatable, not a fixed-size array, even though every
  ! node always allocates exactly BRANCH of them (see PersistentHashMap
  ! .f90's node_assoc/node_dissoc) -- a fixed-size array of hamt_slot
  ! here crashes only on gfortran (confirmed via the official test
  ! suite's own cross-check run, flang unaffected): its auto-generated
  ! finalization of a self-referential struct (hamt_slot embeds a
  ! hamt_ref pointing back to another hamt_node) mishandles a FIXED
  ! array the way it doesn't for vec_node's own children(:)/items(:),
  ! which are allocatable for exactly this reason already.
  type, public :: hamt_node
     integer :: refcount = 0
     type(hamt_slot), allocatable :: slots(:)
  end type hamt_node

  ! --- Env backing: symbol -> value bindings with an outer chain. Lives
  ! here (not in Env.f90, which holds only the operations) because a
  ! closure (added alongside fn*) needs to capture an env_ref, and
  ! cons_value needs to hold a closure -- the same forward-reference
  ! constraint that keeps every other mutually-recursive type together.
  type :: env_node
     integer :: refcount = 0
     type(array_map_t) :: bindings
     type(env_ref), allocatable :: outer
     ! The namespace a fn* was DEFINED in, set only on a closure's own
     ! frame. A free symbol in a function body resolves there, not in
     ! whatever namespace happens to be current when it is called --
     ! real Clojure resolves symbols at compile time, in the defining
     ! namespace. Carried on the env (not on closure_t) so that a tail
     ! call, which reuses the trampoline instead of returning through
     ! apply_closure, still sees it. See env_defining_ns.
     !
     ! An INDEX into Namespace.f90's registry, not a name: this is read
     ! on every symbol resolution in the program, and looking a
     ! namespace up by name means a linear scan of the registry doing
     ! string comparisons, while allocating a deferred-length string
     ! per env frame walked. Both showed up directly in the bootstrap
     ! profile. 0 means "not a closure frame".
     integer :: ns_index = 0
  end type env_node

  type, public :: env_ref
     type(env_node), pointer :: ptr => null()
   contains
     final :: env_ref_finalize
  end type env_ref

  ! --- Extra arity clauses for a multi-arity fn* (see closure_t
  ! below), boxed behind a pointer for the same reason meta_ref is:
  ! a derived type can't hold an allocatable ARRAY of a type that
  ! (transitively, through closure_t) contains itself either --
  ! same self-referential-allocatable-plus-FINAL gfortran codegen bug
  ! as cons_value/meta_val, confirmed by hitting it here too (crashed
  ! only on gfortran; flang was unaffected). Nothing shares one of
  ! these across closures, so no refcount sharing is actually needed,
  ! but the ref/node shape is what already exists and is proven safe.
  type, public :: arity_clauses_node
     integer :: refcount = 0
     type(cons_value), allocatable :: params(:), bodies(:)
  end type arity_clauses_node

  type, public :: arity_clauses_ref
     type(arity_clauses_node), pointer :: ptr => null()
   contains
     final :: arity_clauses_ref_finalize
  end type arity_clauses_ref

  ! --- closure: params/body captured at (fn* ...) time, plus the env
  ! captured lexically. Defined last (not forward-referenced) since it
  ! embeds cons_value and env_ref directly rather than through a
  ! pointer -- both are already fully defined above by this point.
  ! is_macro: real Clojure hangs macro-ness off the Var's metadata, not
  ! the function value -- a macro-created function is an ordinary IFn.
  ! There IS a real Var now (TAG_VAR, see Namespace.f90), but is_macro
  ! still lives here, as a flag on the closure itself, rather than a
  ! whole parallel TAG_MACRO duplicating TAG_FN's shape everywhere
  ! TAG_FN is handled. Still a simplification (real metadata is
  ! per-Var, so the same fn value could in principle be a macro under
  ! one name and not another; not a scenario anything here creates).
  ! extra: additional arity clauses for a multi-arity fn* (params/body
  ! above are the first clause). Real Clojure's (fn* ([a] ...) ([a b]
  ! ...)) syntax -- dispatched by argument count at call time (see
  ! select_clause in Eval.f90), not rewritten away at parse time, so
  ! this stays the one runtime closure representation for both single-
  ! and multi-arity fns.
  type, public :: closure_t
     type(cons_value) :: params
     type(cons_value) :: body
     type(arity_clauses_ref), allocatable :: extra
     type(env_ref) :: env
     logical :: is_macro = .false.
  end type closure_t

  ! --- Atom backing: one genuinely mutable slot, shared by reference.
  ! Mirrors clojure.lang.Atom. Unlike env, nothing else needs to hold an
  ! atom_ref directly (only ever through a cons_value), so it doesn't
  ! need to be defined this early -- kept next to closure_t anyway, by
  ! the same "defined last, embeds cons_value directly" reasoning.
  type, public :: atom_node
     integer :: refcount = 0
     type(cons_value) :: val
     ! Var dynamic-binding stack (`binding`/^:dynamic) -- unused for a
     ! plain TAG_ATOM, only ever pushed/popped by Eval.f90's
     ! push-thread-bindings/pop-thread-bindings for a TAG_VAR. See
     ! Atom.f90's var_dyn_push/var_dyn_pop/atom_deref.
     ! ponytail: one global stack, not real per-thread storage --
     ! clotran is single-threaded today (see NOTES.md/memory: the
     ! concurrency model is a real, separate feature, likely
     ! Rust-inspired, not a JVM-style thread port). Revisit this field
     ! when that lands -- probably keyed by thread/fiber id then,
     ! rather than one shared stack.
     type(cons_value), allocatable :: dyn_stack(:)
     ! A Var's metadata, held HERE rather than on the cons_value's own
     ! meta_val so that it is shared by reference like the root: every
     ! copy of a Var must see an alter-meta! through any other copy.
     ! defn's :arglists/:doc, ^:private, ^:dynamic and clojure.test's
     ! :test all live here.
     type(cons_value), allocatable :: var_meta
  end type atom_node

  type, public :: atom_ref
     type(atom_node), pointer :: ptr => null()
   contains
     final :: atom_ref_finalize
  end type atom_ref

  ! --- LazySeq backing. Three states, exactly clojure.lang.LazySeq's
  ! own: not yet run (thunk), run and produced a first/rest pair, or
  ! run and produced nothing. Realizing flips the state ONCE and keeps
  ! the result -- that memoization is what makes walking a lazy seq
  ! O(1) per element instead of re-running the generator each step.
  ! tail is a full cons_value (not a cons_ref) so it can itself be
  ! another unrealized LazySeq -- which is the whole point, and the
  ! reason a plain cons_cell can't host a lazy rest.
  integer, parameter, public :: LAZY_ST_PENDING = 0
  integer, parameter, public :: LAZY_ST_CONS = 1
  integer, parameter, public :: LAZY_ST_EMPTY = 2

  type, public :: lazy_node
     integer :: refcount = 0
     integer :: state = LAZY_ST_PENDING
     type(cons_value) :: thunk ! (fn* [] body...) while pending; released once realized
     type(cons_value) :: head
     type(cons_value) :: tail
  end type lazy_node

  type, public :: lazy_ref
     type(lazy_node), pointer :: ptr => null()
   contains
     final :: lazy_ref_finalize
  end type lazy_ref

  ! A real Fortran array, of any kind and any rank.
  !
  ! Storage is ONE rank-1 contiguous buffer plus a shape, not a
  ! rank-N component, because rank is part of a Fortran type
  ! declaration -- a derived type cannot have a component that is
  ! "any rank". Indexing is done here, column-major, which is
  ! Fortran's own layout: the buffer is therefore bit-identical to
  ! what a Fortran routine expects, and passing this to dgemm (or to
  ! ChemSol) is a plain by-reference pass with no copy or marshalling.
  ! That is the entire point.
  !
  ! buf is unlimited polymorphic, so a single type covers real(8),
  ! real(4), integer(4), integer(8), complex, logical, a derived type
  ! -- allocated with an explicit type-spec (allocate(real(8) :: buf(n)))
  ! and read back through select type. Same mechanism native_test
  ! already validates for scalars and structs, just with extents.
  !
  ! lows holds each dimension's LOWER BOUND. Fortran arrays can start
  ! at any index, so a Clojure-facing array simply starts at 0 and an
  ! imported Fortran one keeps whatever bounds it was declared with --
  ! no translation layer, no off-by-one convention to remember.
  type, public :: native_array_node
     integer :: refcount = 0
     character(len=:), allocatable :: elem_kind ! "real8", "int4", ... for printing and dispatch
     integer, allocatable :: extents(:)
     integer, allocatable :: lows(:)
     class(*), allocatable :: buf(:)
  end type native_array_node

  type, public :: native_array_ref
     type(native_array_node), pointer :: ptr => null()
   contains
     final :: native_array_ref_finalize
  end type native_array_ref

  ! --- Metadata backing: (with-meta x m)/(meta x). Same shape as atom
  ! (a refcounted box holding one cons_value) even though nothing here
  ! mutates it -- a cons_value can't hold another cons_value directly as
  ! an allocatable component (self-referential allocatable + FINAL is a
  ! known gfortran codegen bug, confirmed by an isolated repro; flang is
  ! unaffected). Going through a pointer indirection, as every other
  ! recursive structure here already does, sidesteps it for free.
  type, public :: meta_node
     integer :: refcount = 0
     type(cons_value) :: val
  end type meta_node

  type, public :: meta_ref
     type(meta_node), pointer :: ptr => null()
   contains
     final :: meta_ref_finalize
  end type meta_ref

  interface assignment(=)
     module procedure cons_value_assign
     module procedure cons_ref_assign
     module procedure node_ref_assign
     module procedure vec_t_assign
     module procedure array_map_ref_assign
     module procedure array_map_t_assign
     module procedure env_ref_assign
     module procedure closure_t_assign
     module procedure atom_ref_assign
     module procedure lazy_ref_assign
     module procedure native_array_ref_assign
     module procedure meta_ref_assign
     module procedure arity_clauses_ref_assign
     module procedure hamt_ref_assign
     module procedure hamt_slot_assign
  end interface assignment(=)

  ! For test programs to confirm every box is eventually freed.
  integer, public :: cons_cell_total_allocated = 0
  integer, public :: cons_cell_total_freed = 0
  integer, public :: vec_node_total_allocated = 0
  integer, public :: vec_node_total_freed = 0
  integer, public :: array_map_node_total_allocated = 0
  integer, public :: array_map_node_total_freed = 0
  integer, public :: env_total_allocated = 0
  integer, public :: env_total_freed = 0
  integer, public :: atom_node_total_allocated = 0
  integer, public :: atom_node_total_freed = 0
  integer, public :: native_array_node_total_allocated = 0
  integer, public :: native_array_node_total_freed = 0
  integer, public :: lazy_node_total_allocated = 0
  integer, public :: lazy_node_total_freed = 0
  integer, public :: meta_node_total_allocated = 0
  integer, public :: meta_node_total_freed = 0
  integer, public :: arity_clauses_node_total_allocated = 0
  integer, public :: arity_clauses_node_total_freed = 0
  integer, public :: hamt_node_total_allocated = 0
  integer, public :: hamt_node_total_freed = 0

  public :: assignment(=)
  public :: cons_value_release, cons_ref_release, node_ref_release, array_map_ref_release, env_ref_release, &
       atom_ref_release, meta_ref_release, arity_clauses_ref_release, hamt_ref_release, &
       lazy_ref_release
  public :: value_equal

contains

  ! Value equality for map/set keys: same tag and same scalar/text
  ! content. Lists/vectors/maps as keys aren't compared deeply yet --
  ! lives here (not in PersistentArrayMap.f90, where it used to be)
  ! since PersistentHashMap.f90 needs it too, and PersistentArrayMap.f90
  ! now depends on PersistentHashMap.f90 for promotion -- a module
  ! cycle either way it stayed put.
  function value_equal(a, b) result(eq)
    type(cons_value), intent(in) :: a, b
    logical :: eq
    eq = .false.
    if (a%tag /= b%tag) return
    select case (a%tag)
    case (TAG_NIL)
       eq = .true.
    case (TAG_BOOL)
       eq = (a%bool_val .eqv. b%bool_val)
    case (TAG_INT)
       eq = (a%int_val == b%int_val)
    case (TAG_REAL)
       eq = (a%real_val == b%real_val)
    case (TAG_STRING, TAG_SYMBOL, TAG_KEYWORD, TAG_CHAR)
       if (allocated(a%str_val) .and. allocated(b%str_val)) then
          eq = (a%str_val == b%str_val)
       else
          eq = (.not. allocated(a%str_val) .and. .not. allocated(b%str_val))
       end if
    end select
  end function value_equal

  ! ---- cons_value ----

  recursive subroutine cons_value_release(v)
    type(cons_value), intent(inout) :: v
    if (allocated(v%str_val)) deallocate(v%str_val)
    if (allocated(v%list_val)) then
       call cons_ref_release(v%list_val)
       deallocate(v%list_val)
    end if
    if (allocated(v%vector_val)) then
       call node_ref_release(v%vector_val%root)
       deallocate(v%vector_val)
    end if
    if (allocated(v%map_val)) then
       call array_map_t_release(v%map_val)
       deallocate(v%map_val)
    end if
    if (allocated(v%fn_val)) deallocate(v%fn_val) ! cascades: releases params/body/env
    if (allocated(v%atom_val)) then
       call atom_ref_release(v%atom_val)
       deallocate(v%atom_val)
    end if
    if (allocated(v%array_val)) then
       call native_array_ref_release(v%array_val)
       deallocate(v%array_val)
    end if
    if (allocated(v%lazy_val)) then
       call lazy_ref_release(v%lazy_val)
       deallocate(v%lazy_val)
    end if
    if (allocated(v%meta_val)) then
       call meta_ref_release(v%meta_val)
       deallocate(v%meta_val)
    end if
    v%tag = TAG_NIL
  end subroutine cons_value_release

  impure elemental subroutine cons_value_assign(lhs, rhs)
    type(cons_value), intent(inout) :: lhs
    type(cons_value), intent(in) :: rhs
    call cons_value_release(lhs)
    lhs%tag = rhs%tag
    lhs%int_val = rhs%int_val
    lhs%real_val = rhs%real_val
    lhs%bool_val = rhs%bool_val
    if (allocated(rhs%str_val)) lhs%str_val = rhs%str_val
    if (allocated(rhs%list_val)) then
       allocate(lhs%list_val)
       lhs%list_val = rhs%list_val
    end if
    if (allocated(rhs%vector_val)) then
       allocate(lhs%vector_val)
       lhs%vector_val = rhs%vector_val
    end if
    if (allocated(rhs%map_val)) then
       allocate(lhs%map_val)
       lhs%map_val = rhs%map_val
    end if
    if (allocated(rhs%fn_val)) then
       allocate(lhs%fn_val)
       lhs%fn_val = rhs%fn_val
    end if
    if (allocated(rhs%atom_val)) then
       allocate(lhs%atom_val)
       lhs%atom_val = rhs%atom_val
    end if
    if (allocated(rhs%lazy_val)) then
       allocate(lhs%lazy_val)
       lhs%lazy_val = rhs%lazy_val
    end if
    if (allocated(rhs%array_val)) then
       allocate(lhs%array_val)
       lhs%array_val = rhs%array_val
    end if
    if (allocated(rhs%meta_val)) then
       allocate(lhs%meta_val)
       lhs%meta_val = rhs%meta_val
    end if
  end subroutine cons_value_assign

  impure elemental subroutine cons_value_finalize(v)
    type(cons_value), intent(inout) :: v
    call cons_value_release(v)
  end subroutine cons_value_finalize

  ! ---- cons_ref (PersistentList cells) ----

  recursive subroutine cons_ref_release(h)
    type(cons_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       call cons_value_release(h%ptr%car)
       if (allocated(h%ptr%cdr)) call cons_ref_release(h%ptr%cdr)
       deallocate(h%ptr)
       cons_cell_total_freed = cons_cell_total_freed + 1
    end if
    h%ptr => null()
  end subroutine cons_ref_release

  impure elemental subroutine cons_ref_assign(lhs, rhs)
    type(cons_ref), intent(inout) :: lhs
    type(cons_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call cons_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine cons_ref_assign

  impure elemental subroutine cons_ref_finalize(h)
    type(cons_ref), intent(inout) :: h
    call cons_ref_release(h)
  end subroutine cons_ref_finalize

  ! ---- node_ref (PersistentVector trie nodes) ----

  recursive subroutine node_ref_release(h)
    type(node_ref), intent(inout) :: h
    integer :: i
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       if (allocated(h%ptr%children)) then
          do i = 1, size(h%ptr%children)
             call node_ref_release(h%ptr%children(i))
          end do
       end if
       deallocate(h%ptr)
       vec_node_total_freed = vec_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine node_ref_release

  impure elemental subroutine node_ref_assign(lhs, rhs)
    type(node_ref), intent(inout) :: lhs
    type(node_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call node_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine node_ref_assign

  impure elemental subroutine node_ref_finalize(h)
    type(node_ref), intent(inout) :: h
    call node_ref_release(h)
  end subroutine node_ref_finalize

  ! ---- vec_t (embeds a node_ref, so needs its own assignment(=)) ----

  subroutine vec_t_assign(lhs, rhs)
    type(vec_t), intent(inout) :: lhs
    type(vec_t), intent(in) :: rhs
    lhs%count = rhs%count
    lhs%shift = rhs%shift
    lhs%root = rhs%root
  end subroutine vec_t_assign

  ! ---- array_map_ref (PersistentArrayMap backing) ----

  subroutine array_map_ref_release(h)
    type(array_map_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       deallocate(h%ptr)
       array_map_node_total_freed = array_map_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine array_map_ref_release

  impure elemental subroutine array_map_ref_assign(lhs, rhs)
    type(array_map_ref), intent(inout) :: lhs
    type(array_map_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call array_map_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine array_map_ref_assign

  impure elemental subroutine array_map_ref_finalize(h)
    type(array_map_ref), intent(inout) :: h
    call array_map_ref_release(h)
  end subroutine array_map_ref_finalize

  ! ---- array_map_t (embeds an array_map_ref, needs its own assignment(=)) ----

  ! Releases both possible backings (root, or big once promoted) --
  ! shared by cons_value_release and hamt_ref_release (a HAMT bucket is
  ! itself a full array_map_t, in the vanishingly rare case a bucket
  ! ever needed to promote too).
  recursive subroutine array_map_t_release(m)
    type(array_map_t), intent(inout) :: m
    call array_map_ref_release(m%root)
    if (allocated(m%big)) then
       call hamt_ref_release(m%big)
       deallocate(m%big)
    end if
  end subroutine array_map_t_release

  subroutine array_map_t_assign(lhs, rhs)
    type(array_map_t), intent(inout) :: lhs
    type(array_map_t), intent(in) :: rhs
    lhs%root = rhs%root
    lhs%big_count = rhs%big_count
    if (allocated(rhs%big)) then
       if (.not. allocated(lhs%big)) allocate(lhs%big)
       lhs%big = rhs%big
    else if (allocated(lhs%big)) then
       call hamt_ref_release(lhs%big)
       deallocate(lhs%big)
    end if
  end subroutine array_map_t_assign

  ! array_map_t didn't need its own FINAL before (a single array_map_ref
  ! field, relying on Fortran's automatic per-component finalization
  ! cascading into array_map_ref's own FINAL was apparently enough);
  ! now that it holds a second, independently-finalizable field (big),
  ! that automatic cascading stopped reliably running both fields'
  ! cleanup at the right time on flang -- confirmed by isolated
  ! debugging where a freshly-assigned array_map_t's root looked
  ! correct one statement and empty the next, with no intervening
  ! assignment. Giving the type an explicit FINAL of its own (matching
  ! every _ref wrapper elsewhere in this file) fixes it.
  impure elemental subroutine array_map_t_finalize(m)
    type(array_map_t), intent(inout) :: m
    call array_map_t_release(m)
  end subroutine array_map_t_finalize

  ! ---- env_ref ----

  recursive subroutine env_ref_release(h)
    type(env_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       if (allocated(h%ptr%outer)) call env_ref_release(h%ptr%outer)
       deallocate(h%ptr)
       env_total_freed = env_total_freed + 1
    end if
    h%ptr => null()
  end subroutine env_ref_release

  impure elemental subroutine env_ref_assign(lhs, rhs)
    type(env_ref), intent(inout) :: lhs
    type(env_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call env_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine env_ref_assign

  impure elemental subroutine env_ref_finalize(h)
    type(env_ref), intent(inout) :: h
    call env_ref_release(h)
  end subroutine env_ref_finalize

  ! ---- closure_t (embeds cons_value and env_ref, needs its own
  ! assignment(=) -- default struct assignment doesn't cascade into an
  ! embedded type's own defined assignment) ----

  subroutine closure_t_assign(lhs, rhs)
    type(closure_t), intent(inout) :: lhs
    type(closure_t), intent(in) :: rhs
    lhs%params = rhs%params
    lhs%body = rhs%body
    if (allocated(rhs%extra)) then
       if (.not. allocated(lhs%extra)) allocate(lhs%extra)
       lhs%extra = rhs%extra
    else if (allocated(lhs%extra)) then
       deallocate(lhs%extra)
    end if
    lhs%env = rhs%env
    lhs%is_macro = rhs%is_macro
  end subroutine closure_t_assign

  ! ---- atom_ref ----

  subroutine atom_ref_release(h)
    type(atom_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       deallocate(h%ptr) ! cascades: releases h%ptr%val
       atom_node_total_freed = atom_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine atom_ref_release

  impure elemental subroutine atom_ref_assign(lhs, rhs)
    type(atom_ref), intent(inout) :: lhs
    type(atom_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call atom_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine atom_ref_assign

  impure elemental subroutine atom_ref_finalize(h)
    type(atom_ref), intent(inout) :: h
    call atom_ref_release(h)
  end subroutine atom_ref_finalize

  ! ---- lazy_ref (same shape as atom_ref) ----

  recursive subroutine lazy_ref_release(h)
    type(lazy_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       deallocate(h%ptr) ! cascades: releases thunk/head/tail
       lazy_node_total_freed = lazy_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine lazy_ref_release

  impure elemental subroutine lazy_ref_assign(lhs, rhs)
    type(lazy_ref), intent(inout) :: lhs
    type(lazy_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call lazy_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine lazy_ref_assign

  impure elemental subroutine lazy_ref_finalize(h)
    type(lazy_ref), intent(inout) :: h
    call lazy_ref_release(h)
  end subroutine lazy_ref_finalize

  ! ---- native_array_ref (same shape as atom_ref) ----

  recursive subroutine native_array_ref_release(h)
    type(native_array_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       deallocate(h%ptr) ! cascades: releases buf/extents/lows
       native_array_node_total_freed = native_array_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine native_array_ref_release

  impure elemental subroutine native_array_ref_assign(lhs, rhs)
    type(native_array_ref), intent(inout) :: lhs
    type(native_array_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call native_array_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine native_array_ref_assign

  impure elemental subroutine native_array_ref_finalize(h)
    type(native_array_ref), intent(inout) :: h
    call native_array_ref_release(h)
  end subroutine native_array_ref_finalize

  ! ---- meta_ref (same shape as atom_ref, nothing here mutates it) ----

  subroutine meta_ref_release(h)
    type(meta_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       deallocate(h%ptr) ! cascades: releases h%ptr%val
       meta_node_total_freed = meta_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine meta_ref_release

  impure elemental subroutine meta_ref_assign(lhs, rhs)
    type(meta_ref), intent(inout) :: lhs
    type(meta_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call meta_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine meta_ref_assign

  impure elemental subroutine meta_ref_finalize(h)
    type(meta_ref), intent(inout) :: h
    call meta_ref_release(h)
  end subroutine meta_ref_finalize

  ! ---- arity_clauses_ref (same shape as atom_ref/meta_ref) ----

  subroutine arity_clauses_ref_release(h)
    type(arity_clauses_ref), intent(inout) :: h
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       deallocate(h%ptr) ! cascades: releases h%ptr%params/bodies
       arity_clauses_node_total_freed = arity_clauses_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine arity_clauses_ref_release

  impure elemental subroutine arity_clauses_ref_assign(lhs, rhs)
    type(arity_clauses_ref), intent(inout) :: lhs
    type(arity_clauses_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call arity_clauses_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine arity_clauses_ref_assign

  impure elemental subroutine arity_clauses_ref_finalize(h)
    type(arity_clauses_ref), intent(inout) :: h
    call arity_clauses_ref_release(h)
  end subroutine arity_clauses_ref_finalize

  ! ---- hamt_ref (PersistentHashMap trie nodes -- same shape as
  ! node_ref, but each slot is one of three kinds needing its own
  ! release rather than a uniform children(:) array) ----

  recursive subroutine hamt_ref_release(h)
    type(hamt_ref), intent(inout) :: h
    integer :: i, j
    if (.not. associated(h%ptr)) return
    h%ptr%refcount = h%ptr%refcount - 1
    if (h%ptr%refcount <= 0) then
       do i = 1, BRANCH
          select case (h%ptr%slots(i)%kind)
          case (HAMT_LEAF)
             call cons_value_release(h%ptr%slots(i)%key)
             call cons_value_release(h%ptr%slots(i)%val)
          case (HAMT_CHILD)
             call hamt_ref_release(h%ptr%slots(i)%child)
          case (HAMT_BUCKET)
             do j = 1, size(h%ptr%slots(i)%bucket_keys)
                call cons_value_release(h%ptr%slots(i)%bucket_keys(j))
                call cons_value_release(h%ptr%slots(i)%bucket_vals(j))
             end do
             deallocate(h%ptr%slots(i)%bucket_keys, h%ptr%slots(i)%bucket_vals)
          end select
       end do
       deallocate(h%ptr)
       hamt_node_total_freed = hamt_node_total_freed + 1
    end if
    h%ptr => null()
  end subroutine hamt_ref_release

  impure elemental subroutine hamt_ref_assign(lhs, rhs)
    type(hamt_ref), intent(inout) :: lhs
    type(hamt_ref), intent(in) :: rhs
    if (associated(lhs%ptr, rhs%ptr)) return
    call hamt_ref_release(lhs)
    lhs%ptr => rhs%ptr
    if (associated(lhs%ptr)) lhs%ptr%refcount = lhs%ptr%refcount + 1
  end subroutine hamt_ref_assign

  impure elemental subroutine hamt_ref_finalize(h)
    type(hamt_ref), intent(inout) :: h
    call hamt_ref_release(h)
  end subroutine hamt_ref_finalize

  ! ---- hamt_slot (embeds a hamt_ref plus a cons_value pair, needs its
  ! own assignment(=) -- confirmed, via an isolated repro, that letting
  ! a bulk array-of-hamt_slot assignment (node_assoc's own path-copy:
  ! new_node%slots = node_in%ptr%slots) fall back on default structure
  ! assignment does NOT reliably cascade into the `child` field's own
  ! defined assignment for a struct this size, on flang -- the same
  ! reason cons_value/closure_t/array_map_t already spell out their own
  ! assignment explicitly rather than relying on default cascading.
  ! Without this, a shared child's refcount silently never gets
  ! bumped, and it's freed out from under a still-live sibling the
  ! next time an unrelated part of the trie changes -- corrupting a
  ! key's tag (cons_value_release's last act) while leaving int_val
  ! untouched, which is exactly the symptom that led here.)
  impure elemental subroutine hamt_slot_assign(lhs, rhs)
    type(hamt_slot), intent(inout) :: lhs
    type(hamt_slot), intent(in) :: rhs
    lhs%kind = rhs%kind
    lhs%key = rhs%key
    lhs%val = rhs%val
    lhs%child = rhs%child
    if (allocated(rhs%bucket_keys)) then
       lhs%bucket_keys = rhs%bucket_keys
       lhs%bucket_vals = rhs%bucket_vals
    else if (allocated(lhs%bucket_keys)) then
       deallocate(lhs%bucket_keys, lhs%bucket_vals)
    end if
  end subroutine hamt_slot_assign

end module values
