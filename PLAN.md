# Plan

A living document. NOTES.md records what was built and why it works the
way it does; this records what we are about to build, what we decided
not to build, and why -- so decisions don't have to be re-argued from
scratch.

## Where we are

Measured, not estimated:

There are TWO evaluators in the tree right now, and the numbers differ
by which one is being measured. `clotran-gc` is the GC-backed one and
the one being built on; `clotran-bin` is the original, still the target
of the upstream suite until step 4a moves it.

| | `clotran-gc` | `clotran-bin` |
| --- | --- | --- |
| core.clj | 615 of 724 forms, stopping at its first `(load ...)` | 9 failing forms |
| startup | **1.68s** | **5.43s** |
| unit tests | green, both compilers | green, both compilers |
| Clojure's own suite | not yet pointed at it | 163/16/41 |
| source | 8,342 lines | 9,319 lines |

core.clj stops where it does because of the HOST, not a defect: its last
forms `(load ...)` five sibling libs that generate JVM bytecode or wrap
`java.*` types. See `src/clj/clojure/PROVENANCE.md`.

The original headline measurement, which is why the GC exists at all. It
is not allocation cost and not garbage collection cost -- it is the cost
of *copying a value*, paid on every assignment, because `cons_value` has
a `FINAL` binding and nine allocatable components. Measured on identical
data:

| type shape | ns per copy |
| --- | --- |
| scalars only, no `FINAL` | 4.1 |
| + pointer component, no `FINAL` | 8.9 |
| + pointer component, **with `FINAL`** | 133.8 |
| `cons_value` (9 allocatable components + `FINAL`) | 497 |

Everything below follows from that. `gc_value` -- four scalars, no
allocatable components, no `FINAL` -- is the answer, and `clotran-gc` is
that answer carried all the way up through the reader and evaluator.

## Decisions taken

**The value type loses `FINAL`.** Nothing else moves the number. No
allocation strategy helps, because the cost is per-copy, not per-free.

**A tracing GC, because that is what makes losing `FINAL` safe.** It
also collects the closure/env cycles that refcounting structurally
cannot (`eval_fn` binds a closure into its own env for `recur`), which
is a correctness fix, not only a speed one.

**Non-moving mark-sweep.** The deciding argument is interop, not
throughput: a compacting collector relocates objects and invalidates
any pointer a Fortran library holds. Handing `native_array` buffers to
dgemm or ChemSol is the point of the project, so addresses must be
stable. A moving collector would also force us to push the *address of
every local* rather than the value, which in Fortran means `target`
attributes throughout the evaluator.

**Design B: an explicit value stack, not a shadow stack.** Both cost
the same (a scope with 8 root pushes measures 0.08 ns, four orders of
magnitude below one copy today), so speed does not decide it. What
decides it:

- Under B, rooting is *by construction*. Make the value type private to
  the heap module and expose only integer handles, and there is no way
  to write code holding an unrooted value. A shadow stack makes a
  missed root merely *testable* (GC torture mode); B makes it
  unrepresentable.
- Every reference becomes an index into an array we own, so it can be
  bounds-checked, dumped, validated and printed. A bad reference is a
  bad index, not a wild pointer. We will spend real time debugging this
  collector, and that asymmetry matters more than the ergonomics of
  writing the evaluator.

The price, stated plainly: the evaluator speaks in slot indices instead
of values, and `eval_form` is ~700 lines of deliberately readable
Fortran. A thin frame API (`vs_enter`/`vs_set`/`vs_leave`) and keeping
every comment is a requirement of the port, not a nicety.

**Not a bytecode VM.** A VM is 2-4x faster again, but it resolves
locals to slots and loses the two things that make a good debugger
cheap here: the env chain is already a name->value map (so "eval in
this frame" is nearly free), and the AST node *is* the source form (so
"where am I" needs no bytecode->source map). Most of the VM's dispatch
win is available without it -- see the opcode item below.

Writing it in clotran is also the only way it works at all. gdb cannot
reliably inspect a modern Fortran object because bounds, allocation
status, deferred length and dynamic type live in a compiler-private
descriptor that DWARF only learned to describe indirectly in v5 --
the same missing ABI that stops C calling modern Fortran (README).
A debugger written in the language, over a value representation this
host defines, has no descriptor to decode.

**The debugger is a protocol, not a UI.** The evaluator's breakpoint
calls a handler Var (`*break-handler*`) with the paused state as data
and gets a command back -- the same dependency inversion
`rt_set_lazy_forcer` already uses. A terminal nested-REPL debugger and
an editor-facing one are both just implementations, written in clotran
and swappable at runtime. The contract:

```clojure
{:reason  :breakpoint          ; or :error
 :message "'this-does-not-exist' not found"
 :frames  [{:fn "t1/broken" :file "/tmp/pos.clj"
            :line 6 :col 3 :end-line 6 :end-col 25
            :env {x 3, coll [1 2]}}
           ...]}
;; handler returns :continue | :step-in | :step-over | :step-out | :abort
;;                 | {:eval form :frame 0}
```

Nothing in the evaluator may assume a terminal.

**Concurrency is Clojure's model, and it comes after the GC.** Earlier
notes recorded a "Rust-inspired" model; the decision is now Clojure's
own -- immutable values, explicit mutable references (atoms, refs,
agents), STM for coordinated change -- because it is built on
persistent immutable structures, which clotran already has. Ordering is
not a preference:

- Refcounting across threads means *atomic* increments on every copy.
  That makes the 497 ns worse and is then thrown away.
- STM sits directly on the value representation (a ref holds a value; a
  transaction snapshots and compare-and-swaps it). Built before the
  representation changes, it is built twice.
- A collector written context-parameterized takes a second thread
  nearly for free. One written single-threaded and later retrofitted
  with safepoints and per-thread roots is a redesign.

So the GC work must put per-thread state in a `context` type rather
than module globals -- cheap now, a rewrite later. What is implicitly
single-threaded today:

| file | state |
| --- | --- |
| `Eval.f90` | `has_error`, `last_error_value`, `gensym_table`/`_count`/`_counter`, `here_line`/`_col`/`_file`, `macro_expand_depth` |
| `LispReader.f90` | `has_error`, `last_error`, `current_file` |
| `Namespace.f90` | `current` -- this is `*ns*`, thread-local in real Clojure |
| `Atom.f90` | a Var's `dyn_stack` and the `binding` frame stack -- thread-local in real Clojure |

**Sockets are not what make debugging non-blocking.** clotran is
single-threaded, so a socket would not let it serve a request while
paused. Pausing into a nested REPL at the breakpoint is the correct
model (Common Lisp's `break`, SLIME's SLDB), and the REPL *becomes* the
debugger prompt and hands back on continue. What is genuinely needed is
**framing** on the existing stdio channel so a client can tell program
output, results and debugger events apart. Sockets buy multiple
concurrent clients and a program that owns its own stdin; they are
additive later and do not constrain anything built now.

## Sequence

Ordering principle: things that survive the value-type change come
first, because they make the port itself debuggable. Things entangled
with the value representation come after it, so they are not built
twice.

### 1. Source positions and error locations -- DONE

Line, column and file on every form, so errors and later stack frames
can point at real source.

- [x] `line`/`col` on reader tokens; tokenizer tracks them across
      newlines, including inside multi-line strings
- [x] `src_line`/`src_col`/`src_file` on `cons_cell` -- three integers
      on the *cell*, not a metadata map on every value the way Clojure
      does it. A map per form is an allocation per form over ~11k lines
      of bootstrap, and only list forms are ever what an error points
      at. Survives the value-type change, because cons cells stay heap
      nodes.
- [x] file-name table, so a cell holds a small integer not a path
- [x] positions carried through `pre_expand`/macro rebuilds --
      without this every form inside a frozen `defn` body loses its
      position, which is every form that matters
- [x] errors report `file:line:col`
- [x] **end** line/column as well as start. Line-only gives a
      line-level debugger; start+end gives sexp-level highlighting,
      which is what makes CIDER's debugger feel good rather than like
      gdb. Cheap now, invasive later.
- [x] `(meta form)` synthesises `{:line :column :end-line :end-column
      :file}` on demand, so core.clj's own `(meta &form)` keeps working
- [x] tests (`eval_test` section 44)

Next up is step 2.

### 2. Metadata round-tripping -- DONE

Turned out `core_print.clj` already emitted metadata correctly under
`*print-meta*`; the real gap was in the READER, which did not normalise
the shorthand. `^:private foo` produced the bare keyword `:private`
rather than `{:private true}`, and `^String foo` the bare symbol rather
than `{:tag String}` -- so every `(:private (meta v))` and
`(:dynamic (meta v))` test in core.clj looked a key up in something
that was not a map, and `print-meta` skipped it because `(count m)` on
a keyword answers nothing.

- [x] reader normalises `^:kw` / `^Type` / `^"str"` / `^{...}`
- [x] `Compiler$HostExpr/maybeSpecialTag` + `maybeClass` shims --
      `defn`'s own `resolve-tag` had never run before, because we never
      produced a `:tag` for it to resolve
- [x] reader errors no longer carry the evaluator's position (a bad
      form at the REPL was being reported at whatever line of core.clj
      ran last)
- [x] verified round-trip: `^:dynamic` survives print -> read
- [x] tests (`eval_test` section 45)

Still open for the cache in step 6: `(meta form)` synthesises
`:line`/`:column`, so printing with `*print-meta*` bakes positions into
the text. A cache writer needs to exclude them.

### 3. The GC -- built, wired in, running real core.clj

- [x] **3a/3b.** `src/f/GC.f90` + `test/f/gc_test.f90`: typed pools
      with free lists, a value type with no allocatable components and
      no `FINAL`, non-moving mark-sweep with an explicit mark stack
      (not recursion -- a long list is a chain thousands deep), pool
      growth, torture mode, 24 checks. Nothing in clotran uses it yet.

      Two results worth keeping: a **cycle is collected** (6a/6b),
      which is what refcounting structurally cannot do and is why
      clotran leaks closures today; and building the test surfaced a
      real hole in the allocator's own API -- a freshly built value
      passed as an ARGUMENT is live but cannot have been listed as a
      root by the caller, since nothing references it yet, so
      allocation has to root its own arguments. `(cons (str ...) ...)`
      freed the string otherwise, and only under torture or at an
      unlucky heap size. Check 10a covers it and was confirmed to fail
      without the fix.
- [x] **3a'.** Generalised to hold clotran's data: 38 checks. clotran
      has ~15 node kinds (cons cells, trie nodes, array maps, HAMT
      nodes, closures, atoms, lazy seqs, metadata boxes, arity clauses,
      environments, namespaces), and one pool per kind would be fifteen
      near-identical allocators, free lists, mark arrays and trace
      routines. Underneath they are two shapes: a FIXED few value slots
      plus small integers (cons, closure, lazy, env, map, vector), or a
      VARIABLE-length run of values (trie children, map keys/vals,
      arity clauses, a Var's binding stack). So three pools -- object,
      value-run, text -- and an object's own `kind` says which it
      means. Adding a clotran type is a new `OBJ_` constant, not a new
      pool.

      `gc_check_heap` walks the whole heap asserting no live object
      references a freed or out-of-range slot; check 14a runs it under
      torture. That is the payoff of handles over pointers -- the heap
      audits itself, and corruption is caught where it happens rather
      than when a wild pointer is next dereferenced.

- [x] **3a''.** Native array buffers: INVESTIGATED, design settled.
      See "Native buffers in a GC pool" in NOTES.md for the probes.
      The rules the port must follow:

      1. A buffer is a `class(*), pointer, contiguous` component,
         **never `allocatable`**. Measured on both compilers: an
         allocatable component is *copied* when the pool grows, so the
         buffer's address changes -- which would defeat the entire
         point of a non-moving collector. A pointer component shares
         its target and the address survives.
      2. Hand a library the **whole buffer, never a slice**. A
         contiguous whole buffer is passed by reference with no copy
         (verified through an old-style `a(*)` dummy, the shape BLAS
         uses). A strided slice is silently copied -- correct by
         copy-in/copy-out, but a library that retained the pointer
         would hold a dangling temporary.
      3. A native node holds **only** pointer and small components. Any
         allocatable component is reallocated on pool growth, which is
         harmless for metadata but must never be where the buffer is.
      4. The wrapper roots the array for the duration of a call, so a
         collection mid-call cannot sweep the buffer out from under a
         library that is still writing to it.
      5. **Generated bindings must be module procedures.** flang
         segfaults passing an internal, host-associated procedure as a
         callback on macOS/ARM64 -- see the gotcha in NOTES.md.
      6. **A native buffer holds only Fortran scalar kinds, never
         clotran values.** The collector cannot see inside a native
         buffer -- it is a leaf, holding real(8)s and integer(2)s, not
         anything traceable. NativeArray's current `:value` kind stores
         cons_value elements, which under the GC would be a hole:
         values the array still holds would look unreachable and be
         swept. `:value` arrays move to the **vec pool** (a run of
         gc_value), which is traced for free and loses nothing, since
         a `:value` array is clotran data that never goes to a Fortran
         library and so does not need a stable address. That makes
         "a native buffer is a leaf" an invariant rather than a thing
         to remember.

      Note what is NOT changing: clotran references stay integer
      handles into pools, and the collector follows those. The Fortran
      `pointer` appears in exactly one place -- the buffer of a native
      array -- purely so its address is stable for foreign code.

      Confirmed on both compilers end to end: buffer survives three
      pool growths, a library sees our memory rather than a copy, its
      writes are visible through the heap, and `c_loc` works for a
      future C-level hand-off. Arbitrary kinds (`integer(2)` tested)
      and zero-length buffers are fine.

- [x] **3a'''.** Namespaces. Not a pool: tracing walks every slot
      regardless of kind, so `OBJ_NS` (name, bindings, aliases) and
      `OBJ_VAR` (root, meta, dynamic stack, name) are two constants and
      no new code. What namespaces genuinely needed is what they are
      the first case of -- a **global root**.

      Every other root so far is a root because a caller passed it. The
      namespace registry is a root because of where it lives: shared by
      every thread, so there is no context to thread it through, and
      alive until exit. So `gc_global_new/set/get` -- a slot, not a
      handle handed over once, since the registry's own handle changes
      each time it grows. The collector scans globals alongside the
      argument roots, and the split survives threading: global means
      shared by all threads, argument means owned by one.

      Checks 15a-15i, both compilers, the last two under torture with
      *nothing* on the stack -- 50 Vars kept alive across 50
      collections by registry -> namespace -> bindings alone. Verified
      to fail: with global scanning removed, 7 of the 9 fail.

      15d is the one that matters for semantics: `(def x 42)` after
      `(def x 41)` mutates slot 1 of the same `OBJ_VAR` and the handle
      is unchanged, which is what makes a closure built before a later
      `def` see the new value.
- [ ] **3c.** Value type: drop the nine allocatable components and
      `FINAL`; keep the inline scalars (`tag`, `int_val`, `real_val`,
      `bool_val`) so `v%tag` and friends keep working, and replace only
      the allocatable components with one handle.

      **It does not have to be one bang.** 959 sites name a component
      directly, but a census showed almost all of them pass the bare
      component to a module function; only ~48 reach through `%ptr%`.
      So split it:

      - **3c-1.** Add a payload accessor per component in Values.f90
        and migrate the call sites to it. Behaviour-preserving, the
        representation *unchanged*, so the full sweep stays green after
        every component. One commit each, smallest first.
      - **3c-2.** Swap the representation underneath the accessors.
        One file, and the only genuinely big-bang part left.

        3c-1 is worth doing whichever way the compiler question lands,
        so it does not need that decision first -- it makes the
        decision later and cheaper.

  - [x] **3c-1 `array_val`** (23 sites). Every real use was a
        `%array_val%ptr%...` chain -- the hardest shape, and it got
        *shorter*: `nd => array_node(v)` once per routine, then plain
        `nd%extents`. `array_is` collapsed to
        `associated(array_node(v))`, one test instead of the
        allocated-then-associated pair each site repeated. The only
        `%array_val` left in the tree is inside the accessors and
        inside the refcounting that 3e deletes, which is the end state
        every component is aiming at.
  - [x] **3c-1 `meta_val`** (35 sites). `meta_node` holds one
        `cons_value`, so the accessors are value-level:
        `has_meta`/`get_meta`/`set_meta`. Both five-line
        allocate-and-refcount blocks (`with-meta`, the reader's `^`)
        became one call, and `eval_def`'s doubly-nested
        allocated/associated guard flattened by two levels.

        `has_meta` is deliberately separate from "get_meta returned
        nil": `(with-meta x nil)` attaches nil, which is not the same
        as carrying no metadata, and `eval_def` branches on the
        difference. Collapsing them would have been a silent semantic
        change -- the kind this whole split exists to avoid.

        Metadata is where the unit tests are weakest relative to the
        risk (`:arglists`, `^:dynamic`, `deftest`'s `:test`), so this
        one was also checked against the upstream suite on the
        pre-change tree: 163/16/41, identical per namespace.
  - [x] **3c-1 `lazy_val`** (36 sites). `lazy_ptr` plus
        `new_lazy_node`. Every read site repeated the same three-level
        `allocated`/`associated`/`state` nest; each lost a level, and
        both constructors went from six lines of allocate-and-refcount
        to three.

        `lazy_ptr`, not `lazy_node`: the type is already called
        `lazy_node` and Fortran is case-insensitive, so a function of
        that name would be the same name -- the `GCT_`/`gc_cons` trap
        again.
  - [x] **3c-1 `atom_val`** (50 sites, 40 of them in `Atom.f90`).
        `atom_ptr` + `new_atom_node` + `share_atom`. Every routine in
        `Atom.f90` opened with the same `allocated`/`associated` pair;
        all of them now start `nd => atom_ptr(a)`, and the file no
        longer names the component at all.

        `atom_ptr` deliberately does **not** check the tag, unlike
        `array_node` and `lazy_ptr`. Five tags share this box --
        `TAG_ATOM`, `TAG_VAR`, `TAG_MULTIFN`, `TAG_REDUCED`,
        `TAG_STRING_BUILDER` -- because "one genuinely mutable slot,
        shared by reference" is the same storage for all of them and
        only the behaviour differs.

        `share_atom` exists because one call site must *share* the box
        rather than copy it, and the comment there recorded a real
        hazard worth keeping: the component has to exist before
        `assignment(=)` runs on it, since `atom_ref_assign` releases
        the old target first and releasing an unallocated component
        reads uninitialized memory.
  - [x] **3c-1 `vector_val`** (59 sites). The first payload that could
        *not* follow the pattern: the accessors live in
        **PersistentVector.f90**, not Values.f90, because reaching an
        element means walking the trie and Values cannot use that
        module -- the dependency runs one way only. So for vectors "the
        one place that knows the representation" is that file plus the
        type declaration in Values. Fine, and arguably the right home;
        worth knowing before 3c-2 assumes one file.

        `has_vector`, `val_vec_count`, `val_vec_nth`, `set_vector`,
        `val_vec_conj`, `val_vec_assoc`. Each absorbs the `allocated()`
        guard its callers repeated, so the common shape

        ```fortran
        if (allocated(v%vector_val)) then
           if (vector_count(v%vector_val) > 0) val = vector_nth(v%vector_val, 0)
        end if
        ```

        is now one line. `conj` and `assoc` lost their
        allocated/else/empty branches entirely -- an absent vector
        conjes onto the empty one, which is what `(conj nil x)` means.

        Residue: three `vector_to_list(...)` calls in RT.f90. That
        function is RT-private and walks `%root`/`%shift` directly;
        moving it into PersistentVector would need PersistentList,
        which PersistentVector does not use. Left deliberately, and
        small enough for 3c-2 to edit in place.
  - [x] **3c-1 `str_val`** (375 sites). Three read accessors, not one,
        because one would be slow: the commonest read is a comparison
        against a literal in `eval_form`'s dispatch, and routing those
        through a function returning `character(len=:), allocatable`
        would allocate and copy a string on the hottest path in the
        interpreter. So `str_is` compares in place, `str_len` measures,
        and `val_str` (a copy) is only for callers that genuinely need
        the text, where a copy was happening anyway. Plus `has_str`,
        `str_sub`, `set_str`.

        The real prize is not the refactor. Every text accessor treats
        an unallocated payload as empty instead of reading it, which
        makes 4a' bug 2 -- a non-short-circuiting `.and.` handing an
        unallocated `str_val` to a procedure -- **unrepresentable**
        rather than merely fixed.

        Two Fortran facts worth keeping: neither compiler accepts a
        substring of a function result (`val_str(v)(1:1)`), hence
        `str_sub`; and an internal `READ` needs a character *variable*,
        not an expression, so one call site keeps a local. Also
        `printer.f90`'s two helpers took `character(len=:),
        allocatable` purely to cope with an unallocated payload; they
        are plain `len=*` now.
  - [x] **3c-1 `list_val`** (158 sites). `has_list`, `val_lst`,
        `val_lst_first`, `val_lst_rest`, `val_lst_count`, `set_list` in
        PersistentList.f90 (the one-way dependency again), plus
        `list_cell` in Values.f90 for the reader's source positions --
        that one can live in Values because a `cons_cell` is declared
        there and no list walking is involved.

        **This migration changed 4a'' from intermittent to
        deterministic**, which is the most useful thing to come out of
        it. See 4a'' below.
  - [x] **3c-1 `map_val`** (108 sites). `has_map`, `val_map`,
        `set_map`, `val_map_count`, `val_map_get`, `val_map_contains`,
        `val_map_entries` in PersistentArrayMap.f90. The most regular
        of the six: `allocate`+assign pairs collapse to `set_map`, and
        `conj`/`assoc` lose their empty-map branches the way the
        vector ones did.
  - [x] **3c-1 `fn_val`** (74 sites, ~48 migrated). `has_fn`,
        `new_fn`, `fn_is_macro`, `set_fn_macro`, `fn_params`,
        `fn_body`, `set_fn_params`, `set_fn_body` -- field at a time,
        in Values.f90.

        Field accessors rather than a pointer to the `closure_t`
        because `fn_val` is ALLOCATABLE, not a pointer: returning a
        pointer would mean giving the dummy `TARGET` and relying on
        every actual argument being a target too. They are not, and a
        pointer to a non-target actual is undefined on return -- which
        is exactly the bug class 4a'' is about. Not while hunting it.

        **`%env` and the arity clauses (`%extra`) deliberately still
        name the component.** `env_new(f%fn_val%env)` is in
        `apply_closure`, the hottest path in the interpreter, and an
        accessor returning `env_ref` by value would add a refcount bump
        and a finalize per function call. `list_val` had just
        demonstrated what extra temporaries do to 4a''; paying that on
        every call for tidiness is not a trade worth making. 26 sites,
        all in Eval.f90, for 3c-2 to edit directly.

        **3c-1 is done.** What 3c-2 now has to touch: Values.f90,
        PersistentVector.f90, PersistentList.f90,
        PersistentArrayMap.f90, and ~29 residue sites in RT.f90 and
        Eval.f90 -- against 959 before.

- [x] **3c-2, first slice: `str_val` is in the heap.** Two pieces of
      scaffolding made a single payload movable on its own:
      `gc_no_collect` (grow-only, because nothing roots anything until
      3d, so a collection would sweep live data -- check 16) and
      `gc_ensure_init` (so nine drivers need no `gc_init` call
      meanwhile). `str_val` became a bare handle into the string pool;
      the ref-level API keeps the is/len/text split so comparing a
      symbol to a literal still does not allocate.

      Not a win yet and expected not to be: gfortran 4.5s -> 5.3s,
      flang 30s -> 33s, RSS 93 -> 145 MB. The cost is `FINAL` plus the
      other eight components. Both compilers stay at 163/16/41.

- [ ] **3c-2, the rest -- and it is the same change as 3d.** A GC
      object's slots are `gc_value`. A `cons_value` cannot go in one
      while `cons_value` still has allocatable components, so a payload
      moves alone only if its backing node holds no clotran values.
      Checked, not assumed:

      | backing node | cons_value components |
      | --- | --- |
      | `cons_cell` | 1 (`car`) |
      | `vec_node` | 1 (`items`) |
      | `array_map_node` | 2 (`keys`, `vals`) |
      | `hamt_node` | via `hamt_slot`: key, val, buckets |
      | `closure_t` | 2 (`params`, `body`) |
      | `atom_node` | 4 |
      | `lazy_node` | 3 (`thunk`, `head`, `tail`) |
      | `meta_node` | 1 |
      | `native_array_node` | 0 -- except the `:value` kind |

      Text was migratable *because it is a leaf*: bytes, nothing
      traceable. The other eight are coupled to each other and to the
      value type, and the moment `cons_value` becomes a handle
      everything must be rooted or the first collection sweeps live
      data. So the remainder of 3c-2 and 3d are **one change**, which
      is the big bang this plan always said it was. `native_array` is
      the near-miss: a leaf apart from `:value` arrays, which 3a''
      rule 6 already moves to the vec pool.

- [ ] **3d.** Evaluator on the value stack.

- [x] **3d, groundwork: the value stack exists and is tested.** Built
      standalone against the collector, the same way the collector
      itself was built before anything used it. `vs_enter(n)` reserves
      a frame and returns its base, `vs_set`/`vs_get` address slots,
      `vs_leave(base)` pops; `gc_collect` scans every live slot
      alongside the globals.

      It lives in GC.f90, not beside the evaluator, because the
      collector must scan it and nothing else may -- which is what
      makes rooting by CONSTRUCTION rather than discipline: there is
      nowhere else to put a value.

      `vs_leave` clears on the way out, and that is not tidiness. A
      stale value left above the stack top is still traced and keeps
      dead data alive -- the characteristic leak of a stack collector.
      Check 17d is what pins it.

      Checks 17a-17j, both compilers: a frame's slots survive
      collection with no argument roots at all; leaving a frame makes
      its values collectable; the stack grows past its initial size
      without losing a slot; and 300 values rooted ONLY by the stack
      survive torture mode with the heap still passing its own audit.
      Verified non-vacuous -- with stack scanning removed, 5 of the 10
      fail.

- [x] **The data layer, built beside the old one.** Since the remaining
      payloads cannot move one at a time, the safe decomposition is not
      slicing the change but the pattern that has now worked three
      times here: build the new thing standalone, test it, wire it in
      last. `GC.f90` was built that way, so was the value stack, and so
      is this.

      **`src/f/GCVector.f90`** -- the same 32-way trie as
      `PersistentVector.f90`, with every reference a GC handle instead
      of a refcounted pointer. `gcv_empty/count/nth/conj/assoc`, path
      copying unchanged, sharing untouched children exactly as before.
      Nothing uses it yet.

      The vector went first on purpose: it is the most intricate
      structure in the layer, and it is where 4a'' lives. Check 6a is
      the point of the whole exercise -- a vector built with a
      collection at EVERY allocation, heap audit clean, every element
      intact. A premature free is not expressible under tracing:
      nothing decrements, so nothing can decrement too often, and a
      node is either reachable or it is not.

      Checks 1-6 (18 in all), both compilers: growth past one trie
      level (the push-down a 32-way trie gets wrong if mis-shifted),
      assoc leaving the original untouched, shared structure surviving
      collection, a vector rooted ONLY through the value stack
      surviving and then being collected when the frame is left, and
      the torture case above.

      **`src/f/GCList.f90`** -- the persistent list, same treatment.
      Count cached on the cell (i1) exactly as `cons_cell` does, so
      `count` stays O(1); the evaluator calls it constantly on argument
      lists. The empty list is a **singleton** registered as a GC
      global root, matching `PersistentList.EMPTY`: `()` must be
      identical to `()` everywhere, and `()` is a list rather than nil.

      Its test found a real bug in that singleton, which is the reason
      to write these checks rather than assume. `gc_init` clears the
      global-root registry, but the module's cached slot index survives
      it -- so after a re-init the "singleton" silently handed back nil
      and every `()` became a fresh object. `gcl_empty` now re-checks
      the slot instead of trusting the index (check 4c).

      Checks 1-5 (17 in all), both compilers: a 2000-cell chain rooted
      only through the value stack (which is also what proves the
      collector's explicit mark stack does not recurse into the real
      one), two lists sharing one tail object across a collection, and
      the torture case.

      **Open, and deliberately not invented at this stage: source
      positions.** `cons_cell` carries `count` plus five position
      integers; a GC object has `i1` and `i2`. Count took `i1`. The
      five remaining have to go somewhere before the switch, and the
      choice matters -- slots 3/4 of the cons object would mean an
      allocation per form, which is the exact cost the current design
      avoided on purpose (see `cons_cell`'s own comment). Packing them,
      widening `obj_node`, or accepting the allocation are all live;
      settle it before porting the reader.

      **`src/f/GCMap.f90`** -- the array map, and `gc_equal` in the
      collector to go with it, mirroring `value_equal` so the two
      representations agree during the migration: same tag and same
      scalar or text content, collections by identity. Deep equality
      for collection keys stays a separate decision rather than one
      made silently here.

      Text keys compare by CONTENT, not by pool slot, and check 4
      pins it: the same string allocated twice is two slots but one
      key. A map that got that wrong would quietly hold duplicates --
      the single most likely way to break a map on a pooled string
      representation.

      `dissoc` moves the LAST entry into the hole rather than shifting
      the tail, which is what Clojure's own array map does and is
      correct because a map is unordered; check 5c walks every other
      key afterwards, including the moved one.

      25 checks, both compilers. **Promotion to a hash trie past 8
      entries is not here** -- it arrives with the HAMT module, and
      until then this stays linear at any size. That is a performance
      gap, not a behavioural one: a linear map answers the same
      questions, slower.

      **`src/f/GCHamt.f90`** -- the hash trie the map promotes into,
      plus `gc_hash` in the collector, mirroring `PersistentHashMap`'s
      `hash_of`: same mix32, same FNV-1a over the text, same tag mixed
      in so `"a"` and `\a` do not collide. It has to agree with
      `gc_equal` or a trie stores one key twice, so text hashes over
      CONTENT exactly as gc_equal compares content.

      Collision buckets **reuse GCMap**: a set of keys sharing a
      32-bit hash is a small linear map, and a second linear scan here
      would be the same code twice.

      The collision path is forced with a REAL pair, not hoped for.
      Integers cannot collide -- mix32 is the Murmur finaliser, which
      is bijective -- so the test searches short strings for a genuine
      FNV-1a collision (open addressing, ~0.2s) and then checks both
      keys are stored, both read back, and replacing inside a bucket
      does not grow the count. A trie that drops one of a colliding
      pair looks perfectly healthy until the day it does not.

      22 checks, both compilers, including 3000 keys across several
      levels of splitting and the torture case.

      **`src/f/GCEnv.f90`** -- the lexical environment: a chain of
      frames, each a name -> value map, searched outward. Structure
      unchanged from Env.f90, including that `gce_set` MUTATES the
      frame rather than returning a new one (`def` and `let*` add to a
      frame a closure may already hold, and everything sharing it must
      see the binding). The walk is iterative rather than recursive:
      an env chain is as deep as the program's nesting and this is the
      hottest path in the interpreter.

      Check 5 is the one that matters, and it is the correctness half
      of why the GC exists at all. A named `fn` binds its own closure
      into its own frame so `recur` can find it -- closure -> env ->
      closure, a cycle. Refcounting never sees either side reach zero,
      so **clotran leaks one of these per named fn for the life of the
      process**. The check builds that cycle, confirms it really is
      one (5b follows the closure's env slot back to the frame), drops
      every reference, and 5d collects it. That is not a speed win; it
      is a class of leak disappearing.

      22 checks, both compilers, also covering shadowing across three
      frames, bound-to-nil counting as bound (which the evaluator needs
      to tell "no such local" from "a local holding nil"), inner
      bindings not leaking outward, defining-namespace inheritance, and
      torture.

      **Closure and atom need no module of their own.** Both are plain
      slot objects -- `OBJ_CLOSURE` (params, body, env, clauses; i1 =
      macro?) and `OBJ_ATOM` (value, meta, dyn stack) -- with no logic
      beyond `gc_obj`/`gc_slot`, which `gc_test` check 11 already
      covers and GCEnv check 5 exercises.

      **`src/f/GCAssoc.f90`** -- the map clotran actually uses: array
      map to 8 entries, hash trie beyond, one-way, matching Clojure.
      It is a THIRD module rather than logic inside GCMap, and that is
      forced rather than stylistic -- GCHamt already uses GCMap for
      collision buckets, so GCMap using GCHamt would be a module cycle
      Fortran rejects. The arrangement is better anyway: neither
      representation knows the other exists.

      Two subtleties the checks pin:

      - **Promotion copies entries POSITIONALLY, not via `get`.** A key
        bound to nil would be silently dropped by a copy that read
        values back, because `get` cannot tell "absent" from "present
        and nil". Check 4 is that key.
      - **Replacing a key in a full array map must not promote.** The
        count does not change, so the representation should not either
        (check 5).

      Writing this also exposed a **vacuous test of my own**, which is
      worth recording as the failure mode to watch for. `gca_dissoc`
      on a trie was a no-op because `gch_dissoc` did not exist, so the
      "stays a trie however small it gets" check passed by never
      shrinking the map at all. Fixed both ways: `gch_dissoc` is now
      implemented (with its own checks, 7a-7d), and the assoc check now
      asserts the count actually dropped, so it cannot pass vacuously
      again. A test that cannot fail is worse than no test, because it
      is counted as coverage.

      `gch_dissoc` deliberately does NOT collapse emptied nodes -- an
      empty child stays a child, a one-entry bucket stays a bucket.
      Correct but slightly wasteful; the collapse is where trie
      deletion gets subtle and nothing needs the space yet.

      **`src/f/GCPrinter.f90`** -- values back to text, written before
      the switch rather than after, for two reasons beyond eventually
      needing it. It is the first thing that walks EVERY structure in
      the new layer at once, so a representation mistake each module's
      own tests miss shows up here; and debugging the switch without
      being able to print a value would be miserable.

      It needed entry iteration, so `gch_entries` and `gca_entries`
      came with it -- filling caller-allocated arrays rather than
      taking a callback, because flang segfaults passing an internal
      procedure as one (NOTES.md).

      Check 5 is the one worth having: the SAME single entry is built
      first in an array map and then, by promoting and dissoc'ing
      everything else, in a trie -- and must print identically. A map
      that printed differently past 8 entries would be the
      implementation leaking into the language. Check 1f is the other:
      a double prints as `2.0`, not `2`, or it reads back as an
      integer, which is a round-trip failure rather than a cosmetic
      one.

      24 checks, both compilers, including a value rooted only by the
      value stack printing correctly after a collection (printing
      allocates as it walks, so the subject has to stay rooted).

      **`src/f/GCReader.f90`** -- text into the heap, and with the
      printer a genuine **round trip**: read a form, print it, get the
      input back. That is the strongest test this layer has. A reader
      and a printer can only agree if the thing between them actually
      holds what it was given, and it exercises every structure against
      real Clojure text rather than against values built by hand.

      41 checks, both compilers. The two that matter most:

      - **6a: a 60-element list round-trips under torture.** Reading
        allocates constantly, so a collection lands between two
        elements of a list far more often than it ever would in
        practice, and every partially built form has to stay rooted
        through it. Elements accumulate in a GC VECTOR rather than a
        Fortran array for exactly this reason -- a plain array of
        gc_value is invisible to the collector.
      - **Group 5: bad input is an error, not a half-built value.**
        Unclosed list, unclosed vector, odd map literal, stray closer,
        unterminated string -- and a good form afterwards clears the
        flag.

      Recursive descent straight over the buffer, with no token array:
      LispReader has one to record a line and column per token, and
      source positions are still the open question above, so this does
      not pretend to solve it.

      Deferred and listed rather than silently missing: metadata `^`,
      the discard macro `#_`, sets `#{}`, regex literals, syntax-quote
      expansion and auto-gensym. Those are reader macros layered on the
      core shapes, and the shapes are what needed proving.

      **`src/f/GCEval.f90`** -- a core evaluator, and the module that
      answers the question the whole port rests on: **does rooting by
      construction hold up under real evaluation?** Everything before
      it was data structures, where the roots are obvious. An evaluator
      is where they are not -- intermediate values live across
      recursive calls, every one of which can allocate and therefore
      collect.

      The answer is yes. Every check runs TWICE, once normally and
      once with `gc_torture` on, and the torture pass is the real one:

          (do (def fib (fn* [n] (if (< n 2) n
                                  (+ (fib (- n 1)) (fib (- n 2))))))
              (fib 10))   =>   55

      computed correctly with a collection at **every single
      allocation**, heap audit clean afterwards. Also under torture:
      lexical capture (`((mk 10) 5)` => 15), recursion through a def'd
      name, shadowing, and vector literals evaluating their elements.

      The rule the module documents and the tests enforce: a value that
      must survive an allocation lives in a value-stack SLOT, never in
      a Fortran local, because the collector cannot see locals. Each
      routine opens a frame, works in slots, and reads its result out
      before leaving.

      Scope is the core, deliberately, not the ~5400 lines of Eval.f90:
      quote/if/do/def/let*/fn*/loop*/recur/defmacro*/quasiquote/try*/
      throw, twelve primitives, closures, varargs, multi-arity.
      Missing and listed rather than silent: destructuring (a macro in
      core.clj, not evaluator work), namespaces, protocols, metadata.

      **Laziness**, which `map`/`filter`/`range` are all built on.
      `(lazy-seq* body)` captures the body in a no-argument closure and
      hands back an unrealised node; nothing runs until something asks
      for an element. Check 16e proves that directly -- a body that
      would `throw` constructs fine, and 16f shows asking does run it.

      Realisation is memoised on the node, so walking a seq costs O(1)
      per cell rather than re-running the thunk, and 16g takes the
      third element of an **infinite** seq, which without laziness
      does not terminate at all.

      Two structural notes:

      - **Printing forces.** A lazy seq has to be realised to print,
        but the printer sits below the evaluator, so the evaluator
        hands its forcer down -- the same dependency inversion
        clotran's `rt_set_lazy_forcer` already uses, and a MODULE
        procedure because flang will not take an internal one as a
        callback.
      - **`(cons x <lazy>)` cannot build a plain cons cell.** Its tail
        would have to be a realised list, and forcing there defeats the
        point, since `(cons n (from (+ n 1)))` is exactly how an
        infinite seq is written. It builds an already-realised lazy
        cell instead, head and tail in place, nothing forced. clotran's
        `RT.f90` has `lazy_cons` for precisely this reason; the tests
        found it the hard way (16g returned nil, 16h `(1 nil nil nil)`)
        before it was put back.

      **Namespaces and Vars** (`src/f/GCNamespace.f90`), which closes
      the `def` divergence: `def` now interns in the CURRENT NAMESPACE,
      so `(let [] (def x 1))` defines at the top level exactly as
      Clojure does (check 17b). Symbol resolution is lexical scope
      first, then the namespace, so a local shadows a Var rather than
      redefining it -- which is what makes `(let [map ...])` legal.

      The point of Vars, and check 17f: a Var is a stable box with
      IDENTITY, so `(def x 2)` after `(def x 1)` MUTATES the same Var
      rather than replacing it. A closure built before the
      redefinition therefore sees the new value -- which is what makes
      redefining a function at a REPL work while everything that
      already called it keeps working. `(var x)` returns the Var
      itself, undereferenced.

      ### A trap that bit three modules, now closed

      `gc_init` clears the global-root table, but a module's saved slot
      index survives it. Three separate modules hit this:

      1. GCList's empty-list singleton -- caught by check 4c, fixed by
         re-checking the slot.
      2. GCNamespace's registry -- `gc_global_set` on a stale index is
         silently a NO-OP (out of range), so the registry was never
         re-registered and every namespace lookup failed.
      3. GCEval's thrown value -- worse: a stale index that lands back
         IN range **overwrites another module's root**. `thrown_root`
         was clobbering the empty-list singleton.

      A bare integer cannot distinguish "my slot" from "someone else's
      slot that now has my number", so the fix is a `gc_root` handle
      carrying an index AND a generation, with the generation bumped by
      `gc_init`. `gc_global_keep` re-registers whenever the claim is
      stale. Every module holding a global root now uses it.

      Worth noting how this was found: not by reasoning, but because
      (2) made eight checks fail at once and (3) left exactly one
      failing that the isolated probe could not reproduce. The second
      one only appears when many `gc_init`s run in sequence, which is
      what a test suite does and a single program never would.

      **`try*`/`catch*`/`throw`, and a rooting point worth keeping.**
      `throw` carries a VALUE, not a message, and that value is held
      as a **GC global root** rather than a plain module variable. It
      has to be: between the throw and the catch, nothing else refers
      to it -- the frames that held it are unwinding -- so an ordinary
      variable would be a live value the collector cannot see, and a
      collection in that window would free the exception before its
      handler ran. Under torture that window is a guaranteed
      collection, and check 14d (throwing a list and counting it in
      the handler) is what proves it.

      An internal error is catchable too, and arrives as a **map**,
      `{:error "message"}`, not a bare string. A string would be
      indistinguishable from `(throw "x")`, so a handler that wants to
      re-raise anything it does not recognise would have no way to
      tell them apart. clotran's older evaluator uses a string here;
      this is a deliberate improvement on it rather than an accident
      of the port. Checks 14i/14j are that distinction.

      **What `catch` cannot catch: a Fortran runtime error.** Fortran
      has no exceptions and no stack unwinding, so a segfault, a failed
      `allocate`, an `error stop` or a trap inside a called library
      ends the process. There is no `try` around it, and that is not a
      gap in this evaluator -- it is the host.

      It matters beyond the REPL. The point of the project is handing
      arrays to real Fortran libraries, and a crash inside one of those
      takes the whole session with it, including whatever the user was
      computing. For the live-monitoring goal that is the difference
      between "the simulation blew up" and "everything you had is
      gone".

      Three things ARE catchable and should be, rather than being left
      to crash:

      - `allocate(..., stat=)` -- out of memory becomes a clotran error
      - `read(..., iostat=)` -- already used by the reader for numbers
      - IEEE flags via `ieee_arithmetic` -- overflow, divide by zero

      Anything else would need a C signal handler plus `longjmp`
      through `iso_c_binding`, which is exactly the fragile territory
      the README's ABI section is about, and is not worth it for a
      crash that has already corrupted the heap.

      ### Surviving a crash inside a called library

      This is the sharp end of it: if ChemSol segfaults, does the whole
      REPL go down, and everything the user had computed with it?

      **Threads do not help.** A segfault is delivered to the PROCESS,
      and threads share one address space -- a wild write in the
      library's thread lands in our heap. Even catching SIGSEGV on that
      thread leaves the damage done and possibly `malloc`'s lock held
      forever. Threads buy concurrency, not isolation. Worth stating
      plainly because it is an easy thing to assume otherwise.

      **A separate process does, and it is measured, not assumed.** A
      probe (`fork` + anonymous `MAP_SHARED` mmap, both through
      `iso_c_binding`) has the child write results into a shared buffer
      and then segfault. The parent survives, `waitpid` reports status
      11, and **the results written before the crash are readable**.
      So the REPL can report "the library died" as an ordinary clotran
      error and keep everything else.

      What makes this a good fit rather than a bolt-on: the collector
      is **non-moving** and native buffers are **contiguous with stable
      addresses** -- decisions already taken for zero-copy interop. An
      array can therefore live in shared memory and be handed to the
      child by offset, with no marshalling. The property that makes
      `dgemm` cheap is the same one that makes isolation cheap.

      Costs, honestly:

      - **`fork` and threads do not mix.** Only async-signal-safe calls
        are legal in the child, so this must happen before OpenMP
        starts, or through a persistent worker spawned early. That is a
        genuine tension with the concurrency step and needs settling
        there, not here.
      - **`fork` does not exist on Windows** -- which is the reason
        not to build on `fork` at all. See below.
      - A fork per call costs on the order of a millisecond -- nothing
        against a large `dgemm`, ruinous in a tight loop of small
        calls. So a **persistent worker** rather than fork-per-call.
      - Partial results are visible, which cuts both ways: you can see
        how far it got, and you can also read half-written garbage.
        The worker protocol has to say which.

      Shape to aim for: isolation is **opt-in per library** in the
      binding generator -- trusted libraries called directly, unknown
      or crash-prone ones through a worker. That is the same
      per-library declaration thread-safety already needs, so it is one
      annotation rather than two.

      ### Windows, without fork

      clotran must not require Linux or macOS, so nothing may depend
      on `fork`. It does not have to: we already wanted a **persistent
      worker** rather than fork-per-call for performance, and a worker
      needs SPAWN, not fork. Spawn exists everywhere.

      **The portable floor is standard Fortran, and it is measured.**
      `execute_command_line` is Fortran 2008 and exists on Windows.
      A probe runs a child that writes results to a file and then
      segfaults: the parent gets `exitstat = 11`, survives, and reads
      back everything the child managed to write. No C, no platform
      branches, nothing POSIX. Whether `exitstat` carries the signal
      or a Windows exception code is processor-dependent, but non-zero
      means "it died", which is the only thing that has to be portable.

      **The fast path is a small shim, not a different design.** The
      floor copies through a file; mapping that same file instead
      removes the copy. The two platform calls are direct analogues:

      | | POSIX | Windows |
      | --- | --- | --- |
      | map a file | `mmap` | `CreateFileMapping` + `MapViewOfFile` |
      | spawn | `posix_spawn` | `CreateProcess` |
      | crash status | `waitpid` / `WIFSIGNALED` | `GetExitCodeProcess` |

      Four functions behind one shim, and the design degrades: if the
      shim is missing on some platform, the standard-Fortran floor
      still works, just with a copy. On Linux the mapped file goes in
      `/dev/shm`, so it is RAM anyway.

      **And the interpreter is already portable.** Checked, not
      assumed: there is **no `bind(c)` or `iso_c_binding` anywhere in
      `src/f`**, and all eleven new GC-layer modules compile clean
      under `gfortran -std=f2018`. The only POSIX thing in the repo is
      `scripts/clotran`, a shell wrapper around `rlwrap` -- a
      convenience, not the interpreter. So Windows support is a
      packaging question rather than a porting one, and this decision
      must not be what breaks it.

      **Multi-arity.** The two shapes real Clojure has, told apart by
      whether the form after `fn*` is a vector or a list, which is
      exactly how the reader leaves them. Clauses live in slot 4 --
      the slot `OBJ_CLOSURE`'s comment already reserved -- with slot 1
      left nil, so "is this multi-arity" is one test rather than a
      flag. Clause selection prefers an exact arity and otherwise
      takes the first variadic one that fits; check 15g runs a
      two-clause function that `recur`s within one clause to sum 1..100.

      **Varargs** are one routine, `bind_params`, used by BOTH fn*
      application and recur -- so a variadic function can recur without
      the two disagreeing about arity. `&` collects the rest into a
      list, empty rather than nil when there is nothing left, which is
      what lets variadic core functions work without special-casing
      zero.

      **Macros and syntax-quote.** A macro gets its arguments
      unevaluated and its result is evaluated in the caller's
      environment; the check happens before the arguments are touched,
      which is the entire difference from a function (check 13c: a
      macro ignoring an unbound symbol, where a function would fail).
      Macro-ness lives on the closure, as clotran's own `is_macro`
      does -- real Clojure keeps it in Var metadata, and there are no
      Vars here. `quasiquote` expands to ordinary `cons`/`concat`
      calls, the same shape as clotran's `qq_expand`, which is why
      those two arrived as primitives with it.

      **`loop*`/`recur`, and why there is no general trampoline.**
      Clojure does not promise tail-call elimination; it promises
      `recur`, an explicit jump to the nearest enclosing `loop*` or
      `fn*`. So iteration lives in exactly those two places: each
      evaluates its body and, if the result is an `OBJ_RECUR`, rebinds
      its parameters and goes round again. Recursion depth is then
      bounded by the program's NESTING rather than its iteration count
      -- which is the guarantee the language actually makes. A general
      trampoline would be more machinery for a promise Clojure never
      made.

      `recur` is a VALUE (`OBJ_RECUR`, holding its evaluated arguments)
      rather than host control flow, because only the recur point
      knows how to rebind, and it is the thing that catches it.

      Check 8e is the one that matters: **100000 iterations**, which
      without rebinding in place is a stack overflow rather than a
      wrong answer. 8f sums to 50005000 the same way.

      **The torture pass then caught a real rooting bug in my own
      `qq_expand`**, and it is the exact mistake this design is meant
      to prevent, made anyway:

          sym = gc_sym("concat", ...)   ! a Fortran LOCAL
          inner = nth_of(...)           ! allocates -- can collect
          call vs_set(base + 3, sym)    ! too late

      The symbol was computed into a Fortran local, then something
      that allocates ran before it reached a slot. Under torture it was
      collected in that window and the accumulated tail went with it --
      every quasiquote returned just its head. The plain pass was
      perfectly green throughout. Fixed by storing each intermediate
      into its slot BEFORE anything that can allocate runs, which is
      the rule the module header already stated.

      That is the argument for torture mode in one example: rooting by
      construction makes the mistake *findable*, not impossible, and
      what makes it findable is collecting at every allocation.

      Check 8g caught a mistake in my own expectation, and is the
      better test for it: a closure built during the iteration where
      `i` is 1 must return **1**, not the loop's final 2. If `recur`
      mutated the frame in place instead of rebinding into a fresh
      one, it would return 2. Rebinding is what makes that right.

      The torture pass caught a real bug on its first run: `has_error`
      is module state and nothing cleared it, so once one check
      expected an error every later evaluation short-circuited.
      `gce_clear_error` is now the caller's job before a top-level
      eval -- it cannot be done inside `gce_eval`, which is recursive
      and would wipe an error raised deeper in the same evaluation.

      ### A host shim, NOT a core library

      `clotran-gc` (`src/f/gc_main.f90`) is a REPL over the new stack,
      and it loads `src/clj/host.clj` at startup.

      That file was briefly a small core -- map, filter, reduce, take,
      range, sort, merge, into, all written in Clojure -- and that was
      a mistake, caught in review. The argument against Fortran
      builtins was that real core.clj defines those in Clojure and the
      thesis is running that actual file. Writing our own versions is
      the same duplication one layer up: a second, different
      implementation that the real file replaces, and a confusing bug
      in the meantime wherever the two differ.

      So host.clj holds ONLY what core.clj cannot supply: the type
      predicates. Real Clojure asks `instance?` about
      `java.lang.String` and `clojure.lang.PersistentVector`; clotran
      has neither, so the host answers with `clotran-type` and the
      predicates are written over it. Three macros (`defn`, `fn`,
      `let`) come with them only because the predicates cannot be
      written without them -- scaffolding, and gone the moment the
      real core.clj loads.

      Its name was wrong too: `gc_core.clj` reads as part of the
      collector, when it targets the GC-backed evaluator and is not a
      core at all.

      **What the oracle measures, after the correction.** 59 of 86
      expressions agree; the 27 that differ name exactly what real
      core.clj must supply:

          <= > >= contains? dec distinct drop even? filter inc
          interpose into last map max merge min neg? odd? pos? range
          reduce reverse sort take vec zero?

      That is a better number than the 86/86 it replaced, because it
      measures the right thing: **how much of real core.clj the
      evaluator can already carry.** It closes by growing the
      evaluator, never by growing host.clj.
      ### Pointing it at the real core.clj

      `clotran-gc some.clj` now loads files named on the command line,
      so the real core.clj can be tried against this evaluator and the
      first error it reports IS the next thing to build. Two bugs of
      mine had to go first:

      - **The file loader was O(n^2).** It appended line by line, and
        each `//` builds a whole new string. On an 8371-line file that
        is not slow, it is indistinguishable from a hang. Now one
        `inquire(size=)` and one stream read. LispReader.f90 carries
        the same warning in two places; I repeated the mistake anyway.
      - **The reader could fail to advance.** core.clj opens with
        `^{...}`, the reader has no case for `^`, so it fell through to
        read_atom, produced an EMPTY token, and never moved `pos` --
        an infinite loop. A reader that can hang is far worse than one
        that errors, so an empty token is now an error naming the
        character it could not dispatch.

      With both fixed it fails in a second, usefully:

          load src/clj/clojure/core.clj: reader error:
            reader: no dispatch for '^'

      ### seq is the abstraction, and it was missing

      Caught in review, and correctly: the evaluator had no seq
      abstraction. Every operation dispatched on concrete type at its
      own call site --

          if (lazy) ... else if (list) ... else if (vector) ...

      repeated in first, rest, count, empty?, seq and second. That is
      not a style complaint: each chain was an independent chance to
      forget a branch, and one of them did. `rest` silently omitted
      vectors, which made `reduce` return its first element and `last`
      return its first -- both looking like arithmetic bugs.

      Two more consequences that had not been noticed:

      - `rest` on a vector COPIED the tail, so walking a vector was
        O(n^2) where Clojure's is O(1).
      - Strings and maps were not seqable at all. `(first "abc")` and
        `(first {:a 1})` both returned nil.

      **`OBJ_SEQ` is now a seq VIEW over an indexable collection** --
      slot 1 the source, i1 the index. `rest` bumps the index and
      shares the source, so it is O(1) and allocates one small object
      rather than copying. Lists and lazy seqs need no view because
      they ARE seqs, which is the same split real Clojure makes:
      PersistentList implements ISeq, PersistentVector does not and
      hands out a ChunkedSeq.

      **`to_seq` is now the only place that knows concrete types.**
      Adding a seqable type means teaching it and nothing else. first,
      rest, second, count, empty? and seq all go through it.

      Strings and maps came for free: `(first "abc")` is `\a`,
      `(first {:a 1})` is `[:a 1]` -- an entry, which is what lets
      destructuring walk a map. Nine new oracle cases, all agreeing
      with real Clojure; 68 of 95 now.

      One thing this does NOT change: the old evaluator (RT.f90) has
      the same per-type dispatch, which is where the shape was
      inherited from. It is not worth fixing there -- that code is
      being replaced -- but it is worth knowing the bug class existed
      in both.

      ### Should everything be built on seq? No -- Clojure does not

      Clojure keeps two layers, and conflating them would be wrong:

      - **collections** -- conj, assoc, get, nth, count: type-specific
        ON PURPOSE. `(conj [1] 2)` appends, `(conj (list 1) 2)`
        prepends, `(conj {:a 1} [:b 2])` assocs. That difference is
        the feature.
      - **sequences** -- first, rest, next, cons: uniform, over seqs.

      Only the second layer routes through `to_seq`. Measured rather
      than assumed: after the seq work, **3 of 32 builtins** still
      dispatched on concrete type -- conj, cons and nth -- so this was
      a three-function fix, not a refactor.

      `conj` stays type-specific (and gained the map case it was
      missing). `cons` and `nth` now go through seq, which is what
      real Clojure does: `(cons 1 "ab")` is `(1 \a \b)` and
      `(nth (range 5) 2)` is 2, neither of which has an index.

      **Two bugs this introduced, both instructive.**

      `(cons x ())` broke macro expansion. An empty tail seq's to nil,
      so cons took the not-a-list branch and built a lazy cell rather
      than a list -- and the evaluator only recognises a LIST as a
      form, so every macro returned its own expansion unevaluated.
      Three checks caught it immediately.

      `(cons n (from (+ n 1)))` then hung, because `to_seq` FORCES a
      lazy seq. Forcing there is not a slowdown, it is an infinite
      loop: building one cell realises the whole infinite seq. A lazy
      tail is now taken as-is and never seq'd.

      **And a flaw in how I was verifying.** That second bug showed up
      as a SEGFAULT under flang while gfortran looked clean -- because
      I was counting `FAIL` lines, and a crash prints none. The test
      had died, not passed. Check the **exit status**; a grep count
      cannot tell a clean run from a dead one. flang caught it purely
      because its stack gave out first.

      ### Metadata, and the reader now parses all of core.clj

      `OBJ_META` became a WRAPPER -- slot 1 the value, slot 2 the
      metadata -- rather than a field, because `gc_value` has no spare
      component (the point of it) and because symbol text is INTERNED,
      so metadata hung off a string-pool slot would apply to every
      `foo` in the program.

      The wrapper's cost is that consumers must see through it. That
      is contained by unwrapping in exactly one place: `gce_eval`
      evaluates the value inside, so metadata is invisible to every
      form that does not specifically ask. Only `def` and `meta` look.

      The payoff is the core.clj bootstrap working:

          (def ^{:macro true} m (fn* [a] (quote :expanded)))
          (m ignored)   =>   :expanded

      which is how let, loop and fn become macros at core.clj line 32,
      before defmacro exists.

      **Reader dispatch.** `#` is a dispatch character, not a symbol
      character, and treating it as the latter is not harmless:
      `#{1 2 3}` read as the symbol `#` followed by a three-element
      map, and the error was "map literal has an odd number of forms"
      -- nowhere near the cause. Added: `#_` discard (of the next
      FORM, not token), `#'` var, `#{}` sets, `#()` anonymous fns,
      `#""` regex literals.

      Sets are `OBJ_SET`, backed by a map from each element to itself
      -- what PersistentHashSet does -- but a distinct kind, so they
      print as `#{...}`, answer `:set`, count elements rather than
      pairs, and seq as elements rather than entries. The backing map
      is representation and stays hidden.

      `#()` takes its arity from the HIGHEST %n used, not the count:
      `#(+ %2 %2)` is a two-argument function. Parameter names are
      fixed rather than gensymed, so a body binding `p1` would shadow
      -- noted where it is written, and waiting on auto-gensym.

      **The reader now parses all 8371 lines of real core.clj.** It
      fails in evaluation instead:

          load src/clj/clojure/core.clj: 'ns' not found
            in form: (ns #<object>)

      which is the right kind of failure: a missing function rather
      than a syntax the reader cannot represent.

      One oracle case had to be dropped rather than fixed: set PRINT
      ORDER differs from Clojure's, and both are unordered, so the
      comparison was meaningless. Order-independent set facts are
      checked instead.

      ### Metadata: not lost, unported

      `clotran-bin` supports metadata fully -- `^`, `with-meta`,
      `meta`, Var metadata. `clotran-gc` does not yet. Checked:
      `(meta (with-meta [1] {:a 1}))` is `{:a 1}` on the old
      evaluator and `with-meta not found` on the new one.

      It is load-bearing rather than decorative, and core.clj proves
      it at line 32 with Rich Hickey's own comment:

          ;during bootstrap we don't have destructuring let, loop or fn
          (def ^{:macro true} let (fn* let [&form &env & decl]
                                    (cons 'let* decl)))

      Macro-ness IS `:macro true` in a Var's metadata; `defmacro` only
      sets it for you. So a reader that parses `^` and discards it
      produces a core.clj where nothing is a macro.

      That also narrows the design question below: what needs metadata
      first is the **Var**, and `OBJ_VAR` slot 2 is already reserved
      for it. `(def ^{...} name val)` may be reachable without solving
      metadata-on-any-value at all.

      ### The next blocker, and it is a real design question

      **Metadata cannot simply be dropped.** core.clj defines `let`,
      `loop` and `fn` as `(def ^{:macro true} name (fn* ...))` before
      `defmacro` itself exists -- so a reader that parses `^` and
      discards it produces a core.clj where nothing is a macro.

      But there is nowhere to put it. `gc_value` is {tag, ival, rval,
      ref} and deliberately has no spare component -- that is the
      entire point of the new representation. Worse for symbols: text
      is INTERNED, so two `foo` symbols share one string-pool slot,
      and metadata hung off that slot would apply to every `foo` in
      the program. Real Clojure has no such problem: a Symbol is an
      object with its own metadata, equal to but distinct from another
      `foo`.

      Options, none obviously right:

      1. **Wrap**: a metadata-bearing value becomes an `OBJ_META`
         holding {value, metadata}. Contained if unwrapping lives in
         one accessor, invasive if it does not -- every consumer must
         see through it.
      2. **Un-intern symbols**: give each its own object with a meta
         slot. Costs an allocation per symbol and makes symbol
         comparison a text compare rather than a slot compare, on the
         hottest path in the interpreter.
      3. **A side table** keyed by value identity -- which does not
         exist for interned text, so this reduces to (2).

      Settle before writing any of it. The old representation dodged
      this by giving every `cons_value` a `meta_val` component, which
      is exactly the nine-allocatable-component design being removed.

      Three bugs the bootstrap found that 266 unit tests had not:

      - **`rest` did not handle vectors**, so `(rest [1 2 3])` was nil
        and every seq walk over a vector stopped after one element.
        `reduce` returned its first element and `last` returned its
        first -- both looking like arithmetic bugs rather than a seq
        bug.
      - **A non-advancing `read` reports end-of-RECORD as a negative
        iostat**, exactly as end-of-file does, so the file loader
        stopped after line one and silently loaded nothing. Standard
        Fortran, easy to write, invisible without a diagnostic.
      - Auto-gensym (`sym#` in a syntax-quote) is missing from the
        reader.

      34 host primitives, and the split stays a dial rather than a
      wall: a primitive can move into Fortran when measurement says
      so. What must NOT happen is re-implementing core.clj in either
      language.

      **The new stack is now complete and proven end to end:** vector,
      list, array map, hash trie, promotion, environment, printer,
      reader, evaluator -- 21 suites green on both compilers. Real
      Clojure text is read, evaluated and printed entirely in the new
      representation, under a collector running at maximum paranoia. Closure and atom need no module of their
      own. What remains for 3c-2/3d is the switch itself: `cons_value`
      becomes a handle, the evaluator moves onto the value stack, and
      `Values.f90`'s old backing types go.
- [ ] **3e.** Retire `FINAL`-based refcounting; `rc_test` becomes a GC
      test. Finalizers survive only on the few heap nodes owning
      foreign resources, run once per object by sweep rather than once
      per copy.

Gate: `rc_test`, 226 `eval_test` checks and the upstream suite all pass
under torture mode. This is a branch, and it is genuinely big-bang at
step 3c.

### 4. Load clean, load fast

Everything after this step is paid for by the edit-test loop, so make
the loop cheap before starting on the expensive steps.

- [ ] **4a.** Point `scripts/run-clojure-tests` at `clotran-gc` and get
      it green. This is now the step that matters most: the suite is
      Clojure's own assertions over the real core.clj functions, where
      `scripts/gc-oracle` is 107 cases someone wrote by hand. Expect it
      to drop hard at first -- that is the signal being asked for.

      Two things it will force, both wanted:

      - **Retire `clotran-bin`.** ~9,300 lines of the original
        evaluator go once the suite passes on the GC one. That deletion
        is what the whole GC effort was for, and keeping two evaluators
        means every fix has to be considered twice.
      - **Startup cost becomes the bottleneck.** The runner launches a
        process per namespace, so ~40 namespaces x 1.68s is around a
        minute of pure loading per run. Annoying, not blocking -- but it
        is what finally makes 4c worth doing.

- [x] **4a'. The gfortran-only crashes.** Three real bugs, none of them
      a gfortran defect. Found with `-fcheck=all -fbacktrace`, which is
      worth reaching for first every time: the raw crash was SIGTRAP
      inside `malloc` at an unrelated `allocate`, and named nothing.

      1. **Missing Fortran 2018 recursion semantics.** F2018 makes every
         procedure recursive by default; flang follows it, gfortran
         still defaults to F2008, where a procedure not marked
         `RECURSIVE` may keep its locals in *static* storage. Re-enter
         it and the outer invocation's variables are overwritten.
         gfortran rejects *direct* recursion at compile time, which is
         why this hid for so long -- but an evaluator is mutually
         recursive everywhere (`eval_form` -> `eval_let_head` ->
         `eval_form`), and so is refcounting (`release` -> `deallocate`
         -> `final` -> `release`). Fixed with `-frecursive` in the
         Makefile, which is exactly flang's semantics. `-std=f2018`
         does **not** do it (checked on gfortran 16). Rejected marking
         ~200 procedures by hand: this is one build-level property, not
         an annotation per procedure.
      2. **Non-short-circuiting `.and.`** at `Eval.f90`'s
         `eval_instance_call`: `target%tag == TAG_KEYWORD .and.
         names_a_class(target%str_val)` evaluated the right operand for
         every target, passing an *unallocated* `str_val` as an actual
         argument whenever the target was not a keyword. Same trap as
         `resolves_to_macro`; fixed the same way, by nesting. flang read
         whatever was there and carried on.

      Those two fix the *deterministic* `multimethods` crash, and a
      clean run of the whole suite is 163/16/41 on both compilers.

      Correction: an earlier note here said they fixed `multimethods`
      "permanently". That was claimed on two sampled runs and is wrong.
      `multimethods` now fails the same way `logic` does -- sometimes,
      with the 4a'' signature below. Two samples are not evidence of
      absence for a 1-in-6 bug; take ten.

- [ ] **4a''. An intermittent use-after-free (~1 run in 6).** Hits
      whichever namespace happens to trip it -- `logic` and
      `multimethods` both do. Not the same class as the two above, and
      not fixed:

      ```
      node_ref_release -> cons_value_release -> cons_value_finalize
      Index '1' of dimension 1 of 'h...%children' above upper bound of 0
      ```

      What is established, by instrumenting `node_ref_release` to report
      any entry on a non-positive refcount:

      - The refcount read is **-675019966** -- garbage, not `0` or `-1`.
        So this is not a double-release of a live node; `h%ptr` points
        at memory that is no longer a `vec_node` at all. A `node_ref`
        outlived the node it referenced: a **missing increment**, not an
        extra decrement.
      - It is **not** a defined-assignment dispatch failure. The
        suspicion was `node_assoc`'s bulk slice copy
        (`new_node%children(1:n) = node_in%ptr%children(1:n)`) silently
        falling back to intrinsic assignment and skipping the refcount
        bump -- the same shape as the `hamt_slot` problem already in
        NOTES. Disproved with an isolated probe: both compilers
        dispatch to the elemental defined assignment, 4 calls for 4
        elements, slice and whole-array alike.
      - Every `_assign` *is* in the `assignment(=)` interface, and
        `cons_value_assign` does release the LHS before copying.
      - It is reached from `cons_value_finalize`, i.e. the compiler's
        own finalization, not from an explicit release.

      So the remaining candidates are the paths where a `node_ref` is
      copied WITHOUT defined assignment: function results, `intent(out)`
      dummies, and component finalization of the types that have no
      `FINAL` of their own (`vec_t`, `closure_t`) and rely on the
      standard cascading into their components.

      **Recommendation: do not root-cause this further.** Every routine
      in the failing path -- `node_ref_release`, `cons_value_release`,
      `cons_value_finalize` -- is deleted by 3e. Refcounting is the
      subsystem being replaced, and this is a bug *in the thing being
      thrown away*. The GC finds this class of fault deterministically
      (`gc_check_heap` under torture) where this takes six runs to
      reproduce once.

      It does not block 3c-1, which is a mechanical refactor with the
      representation unchanged. It is an argument for getting to 3c-2
      and 3e promptly rather than lingering in 4a.

      **Update, after 3c-1.** The migration made this fire much harder
      on gfortran. Measured over six runs after all six payloads:
      `multimethods` crashes **every** run, `logic` 2 of 6. gfortran
      never reaches 163 any more; its best is 161 and its worst 51.
      flang is unaffected at 163/16/41 every run, and both compilers
      pass all twelve unit suites.

      So the accessors are correct -- each is assign-then-return,
      refcount balanced, and the oracle agrees. What changed is that
      value-level accessors create more temporaries, so more refcount
      traffic goes through the broken path. A latent bug that fires
      reliably is more useful than one that fires sometimes, but be
      clear about the cost: on gfortran this went from unreliable to
      unusable on `multimethods`.

      With the deterministic repro, two more things are now known.
      Poisoning a `vec_node` instead of freeing it and checking for the
      poison on entry proves it exactly:

      - **A `vec_node` is released after it has already been freed**,
        and the second release arrives through `cons_value_release`'s
        explicit call, not through finalization. So two `cons_value`s
        hold a `vec_t` pointing at the same node with only one
        increment between them: a missing increment, confirmed, not an
        extra decrement.
      - **It is not the copy-in/copy-out hazard.** The obvious suspect
        was `call node_ref_release(v%vector_val%root)` -- an
        `intent(inout)` actual whose type has a `FINAL` -- nulling a
        copy while the original stayed pointing at freed memory.
        Dropping the explicit release and relying on `deallocate`'s
        cascade changes nothing. Disproved.

      Also ruled out: AddressSanitizer. The gfortran build runs `logic`
      to completion under ASan with no report at all, because its
      allocator does not recycle the freed node into the path that
      trips it. `-fcheck=all` says nothing either -- a dangling pointer
      is invisible to bounds and recursion checks.

      **Every compiler-mechanism hypothesis is now eliminated.** Each
      was checked with an isolated probe on BOTH compilers, and all
      four behave correctly:

      | suspected mechanism | verdict |
      | --- | --- |
      | bulk slice assign skipping defined assignment | correct, 4 calls for 4 elements |
      | array constructor copying a ref without a bump | correct, refcounts balance |
      | function result of a type whose *component* has the FINAL (`vec_t`'s exact shape) | correct, one finalize of the temp |
      | copy-in/copy-out on `intent(inout)` with a FINAL | not it -- removing the explicit release changes nothing |

      That matters more than any single one of them: **the bug is in
      this codebase's own logic, not in a compiler behaviour we
      misunderstood.** It is findable by reading the code that shares a
      `vec_t` between two `cons_value`s, and it does not need another
      compiler experiment.

      **There is now a minimal repro: `test/clj/uaf_repro.clj`.** It
      runs in seconds instead of a 30-second suite sweep, crashes ~6
      runs in 8 on gfortran, and is deterministic under the poison
      instrument its header describes. It was reduced from
      `multimethods`' `methods-test`, and **it crashes identically on a
      tree with the 3c-1 accessors stashed** -- which is the proof that
      3c-1 exposed this rather than caused it.

      Two facts the reduction handed over:

      - **The bare forms do not crash.** `defmulti`/`defmethod`/
        `remove-method`/`methods`/`into #{}` at the top level are fine.
        It needs `deftest`/`testing`/`is` around them -- i.e.
        clojure.test's *dynamic bindings* and its report machinery.
        That points at the `binding` stack (`atom_node%dyn_stack`, an
        allocatable array of `cons_value` grown and shrunk with
        `move_alloc`) rather than at vectors, even though a `vec_node`
        is what dies.
      - **The corruption and the crash are in different places.** The
        fault is a stale `node_ref`; the SIGTRAP lands later at an
        unrelated `allocate` in `node_assoc`. Reading the backtrace
        alone was never going to find this, which is why the poison
        instrument matters.

      **Mitigated, not fixed: `node_ref_release` no longer frees.**
      Leaking the `vec_node` makes the premature free harmless, and the
      measured cost is small -- bootstrap RSS 93 MB against 84 MB,
      about 10%. In exchange gfortran goes from "multimethods crashes
      every run" to **163/16/41, identical to flang**, three runs in a
      row, with every unit suite green on both compilers.

      That trade is worth taking because gfortran is the default build
      and the one most people will use, and because step 3e deletes
      this refcounting outright: the GC frees these by tracing, so the
      missing increment stops mattering rather than needing to be
      found. Ceiling: a long-running process building many vectors
      grows without bound. If 3e slips, fix the bug instead -- the
      repro plus the poison instrument finds it in one run.

      **Bisect: attempted, and it does not isolate this.** Two things
      worth recording so nobody repeats them:

      - The first run was invalid. The harness accepted any commit that
        printed a `:type :summary`, but the bisect-specific repro used
        fully-qualified `clojure.test/deftest`, which does not register
        a test -- every commit ran **0 assertions** and looked "good".
        It accused a docs-only commit, which is what gave it away. A
        bisect harness has to assert that the test genuinely ran, not
        merely that it finished.
      - With a correct harness (force `FC=gfortran` and `-frecursive`
        at every commit, since older trees default to flang and
        pre-date that fix; require `Ran N tests containing M
        assertions` with M > 0), **every commit back to `a3bb429` is
        bad** -- 22 commits, and further back the repro cannot even be
        expressed because `:refer` did not exist yet. The bug predates
        the earliest commit that can express it. It is old code, not a
        regression, and bisect has nothing to bracket.

      Correction to an earlier note here: this entry previously said
      "pre-existing" on the strength of stashing `src/f` and rebuilding.
      That test was worthless -- 3c-1 was already committed, so the
      stash removed nothing relevant. The conclusion happens to be
      right, but the evidence for it is the bisect above (`931c93a`,
      which predates every accessor commit, is bad), not that stash.
- [ ] **4b. Integer opcodes.** `eval_form` dispatches special forms by
      a cascade of string comparisons: 5.26 ns for ten of them, against
      0.09 ns for an integer `select case`, and there are ~30.
      Invisible under 497 ns copies, very visible after. `pre_expand`
      already walks every form at definition time, so it can stamp an
      integer id on each list node -- most of a VM's dispatch win
      without becoming one.
- [ ] **4c. Bootstrap cache.** UNBLOCKED: the GC exists and its heap is
      index-based, so it serialises almost for free -- which is most of
      a cache. Snapshot after core.clj and start from that.

      The old fallback -- caching expanded forms as text -- is moot now:
      it saved macroexpansion but not evaluation, and on `clotran-gc`
      analysis is only ~4% of the 1.68s startup anyway (profiled: 218
      samples in `mx_walk` against 3603 in `gce_eval`). The cost is
      RUNNING core.clj, which only a heap snapshot avoids.

      Key must include every `.clj` loaded *and* the binary, since both
      expansion and evaluation depend on the evaluator.

### 5. Concurrency -- STM, agents

Before the debugger, not after. The debugger's central object is the
CallInfo frame array plus the `*break-handler*` Var, and under threads
both are per-thread: a frame stack belongs to a thread, and "which
thread is stopped" is part of every command. Building the debugger
first means building it twice.

The same argument applies backwards to step 3, which is why the
collector needs **safepoints** designed in now even though nothing is
threaded yet -- a stop-the-world mark-sweep is fine with threads, but
only if every thread can be brought to a known point. Cheaper to leave
the hook in during 3c than to retrofit it.

`binding`'s stack and `dosync`/refs are placeholders waiting on this
and should be revisited together. Three things to settle:

- **The substrate is unanswered.** OpenMP (both compilers support it,
  gives locks and atomics, but fork-join around parallel regions
  rather than long-lived workers), pthreads via `iso_c_binding`
  (general, but Fortran runtime thread-safety is compiler-dependent,
  and flang's runtime is already the dominant cost -- assuming it is
  reentrant from a raw pthread is a large assumption), or coarrays
  (wrong model: images have separate memory, SPMD rather than
  shared). Settled by a spike -- *can two OpenMP threads each run an
  independent clotran evaluation without corrupting flang's
  runtime?* -- not from the armchair.
- **core.async is not free.** `go` is a CPS/state-machine transform
  depending on `tools.analyzer`, and the impl namespaces use Java
  executors and locks. The blocking ops (`chan`, `>!!`, `<!!`,
  `thread`) are the attainable target; `go` is not.
- **Interop thread-safety.** Many Fortran libraries are not
  thread-safe (module `save` variables, COMMON blocks, shared
  workspace). The binding generator needs a per-library declaration
  and must serialize calls into unsafe ones. And a `native_array` is
  shared *mutable* memory that STM does not cover -- a ref protects
  the reference, never the array's contents. That gap needs a
  decision before agents exist.

### 6. Debugger

- [ ] CallInfo frame array, populated from the positions in step 1,
      pushed at apply. Must record frames elided by tail calls: the
      trampoline reuses a frame for `recur`, so a deep `loop` shows one
      frame, and a trace that does not say so is misleading.
- [ ] `*break-handler*` Var + the state contract above
- [ ] step in / over / out -- one check at the top of `eval_form`
- [ ] eval-in-frame (nearly free: envs are name->value chains)
- [ ] terminal nested-REPL handler, written in clotran
- [ ] framed stdio wire + an editor-facing handler, written in clotran

## Should we JIT?

Recorded so it does not get re-argued. Short answer: not now, and when
the reasons to do it arrive, most of them will have better answers.

### The thing that prompted it

Clojure is NOT interpreted. Every form, REPL-typed included, goes read ->
`Compiler.analyze` -> JVM bytecode -> load -> invoke. ClojureScript is a
compiler too. clotran is a tree-walking interpreter, so it is the odd one
out, and a run of Clojure's own test suite surfaced the cost as a cluster
of name-resolution bugs: an alias resolved at call time against the wrong
namespace, an unqualified symbol falling back to `clojure.core`,
`__defining-ns__` read from `*ns*` instead of inherited. SEAMS.md has the
argument; DEVIATIONS 16 is the ledger entry.

The tempting conclusion is "so we should compile." It does not follow.

### Compiling to Fortran and growing a binary -- no

An executable cannot be appended to, and Fortran has no `eval` and no
runtime linking in the standard. The workable version is: emit `.f90`,
shell out to gfortran, build a SHARED LIBRARY, `dlopen` it. Real
technique -- Fortran auto-tuners do it -- but here:

- gfortran costs ~100ms-1s per invocation, so it loses to interpreting
  for everything except a genuinely hot loop.
- Generated code still has to cooperate with `gc_value`, the shadow
  stack and the collector. Every compiled function roots its own
  temporaries or the GC eats them.
- `dlopen` is POSIX, not Fortran, so it needs a C shim. We have
  precedent in `src/c`, but it is not free.

### LLVM, the way jank does it -- coherent, but a different project

jank (https://jank-lang.org) compiles Clojure to LLVM IR and JITs it in
process, with C++ interop. That is the right shape for a compiled native
Clojure, and the clotran analogue is real: the analyser emits LLVM IR
directly, ORC JITs it, and the Fortran becomes the RUNTIME LIBRARY the
compiled code calls -- exactly what `clojure.lang` is to the JVM.

Note what that is not: **flang does not help.** flang is a Fortran
frontend; it turns Fortran source into LLVM IR. clotran's special forms
are not Fortran source, so "clotran + flang" collapses back into
generating Fortran text and invoking a compiler on it -- the slow shared
library path again.

Note also what it costs conceptually. It is not a JIT for Fortran. It is
a JIT for Clojure in which Fortran stops being the host and becomes the
runtime. The premise of this project is that Fortran IS the host. That is
a fine thing to change one's mind about, but it should be changed
deliberately and not arrived at sideways while chasing a startup time.

### What to do instead, in order

1. **Resolve names in `gce_analyze`.** It already runs once per
   top-level form, deliberately mirroring `Compiler.analyze`, and its
   entire body today is `macroexpand_all`. Doing resolution there,
   lexically, with the namespace known, retires the whole bug class
   above. No new technology, no codegen, and it is what an interpreter
   is supposed to do.
2. **Cache the analysed core.clj** (step 4c). Startup is the cost anyone
   actually notices, and an image fixes it without machine code.
3. **Closure-compile the analysed tree.** Have the analyser emit nested
   closures instead of re-walking S-expressions on every call. The
   classic interpreter 5-10x, still no toolchain.
4. **Only then** measure, and if the profile still demands it, do it
   jank's way -- LLVM IR and ORC -- rather than generated Fortran.

Steps 1-3 are each smaller than the JIT and each removes one of the
reasons to want it.

## Deferred, deliberately

- **`deftype`/`defrecord`/`reify`** -- need the `deftype*` special form.
  `defprotocol`/`extend-protocol` already work.
- **`genclass.clj`, `core_proxy.clj`** -- JVM bytecode generation.
  Never.
- **CIDER/nREPL wire compatibility** -- bencode framing and a protocol
  contract. A separate decision, not constrained by step 6.
- **Passing a clotran array to a real Fortran procedure.** Storage is
  deliberately ready (contiguous, column-major, declared kind); the
  binding generator is the missing half.

## Open questions

- Does the value-stack port have to be atomic across Eval/RT/printer,
  or can the inline-scalars trick in 3c stage it further?
- Frames for every call, or only non-tail ones? Pushing per call
  measures as free, so this is about trace readability.
- Where does the Fortran binding generator read type information from
  -- parsing `interface` blocks, or a declaration written in clotran?

# bugs

user=> (+1 1)
Error: "not a function: 1"

should not be reported at " 1"

this works as it should:
user=> (++1 1)
Error: "'++1' not found"