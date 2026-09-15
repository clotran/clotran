# Plan

A living document. NOTES.md records what was built and why it works the
way it does; this records what we are about to build, what we decided
not to build, and why -- so decisions don't have to be re-argued from
scratch.

## Where we are

Measured, not estimated:

| | |
| --- | --- |
| core.clj load | 9 failing forms of 728 |
| `eval_test` | 239/239, flang and gfortran |
| Clojure's own suite (`scripts/run-clojure-tests`) | 163 assertions passing, 6 namespaces |
| startup (bootstrap) | ~28s, of which ~15.6s is macroexpansion |
| one `cons_value` copy | **497 ns** |
| share of runtime in flang's derived-type machinery | **94.7%** |

That last row is the headline. It is not allocation cost and not
garbage collection cost -- it is the cost of *copying a value*, paid on
every assignment, because `cons_value` has a `FINAL` binding and nine
allocatable components. Measured on identical data:

| type shape | ns per copy |
| --- | --- |
| scalars only, no `FINAL` | 4.1 |
| + pointer component, no `FINAL` | 8.9 |
| + pointer component, **with `FINAL`** | 133.8 |
| `cons_value` (9 allocatable components + `FINAL`) | 497 |

Everything below follows from that.

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

### 3. The GC -- collector built, not yet wired in

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
- [ ] **3d.** Evaluator on the value stack.
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

- [ ] **4a.** The 9 remaining `core.clj` failures, and the upstream
      suite green. Independent of the GC, but the baseline has to be
      *stable* before 3c or a new failure can't be attributed.
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
- [ ] **4c. Bootstrap cache.** After the GC, with an index-based heap,
      the heap serialises almost for free -- which is most of a cache.
      Until then: caching expanded forms as text saves the 15.6 s of
      macroexpansion but not the ~13 s of evaluation, and needs step 2
      first or it silently drops metadata. Key must include every
      `.clj` loaded *and* the `clotran-bin` binary, since expansion
      depends on the evaluator.

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
