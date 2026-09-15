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
- [ ] **4a'. The gfortran-only crashes.** A gfortran build crashes
      `test-clojure.multimethods` every run and `test-clojure.logic`
      intermittently (51 or 161 assertions depending on the run);
      flang gives 163 every time. Intermittent under one compiler and
      not another means undefined behaviour in *this* code that flang's
      codegen masks -- a real latent bug, not a gfortran defect, and
      the most valuable thing the second compiler has found. Worth
      doing before 3c: 3c-2 rewrites the value representation, and
      hunting a live memory bug through that change is much harder
      than hunting it now.
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
