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
| `eval_test` | 232/232, flang and gfortran |
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

### 2. Metadata in `pr_str`

The printer does not emit metadata, so anything that round-trips a form
through text silently drops `^:dynamic`, `:arglists`, `:test`. Needed
for correctness on its own, and a prerequisite for any form cache.

### 3. The GC -- nothing built yet

- [ ] **3a.** Heap module: typed node arrays (one per node kind) with
      free lists, a handle type, an allocator. One array per kind
      because Fortran cannot cast -- a single untyped blob would mean
      `class(*)` everywhere and buy back the dispatch cost we are
      removing.
- [ ] **3b.** Mark-sweep collector + torture mode (collect at every
      allocation) + `gc_test.f90`, standalone. Working and tested
      before anything else depends on it.
- [ ] **3c.** Value type: drop the nine allocatable components and
      `FINAL`; keep the inline scalars (`tag`, `int_val`, `real_val`,
      `bool_val`) so `v%tag` and friends keep working, and replace only
      the allocatable components with one handle. Smaller blast radius
      than a full rewrite, same win.
- [ ] **3d.** Evaluator on the value stack.
- [ ] **3e.** Retire `FINAL`-based refcounting; `rc_test` becomes a GC
      test. Finalizers survive only on the few heap nodes owning
      foreign resources, run once per object by sweep rather than once
      per copy.

Gate: `rc_test`, 226 `eval_test` checks and the upstream suite all pass
under torture mode. This is a branch, and it is genuinely big-bang at
step 3c.

### 4. Integer opcodes

`eval_form` dispatches special forms by a cascade of string
comparisons: 5.26 ns for ten of them, against 0.09 ns for an integer
`select case`, and there are ~30. Invisible under 497 ns copies, very
visible after. `pre_expand` already walks every form at definition
time, so it can stamp an integer id on each list node -- most of a VM's
dispatch win without becoming one.

### 5. Debugger

- [ ] CallInfo frame array, populated from the positions in step 1,
      pushed at apply. Must record frames elided by tail calls: the
      trampoline reuses a frame for `recur`, so a deep `loop` shows one
      frame, and a trace that does not say so is misleading.
- [ ] `*break-handler*` Var + the state contract above
- [ ] step in / over / out -- one check at the top of `eval_form`
- [ ] eval-in-frame (nearly free: envs are name->value chains)
- [ ] terminal nested-REPL handler, written in clotran
- [ ] framed stdio wire + an editor-facing handler, written in clotran

### 6. Bootstrap cache

After the GC, with an index-based heap, the heap serialises almost for
free -- which is most of a cache. Until then: caching expanded forms as
text saves the 15.6 s of macroexpansion but not the ~13 s of
evaluation, and needs step 2 first or it silently drops metadata. Key
must include every `.clj` loaded *and* the `clotran-bin` binary, since
expansion depends on the evaluator.

## Deferred, deliberately

- **Concurrency.** A Rust-inspired model, not a JVM thread port.
  `binding`'s thread-local stack and `dosync`/refs are both placeholders
  waiting on it, and should be revisited together.
- **`deftype`/`defrecord`/`reify`** -- need the `deftype*` special form.
  `defprotocol`/`extend-protocol` already work.
- **`genclass.clj`, `core_proxy.clj`** -- JVM bytecode generation.
  Never.
- **CIDER/nREPL wire compatibility** -- bencode framing and a protocol
  contract. A separate decision, not constrained by step 5.
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
