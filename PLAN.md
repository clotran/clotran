# Plan

A living document. NOTES.md records what was built and why it works the
way it does; this records what we are about to build, what we decided
not to build, and why -- so decisions don't have to be re-argued from
scratch.

## Where we are

Measured, not estimated. Re-measure before editing this section; it has
been stale before.

There are TWO evaluators in the tree. `clotran-gc` is the GC-backed one,
the one `./clotran` runs and the one being built on. `clotran-bin` is the
original, pre-GC, kept only because the mal regression suites still drive
it; retiring it is step 3.

| | `clotran-gc` | `clotran-bin` |
| --- | --- | --- |
| core.clj | **724 of 724 forms**, loads completely | 9 failing forms |
| startup | **6.8s** | 5.4s |
| our tests | 1145/1145, both compilers | green, both compilers |
| Clojure's own suite | **766 pass / 111 fail / 267 error** over 196 tests | not run against it |
| Clojure's libraries | **15 of 21 load** | not measured |
| source | 11,200 lines | 10,929 lines |

Startup went UP, from 1.68s, and that is not a regression to chase: we
load all 724 forms now rather than 615, and far more of them do real work.
core.clj is re-read and re-analysed on every launch. An image (step 4c)
is the fix; nothing else will move it much.

The three scorecards, and what their denominators exclude:

- **our tests** are a GATE, not a grade. 100% or do not commit. Two
  suites now: `test/f` (1030) runs against the BASE environment, with
  no core.clj, which is the right place for a special form and cannot
  reach anything built on one; `test/clj/language_test.clj` (37) runs
  with core.clj loaded, and covers deftype, defrecord, reify,
  protocols and letfn -- none of which test/f can see. `make test`
  greps it for a final PASSED marker, so a crash part-way through
  fails too.
- **Clojure's suite** is 67 vendored namespaces. 8 still crash before
  reporting anything, so they contribute ZERO assertions to both halves
  of the pass rate: 766/1144 is over assertions that EXECUTED, not
  assertions that exist. Only 19 of 67 namespaces produce a single
  passing assertion, and that 28% is the more honest headline.
  Several of the 67 can never pass here -- `proxy`, `genclass`,
  annotations, AOT -- and they have not been subtracted, deliberately.
- **libraries loading** is the measure that moves when a host member
  lands. `set`, `data`, `edn`, `datafy`, `walk`, `string`, `template`,
  `zip`, `stacktrace`, `test`, `inspector`, `reflect`, `parallel`,
  `core.protocols` and `core.reducers` load today -- the last of those
  needed `clojure.lang.Delay`, which arrived with the core.clj tail.

  LOADED means a var of theirs RESOLVES afterwards, not that `require`
  returned without complaint. `clojure.uuid` is skipped by name, so
  requiring it succeeds and defines nothing; counting that as a load is
  how this number was once too high. Re-measure with a resolve, not an
  absence of errors.

**core.clj loads completely: 724 of 724 forms.** There is no wall left
in it, which has not been true before, so the measurement that used to
lead this section is now just a number rather than a target.

What the last two were, since the shape is worth knowing:

- **708** was `(try (load-data-readers) (catch Throwable t
  (.printStackTrace t) (throw t)))`. The reported error named
  `.printStackTrace` -- the HANDLER -- and implementing it would have
  changed nothing, because the handler re-throws. `load-data-readers`
  itself had to succeed. It could not, because `getResources` and
  `enumeration-seq` were missing; both now answer EMPTY, which is the
  honest answer for a host with no classpath to enumerate.
- **711** was `ArrayBlockingQueue`, and `clojure.lang.Delay` behind it.

`tap>` is the one thing in the tail that still does not run: it forces a
delay that constructs a `Thread`, and that is a real seam rather than a
missing member. It fails loudly.

`scripts/split-forms` is how a wall gets located when one appears again.

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

## Start here

If you are picking this up cold: read `CLAUDE.md` first (how we work, and
the oracles), then this section. `README.md` is what clotran is.
`DEVIATIONS.md` is every known difference from Clojure. `NOTES.md` is why
things are built the way they are.

The work is ranked. Each item says what moves and how it is measured.

**1. `deftype*` -- DONE.** It was the wall at form 692; core.clj now
reaches 707. `deftype` and `reify` work, including a method body seeing
its fields as plain names and a reify body closing over its scope.
`defrecord` does NOT: it expands through `letfn`, so it is blocked on
item 5 below and not on anything about types. A type is an object in a
global table -- a name, its fields, a method table, and the class names
it claims -- and no class is generated, because `instance?` is the only
question anything asks of one. SEAMS.md has why this is a real host
seam rather than something we chose to make native; DEVIATIONS 17-20
are what it costs.

**2. The 8 namespaces that crash before reporting.** Was 13; five were
freed by `require` learning `:refer` again. Find them with:

    CLOTRAN_TEST_TIMEOUT=45 ./scripts/run-clojure-tests
    # then, per namespace, load the file alone and read the first error

This item used to say "each is usually ONE missing host member taking
out a whole file". That is NOT true of most of what is left. Measured,
the eight split into two groups:

| namespace | first error |
| --- | --- |
| `api`, `edn` | needs `clojure.test.generative` |
| `generators` | needs `clojure.data.generators` |
| `pprint` | `clojure.lang.PersistentStructMap/createSlotMap` |
| `reflect` | `'0x0001' not found` -- reader gap, now FIXED; re-measure |
| `multimethods` | not yet diagnosed |
| `ns-libs-load-later` | not yet diagnosed |
| `run-single-test` | not yet diagnosed |

The first three want THIRD-PARTY LIBRARIES that are not in
`clojure/clojure` at all -- separate artifacts (`test.generative`,
`data.generators`, and `test.check` and `spec.alpha` behind two more).
They belong with `proxy`, `genclass` and AOT: not reachable without
vendoring someone else's tree, and not a host member anyone can add.

So the small-work-large-unlock framing applies to at most four of them,
and `0x0001` (a reader gap) was the cheapest -- done: the reader now
implements Clojure's three number patterns, so hex, octal, explicit
radix and exponents all read. Whether `reflect` actually leaves the
CRASHED column is unmeasured; the paragraph below is the reason not to
assume it does.

Two SILENT wrong answers fell out of the same gap and are the better
reason the work was worth doing: `077` read as 77 rather than 63, and
`.5` read as 0.5 rather than interning a symbol. Neither shows on any
scorecard.

Worth knowing before starting: a namespace leaving the CRASHED column
does not mean it passes. All five freed by the `:refer` fix went
straight to reporting errors instead -- crashes 13 -> 8, passes
unchanged at 681. The number that moved that day was sequential and set
equality, not the crash count.

**3. The error clusters.** 232 errors, but not 232 causes. Last count, by
frequency: `java.math.MathContext` (10), BigDecimal literals `1M` (8),
ratio literals `2/3` (6), `String/format` (4),
`clojure.lang.RT/seqToTypedArray` (4), `Compiler/macroexpand1` (4).
Re-cluster before working -- the list changes under you:

    ./clotran-gc src/clj/clojure/core.clj < run-one-ns.clj 2>&1 \
      | grep 'actual:' | grep ':error' \
      | sed 's/.*:error "//;s/"}.*//' | cut -c1-44 | sort | uniq -c | sort -rn

`macroexpand1` is worth more than its count: it would make
`macroexpand-1` work, which is the debugging tool most missed here.

**4. `Pattern.split`,** which is all that blocks `clojure.string/split`.
The regex machinery (find_next, group spans) is already there.

**5. `letfn*` -- DONE.** `letfn`, `map-indexed` and `defrecord` all
work. Landing it also meant teaching the generic operations
(`get`, `count`, `seq`, `assoc`, `keys`, `=`, `contains?`) to ask an
instance for its own method, because without that a record answered
nil, 0 and false rather than failing -- and then rewriting sequential
equality, which the new language suite caught answering false for
(= (map inc [0 1]) [1 2]).

**6. Retire `clotran-bin`.** ~10,900 lines of pre-GC evaluator, kept only
because the mal regression suites drive it. Retiring it DELETES the rest
of step 3 below, which is otherwise dead weight in this document. Its
absence is also load-bearing in a way worth knowing: see
`src/clj/clojure/PROVENANCE.md` on why adding a vendored file broke it.

**7. Startup (step 4c).** 6.8s, all of it re-reading and re-analysing
core.clj on every launch. An image fixes it; nothing else will. This is
the first thing any new user notices, and the last thing that blocks
anyone.

**8. Stop writing Java names. Our own vocabulary, in our own tests.**
`src/f` carries **59 distinct `clojure.lang.*` and 29 distinct `java.*`**
string literals, and `test/f` asserts Java names **27 times**. clotran
is Fortran; ClojureScript names `js/Error` and `js/Number` and never
names Java at all. SEAMS.md has the argument -- this is the work.

The split decides the work, so do not treat the 88 as one pile:

- **READ-only, and keep.** `core.clj` writes `(Double/valueOf s)` and
  `(clojure.lang.Util/hash x)`, and running it unmodified is the whole
  premise. Recognising those strings is forced. The change here is to
  put them in ONE translation table instead of scattered across
  `is_host_class`, `static_member`, `instance_member`, `is_instance` and
  `host_super` -- five places that must currently agree by hand, and
  `Double` already proved they do not: `static_member` grew a `Double`
  branch that nothing reached, because `is_host_class` had never heard
  of it.
- **Our tests, and fix.** `(instance? java.util.regex.Pattern p)` and
  `(clojure.lang.Util/hash x)` in `test/f` assert that a JVM-shaped shim
  exists, not that clotran matches or hashes. Rewrite them against
  clotran's own vocabulary so they would survive renaming every Java
  name in the tree. This is the part with no downside and no
  compatibility cost.
- **`instance?` should accept our names too.** `clotran-type` answers
  `:regex`, `:vector`, `:delay`; `(instance? Regex p)` is unwritable.
  Additive, not a replacement -- the Java names keep working because
  core.clj needs them.

The scheme is a PREFIX PER BUCKET, so the name says which seam it is:
`clotran.*` for our own types, `fortran.*` for a real Fortran object
crossing a real boundary, `java.*`/`clojure.lang.*` for read-only
compatibility. Today nothing distinguishes an obligation from a habit
by sight. SEAMS.md has the table.

MIGRATION HAZARD, so it is not attempted casually: `(class x)` is
observable and is the key a protocol's `:impls` map is built on.
Renaming `:vector` to `:clotran.vector` changes every dispatch key at
once, and `host_super` is what keeps a method registered on
`clojure.lang.IPersistentVector` still reachable. Change the tables
and the tests first; change what `class` ANSWERS last, behind the
language suite.

Already correct, and worth not breaking: `type_name` is clotran's own
vocabulary throughout -- `vector`, `map`, `symbol`, `int`, `regex`,
`delay` -- so what clotran ANSWERS is already ours. It is the tables and
the tests underneath that speak Java.

Moves no scorecard. It is a correctness-of-description change: the
project's claim is that Fortran is the host, and a host that answers
to `java.lang.Double` is not describing itself.

This item is about CLOTRAN'S OWN source -- the Fortran, our tests,
our namespaces -- and needs no change to core.clj. We are BOOTSTRAPPING
off Clojure's core.clj for now, and it keeps its Java names because it
is Rich's file describing the JVM it was written for.

Later, once the port is done and the suite is green, that file gets
forked to `core.cljf` and renamed the same way -- `.cljf` so the two
are never confusable, the way `.cljs` is not `.clj`. Three things about
that are worth fixing now rather than arguing then:

- **Derive it, do not hand-edit it.** 693 call sites across 122 names.
  A rename map plus a generator means the next Clojure release is a
  diff to read; 693 hand edits means a manual merge forever.
- **Rename is not the same as drop.** `re-matcher` and `re-groups`
  occur ZERO times in all of ClojureScript, which is SEAMS' own test
  for "this was never Clojure". Those go, rather than getting a
  clotran name for a JVM shape.
- **Green cannot mean 67 of 67.** Some namespaces need third-party
  artifacts and some test the JVM. Write the excluded list into
  `scripts/run-clojure-tests` before anyone claims the gate is met,
  and keep the vendored tree loadable afterwards -- once our tests are
  renamed too, it is the only thing left that can catch a drift.

**9. Arrays, as close to Clojure's as a better representation allows -- DONE.**
`fortran/make-array` exists and works, but it is a parallel vocabulary
where Clojure already has one. The decision was to move to Clojure's
names and semantics -- `make-array`, `aget`, `aset`, `alength`, with
Clojure's type spellings -- keeping the Fortran representation
underneath. core.clj's own definitions now run: `make-array`, `aget`,
`aset`, the `aset-int`/`aset-double` family, `alength` and `aclone`,
each verified against `clj` on the same script and agreeing line for
line, slices included. What is left is `into-array`/`to-array`
(`RT/seqToTypedArray`), which is item 3's cluster, not this one.

Nothing has to be given up to do that, which was not obvious and is
worth writing down. A Fortran rank-2 array gives `a(i,j)` access AND
one contiguous column-major block, measured:

    a(2,3) = 23.0
    flat   = 11 21 31  12 22 32  13 23 33  14 24 34
    is_contiguous(a) = T
    flat(i + (j-1)*3) == a(i,j)   for every cell
    passed to a callee taking buf(*) -- the BLAS shape

Java's `[[I` is nested and cannot be handed to a BLAS routine at all.
Ours can. So this is a case where matching Clojure's SPELLING and
beating its representation are compatible.

The route is NOT to shadow core.clj's functions. They are written as
`(. Array (newInstance type len))`, `(. clojure.lang.RT (alength a))`,
`(clojure.lang.Reflector/prepRet ... (. Array (get array idx)))` -- so
implementing those host members makes Clojure's own definitions work,
and every piece of Clojure code that touches an array works with them.
That is also the 23 errors in Clojure's suite: `RT/alength` (14) and
`RT/seqToTypedArray` (9).

**The piece that needs real design: slices.** Clojure's multi-dimensional
`aget` is

    ([array idx & idxs] (apply aget (aget array idx) idxs))

so `(aget m 1 2)` is `(aget (aget m 1) 2)` and `(aget m 1)` must return
an inner array. In column-major, fixing the FIRST index gives a STRIDED
view, not a contiguous one -- so an array object needs an offset and a
stride, and the slice must borrow its parent's buffer rather than own
it (the finalizer must not free a borrowed one, and the parent must be
kept alive by the slice).

`alength` of a multi-dimensional array is the FIRST EXTENT, which is
what Clojure answers for the outer dimension of a nested array, and for
rank 1 is the same as the total. That one matches for free -- though it
cost an existing test, which had asserted the total.

`aclone` is the other place the view matters: it must clone the SHAPE
OF THE VIEW, not of the buffer behind it, or `(aclone (aget m 0))` on a
2x3 hands back a 2x3 instead of a length-3 row.

**Ragged arrays are not supported and will not be** -- see DEVIATIONS.
`[[I` rows may differ in length; a Fortran rank-2 cannot, and the
contiguity that buys is the entire point. This one is NOT a JVM artifact
(JavaScript arrays are nested too, so ClojureScript would not help), it
is a capability deliberately traded away.

**Where this is going: core.matrix on Fortran.** `core.matrix` has a
BLAS-backed implementation in clatrix (github.com/tel/clatrix) that
reaches BLAS through the JVM. clotran would not need to reach anywhere
-- the array IS the thing BLAS wants. Not now, but it is the reason to
keep the array representation honest rather than convenient.

Not on the list, deliberately: analyse-time name resolution. It is the
right architecture (`SEAMS.md`), and `gce_analyze` already exists to hold
it, but the bugs that seemed to demand it turned out to be a Var
ownership bug instead. Do it when something actually needs it.

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

Historical. Steps 1-3 are done or superseded and are kept for their
reasoning, not as work. **What to do is in "Start here" above**; this
section is what to read when you want to know why something is the way
it is, and it is long.

Ordering principle: things that survive the value-type change come
first, because they make the port itself debuggable. Things entangled
with the value representation come after it, so they are not built
twice.

### 1. Source positions and error locations -- DONE IN `clotran-bin`, NOT IN `clotran-gc`

Line, column and file on every form, so errors and later stack frames
can point at real source.

**Read this before trusting the boxes below.** Every one of them was
ticked against `Eval.f90`/`LispReader.f90` -- the ORIGINAL evaluator,
the one being retired. `GCReader.f90` has no positions at all and says
so in its own header, pointing back at this file: "source positions are
an open question for the new representation (PLAN.md: a GC object has
i1/i2 and count already took i1), so this deliberately does not pretend
to solve it."

So `./clotran` reports no `file:line:col` on anything, and the
`in: (form)` line names the top-level form rather than the failing
subform. That is why the `(+1 1)` note at the bottom of this file has
no position to be wrong about. Redoing step 1 on `gc_value` is real,
unscheduled work, and step 6 (the debugger) is blocked on it -- its
CallInfo frames have nothing to record.

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

### 3. The GC -- DONE, and 3c-2/3d/3e superseded

Built, wired in, running real core.clj. `clotran-gc` is the evaluator
`./clotran` runs.

3c-2, 3d and 3e are NOT work: they are a plan to retrofit `cons_value`
in the ORIGINAL evaluator, and what happened instead is that
`clotran-gc` was built fresh on `gc_value` -- that plan's endpoint by a
different road. They apply only to `clotran-bin`, and retiring it
(Start here, item 6) deletes them.

The design reasoning -- typed pools, the tracing walk, why the value
stack looks like it does, and each of the data-layer modules -- is in
NOTES.md under "The GC: design and construction". Read it when you want
to know why something is the way it is, not to find work.

### 4. Load clean, load fast -- 4a done, 4b/4c open

- [x] **4a -- DONE.** `scripts/run-clojure-tests` drives `clotran-gc`
      with core.clj loaded. It dropped hard at first, which was the
      signal being asked for; "Where we are" has the current numbers.
      Its summary parser also had to learn that maps print with commas
      now, which `clotran-bin` did not do.

- [x] **4a', 4a'' -- superseded.** Three gfortran-only crashes and an
      intermittent use-after-free, all in `clotran-bin`'s refcounting.
      They die with it. The investigation is in NOTES.md under "The GC:
      design and construction"; the method in it is worth keeping --
      two samples are not evidence of absence for a 1-in-6 bug.

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
      it saved macroexpansion but not evaluation, and analysis was only
      ~4% of startup even when startup was 1.68s (profiled: 218 samples
      in `mx_walk` against 3603 in `gce_eval`). Startup is 5.8s now and
      the shape has not changed: the cost is RUNNING core.clj, which
      only a heap snapshot avoids. Re-profile before trusting the 4%.

      Key must include every `.clj` loaded *and* the binary, since both
      expansion and evaluation depend on the evaluator.

### 5. Concurrency -- STM, agents -- not started

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

### 6. Debugger -- not started

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
- **Passing a clotran array to a real Fortran procedure.** The storage
  half is DONE, in the shipping evaluator this time:
  `GCNativeArray.f90`, reached through a `fortran` namespace. The
  binding generator is what is left, and it is now genuinely the only
  missing half rather than one of two.

  Worth remembering how it got lost, because the same shape could
  happen again. `NativeArray.f90` was referenced by `Eval.f90` and by
  nothing else; `aget`, `aset`, `make-array` and `alength` appeared
  eight times in the old evaluator and ZERO times in the shipping one.
  The capability did not survive the GC port, nobody wrote that down,
  and retiring `clotran-bin` (item 6) would have deleted the only copy
  of it. A feature living only in the evaluator being retired is
  invisible to every scorecard here -- our tests are per-module,
  Clojure's suite does not reach it, and core.clj never calls it.

  The port is not a copy. The buffer cannot live in a gc pool -- four
  scalars and no pointer, which is the point of `gc_value` -- so it
  lives in a registry and the object holds a handle, exactly what
  `Regex.f90` does with ICU. That needed a FINALIZER in the sweep,
  which the collector did not have: it zeroed the kind and moved on,
  so anything owning storage outside the heap leaked. Deviation 14
  records the same leak for Matcher and is now fixable the same way.

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