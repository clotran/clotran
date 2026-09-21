# clotran

Clojure, hosted on Fortran.

It runs Rich Hickey's actual `clojure/core.clj` -- the file, unmodified,
vendored from `clojure/clojure` at `71b4623d`. Not a Clojure-like
language implemented in Fortran: the Fortran is the *host*, standing
where the JVM stands, and the language comes from Clojure's own source.

```
$ make && ./clotran
user=> (defn greet [who]
  #_=>   (str "hello, " who))
#'greet
user=> (greet "world")
"hello, world"
user=> (->> (range 20) (filter odd?) (partition-all 3) (map vec))
([1 3 5] [7 9 11] [13 15 17] [19])
user=> (clojure-version)
"1.13.0-master-SNAPSHOT"
```

That version string is real: core.clj reads it off the classloader and
parses it with a regex, and both of those had to exist for it to answer.

## What works

**All 724 of core.clj's top-level forms load.** That includes
destructuring, the macro system, protocols, multimethods, lazy seqs,
transducers, metadata, `case`, regex literals, `deftype`, `reify`,
`defrecord`, `letfn`, `delay` and the whole seq library -- because
clotran does not implement those, core.clj does.

**17 of the 27 Clojure library namespaces probed load** (measured
2026-09-19): `set`, `data`, `edn`, `datafy`, `walk`, `string`,
`template`, `zip`, `stacktrace`, `test`, `inspector`, `reflect`,
`parallel`, `pprint`, `math`, `core.protocols` and `core.reducers`.
Loaded means a var of theirs RESOLVES afterwards, not merely that
`require` returned without complaint: `clojure.uuid` and
`clojure.java.io` are skipped by name, so requiring them succeeds and
defines nothing, and counting that as a load is how this number was
once too high. The eight that fail -- `repl`, `main`, `instant`,
`xml`, `java.shell`, `java.browse`, `core.server`, `process` -- each
want a JVM class (`Thread`, `Socket`, `SimpleDateFormat`, a SAX
parser).

`clojure.test` running means Clojure's own tests run. The suite
clotran is measured by is DERIVED from them: `scripts/derive-tests`
keeps every `deftest` whose symbols lie in the intersection of
`clojure.core` and `cljs.core` -- the language, as two implementations
agree on it -- and leaves out the ones that name a Java class, a
member call or a `clojure.core` function ClojureScript never had.
That keeps 314 of 578 tests, in 39 files that all load. **2170
passing assertions** against 235 failures and 370 errors, so **78% of
the assertions that executed** (measured 2026-09-19).

That denominator is assertions that executed, not assertions that
exist: a test that errors part-way contributes only what ran. The 67
vendored namespaces also run verbatim, for reference, at 53% of
executed assertions; the JVM-shaped half of them is why that number is
not the one to watch.

**Real Fortran arrays**, which is the one thing this host has that the
JVM does not:

```clojure
(alias (quote f) (quote fortran))
(def m (f/make-array "real8" 2 3))   ; contiguous, column-major, zero-filled
(f/aset m 1 2 3.5)
(f/aget m 1 2)                        ;=> 3.5
(f/array-kind m)                      ;=> "real8"
```

The bytes ARE a Fortran array at an address the collector never moves,
which is what a Fortran library expects to be handed -- and is:

```clojure
(def a (f/make-array "real8" 2 3))    ; fill with 1..6, row-major reading
(def b (f/make-array "real8" 3 2))    ; 7..12
(fortran/load-package "packages/blas") (require 'blas)
(def c (blas/dgemm a b))              ; the reference BLAS, vendored in src/f/blas, a package
(f/aget c 1 1)                        ;=> 154.0
```

`dgemm` is netlib's own F77 source, compiled by the same compiler and
handed the two buffers exactly as `A(LDA,*)` declares them: no copy,
no descriptor, no C shim. That is the claim the project rests on, and
this is the first routine that tests it. The `fortran` namespace names
a Fortran KIND rather than a class -- see `SEAMS.md`.

**ChemSol runs on clotran.** ChemSol is a solvation-energy program, a
real scientific code with a 1,600-line library module whose routines
take twenty to thirty positional arguments. Its `main.f90` is replaced
by `examples/chemsol.cljf`, the library is vendored unmodified in
`src/f/chemsol/`, and it is a PACKAGE: a shared library beside its
Clojure in `packages/chemsol/`, opened at run time by one unchanged
clotran binary, never linked in. Each routine is a map-in, map-out
function keyed by the routine's own argument names:

```clojure
(fortran/load-package "packages/chemsol")
(require 'chemsol)
(-> mol (chemsol/readopt vdw-par) (chemsol/dg-ld atoms) chemsol/solvout)
```

`scripts/chemsol-check` runs it on ChemSol's three reference inputs and
diffs against the original program's output: all three match byte for
byte. The arrays cross as the same buffers the Fortran writes into,
with no copy. `scripts/bind-fortran` writes the shims and manifest for a library from its own signatures, so a package is declared rather than hand-bound.md step 7 records
what the library dictated for it.

**`pprint` works.** Through Clojure's own `clojure.pprint`, verbatim:
the pretty writer is a `proxy` over `Writer` and `IDeref`, the column
writer another, and six `with-out-str` cases in the oracle print
byte-for-byte what `clj` prints for vectors, nested maps, a `defn`
form and `print-table`. What it took was not pprint code but host
contract: `class` answering the literal's keyword, `import` recording
short names, `String.split`, `String.replaceAll`, `Writer.append`
reaching a proxy's `write`, and `Writer.write(int)` writing the
character.

**Three extensions.** `.cljf` is a clotran file: it may use the
`fortran` namespace and is looked for first. `.cljc` is portable
Clojure; clotran reads its `#?` branches with the feature `:cljf`
(and `:default`), so porting a `.cljc` library is adding a `:cljf`
branch beside each `:clj` one. `.clj` is JVM Clojure, which clotran
loads as written -- that being the point. `require` looks for the
three in that order.

**Sorted collections.** `sorted-map`, `sorted-map-by`, `sorted-set`,
`sorted-set-by`, `subseq`, `rsubseq` and `rseq`, from core.clj's own
definitions: a sorted map is the array map with its keys kept in
comparator order, never promoted to a hash trie, and a sorted set is
a set over one. Verified: `(subseq (sorted-set 1 2 3 4 5) >= 2 < 4)`
is `(2 3)`, and `(into (sorted-set) (range 20 0 -1))` counts up.

**Host members written in Clojure.** `sequence`, `eduction`,
`iterator-seq`, `volatile!`, `shuffle` and the transducers that buffer
(`partition-all`, `partition-by`) are core.clj's own definitions, which
name `RT/iter`, `RT/chunkIteratorSeq`, `TransformerIterator`,
`java.util.ArrayList` and `Eduction`. ClojureScript writes those in
Clojure, so clotran does too: `src/clj/clotran/rt.cljf` holds them,
the host table's rows for those members call its vars, and the file
loads the first time one is reached. `Volatile` is a box the host
supplies. Verified: `(sequence (comp (take 3) (map inc)) (range))` is
`(1 2 3)`, and `(into [] (partition-by odd?) [1 3 2 4])` is
`[[1 3] [2 4]]`.

Clojure's OWN array functions run over the same representation -- not
reimplemented, the definitions in `core.clj`, which are written against
`java.lang.reflect.Array` and `clojure.lang.RT`:

```clojure
(def m (make-array Integer/TYPE 2 3))
(aset-int m 1 2 22)
(aget m 1 2)                          ;=> 22
(alength m)                           ;=> 2   ; the OUTER length
(alength (aget m 1))                  ;=> 3   ; a row is an array
```

A Java `[[I` is two separate row objects; ours is one rank-2 block, so
`(aget m 1)` hands back a strided VIEW over the same buffer -- writing
through it is visible in the parent, as it is on the JVM. The cost is
that rows cannot differ in length; the gain is that the whole thing is
one contiguous column-major block a BLAS routine can take, which `[[I`
cannot be at any price. `DEVIATIONS.md` 24 and 25 carry both.

**A debugger, as data.** `(clotran-break)` pauses. The paused state
is a map -- why, and one frame per pending call with its position and
its locals by name -- handed to `*clotran-break-handler*`, whose
answer resumes it: `:continue`, `{:continue v}`, `:step-in`,
`:step-over`, `:step-out` or `:abort`. `binding` the Var scopes a
handler; with none bound the break is a snapshot and the map is its
value, which is what a script wants. At the REPL the handler is a
nested REPL, and this is verified output:

```
user=> #'sq
user=> #'hyp
user=> break: :break 
  0 user/hyp (1:17)
      a = 3
      b = 4
;; (clotran-resume :continue | {:continue v} | :step-in | :step-over | :step-out | :abort)
[1] user=> {a 3, b 4}
[1] user=> break: :step 
  0 user/sq (1:14)
      x = 3
  1 user/hyp (1:36)
      a = nil
      b = 4
;; (clotran-resume :continue | {:continue v} | :step-in | :step-over | :step-out | :abort)
[1] user=> 25
```

`(clotran-break-on! true)` breaks at every error too, taken at the
throw so the frames are still there, and `CLOTRAN_BREAK_FILE=path`
appends every break to a file for a run that ends before anyone can
ask. Steps count calls, not lines, since a call is the event the
executor has: in stops at the next call anywhere, over walks the
current fn's own calls without descending, out stops at the next call
once the current frame has returned. Evaluating in a frame is the
handler's own `let` over `:env`, since locals are immutable and the
values are already in the map.

**Futures and promises, on one thread.** core.clj's own `future`,
`promise`, `pmap`, `pcalls`, `pvalues` and `deref`, verbatim, over a
task the host runs in an evaluator context of its own -- a green
thread: it runs when made, parks when it blocks, and resumes when
something waits for it. Verified output:

```
user=> #'p
user=> #'f
user=> false
user=> #object[clotran.reify__2]
user=> 15
user=> (2 3 4)
user=> :nobody-delivered
```

There is one OS thread, so this is concurrency without parallelism;
what it buys is that pipeline code reads as straight-line Clojure.
DEVIATIONS 38 lists what differs from a JVM thread.

**A thread is a contract, and green is its default.** `clotran.thread`
is the protocol a kind of thread implements -- `spawn`, `join`,
`status`, `cancel!`, a mailbox with `send!` and `receive`, and `self`
for replies -- with one current kind, the way core.matrix keeps a
current implementation. `green` is the task above; a process kind is
next, behind the same names. Verified output:

```
user=> nil
user=> nil
user=> :green
user=> #'worker
user=> :parked
user=> nil
user=> 144
user=> nil
user=> nil
user=> :done
```

Four oracles keep it honest: gfortran and flang must agree
(`make crosscheck`), `clj` -- real JVM Clojure --
answers what Clojure actually does rather than what anyone remembers,
and pinned clones of Clojure and ClojureScript are cited rather than
recalled. See `CLAUDE.md`.

## What does not

| | |
|---|---|
| speed | measured by `scripts/bench`, the same forms on a warmed JVM and on clotran: a function call ~1.3 µs, a loop/recur iteration ~1.7 µs, a reduce step over a range ~1.3 µs. Against the JVM that is 23x on plain recursion, 39x on a reduce building a map, 40x on fib, 120x on loop/recur, 454x on `(reduce + (range n))` and 514x on `into` over a mapped range. Between one and a half and two and a half orders of magnitude, an AST interpreter's honest number; PLAN.md step 8 has the JIT decision |
| startup | 0.6s: core.clj is re-read and re-analysed every launch; there is no image yet |
| memory | 168 MB after loading core.clj, and a 100000-element reduce stays there since locals are cleared after their last read; the image (PLAN.md step 5, stage 3) is what would shrink the baseline |
| debugger | steps count calls, not lines, since a call is the event the executor has; one level, so a break inside the handler is a snapshot; no socket. What it does is under "What works" |
| `BigDecimal` and `BigInt` | `1M` reads as a double and `1N` as an integer; DEVIATIONS 30 |
| mutable deftype fields | `(set! afield v)` is refused, loudly; DEVIATIONS 20 |
| `tap>`, agents that run apart | queues; an agent's action runs at `send`, on the one thread there is |
| futures | run on the one OS thread, at creation until they first block; a wait under a `map` or `reduce` callback cannot park, and a wait nothing can satisfy is an error, not a hang; DEVIATIONS 38 |
| the five JVM-only sibling libs | bytecode generation; see `src/clj/clojure/PROVENANCE.md` |
| regex | ICU, with ASCII/Latin-1 offsets only |
| calling a Fortran library | one routine, `dgemm`, hand-bound; the generator that would do it for any routine is PLAN.md step 7 |

`DEVIATIONS.md` is the full ledger: every place clotran does something
real Clojure does not, why, and what removing it would take. A
deviation with no entry there is a bug. `SEAMS.md` covers the other
question -- what must be native versus what we merely chose to make
native, using ClojureScript as the control group.

## Layout

- `src/f` -- the Fortran host: value representation, a tracing GC,
  persistent list/vector/map, namespaces, reader, evaluator.
- `src/c` -- vendored ICU, built from source for regex. No Homebrew,
  no system library, no runtime dependency.
- `src/clj` -- Clojure's own source, vendored and unmodified.
- `test/f` -- unit tests for the Fortran host, one file per module.
- `test/clj` -- Clojure's own test suite, vendored verbatim. The
  conformance measure; `scripts/run-clojure-tests` drives it.
- `scripts/clotran` -- the user-facing launcher (see below).

## Build

```
make            # builds ./clotran-bin and the test binaries under build/
make test       # the gate: host tests, language_test.clj, scripts/oracle
make crosscheck # the same on flang and gfortran -- run before committing
make FC=flang all test      # just the flang side
```

Every build product lives under `build/` -- objects, `.mod` files, the
test binaries in `build/test/` -- and the only artifact in the root is
`./clotran-bin` itself. The first build also compiles vendored ICU from
source, which takes a few minutes once; after that it is cached.

`./clotran` is the entry point, a shell script: it hands `clotran-bin`
core.clj and wraps the REPL in `rlwrap` when there is a terminal and
`rlwrap` is installed, for history and arrow-key editing, exactly the
way real Clojure's own `clj` wraps `clojure`. Files named after it load
after core.clj, so `./clotran prog.cljf` runs a program. It works from
any directory: the binary takes its own directory as a classpath root.

`./clotran-bin` is the interpreter alone, a plain stdin/stdout REPL that
loads only `host.clj` and the files named on its command line -- which
is what the scripts and the Makefile use, passing core.clj explicitly.

```
./clotran
```

## Why host it on Fortran rather than bridge to it

Clojure on the JVM can already call Fortran, and for linear algebra it
does it well -- core.matrix and Neanderthal reach BLAS/LAPACK through
JNA or Panama, and if what you want is fast matrix math from Clojure,
use those. They are less work than this and they are finished.

They reach *F77*, though, and that is the distinction this project is
built on.

### There is no Fortran ABI above F77

Everything an FFI bridge can call easily is the 1978 subset: scalars
passed by reference, explicit-shape arrays, external (non-module)
procedures, no allocatables, no derived types. BLAS is exactly that
subset, which is why BLAS bindings exist for every language and why
they were never hard to write.

Above that line there is no standard. An assumed-shape array, an
`allocatable`, a `pointer`, a `character(len=:)`, an `optional`
argument, a `class(*)` -- none of these are passed as an address.
They are passed as a *descriptor*, a compiler-private struct whose
layout is not specified by the standard and is not the same between
gfortran, flang, and ifx. Add to that module-symbol mangling, which
is also per-compiler:

```
gfortran   __modname_MOD_procname
flang      modname_procname_
ifx        modname_mp_procname_
```

So "call a modern Fortran library from C" means: know the target
compiler, know its descriptor layout, know its mangling, and redo all
three when the library is rebuilt elsewhere. `ISO_Fortran_binding.h`
is the standard's answer and it is both painful and unevenly
implemented.

[clojure-fortran](https://github.com/memmett/clojure-fortran) shows
the shape of the workaround honestly: mark each routine `bind(c)`,
write a C header for it, run `jextract`, call the generated Java from
Clojure. That works -- but `bind(c)` is precisely a promise *not* to
use assumed-shape arrays, allocatable or optional arguments, derived
types with allocatable components, generic interfaces, or polymorphism.
You get Fortran back only by giving up the parts of Fortran written
after 1990, and you hand-write a wrapper per routine to do it.

Hosting *on* Fortran removes the boundary instead of crossing it.
A clotran array is a Fortran array; handing it to a library is an
ordinary call, with no descriptor to fabricate, no mangling to guess,
and no copy (verified: a contiguous buffer passed as `a(*)` reaches
the callee at the same address).

### The same reason gdb can't show you a Fortran object

Worth noting because it's the identical root cause, not a coincidence.

gdb being written in C/C++ isn't really why -- but the instinct behind
the question is right. Two things are:

1. **There is nothing stable to read.** An allocatable array's bounds,
   allocation status, deferred string length, and dynamic type all
   live in that same compiler-private descriptor. A debugger can't
   decode it directly; it can only follow whatever DWARF says, and the
   attributes needed to describe it indirectly
   (`DW_AT_data_location`, `DW_AT_allocated`, `DW_AT_associated`,
   `DW_TAG_generic_subrange`) only landed properly in DWARF 5, with
   emitter support arriving late and unevenly.

2. **gdb's type model was built for C.** It assumes a type's layout is
   known statically from the debug info. Fortran's interesting types
   describe themselves *at runtime*. That's a genuinely C-shaped
   worldview, and retrofitting it is why `print my_alloc_array` works
   on a good day with one compiler and prints garbage on another.

Both failures -- C can't call it, gdb can't see it -- are the same
missing thing: no ABI for anything Fortran gained after F77.

This is also why clotran's debugger is planned in clotran itself
(see `PLAN.md`). A debugger written in the language, over a value
representation the host defines, has no descriptor to decode and no
DWARF to depend on.

### What Fortran gives back

- Arrays of any rank and any lower bound, column-major, bit-identical
  to what a Fortran routine expects.
- `class(*), allocatable` -- arbitrary kinds and derived types in one
  component, with the type checked at `select type` rather than
  tracked by hand behind a `void*`.
- Kinds, `complex`, IEEE control, whole-array operations: the reasons
  anyone calls a Fortran library in the first place.
- It runs where Fortran runs. No JVM, which matters on the clusters
  where the libraries being called actually live.

### Why the arrays are fast

The old Fortran-beats-C benchmark folklore is mostly one rule:
**dummy arguments may not alias.** If a variable is reachable through
two arguments of the same call, the standard forbids defining it
through one and referencing it through the other. So in

```fortran
subroutine saxpy(n, alpha, x, y)
```

the compiler may assume `x` and `y` do not overlap, and is free to
vectorize, reorder, fuse, and keep values in registers across stores.

C assumes the reverse -- any two pointers may alias -- which is why
`restrict` had to be added in C99. Fortran gets `restrict` on every
argument, everywhere, without anyone remembering to write it and
without the chance of asserting it wrongly.

Two smaller things compound it:

- **Contiguity is in the type.** `contiguous`, explicit-shape and
  assumed-size say so at compile time; a `float *` never does.
- **Whole-array syntax hands the compiler the loop** (`y = y + a*x`)
  rather than making it recover one from pointer arithmetic.

Honest version: modern C with `restrict`, `-ffast-math` and a good
vectorizer closes most of this gap, and the remaining difference on
straight kernels is usually small. What doesn't close is the default
-- the Fortran code is fast without the author doing anything, and the
C code is fast when the author annotates correctly. For a language
host handing arrays to numerical libraries written by other people,
the default is the part that matters.

### And what it costs

C would have been easier for the *interpreter*. C has a real `union`
and real casts, so the tagged value is 16 bytes in one arena instead
of a component per payload kind across several pools; struct
assignment is a plain copy rather than an overloaded `=` with a
`FINAL` attached, so refcounting stays visible at the sites that do
it; and function pointers, sanitizers, and libffi are all first-class.

That's the trade, and it's the right way round: the friction is in the
value representation, which is a solved problem in any language, and
the payoff is at the interop boundary, which is not.

## Status

`PLAN.md` is where this is going and why, in order. `NOTES.md` is the
design history. The code began as a [mal](https://github.com/kanaka/mal)
implementation; that evaluator and its test suites have been removed.


## License

clotran is EPL-2.0 (`LICENSE`).

It redistributes Clojure (EPL-1.0) and ICU4C (Unicode License v3), each
under its own license. `NOTICE` says which is which; neither is
relicensed by this repository.
