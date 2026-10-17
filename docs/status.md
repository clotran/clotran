# Status

What works, measured, and what does not; the version policy. Each
number names its denominator and the day it was measured.

## What works

**All 719 of core.clj's top-level forms load.** That includes
destructuring, the macro system, protocols, multimethods, lazy seqs,
transducers, metadata, `case`, regex literals, `deftype`, `reify`,
`defrecord`, `letfn`, `delay` and the whole seq library -- because
clotran does not implement those, core.clj does.

**25 of the 30 library namespaces Clojure ships load** (measured
2026-10-12): `core.protocols`, `core.reducers`, `core.specs.alpha`,
`data`, `datafy`, `edn`, `inspector`, `main`, `math`, `pprint`,
`reflect`, `repl`, `set`, `spec.alpha`, `spec.gen.alpha`,
`spec.test.alpha`, `stacktrace`, `string`, `template`, `test`,
`test.junit`, `test.tap`, `uuid`, `walk` and `zip`. Loaded means every
public var a namespace defines is bound afterwards, as clj binds it --
protocol methods included -- not merely that `require` returned:
`clojure.uuid` was once skipped by name so that requiring it succeeded
and defined nothing, and counting that as a load is how this number was
once too high. The five that fail want clj's host: `core.server` a
`ReentrantLock` and its sockets (clotran's own server is
`clotran.server`), `parallel` jsr166y's `ParallelArray`, which clj
cannot load without either, `xml` a SAX parser, `repl.deps` and
`tools.deps.interop` tools.deps and a process. `reflect` loads, and its
`reflect` asks the host's reflection, which clotran does not have
(DEVIATIONS 4).

`clojure.test` running means Clojure's own tests run. The suite
clotran is measured by is DERIVED from them: `upstream/derive-tests`
keeps every `deftest` whose symbols lie in the intersection of
`clojure.core` and `cljs.core` -- the language, as two implementations
agree on it -- and leaves out the ones that name a clj class, a
member call or a `clojure.core` function ClojureScript never had.
That keeps 312 tests, in 39 files that all load and run: **2719
passing assertions, none failing and none erroring** (measured
2026-10-12).

That denominator is assertions that executed, not assertions that
exist: a test that errors part-way contributes only what ran. The 66
vendored test namespaces also run verbatim, for reference: 2297 of the 2567
assertions that executed pass (89%), and two namespaces, `param-tags`
and `rt`, which test clj's host's method values and its RT class, stop
before they report. clj-shaped as half of them are, that is not the
number to watch.

Four oracles keep it honest: gfortran and flang must agree
(`make crosscheck`), `clj` -- real clj --
answers what Clojure actually does rather than what anyone remembers,
and pinned clones of Clojure and ClojureScript are cited rather than
recalled (`scripts/oracle`).

## What does not

| | |
|---|---|
| speed | measured by `scripts/bench` 2026-10-12, the same forms on a warmed clj and on clotran, interpreted: 2x to 17x slower on general code -- plain recursion 2x, fib 3x, a reduce building a map 6x, `(dorun (take 1e6 (range)))` 9x, `(apply + (take 1e6 (range)))` 16x, `into` over a mapped range 17x -- and 35x to 209x on numeric loops over arrays written inline. The same loops compiled by `clotran compile` (pure Fortran, `docs/guide.md`) take 1.0 to 3.7 ms where clj takes 13 to 17. An AST interpreter's honest number; compiling core is the work that closes the first gap (PLAN.md) |
| startup | 0.17 s from the image, and on a terminal the REPL opens by naming the build -- clotran's `VERSION`, the Clojure and ClojureScript commits the language is pinned to (`test/clj/derived/PROVENANCE.md`, written by the deriver), the compiler, the machine and the image's hash; a pipe gets no banner: `build/core.image` is the heap as it stood once core.clj and spec had loaded (`make image`, built with the binary), read back in place of loading them; from source, about 0.9 s. An image belongs to one build of the binary and to the sources it holds, and is left alone with a note when either has changed; `CLOTRAN_IMAGE=0` loads from source |
| memory | 140 MB after starting from the image (165 MB after loading core.clj from source; measured 2026-10-12), and a walk over a lazy seq stays there: `last`, `nth`, `count` and `dorun` over 10^6 elements of a range, an `iterate` or a mapped seq run at the baseline (PLAN.md step 16: the collector ages survivors before promoting them, and a builtin lets go of its arguments before it walks); the baseline is the heap core.clj and spec leave behind |
| debugger | steps count calls, not lines, since a call is the event the executor has; one level, so a break inside the handler is a snapshot; no socket. What it does is in `docs/guide.md` |
| `BigDecimal` | real: `1M`, scale kept, `with-precision` and all eight rounding modes. `(/ 1M 3)` ANSWERS at decimal128 rather than throwing, as MATLAB, Octave and Julia do (DEVIATIONS 43) |
| threads | a future runs on a thread of its own beside its maker (PLAN.md 14f); an agent's `send` actions run in order on a pool of worker threads with a run queue each, work stealing and a batch cap, designed in ACL2 (`model/agents.lisp`, PLAN.md 24) and `send-off` actions on a thread of the agent's own, a send inside an action or a transaction held until it ends and a failed agent's queue kept for `restart-agent` (DEVIATIONS 29); `dosync` is a transaction with a log and a commit, transactions serialized under one lock (a valid schedule, no retries; DEVIATIONS 10); a wait nothing can satisfy is an error, not a hang (DEVIATIONS 38) |
| the five host-bound sibling libs | bytecode generation; see `upstream/clojure/src/clj/clojure/PROVENANCE.md` |
| regex | ICU over UTF-8; its `\w` and `(?i)` are Unicode where clj's are ASCII |
| `clojure.spec.alpha` | vendored and consulted before every macro expansion, as the Compiler does; `s/check-asserts` turns `s/assert` on, as in clj (DEVIATIONS 42, resolved) |
| calling a Fortran library | a package per library: `scripts/bind-fortran` writes its shims and manifest from the library's own signatures, free-form or F77 (`packages/blas`, `packages/chemsol`); derived types, optional and pointer dummies are listed, not bound (PLAN.md step 9). A package built by another compiler than clotran's brings a second Fortran runtime into the process: built by clotran's own is the supported case |

`DEVIATIONS.md` is the full ledger: every place clotran does something
real Clojure does not, why, and what removing it would take. A
deviation with no entry there is a bug. `SEAMS.md` covers the other
question -- what must be native versus what we merely chose to make
native, using ClojureScript as the control group.

## Versions

clotran is `1.0.0-rc.4`: the release candidate of 1.0, which is the
language and nothing else -- the binary, its image, core and the
libraries vendored from Clojure, the launcher and, beside it,
`clotran-deps` (`PLAN.md` step 35). It runs Clojure **1.12.6**: the
vendored `core.clj` and test suite are that release (`upstream/`), and
`clj`, the oracle every behaviour is checked against, is pinned to it.

What a release may change, by its number:

- **A patch** (1.0.x) fixes. A difference from clj made smaller, or a
  bug fixed, with its oracle case or regression; a DEVIATIONS entry
  resolved or narrowed toward clj. Nothing a correct program relies on
  changes, the compiled-code ABI (`clotran.loader/abi`, 5) and the
  package format (`PACKAGES.md`) stay as they are, and a library
  compiled by 1.0.0 loads.
- **A minor** (1.x) adds. New libraries and packages, new `clotran.*`
  names, the Clojure release moved to a later 1.12 patch, a new entry
  point in the ABI. A DEVIATIONS entry may be added only as a host limit
  or by design, saying why. The ABI version moves only for an addition
  an older library does not need, and an older library still loads.
- **A major** (2.0) may break. An ABI change that refuses older
  compiled libraries, an incompatible package format, a Clojure minor
  release (1.13), or a by-design deviation reversed in a way a correct
  program can see.

The heap image (`build/core.image`) is not a format anything keeps: a
binary refuses an image from another build and rebuilds it from the
sources.

## Where it is going

`PLAN.md` is where this is going and why, in order. `NOTES.md` is the
design history. The code began as a [mal](https://github.com/kanaka/mal)
implementation; that evaluator and its test suites have been removed.

