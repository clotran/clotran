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

**15 of Clojure's own 21 libraries load** -- `set`, `data`, `edn`,
`datafy`, `walk`, `string`, `template`, `zip`, `stacktrace`, `test`,
`inspector`, `reflect`, `parallel`, `core.protocols` and
`core.reducers`. Loaded means a
var of theirs RESOLVES afterwards, not merely that `require` returned
without complaint: `clojure.uuid` is skipped by name, so requiring it
succeeds and defines nothing, and counting that as a load is how this
number was once too high.

`clojure.test` running means Clojure's own test suite runs:
**771 passing assertions** across 196 of its tests, from the 67
namespaces vendored verbatim in `test/clj`.

That number is over assertions that EXECUTED. 7 namespaces still crash
before reporting anything and contribute zero to both halves of it, and
several of the 67 -- `proxy`, `genclass`, annotations, AOT -- can never
pass here. 18 of 67 namespaces produce a passing assertion today.

Leaving the crashed column is not the same as passing. `reflect` left
it when the reader learned hex literals, and went straight to reporting
nothing: `tests=0`. It is counted in the 8 becoming 7, not in the 771.

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
which is what a Fortran library expects to be handed. The `fortran`
namespace is the version that names a Fortran KIND rather than a class
-- see `SEAMS.md`. The binding generator that would pass one to `dgemm`
is not written yet.

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

Four oracles keep it honest: gfortran and flang must agree
(`make crosscheck`, 1145 assertions each), `clj` -- real JVM Clojure --
answers what Clojure actually does rather than what anyone remembers,
and pinned clones of Clojure and ClojureScript are cited rather than
recalled. See `CLAUDE.md`.

## What does not

| | |
|---|---|
| mutable deftype fields | `(set! afield v)` is refused, loudly; DEVIATIONS 20 |
| source positions | the GC evaluator has none, so no error reports `file:line:col` |
| ratio and BigDecimal literals | `2/3`, `1M` do not read |
| `clojure.string/split` | needs `Pattern.split` |
| the five JVM-only sibling libs | bytecode generation; see `src/clj/clojure/PROVENANCE.md` |
| `tap>`, `promise`, `shuffle`, `format` | need threads, queues, `ArrayList`, or `String/format` |
| startup | core.clj is re-read every launch; there is no image yet |
| regex | ICU, with ASCII/Latin-1 offsets only |

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
make            # builds clotran and every test binary
make test       # builds and runs every test binary
make crosscheck # the same on flang and gfortran -- run before committing
make FC=flang all test      # just the flang side
```

The first build also compiles vendored ICU from source, which takes a
few minutes once; after that it is cached.

`clotran-gc` is the raw interpreter, a plain stdin/stdout REPL with no
line editing of its own. `clotran` is what you actually run -- a thin
launcher (`scripts/clotran`) that loads core.clj and wraps the binary
in `rlwrap` when installed, for history and arrow-key editing, exactly
the way real Clojure's own `clj` wraps `clojure`; falls back to the raw
binary with a note if `rlwrap` isn't found.

```
./clotran
```

There is a second, older evaluator in the tree: `clotran-bin`, built
from `src/f/Eval.f90`. It predates the GC and is kept only because the
mal regression suites below still drive it. It is not the interpreter
this project is about, and it is on its way out.

`test/regression/` carries the official mal per-step test suites (see
`NOTES.md`) -- running those needs mal's own `runtest.py`, external to
this repo (no Python vendored here), against the raw binary (not the
rlwrap-wrapping launcher, same as testing `clojure` rather than `clj`):

```
python3 ~/jborden/mal/runtest.py --deferrable --rundir test/regression \
    step9_try.mal -- ../../clotran-bin
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

This code originated as a [mal](https://github.com/kanaka/mal)
implementation -- mal was bootstrap/validation scaffolding to get a
real interpreter working against a real test suite, not the identity
of this project. See `NOTES.md` for the actual design history,
decisions, and what's ahead.


## License

clotran is EPL-2.0 (`LICENSE`).

It redistributes Clojure (EPL-1.0), ICU4C (Unicode License v3) and mal
test suites (MIT), each under its own license. `NOTICE` says which is
which; none of them is relicensed by this repository.
