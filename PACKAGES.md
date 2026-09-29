# Packages

How clotran brings in code that is not clotran: what a package is, which
ones exist, which ones are planned, and the rules for vendoring what they
depend on. PLAN.md step 9 has the decision record; this is the ledger.

## What a package is

One clotran binary, and everything else loaded at run time. A package is
a shared library (`.dylib`, `.so`) that clotran opens with `dlopen`
(src/f/DynLoad.f90) and never links. It exports:

- `clotran_manifest`: a C string of EDN naming the package and each
  routine, with its arguments' type, intent and rank. clotran's own
  reader reads it.
- one shim per routine, `<name>_shim(argc, argv)`, so clotran has exactly
  one calling convention for every package, whichever compiler built it.

Beside the library sits a Clojure namespace that is the API:
packages/blas/blas.cljf wraps `blas.raw/dgemm`, thirteen positional
arguments as netlib declares them, as `(blas/dgemm a b)`.

Shims and manifests are GENERATED from the Fortran sources by
`scripts/bind-fortran`, for free-form modules and F77 fixed form alike.
A hand-written shim, as ChemSol's is, is still a shim.

A namespace compiled by `clotran compile` goes through the same door: a
library with a `clotran_manifest`, installed over the functions its
source defined (src/clj/clotran/loader.cljf).

## Core packages

A CORE package is one this repository maintains and ships:

- its source is vendored under `src/f/<name>/`, unmodified, with a
  PROVENANCE.md saying where it came from, at what version, and under
  what licence;
- `make packages` builds it into `packages/<name>/`, beside its Clojure;
- the gate (`make crosscheck`) builds and tests it under both compilers.

| package | what | source | status |
|---|---|---|---|
| `blas` | the reference BLAS: `dgemm` | netlib, src/f/blas | shipped |
| `chemsol` | ChemSol solvation, the interop finish line | src/f/chemsol | shipped |

What is NOT a package: the thread primitive. core.clj's own `future`,
`promise` and `pmap` are built on it, so it belongs to the base binary
(PLAN: threads are contexts). The same goes for `do concurrent`, which
is code the compiler emits, not a library.

## Planned packages

### `repro`: reproducible floating-point reductions

`(repro/sum xs)`, `(repro/reduce + xs)`: sums whose answer is the same
bits whatever the order, so the same on 1 thread, 400 threads, a laptop
or a cluster. Explicit by design: plain `reduce` stays serial and
bit-identical to Clojure, and nothing switches to reproducible summation
behind the programmer's back.

The method is Demmel and Nguyen's binned summation, as in ReproBLAS
(C: sum, dot, 2-norm, gemv, gemm, and MPI reduction operators). Two
routes, not yet chosen:

- vendor ReproBLAS: its licence was not found on the project page and
  must be settled first;
- write the binned accumulator in Fortran, from the published papers.

Either way it suits `do concurrent`: each chunk fills its own
accumulator, and binned accumulators combine in any order to the same
answer.

### `coarrays`: many images, many machines (parked)

SPMD: N copies of the program, each with its own memory, exchanging data
through coarrays (`x[*]`, `co_sum`). Each image would have its OWN clotran
heap, so the collector never needs locking.

Parked, because on one machine it is the wrong tool. One clotran process
peaks at 348 MB and takes 2.3 s to start with core.clj loaded (measured
2026-09-24), and eight images cost eight of those to do what threads do
in one. It earns its keep across machines, where separate processes are
unavoidable anyway.

Open questions for when it is unparked:

- The coarray runtime starts up with the MAIN program and needs a
  launcher (`cafrun`, `mpirun`) to start the images. Whether a coarray
  package loaded with `dlopen` into a coarray-enabled clotran works at
  all is untested. `./clotran -n 8` could hide the launcher from users.
- Compilers: gfortran needs `-fcoarray=lib` plus OpenCoarrays, over MPI.
  flang's coarrays are experimental (off by default; with `-fcoarray` it
  lowers to PRIF and needs the Caffeine runtime, which failed to link
  here without it).

The recipe, tried 2026-09-24: MPICH built and installed into a private
prefix with nothing from Homebrew; OpenCoarrays not yet built.

| source | version | sha256 | checked against |
|---|---|---|---|
| MPICH | 4.3.2 | `47d774587a7156a53752218c811c852e70ac44db9c502dc3f399b4cb817e3818` | GitHub's published release digest |
| OpenCoarrays | 2.10.3 | `f9f2fb6ac1fe92c1ea66976894b5cebe53812827b7d1238fed933e2845e8a022` | nothing: a tag archive has no published digest; recorded at first fetch |

MPICH 4.x rather than the newer 5.0.1 because OpenCoarrays 2.10.3 predates
it and its notes mention MPICH 4 fixes. MPICH was configured with
`CC=clang FC=gfortran --enable-fortran=all`.

### Later

- A GPU BLAS (`cublas`): cuBLAS, cuFFT and cuRAND have C interfaces a
  shim can call. Needs a Linux machine with an NVIDIA GPU; this Mac has
  an Apple GPU, and NVIDIA's Fortran compiler is Linux-only.

## Vendoring rules

We vendor. We do not tell users to install things with a system package
manager, because the library changes, moves or disappears under them.

1. A source is pinned by URL AND sha256. A download that does not match
   is refused. Where upstream publishes a digest, the pin is checked
   against it, and this file says which pins were and were not.
2. The licence is known and recorded before anything is included.
3. Everything builds into a private prefix. Nothing is installed into
   the system, and nothing comes from Homebrew.
4. Vendored source is unmodified, with a PROVENANCE.md (CLAUDE.md: never
   edit vendored source).
5. A package carries its compiler's Fortran runtime. One process holding
   two, gfortran's and flang's, is a case to test, not to assume.
6. A ported `.cljc` library is its upstream file, pinned as in rule 1,
   plus a PATCH that adds `:cljf` branches where it has `:clj` ones
   (DEVIATIONS 33), applied when the package is built. The patch is the
   whole port: it is reviewed on its own, it can be sent upstream, and
   rule 4 still holds for the file it applies to. `:clj` is never
   claimed in its place -- that branch is the JVM. Nothing under
   `src/clj/clojure/**` is ever patched this way.

## The package manager: `clotran-deps` (designed 2026-09-29)

**The split, as the JVM and tools.deps have it.** clotran itself knows
one thing: a list of source roots, `CLOTRAN_PATH` (as the JVM knows
`-cp`), searched after its own `src/clj` for `name.cljf`, `.cljc`, `.clj`
(DEVIATIONS 33). Everything else -- reading a project's file, fetching
what it names, pinning it, walking its dependencies' own files, working
out the path -- is a separate program in its own repository,
`~/jborden/clotran-deps`, written in Clojure and run BY clotran, as
tools.deps is run by the JVM.

**The project file is `deps.edn`, the same file, with the same keys:**

    {:paths ["src"]
     :deps  {io.github.jborden/clotran-nrepl {:local/root "../clotran-nrepl"}
             some/lib {:git/url "https://github.com/some/lib"
                       :git/sha "4a1b2c3d..."}}
     :aliases {:test {:extra-paths ["test"]}}}

One file for both hosts, as a Clojure project already has it. What a
`deps.edn` can name that clotran cannot load is handled by name, not
ignored: `org.clojure/clojure`, `org.clojure/spec.alpha` and
`org.clojure/core.specs.alpha` are PROVIDED -- clotran is the Clojure,
and ships those (src/clj/clojure/PROVENANCE.md) -- so this repository's
own `deps.edn`, which pins the oracle's `clj`, reads as having no
dependencies at all.

**Coordinates.**
- `:local/root` -- a directory with its own `deps.edn`.
- `:git/url` + `:git/sha` -- the full sha is REQUIRED (vendoring rule 1:
  pinned), `:git/tag` optional and checked against it. Checked out once
  into `~/.cache/clotran/gitlibs/<lib>/<sha>`, never modified after.
- `:mvn/version` -- refused, naming the library, unless it is one of
  the three provided above: a jar is JVM bytecode. A project that needs
  one on the JVM and something else here says so with an alias.
- A native package (a Fortran or C library with a manifest, above) is a
  dependency like any other whose `deps.edn` says how to build it
  (`:build` -- a recipe run on the target, rule 3); later.

**Resolution.** Breadth-first from the project, as tools.deps does; a
library named twice at two different shas is an ERROR naming both
paths, not a silent pick -- the choice is the project's, written in its
own `:deps`, which always wins.

**Caching.** The resolved path is written to `.clotran-cache/path`,
keyed by a hash of every `deps.edn` that went into it, so an
unchanged project starts with no resolution at all. The `clotran`
launcher, run in a directory holding a `deps.edn`, asks
`clotran-deps` for the path (cached) and sets `CLOTRAN_PATH`.

**First users.** `~/jborden/clotran-nrepl`, the nREPL server (PLAN step
21 d), as a `:local/root`, then over git.

**Status (2026-09-29).** clotran has `CLOTRAN_PATH` (check-path in the
gate) and exits 1 when a script fails to load. `~/jborden/clotran-deps`
resolves `:paths`, `:local/root`, `:git/url` + full `:git/sha` (cached
under `~/.cache/clotran/gitlibs`), aliases, the provided Clojure
libraries and refused jars, transitively, with conflicts an error unless
the project settles them; its `test/run.sh` checks each. It resolves and
loads the `clotran-nrepl` stub both ways. Not yet: caching the resolved
path, the `clotran` launcher calling it in a directory with a
`deps.edn`, `:git/tag`, native packages with a build recipe, and `-main`
with `*command-line-args*` (PLAN step 22), which replaces the one-line
driver its `bin/clotran-deps` writes.

What the rules above add up to. The decisions made earlier (PLAN.md
step 9), which this keeps:

- a package is source plus a recipe, built on the target;
- manifests are versioned, and record the compiler and the target;
- a project names its packages in a `deps.edn`-shaped file;
- clotran itself is built the same way, with the vendored pieces it
  needs;
- prebuilt third-party binaries are out of scope for now, but nothing may
  make them impossible: keep the C ABI.

The MPICH recipe above is the first recipe it would run.
