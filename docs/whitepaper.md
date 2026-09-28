---
title: "clotran: Clojure, hosted on Fortran"
subtitle: "White paper and north star"
date: 2026-09-27
---

## The one-sentence version

clotran runs Rich Hickey's `clojure/core.clj` -- the file, unmodified --
on a host written in Fortran, where the JVM normally stands. Clojure's
data structures, macros, protocols, lazy sequences and transducers come
from Clojure's own source; the host supplies memory, arrays, the reader,
the evaluator and the door to Fortran libraries. There is one binary,
no JVM, no Python, and a Fortran routine is an ordinary call.

Everything in this paper is either measured or marked as not yet built.
The measured numbers are from `scripts/bench`, `scripts/oracle`,
`scripts/clojuredocs` and the derived language suite, on 2026-09-27.

## Why this exists

Scientific and financial computing runs on Fortran. The orchestration
around it -- configuration, data ingest, workflow, experiments -- runs
on whatever the team could glue on: Python through f2py, shell,
namelist files, C bindings. That glue is where the brittleness, the
GIL and the "recompile to change a parameter" pain live.

Clojure is the orchestration language that glue is missing: immutable
data, a REPL, macros, a concurrency story built on values rather than
locks. On the JVM it cannot reach a Fortran array without a foreign
function layer and a copy. On a Fortran host, a clotran array *is* a
Fortran array, and calling `dgemm` on it is a function call.

## Where we started

Before the scenarios there were four goals, in order, and they still
decide what work counts:

1. **Complete Clojure/Fortran interoperability.** A clotran array is a
   Fortran array; a Fortran routine is an ordinary call. The finish
   line was ChemSol, a computational-chemistry program whose Fortran
   main is replaced by clotran code and reproduces its output byte for
   byte -- done.
2. **A better way to debug Fortran.** Frame-based stack analysis and
   live inspection of Fortran values, over a representation the host
   defines. gdb cannot do this: an allocatable's bounds, status and
   dynamic type live in a compiler-private descriptor DWARF describes
   only indirectly and late.
3. **A multi-threaded story.** Clojure's model: immutable values,
   atoms, refs, agents, STM.
4. **Compilation**, ahead of time and per namespace, to Fortran --
   which is also what lets clotran code be transpiled.

The principle under them: the pure Clojure language is reproduced in
full; the JVM is an implementation detail this implementation does not
have. No `java.*` is modelled beyond what core.clj itself reaches for.

### Why host on Fortran rather than bridge to it

Clojure on the JVM can already call Fortran -- for BLAS. Every FFI
bridge reaches the F77 subset: scalars by reference, explicit-shape
arrays, external procedures. Above that there is no ABI: assumed-shape
arrays, `allocatable`, `optional`, `character(len=:)` and `class(*)`
are passed as compiler-private descriptors, and module procedures are
mangled per compiler (`__m_MOD_p`, `m_p_`, `m_mp_p_`). `bind(c)` is
precisely a promise not to use Fortran written after 1990. Hosting *on*
Fortran removes the boundary instead of crossing it: no descriptor to
fabricate, no mangling to guess, no copy -- a contiguous buffer reaches
the callee at the same address.

### Our domains

- **Computational chemistry** -- ChemSol, above.
- **HPC** -- one shape at every scale: split the data, compute each
  piece locally, combine with an associative function. `do concurrent`
  in one loop, threads in one process, coarrays across machines
  (parked until it earns its keep across machines; PACKAGES.md).
- **Binary data** -- real byte, short and char arrays with Clojure's
  signed semantics and bit operations, for instrument data, encryption
  and protocols. "Binary analysis is key to scientific software."
- **Reproducible numerics** -- `repro`: binned summation after Demmel
  and Nguyen, as in ReproBLAS, so a sum is the same bits on one thread
  or four hundred. Explicit by design; plain `reduce` stays serial and
  bit-identical to Clojure.
- **Linear algebra** -- `packages/blas`, `dgemm` on clotran arrays
  without a copy.

## The four scenarios

These are the north star: when weighing what to build next, the
question is which of these it serves.

### A. Modernising Python/Fortran data pipelines

*Pain.* Researchers use Python to glue Fortran binaries: Python does
configuration, ingest and control; Fortran does the computing. The
result is glue scripts, GIL bottlenecks and C-ABI bindings that break
on every compiler upgrade.

*Pitch.* Write the orchestration in Clojure -- immutable data, threads,
STM, REPL-driven development -- targeting Fortran arrays directly, with
no copy and no bridge.

*Where we stand.*

- Fortran libraries are **packages**: shared libraries the unchanged
  binary opens at run time (`packages/blas`, `packages/chemsol`).
  `scripts/bind-fortran` writes the binding from a library's own
  signatures. `examples/chemsol.cljf` replaces a Fortran main program
  and reproduces its output byte for byte on three reference inputs.
- Arrays are Fortran arrays: `double`, `long`, `int`, `float`, `boolean`,
  `byte`, `short`, `char` and object arrays, multi-dimensional through
  `make-array`, with Clojure's `aget`/`aset` semantics checked value by
  value against Clojure (`test/clj/oracle.clj`). Byte and short arrays
  are one and two bytes an element, for binary data.
- Immutable data, the seq library and transducers are core.clj's, so
  they are Clojure's -- 2880 of 2880 assertions in the derived language
  suite, 97.5% of clojuredocs.org's portable examples agreeing with
  real Clojure.
- Threads: a future runs on a thread of its own beside its maker
  (PLAN.md 14f, 2026-09-26); an agent's actions run in order on a
  thread of the agent's own; `dosync` is a transaction -- a log, a
  commit that validates then writes, watches notified -- with
  transactions serialized under one lock, which is a valid STM
  schedule without the retries (DEVIATIONS 10); a send inside an
  action or a transaction is held until it ends, as the JVM holds it.
  Not yet: a thread pool for agents, parallel marking in the collector.
- Not there: sockets and streaming network input.

### B. Dynamic scripting for legacy solvers

*Pain.* Changing a simulation strategy in WRF or a CFD code means
recompiling a large codebase or editing `namelist.input` by hand.

*Pitch.* Interactive control of a running solver: parameters tweaked at
a REPL, strategies expressed as code, evaluated inside or alongside the
Fortran runtime.

*Where we stand.*

- The REPL drives package routines directly: load a library, call its
  routines with clotran arrays, inspect the results, change a value,
  call again. ChemSol is exactly this shape today.
- The runtime has a C ABI (`src/f/ClotranABI.f90`) through which
  compiled code and packages reach the heap, and `examples/embed` is a
  Fortran program embedding it: a heat solver that owns `main` and its
  time loop, links the runtime in, loads core.clj and takes its control
  strategy from Clojure -- the initial condition, a source switched on
  mid-run, the stopping rule -- on the solver's own grid. Fortran
  integrates `u(:)` in place and Clojure's `aget`/`aset` read and write
  the same buffer; nothing is copied. `make test` runs it under both
  compilers and diffs its output.
- Text files: `slurp`, `spit`, `line-seq`, `clojure.java.io` for text;
  a namelist reader would be a small library on top.
- Not there: a REPL socket into the running program, so the strategy
  can be changed from outside while it runs; today the program
  evaluates the forms it is given.

### C. High-throughput financial modelling

*Pain.* Legacy Fortran yield-curve models must be exposed to cloud
services and event streams, and today that means JNI or FFI wrappers
around binaries.

*Pitch.* Functional data structures compiled into Fortran-compatible
numerical engines: lean, fast, deterministic binaries.

*Where we stand.*

- Compilation is ahead of time, per namespace, on request (`clotran
  compile`): 528 of core.clj's 529 defns compile; compiled calls are
  faster than interpreted ones (a small-fn loop 182 to 19 ms). What the
  generator does not yet emit -- closures, `lazy-seq`, `try`, `case`,
  protocol dispatch -- is handed to the interpreter (PLAN.md step 12).
- One binary, no runtime dependency: ICU is vendored and built from
  source; packages are pinned by sha256; no system package manager.
- Determinism: `packages/repro`, reproducible floating-point
  reductions, is planned (PACKAGES.md).
- Speed today, interpreted: 23x to 514x slower than a warmed JVM
  depending on the form (`scripts/bench`), the honest number for an
  AST interpreter; the compiler is how that closes.
- Not there: standalone linked binaries (step 12's direction), Kafka
  or any network client.

### D. Domain-specific languages for scientists

*Pain.* Physicists and climate scientists want to write the
mathematics, not memory layout, `GOTO`, implicit typing or manual
allocation.

*Pitch.* Clojure's macro system builds the DSL; declarative math
compiles down to clean, vectorizable Fortran.

*Where we stand.*

- The macro system is Clojure's own -- `defmacro`, syntax-quote,
  `clojure.spec` consulted at every expansion, as the JVM Compiler does.
  A DSL written for Clojure runs here unchanged.
- The compiler's pure-Fortran tier (PLAN.md step 13) is the path from a
  typed form to Fortran that has no heap value in it, with warnings
  that say what stopped a form reaching that tier.
- `fortran/make-array` and typed array hints exist; a matrix DSL over
  them would be a library.
- Not there: the vectorizable tier itself, and `do concurrent`
  emission (step 11's first stage).

## The landscape: Fortran software by domain, and how it is driven

What follows is what the domains actually run and what they glue it
with; the sources are listed at the end.

**Climate and weather.** CESM, WRF, MOM6, NEMO, MPAS, ICON, ECMWF's IFS
and GEOS-Chem are Fortran. They are configured through Fortran
namelists: CESM's CIME keeps settings in XML and generates each
component's namelist with a `buildnml` script; WRF reads
`namelist.input` (WRF-Hydro adds `hydro.namelist`). Analysis happens
after the run, in Python and xarray, from files the model wrote.

**Electronic structure and materials.** Quantum ESPRESSO, VASP, CP2K,
SIESTA, ABINIT, FLEUR, GAMESS and NWChem are Fortran. The workflow
layer is Python: ASE's calculators and AiiDA's plugins (30+ codes)
drive them by writing input files, running the executable and parsing
its output text -- Quantum ESPRESSO has no Python bindings, so that is
the only way in.

**Molecular dynamics and solvation.** AMBER's pmemd and sander, CHARMM,
DL_POLY and Tinker are Fortran (GROMACS, LAMMPS and NAMD are C++). Our
ChemSol is a Fortran solvation program; it is the one clotran drives
in-process today, and its output matches byte for byte.

**Engineering: FEA and CFD.** Abaqus takes constitutive models as
Fortran user subroutines (UMAT, VUMAT); ANSYS's equivalent is the UPF.
Python automates the model -- geometry, assembly, boundary conditions,
job submission -- while the physics is Fortran, compiled with Intel
Fortran and Visual Studio. NASA's FUN3D, OVERFLOW and CFL3D and Argonne's
Nek5000 are Fortran CFD codes.

**The Python scientific stack.** SciPy wraps Fortran -- ODEPACK,
QUADPACK, MINPACK, FITPACK, ARPACK -- through f2py, and its roadmap is
to remove all of it: the Fortran 77 is hard to maintain, wheel builds
break on new platforms (macOS arm64, Windows on Arm, Pyodide), and
"f2py is not cutting it anymore". The reference Python/Fortran bridge
is being abandoned by its biggest user.

**Finance.** Legacy risk and curve models in Fortran sit behind C++,
.NET and Python wrappers, alongside the NAG and IMSL numerical
libraries (NAG ships for C, C++, Python, Java, .NET and Fortran).
Translation projects to C++ run into paradigm and library differences
-- enough that LLM-assisted Fortran-to-C++ translation is a published
research topic.

**Nuclear, astrophysics, geophysics.** MCNP and RELAP5, MESA and FLASH,
SPECFEM3D: Fortran, driven by input decks and shell, read back with
Python.

### Existing solutions, and where each stops

| solution | what it is | where it stops |
|---|---|---|
| f2py / SciPy | the reference bridge | being removed by SciPy itself; F77 only; array layout mismatch |
| ASE / AiiDA | Python workflows over 30+ codes | by files: no shared memory, no REPL into a running calculation |
| namelists / CIME | XML to namelist to Fortran | a parameter change is a case rebuild |
| user subroutines | Fortran physics inside a vendor solver | recompile to change, `WRITE(*,*)` to inspect |
| jextract / JNA / Panama | JVM to C to Fortran | `bind(c)`: modern Fortran given up |
| rewrite in C++ | leave Fortran | the translation studies exist because it keeps failing |

### What clotran changes

The namelist becomes a map; the workflow becomes a function over values
rather than a parser over text; the code becomes a package whose arrays
cross at the same address; the constitutive model is developed at a REPL
against real arrays and compiled to Fortran for the solver; the legacy
financial model stays where it is with a compiled Clojure namespace
beside it in one binary. What is not there yet -- sockets, standalone
linked binaries -- is on the road in PLAN.md.

### Sources

- SciPy roadmap on Fortran removal: <https://docs.scipy.org/doc/scipy/dev/roadmap-detailed.html>; inventory <https://github.com/scipy/scipy/issues/18566>; "f2py is not cutting it" <https://fortran-lang.discourse.group/t/the-difficulties-of-using-fortran-in-scipy/6753>
- AiiDA plugin registry <https://aiida.net/plugin-registry/>; ASE plugin <https://aiida.net/wp-content/uploads/aiidadocs/plugins/ase/ase.html>; MaX workflows <https://www.max-centre.eu/software/workflows>
- Abaqus user subroutines <https://www.3ds.com/fileadmin/PRODUCTS-SERVICES/SIMULIA/RESOURCES/user_subroutines-summary.pdf>; UMAT to UPF <https://www.researchgate.net/post/Crystal_plasticity_Fortran_code_for_usermat_in_ansys>; Python + Fortran in Abaqus <https://www.fidelisfea.com/post/abaqus-fortran-user-subroutines-what-they-are-and-how-to-execute-them>
- CIME namelists <https://esmci.github.io/cime/versions/cesm2.2/html/users_guide/cime-change-namelist.html>; WRF-Hydro configuration <https://wrf-hydro.readthedocs.io/en/readthedocs/model-code-config.html>
- NAG Library <https://nag.com/nag-library/>; LLM-assisted Fortran to C++ translation <https://arxiv.org/pdf/2504.15424>

## What is true today, measured

| measure | value |
|---|---|
| core.clj | 724 of 724 forms load, unmodified, pinned to `71b4623d` |
| our tests | 100% on gfortran and flang, the commit gate; 1039 oracle forms value-compared against `clj`, 0 unexpected differences |
| derived language suite | 2880 pass / 0 fail / 0 error over 321 tests |
| clojuredocs.org examples | 1233 of 1264 portable examples agree with real Clojure (97.5%) |
| Clojure's own library tests | set, walk, string, math, pprint verbatim: 859 assertions, 0 failures |
| libraries loading | 35 of 40 vendored namespaces `require` |
| deviations | 57 recorded in DEVIATIONS.md, 18 resolved; every known difference has an entry |
| startup | 0.2 s from the heap image (`make image`); 1.4 s from source; 125 MB resident |
| speed | 23x to 514x the JVM's time, interpreted |

The denominators matter: "portable" excludes examples that name a Java
class; the language suite is the clojure.core/cljs.core intersection;
a pass rate is over assertions that executed.

## The road

1. **The test suites.** The clojuredocs suite to 100% of portable
   examples: known deviations, then performance (constant-space lazy
   walks, `count` of a range in O(1)), then the long tail.
2. **Threads.** Futures, agents and transactions run as Clojure means
   them (PLAN.md step 14, landed 2026-09-26 and 2026-09-28). What is
   left is speed: parallel marking in the collector, a thread pool
   for agents, and the collector's pauses measured with many threads.
3. **Everything else works.** The compiler's remaining node kinds, the
   pure-Fortran tier, standalone binaries, sockets, a REPL socket into an embedding
   example -- each weighed against the four scenarios.

## What clotran is not

Not a Clojure-like language: the language is Clojure's source. Not a
Fortran-to-Clojure translator. Not a JVM emulator: matching Java's
classes is not the goal, and `SEAMS.md` records which parts of
`clojure.lang.*` are the language and which are Java showing through.
