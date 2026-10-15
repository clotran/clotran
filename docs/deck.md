---
title: "clotran"
subtitle: "Clojure, hosted on Fortran"
date: 2026-10-14
---

## Clojure, hosted on Fortran

- Runs Rich Hickey's `clojure/core.clj` -- the file from Clojure 1.12.6, its classes in clotran's names
- The Fortran host stands where the JVM stands
- One binary. No JVM, no Python, no bridge
- A clotran array **is** a Fortran array; a Fortran routine is a function call

```
user=> (->> (range 20) (filter odd?) (partition-all 3) (map vec))
([1 3 5] [7 9 11] [13 15 17] [19])
```

## The problem we solve

- Scientific and financial computing runs on Fortran
- The orchestration around it is glue: Python/f2py, shell, namelists, C bindings
- The glue is where the pain is: brittle, GIL-bound, "recompile to change a parameter"
- Clojure is the orchestration language that glue is missing -- but the JVM cannot touch a Fortran array without a copy

## Four goals, in order

1. **Complete Clojure/Fortran interoperability** -- a clotran array is a Fortran array; a Fortran routine is an ordinary call
2. **A better way to debug Fortran** -- `(clotran-break)` hands over the paused state as data: frames, locals by name, step in, over and out
3. **A multi-threaded story** -- Clojure's: immutable values, atoms, refs, agents, STM, on OS threads
4. **Compilation** -- ahead of time, per namespace, to Fortran; pure Fortran modules; one executable per program

Everything is weighed against these four. The pure Clojure language is reproduced; the JVM is an implementation detail we do not have.

## Why host on Fortran instead of bridging to it

- Every FFI reaches **F77**: scalars by reference, explicit-shape arrays, no allocatables, no derived types. BLAS is that subset -- which is why BLAS bindings are easy
- Above F77 there is **no ABI**: assumed-shape arrays, `allocatable`, `optional`, `class(*)` travel as compiler-private descriptors, mangled per compiler
- `bind(c)` is a promise *not* to use Fortran written after 1990
- The same descriptor is why **gdb cannot show you a Fortran object**
- Hosting *on* Fortran removes the boundary: no descriptor to fabricate, no mangling, no copy -- verified at the same address

## Our domains: scientists

| domain | what we ship or plan |
|---|---|
| **Computational chemistry** | ChemSol: a Fortran main program replaced by `examples/chemsol.cljf`, output identical byte for byte |
| **HPC** | one shape at every scale -- split, compute locally, combine: `do concurrent`, threads, coarrays across machines |
| **Binary data** | real byte, short and char arrays with Clojure's signed semantics: instrument data, encryption, protocols |
| **Reproducible numerics** | `repro`: binned summation, the same bits on 1 thread or 400 (Demmel-Nguyen, as ReproBLAS) |
| **Linear algebra** | `packages/blas`: `dgemm` on clotran arrays, no copy |

## The pitch to a Fortran shop

- **Keep your Fortran.** Nothing is rewritten; a library becomes a package, pinned by sha256, opened at run time by the one unchanged binary
- **Your arrays, not copies of them.** Column-major, typed, at the same address on both sides
- **A REPL and a debugger over your code.** Call a routine, look at the result, change a value, call again; frames the host can describe, which DWARF cannot
- **All of Clojure, unmodified.** The language comes from Clojure's own source; a Clojure programmer is productive on day one
- **No JVM, no Python, no system package manager.** One binary, packages, two compilers agreeing before every commit

## Four scenarios -- the north star

| | pain | pitch |
|---|---|---|
| **A** Pipelines | Python gluing Fortran binaries | Clojure orchestration over Fortran arrays, no copy |
| **B** Legacy solvers | recompile or edit namelists | REPL-driven control of a running solver |
| **C** Finance | JNI/FFI around legacy models | functional code compiled to lean deterministic binaries |
| **D** DSLs | memory layout, GOTO, implicit typing | macros compile math to vectorizable Fortran |

## A. Pipelines -- today

- Fortran libraries are **packages**: shared libraries opened at run time, pinned by sha256
- `scripts/bind-fortran` writes the binding from the library's own signatures
- `examples/chemsol.cljf` replaces a Fortran main program: same output, byte for byte
- Arrays of every primitive kind, `aget`/`aset` checked value by value against Clojure
- Futures on OS threads; agents on a work-stealing pool proved in ACL2; `dosync` a real transaction, serialized
- `deps.edn` projects, `clotran-deps`, TCP sockets and a socket REPL
- Missing: parallel marking in the collector

## B. Legacy solvers -- today

- The REPL calls package routines on clotran arrays: load, call, inspect, change, call again
- A C ABI (`ClotranABI`) is the surface an embedding host uses
- Text files in and out: `slurp`, `spit`, `line-seq`
- `examples/embed`: a Fortran heat solver with clotran linked in; its initial condition, a mid-run source and the stopping rule are Clojure, on the solver's own grid, no copy
- A socket REPL into the running solver: read the live grid, write it, stop the run

## C. Finance -- today

- Ahead-of-time compilation per namespace; numeric code lowers to pure Fortran
- Those loops: 1.0 -- 3.7 ms compiled, where a warmed clj takes 13 -- 17
- `clotran build`: one executable, no install, no sources, 0.2 s to start
- No runtime dependency: ICU vendored, packages pinned, builders pinned by digest
- Missing: reproducible reductions (`repro`), message-queue clients

## D. DSLs for scientists -- today

- The macro system is Clojure's own; `clojure.spec` checked at every expansion
- A DSL written for Clojure runs unchanged
- `clotran compile --pure`: typed math to an ordinary Fortran module, no runtime in it
- `--report` says what kept a form out; `pure-check` compares clj, gfortran and flang
- Missing: `do concurrent` emission

## The landscape (1): science runs on Fortran

| domain | Fortran codes | driven today by |
|---|---|---|
| **Climate & weather** | CESM, WRF, MOM6, NEMO, MPAS, ICON, IFS | XML and shell to **namelists** (CIME, `namelist.input`); Python after the run |
| **Electronic structure** | Quantum ESPRESSO, VASP, CP2K, SIESTA, ABINIT | **ASE**, **AiiDA**: write input files, run the binary, parse the text |
| **Molecular dynamics** | AMBER, CHARMM, DL_POLY, Tinker; ChemSol | shell and Python around executables |
| **Nuclear, astro, geo** | MCNP, RELAP5, MESA, FLASH, SPECFEM3D | input decks; Python readers |

## The landscape (2): engineering, Python, finance

| domain | Fortran codes | driven today by |
|---|---|---|
| **FEA and CFD** | Abaqus / ANSYS **user subroutines** (UMAT, UPF); FUN3D, OVERFLOW, Nek5000 | Python scripts the model; physics compiled with Intel Fortran + Visual Studio |
| **Python scientific stack** | SciPy's ODEPACK, QUADPACK, MINPACK, ARPACK | **f2py** -- which SciPy is now removing, Fortran and all |
| **Finance** | legacy risk and curve models; NAG, IMSL | C++, .NET and Python wrappers; translation projects to C++ |

## Existing solutions, and where they stop

- **f2py / SciPy** -- the reference bridge. SciPy's own roadmap: remove all Fortran, because f2py "is not cutting it", wheels break on new platforms, Fortran arrays cannot be sliced the way NumPy needs. *The bridge is being abandoned by its biggest user.*
- **ASE / AiiDA** -- 30+ codes, but by files: write the input, run the binary, parse the text. No shared memory, no REPL into a running calculation, one process per step.
- **Namelists + CIME** -- XML generates namelists generates Fortran reads; a parameter change is a case rebuild.
- **User subroutines (UMAT, UPF)** -- your physics in Fortran, compiled into the vendor's solver; changing it is a recompile, inspecting it is `WRITE(*,*)`.
- **jextract / JNA / Panama** -- reach F77 only; `bind(c)` gives up modern Fortran.
- **Rewrite in C++** -- the LLM-assisted translation studies exist because the rewrites keep failing on paradigm and library differences.

## What clotran changes (1)

- **Climate & weather** -- the namelist is a map; the run is orchestrated in-process; a parameter changes at the REPL between steps, no case rebuild
- **Electronic structure & MD** -- the code is a package; arrays cross at the same address; a workflow is a function over values, not a parser over text
- **Nuclear, astro, geo** -- input decks generated from data, output read as values; the REPL and the debugger over the run

## What clotran changes (2)

- **FEA and CFD** -- the constitutive model is written and tested at a REPL against real arrays, then compiled to Fortran for the solver
- **Python stack** -- the Fortran SciPy is dropping runs unchanged as packages, with Clojure's data structures in front
- **Finance** -- the legacy model stays; a compiled Clojure namespace sits beside it in one binary, no JVM to certify

## Measured: the 1.0 release candidate

| | |
|---|---|
| core.clj | 719 / 719 forms load |
| our tests | 100% on gfortran **and** flang -- the gate |
| oracle vs real Clojure | 1332 forms: 1310 agree, 22 differ as recorded, 0 unexpected |
| derived language suite | 2719 / 2719 assertions |
| clojuredocs.org examples | 1233 / 1264 portable agree (97.5%, scored 2026-09-27) |
| deviations | 81 recorded, 41 resolved, none unrecorded |
| platforms | macOS arm64; Linux aarch64, x86_64 (glibc, musl); Windows x86_64 |
| speed | interpreted: 2x -- 17x a warmed clj on general code; numeric loops compiled: faster than clj |
| startup | 0.17 s from the heap image |

## How we keep ourselves honest

- `clj` is the oracle: no expected value is typed by hand
- Two compilers must agree before anything is committed
- Every deviation from Clojure has a written entry, or it is a bug
- Scorecards name their denominators

## The road

1. **Interop beyond F77** -- derived types, `optional` and pointer dummies bound, not just listed
2. **Speed** -- core compiled, so general code stops paying the interpreter; parallel marking
3. **Tooling** -- editor support and each platform's package manager
4. **Packages** -- `repro`, a matrix DSL, plotting and a GUI as Clojure libraries

## Why Fortran as the host

- Arrays, numerics and the libraries scientists already run are Fortran's
- Hosting Clojure there gives the orchestration layer the same memory, no bridge
- Column-major, typed, allocation-free numerics are the *default*, not a foreign call
- The language is Clojure's source, so it stays Clojure as Clojure moves
