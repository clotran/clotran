# clotran 1.0.0 -- release notes

clotran is Clojure hosted on Fortran: Rich Hickey's own `core.clj`, from
the `clojure-1.12.6` release, running on a Fortran host. 1.0 is the
language as the smallest package: the binary, its heap image, the
Clojure sources it loads, the launcher, and `clotran-deps` beside it to
pull in everything else from a project's `deps.edn` (`PLAN.md` step 35).
README's Versions section says what a patch, a minor and a major may
change.

## What 1.0 is

- **The language, from Clojure's own source.** All 719 top-level forms
  of `core.clj` load, as written; the libraries Clojure vendors with it
  load beside it, and `clojure.spec.alpha` is consulted before every
  macro expansion, as Clojure's compiler does.
- **Measured against Clojure itself.** `clj` 1.12.6 is the oracle for
  every behaviour: 1,325 forms run through both, 1,303 agreeing and 22
  differing as their DEVIATIONS entries say they must, none otherwise. Clojure's own test suite, derived
  to the language that clj and ClojureScript share: 39 namespaces, 312
  tests, 2,719 assertions, every one passing and every namespace run.
  The portable libraries (set, walk, string, math, pprint) on Clojure's
  own tests, verbatim: 141 tests and 1,009 assertions, 1,001 passing
  and 8 failing as `test/clj/library-expected.edn` says they must -- each
  tests clj's host (a proxy's superclass, a semaphore, clj's class names)
  and is a DEVIATIONS entry.
- **Every place it differs is written down.** `DEVIATIONS.md` names each
  difference, why, and what removing it would take, with its kind:
  81 entries, 41 resolved and kept as the record, 29 by design, 6 forced
  by the host, 4 staying through 1.0 by decision (48, 51, 54, 74). One
  is open for a decision: entry 33, reader
  conditionals read in every file rather than only in `.cljc`.
- **Fortran underneath, on purpose.** Arrays are Fortran arrays a
  library takes as they are; a package is a shared library opened at run
  time, its shims written by `scripts/bind-fortran` from the library's
  own signatures; `clotran compile` turns a namespace into Fortran, and
  a numeric function into a pure Fortran loop that needs no runtime.
- **Threads.** A future runs on an OS thread of its own; agents on a
  pool of workers designed in ACL2 (`model/agents.lisp`); `dosync` a
  transaction with a log and a commit.

## Said plainly

- **Speed.** An interpreter: 2x to 17x slower than a warmed clj on
  general code, 35x to 209x on numeric loops over arrays written inline
  (`scripts/bench`, README's table). `clotran compile` turns those loops
  into pure Fortran that runs in 1.0 to 3.7 ms where clj takes 13 to 17;
  core itself still runs interpreted. Startup is 0.17 s from the heap
  image.
- **The debugger** is data: a break is a map of frames and locals
  handed to a handler, the REPL by default. Steps count calls, not
  lines; one level, so a break inside the handler is a snapshot; no
  socket.
- **Interop** is `call-package*` over the shims `bind-fortran`
  generates. Derived types, optional and pointer dummies are listed,
  not bound -- the first thing in 1.x. A package built by a compiler
  other than clotran's brings a second Fortran runtime into the
  process; built by clotran's own is the supported case.
- **The host is Fortran, not clj's.** Classes have clotran's names
  (`clotran.host.int8`, not `Long`), `.hashCode` is not a member, a
  string is indexed by code point, a shift by 64 follows Fortran: each
  is a DEVIATIONS entry of kind *design*.

## Platforms

- **macOS** (arm64): built and gated with gfortran and flang.
- **Linux**: built and gated in a container (Debian 13, gfortran and
  flang, aarch64). The release is a tarball built on glibc 2.28
  (manylinux_2_28) carrying the libraries the binary needs beyond the
  C library -- libgfortran, libquadmath, libstdc++, libgcc_s -- beside
  it, so it runs on any glibc as new or newer: Debian 10, Ubuntu 18.10,
  RHEL 8 and on. It is not a static binary: packages and compiled
  namespaces are opened into the running binary and resolve its
  symbols, which a static glibc or musl binary cannot do. `clotran
  compile` needs a gfortran on the machine. The aarch64 tarball was run
  on Debian 10, Ubuntu 20.04 and 24.04, Fedora (glibc 2.43) and Rocky 9:
  a program, a `deps.edn` project, a future, a Unicode regex
  (`scripts/dist-check`). Alpine has a tarball of its own, `-musl`,
  built on Alpine 3.20 and run the same way on 3.20, 3.22 and edge --
  dynamically linked, so packages open as on glibc; musl's gfortran on
  aarch64 has no `ieee_arithmetic`, and clotran's own bit-level version
  stands in (`src/f/ieee_lite.f90`, checked against the intrinsic one on
  every gate). x86_64 is built the same way (`scripts/dist-linux
  x86_64`, emulated on an arm64 machine) and is gated nowhere yet.
- **Windows** is not in 1.0: the build needs a mingw gfortran toolchain
  and a runner to gate on (PLAN step 35, item 6).

## Install

    tar xzf clotran-1.0.0-<os>-<arch>.tar.gz
    clotran-1.0.0-<os>-<arch>/bin/clotran

or from a checkout, `make install` (README, "Build"; `PREFIX=` names
where). `make dist` builds the tarball for the machine it runs on, and
`scripts/dist-linux` the Linux one in its container.
