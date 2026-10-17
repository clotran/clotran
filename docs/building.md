# Building clotran

clotran builds and passes on macOS arm64, Linux aarch64 and x86_64
(glibc and musl), and Windows x86_64 (MSYS2 UCRT64).

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

To have the build on your PATH:

```
make install                        # into ~/.local: ~/.local/bin/clotran
sudo make install PREFIX=/usr/local # or anywhere else
make uninstall                      # the same PREFIX
```

What it installs, and `clotran-deps` beside it, is in `guide.md`
(Dependencies and editors).

On Windows the build is native, in MSYS2's UCRT64 environment (its
gfortran, gcc, make and git: `pacman -S mingw-w64-ucrt-x86_64-gcc-fortran
mingw-w64-ucrt-x86_64-gcc mingw-w64-ucrt-x86_64-libgomp make git`), with the
same commands. The binary is `clotran-bin.exe`, its runtimes linked in, so
it and a program `clotran build` makes run where there is no MSYS2. A
release (`make dist`) is a zip: `bin\clotran.cmd` runs
`clotran-bin.exe --launch`, the command itself, with no shell.

On every system the command is `clotran-bin --launch`: the binary loads
core and `clotran.launcher` reads the arguments (`new`, `compile`,
`build`, `test`, a project's `deps.edn`), running whatever it needs --
the Fortran compiler, a clotran of its own -- from an argument list
(`clotran-run`), never through a shell.

`./clotran` is the entry point, a shell script: it hands `clotran-bin`
core.clj and wraps the REPL in `rlwrap` when there is a terminal and
`rlwrap` is installed, for history and arrow-key editing, exactly the
way real Clojure's own `clj` wraps `clojure`. Files named after it load
after core.clj, so `./clotran prog.cljf` runs a program. It works from
any directory: the binary takes its own directory as a classpath root.

`./clotran-bin` is the interpreter alone, a plain stdin/stdout REPL that
loads only the files named on its command line -- which
is what the scripts and the Makefile use, passing core.clj explicitly.

```
./clotran
```

## Layout

- `src/f` -- the Fortran host: value representation, a tracing GC,
  persistent list/vector/map, namespaces, reader, evaluator.
- `src/c` -- vendored ICU, built from source for regex (no Homebrew,
  no system library, no runtime dependency), and the small C shims the
  host needs: sockets, the filesystem, the JIT's memory, Windows.
- `upstream/` -- Clojure's own source and test suite, vendored and
  unmodified, and `derive`, which writes them into `src/clj/clojure`
  and `test/clj/clojure` in clotran's class names.
- `src/clj` -- that derived source, and clotran's own (`src/clj/clotran`).
- `test/f` -- unit tests for the Fortran host, one file per module.
- `test/clj` -- Clojure's own test suite, derived the same way, and
  clotran's own checks (`oracle.clj`, `language_test.clj`). The
  conformance measure is `test/clj/derived/`, run by
  `scripts/run-clojure-tests-parallel test/clj/derived`.
- `clotran` -- the launcher, and `clotran-bin` the binary it runs
  (see below).
