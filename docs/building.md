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
source, which takes a few minutes once; after that it is cached. ICU's
data is cut to what regex and case mapping read (the Makefile's
`ICU_KEEP`, applied by ICU's own `icupkg`), most of the difference
between a 38 MB binary and a 9.5 MB one.

`make crosscheck` is the gate before a commit, on this machine.
`scripts/gate-linux` runs it in a Debian container (Docker), and
`scripts/gate-wsl` on an x86_64 machine's WSL; `make fuzz-all` runs
every fuzzer at full size, for a release candidate. Each writes a log
whose last line is `EXIT n`, and that line is the verdict.

To have the build on your PATH:

```
make install                        # into ~/.local: ~/.local/bin/clotran
sudo make install PREFIX=/usr/local # or anywhere else
make uninstall                      # the same PREFIX
```

What it installs, and `clotran-deps` beside it, is in `guide.md`
(Dependencies and editors); the licenses a distribution carries --
`LICENSE`, `NOTICE`, Clojure's `epl-v10.html`, ICU's -- go in beside the
binary. `make dist` makes the same install relocatable, as the release
archive for this machine (`scripts/dist-bundle`); `scripts/dist-linux`
builds the Linux ones in their containers.

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

`./clotran` runs `clotran-bin --launch`. On a terminal the REPL edits
its own input -- history, Tab completion from the running REPL,
multi-line forms (`src/clj/clotran/lineedit.cljf`); `CLOTRAN_NO_EDITOR=1`
reads plain lines instead. It works
from any directory: the binary finds its home, image and sources from
its own path. `./clotran-bin` without `--launch` is the interpreter
alone, a plain stdin/stdout REPL that loads only the files named on its
command line, which is what the scripts and the Makefile use, passing
core.clj explicitly.

## Beside the checkout

Some of the build looks in `..`, for siblings:

- `../clotran-deps` -- the package manager (`CLOTRAN_DEPS=dir` names
  another). `make install` installs it beside clotran, and
  `check-install` runs a `deps.edn` project through the pair.
- `../clotran-nrepl` and `../clotran-ide` -- the nREPL server and the
  language server (`CLOTRAN_NREPL`, `CLOTRAN_IDE`), which `check-nrepl`
  and `check-lsp` run beside the checkout and then as an installed
  clotran fetches them, by the commits `tools.edn` pins; `../cljfmt`,
  whose tests `check-cljfmt` runs. Each check skips without its
  checkout.
- `../clojure` and `../clojurescript` -- clones of Clojure at
  `clojure-1.12.6` and ClojureScript at `r1.12.145`, which
  `upstream/derive-tests` and `scripts/clojuredocs` read. The derived
  tests are committed, so a build and the gate need neither.
- `../acl2/saved_acl2` -- ACL2, which `make model` runs to certify the
  books in `model/` (`ACL2=path` names another). The gate does not need
  it; `make fuzz-door` does.

`clj` itself (the Clojure CLI, with a JDK) is the oracle `make test`
runs the same forms through, and `bb` (babashka) runs the scripts.

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
  clotran's own checks (`oracle.clj`, `language_test.clj`, and
  `fuzz-regressions.edn`, every case a fuzzer found). The
  conformance measure is `test/clj/derived/`, run by
  `scripts/run-clojure-tests-parallel test/clj/derived`.
- `model/` -- the ACL2 books: the VM, the allocator and collectors, the
  agent pool, each proved before it was built (`model-coverage.md`).
- `scripts/` -- babashka scripts: the oracle, the fuzzers, the gates
  and the release.
- `packages/` -- BLAS and ChemSol as packages (`../PACKAGES.md`), and
  `packaging/` -- the Linux containers, and the Windows commands and
  notices a release carries.
- `examples/` and `bench/` -- what the README and `guide.md` run, and
  what `scripts/bench` and `scripts/bench-langs` time.
- `clotran` -- the command, and `clotran-bin` the binary it runs
  (see above).
