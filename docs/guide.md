# Using clotran

Running programs and projects, Fortran arrays and packages, compiling,
the debugger and threads. Install it first (`README.md`); what is
measured and what is missing is in `docs/status.md`.

## Programs and projects

A new project -- `deps.edn`, `src/NAME/core.cljf`, a test, a README:

```
$ clotran new my-app
```

Running a program is as with `clj -M`: a file with arguments, or a
namespace's `-main`. Either ends when the program does, with status 1 on
an uncaught error. `clotran test` runs the project's `-test` namespaces
through `clojure.test`, with `deps.edn`'s `:test` alias, and ends with
status 1 on a failure:

```
$ clotran app.cljf a "b c"            # *command-line-args* is ("a" "b c")
$ clotran -m my-app.core a b          # (my-app.core/-main "a" "b")
$ clotran test                        # every -test namespace under test/
```

`clotran build` makes one executable of a program: the binary, with the
heap image of the program's namespace loaded, the compiled libraries of
what it loaded, and its entry appended. It needs no clotran installed
and no sources where it runs, starts in about 0.2 s, and is about 130 MB
(the image is most of it). The program's own code runs compiled -- a
loop 19x faster than interpreted -- and core, for now, interpreted;
`--interpreted` leaves the libraries out:

```
$ clotran build -m my-app.core -o my-app
$ ./my-app a b                        # (my-app.core/-main "a" "b")
```

## Dependencies and editors

`make install` installs clotran -- the binary, its heap image, the Clojure sources
it loads on first use, and the launcher -- under `PREFIX/lib/clotran`,
built for this machine's architecture, and beside it the package
manager, `clotran-deps`, from the checkout next to this one
(`CLOTRAN_DEPS=dir` names another), as the `clj` script ships
tools.deps. In a directory with a `deps.edn`, `clotran` asks it for the
project's path; nobody sets `CLOTRAN_PATH` by hand. Everything else --
packages, and the optional tools (`clotran-nrepl`, `clotran-mode`) --
comes from a project's `deps.edn` as a `:local/root` or a `:git/url`
pinned by its full `:git/sha` (`PACKAGES.md`).

For Emacs, `clotran-mode` opens `.cljf` files in clojure-mode and has
`M-x clotran-jack-in`, which starts clotran with the nREPL server from
`clotran-nrepl` and connects the stock CIDER to it. Both are separate
libraries, not yet published.

## What it does

**Real Fortran arrays**, which is the one thing this host has that the
clj does not:

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
(alias 'f 'fortran)
(def a (f/make-array "real8" 2 3))    ; 1 2 3 / 4 5 6
(doseq [i (range 2) j (range 3)] (f/aset a i j (double (+ 1 (* 3 i) j))))
(def b (f/make-array "real8" 3 2))    ; 7 8 / 9 10 / 11 12
(doseq [i (range 3) j (range 2)] (f/aset b i j (double (+ 7 (* 2 i) j))))
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
with no copy. `scripts/bind-fortran` writes the shims and manifest for a library from its own signatures, so a package is declared rather than hand-bound. PLAN.md step 7
records what the library dictated for it.

**A Fortran program can embed clotran.** `examples/embed/heat.f90` is
a heat solver that owns `main` and its time loop and links the runtime
in (the same objects as `clotran-bin`), booting it through the C
surface with no clotran module used. It loads core.clj and
`examples/embed/control.cljf`, asks Clojure for the grid, and takes a
pointer to it: the Fortran loop integrates `u(:)` in place while the
strategy -- initial condition, a source switched on at step 300, the
stopping rule -- is Clojure reading and writing the same buffer with
`aget` and `aset`. `make embed && examples/embed/heat` prints

```
clojure  wrote a pulse            total  100.000  peak  100.000
fortran  read it back              total  100.000  peak  100.000
clojure  step  100                 total   99.998  peak    5.635
clojure  step  200                 total   99.671  peak    3.987
clojure  switched a source on at cell 8
clojure  step  300                 total  137.964  peak   40.462
...
clojure  step 1100                 total   76.337  peak    1.908
fortran  stopped at step 1100      total   76.337  peak    1.908
```

and `make test` diffs that output under both compilers.

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
branch beside each `:clj` one. `.clj` is clj, which clotran
loads as written -- that being the point. `require` looks for the
three in that order.

**Sorted collections.** `sorted-map`, `sorted-map-by`, `sorted-set`,
`sorted-set-by`, `subseq`, `rsubseq` and `rseq`, from core.clj's own
definitions: a sorted map is the array map with its keys kept in
a counted B+-tree in comparator order, O(log n) to find, insert and
remove, as clj's red-black tree is, and a sorted set is a set over one. Verified: `(subseq (sorted-set 1 2 3 4 5) >= 2 < 4)`
is `(2 3)`, and `(into (sorted-set) (range 20 0 -1))` counts up.

**Host members written in Clojure.** `sequence`, `eduction`,
`iterator-seq`, `volatile!`, `shuffle` and the transducers that buffer
(`partition-all`, `partition-by`) are core.clj's own definitions, which
name `RT/iter`, `RT/chunkIteratorSeq`, `TransformerIterator`,
`ArrayList` and `Eduction`. ClojureScript writes those in
Clojure, so clotran does too: `src/clj/clotran/rt.cljf` holds them,
the host table's rows for those members call its vars, and the file
loads the first time one is reached. `Volatile` is a box the host
supplies. Verified: `(sequence (comp (take 3) (map inc)) (range))` is
`(1 2 3)`, and `(into [] (partition-by odd?) [1 3 2 4])` is
`[[1 3] [2 4]]`.

Clojure's OWN array functions run over the same representation -- not
reimplemented, the definitions in `core.clj`, which are written against
`Array` and `RT`:

```clojure
(def m (make-array clotran.host.int4/TYPE 2 3))
(aset-int m 1 2 22)
(aget m 1 2)                          ;=> 22
(alength m)                           ;=> 2   ; the OUTER length
(alength (aget m 1))                  ;=> 3   ; a row is an array
```

A clj `[[I` is two separate row objects; ours is one rank-2 block, so
`(aget m 1)` hands back a strided VIEW over the same buffer -- writing
through it is visible in the parent, as it is in clj. The cost is
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
nested REPL, and this is verified output (`scripts/readme-check` runs
it):

```
user=> (defn sq [x] (* x x))
#'user/sq
user=> (defn hyp [a b] (clotran-break) (+ (sq a) (sq b)))
#'user/hyp
user=> (hyp 3 4)
break: :break 
  0 user/hyp (1:17)
      a = 3
      b = 4
;; (clotran-resume :continue | {:continue v} | :step-in | :step-over | :step-out | :abort)
[1] user=> (:env (first (:frames (clotran-last-break))))
{a 3, b 4}
[1] user=> (clotran-resume :step-in)
break: :step 
  0 user/sq (1:14)
      x = 3
  1 user/hyp (1:36)
      a = nil
      b = 4
;; (clotran-resume :continue | {:continue v} | :step-in | :step-over | :step-out | :abort)
[1] user=> (clotran-resume :continue)
25
```

`a` is nil in the second break because its last use has passed: the
compiler's locals clearing, which clj does too.

`(clotran-break-on! true)` breaks at every error too, taken at the
throw so the frames are still there, and `CLOTRAN_BREAK_FILE=path`
appends every break to a file for a run that ends before anyone can
ask. Steps count calls, not lines, since a call is the event the
executor has: in stops at the next call anywhere, over walks the
current fn's own calls without descending, out stops at the next call
once the current frame has returned. Evaluating in a frame is the
handler's own `let` over `:env`, since locals are immutable and the
values are already in the map.

**Futures, promises and agents, on threads.** core.clj's own `future`,
`promise`, `pmap`, `pcalls`, `pvalues`, `deref` and agents, verbatim:
a future runs on an OS thread of its own beside its maker, and an
agent's actions on a pool of workers (`docs/status.md`'s table says
more, and DEVIATIONS 29 and 38 how they came to be). Verified:

```clojure
(def p (promise))
(def f (future (* 3 @p)))
(realized? f)                                  ;=> false
(deliver p 5)
@f                                             ;=> 15
(pmap inc [1 2 3])                             ;=> (2 3 4)
(deref (promise) 10 :nobody-delivered)         ;=> :nobody-delivered
(let [a (agent 0)] (send a + 5) (await a) @a)  ;=> 5
```

**A thread is a contract.** `clotran.thread` is the protocol a kind
of thread implements -- `spawn`, `join`, `status`, `cancel!`, a
mailbox with `send!` and `receive`, and `self` for replies -- with one
current kind, the way core.matrix keeps a current implementation. The
default, `:green`, is the task a future is; another kind -- a process,
a coarray image -- would answer the same names. Verified:

```clojure
(require '[clotran.thread :as t])
(t/kind-name)                                  ;=> :green
(def worker (t/spawn (fn [] (* 12 (t/receive)))))
(t/send! worker 12)
(t/join worker)                                ;=> 144
(t/status worker)                              ;=> :done
```

## Compiling a namespace

`clotran compile stats.cljf` turns every `defn` in the file into
Fortran and builds `stats.dylib` (`stats.so` on Linux) beside it.
Loading `stats.cljf` afterwards -- by `load-file`, `require` or the
command line -- loads the source as usual and then puts the compiled
functions in place of the interpreted ones. No hints needed:

```clojure
(ns stats)
(defn total [a]
  (let [n (alength a)]
    (loop [i 0 s 0.0] (if (< i n) (recur (inc i) (+ s (aget a i))) s))))
```

    $ ./clotran compile stats.cljf
    pure Fortran: total (2 versions)
    compiled: 1 functions; 1 pure Fortran
    wrote stats.dylib

`(stats/total (double-array (range 200000)))` takes 134 ms
interpreted and 0.192 ms compiled; a warmed clj takes 0.202 ms with a
`^doubles` hint and 515 ms without one. Each function's road is
printed: a function the tier report calls A (numbers and arrays in,
a number or an array out) is compiled as PURE Fortran, a plain loop with no
clotran runtime underneath, behind a dispatcher that unboxes the
arguments by their tags and boxes the answer; one version per
combination of argument types, so `total` of a `long-array` is its
own loop. Any other arguments go to the same function compiled
through the runtime, and an error inside the pure loop -- an index
out of bounds, a long overflow -- is the exception the interpreter
throws, with its class and message, caught by the same `try`. A pure
loop runs with the mutators released, as a foreign routine does, so
one in a `future` never holds up another thread's collection. What
the compiler declines -- a variadic function, say -- stays
interpreted and says why. Edit the source and the library is
reported stale and not used until it is recompiled.
`scripts/compiler-check` runs every case both ways and compares the
answers, and `scripts/pure-check` runs its cases through the installed
library against `clj`.

With `CLOTRAN_AUTOCOMPILE=1`, `./clotran` compiles what it loads, in the
background, into a cache (`~/.cache/clotran`, or `$CLOTRAN_CACHE`), and
installs a namespace from the cache whenever the same text loads again.
It is off by default for now: compiled core still calls through heap
frames, and seq code runs slower compiled than interpreted --
`(apply + (take 1e6 (range)))` takes 1440 ms with it and 915 without.
Numeric code like the example below still gains, so turn it on for
that.
A namespace you are working on goes around the loop by itself: edit it,
reload it, and it runs interpreted while its new build compiles; at a
later prompt the REPL says so and the compiled version is in place, with
no restart:

    user=> (load-file "demo_impl.cljf")
    user=> (time (demo-impl/sumsq 300000))
    "Elapsed time: 716.8 msecs"
    user=> (clotran.loader/compile-status)
    {"demo_impl.cljf" :compiling, ...}
    note: demo_impl.cljf is compiled now
    user=> (time (demo-impl/sumsq 300000))
    "Elapsed time: 1.033984 msecs"

`(clotran.loader/compile-now "file.cljf")` builds and installs at once,
waiting for it; `CLOTRAN_AUTOCOMPILE=0`, the default, turns all of this off. What you
type at the prompt stays interpreted: a build takes seconds, and the
form you typed takes microseconds -- the time is spent in the
namespaces it calls, and those are the ones that get compiled.

## Which code can be pure Fortran

`clotran compile --report file.cljf` sorts every function into a tier --
**A** pure Fortran, needing no clotran runtime; **B** the collector and
collections; **C** the interpreter -- and, at every call site that
leaves tier A, says why and what would keep it there:

    tier A  tiers-sample/sum-squares
    tier B  tiers-sample/squares

    warning[B001]: lazy seq kept: the result of `map` is returned or stored, so it needs the collector
      in `tiers-sample/squares`
       --> test/clj/tiers_sample.cljf:17:20
       |
    17 | (defn squares [xs] (map #(* % %) xs))
       |                    ^
       = help: consume it where it is made, so the chain fuses into one loop: (reduce f init (map ...)), (run! f (map ...)), or (into-array (map ...))

`clotran compile --pure file.cljf` then writes the tier-A functions as
one ordinary Fortran module, with no clotran runtime at all -- any
Fortran program can `use` it. Each function gets one generic name and
one version per argument type:

    $ ./clotran compile --pure test/clj/tiers_sample.cljf ts_pure.f90
    module tiers_sample_pure -> ts_pure.f90
      pure        tiers-sample/count-big (2 versions)
      pure        tiers-sample/mean (2 versions)
      ...
      not lowered tiers-sample/describe -- tier B: see --report

Loops, arithmetic, Math functions, arrays, fused `map`/`filter`/`reduce`
chains, strings and `println` lower today; `scripts/pure-check` runs
every case through `clj`, gfortran and flang and compares. Numbers
become text the Fortran way (DEVIATIONS 50). PLAN.md step 13 has the
design.

## A whole program as pure Fortran

When a program's `-main` and everything it calls are tier A, `clotran
build --pure` makes it one small executable with no clotran in it: the
namespace is lowered to pure Fortran, wrapped in a Fortran `program`,
and linked with the compiler's runtimes built in.

    (ns sums)

    (defn sum-to ^long [^long n] (loop [i 0 s 0] (if (< i n) (recur (inc i) (+ s i)) s)))

    (defn -main [^long n ^double scale]
      (println "sum" (sum-to n))
      (println "scaled" (* scale (double (sum-to n)))))

    $ clotran build --pure sums.cljf
    $ ./sums 10 2.5
    sum 45
    scaled 1.1250000000000000E+002
    $ ./sums 10
    usage: sums n scale

The executable is a few hundred KB, where `clotran build` copies the
whole of clotran and its image into one. `-main`'s parameters are its
command line: hint each `^long`, `^double` or `^clotran.host.string`,
and the program reads its arguments as those types -- a wrong count, or
an argument that is not its type, prints the usage or names the
argument and ends with status 2. An error Clojure would throw, a long
overflow say, ends the program with Clojure's message and status 1.
`-m ns` builds a namespace on the source path instead of a file, and
`-o` names the executable.

If `-main` is not tier A, nothing is built: the message says why, and
`clotran compile --report` shows each call site that keeps a function
out. Doubles print the Fortran way (DEVIATIONS 50). `make
check-build-pure` builds this example; `scripts/fuzz-build-pure`
generates programs, builds and runs them, and compares their output
with `clj` running the same `-main`.
