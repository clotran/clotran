# Working on clotran

Clojure, hosted on Fortran. It runs Rich Hickey's actual `clojure/core.clj`
-- the file, unmodified. The Fortran is the HOST, standing where the JVM
stands; the language comes from Clojure's own source.

That premise decides most arguments. When clotran and Clojure disagree,
clotran is wrong until proven otherwise.

## Do not trust memory. Use the oracles.

Claims get cited to these rather than recalled. The rule exists because a
deviation once traced back to a misremembered Java detail, and because "I
think Clojure does X" has been wrong here more than once.

Note which tool answers which question: `clj` decides language behaviour,
`bb` writes the scripts, and the two clones are read for internals. bb is
not an oracle, and neither is clojuredocs -- both are read for ideas and
then checked.

**gfortran and flang.** gfortran is the default build; flang is the
correctness oracle. `make crosscheck` builds and tests under both and
they must agree. This is the gate: it runs before every commit, and a
red crosscheck means nothing gets staged.

**`clj` -- the LANGUAGE oracle.** Real JVM Clojure, and startup is ~0.7s,
so there is no excuse for not running it. To find out what Clojure does
with a form, run it:

    clj -M -e '(pr-str `x)'

This is the authority. It IS the implementation `~/jborden/clojure` is
the source of, so it cannot disagree with the Java the way a
reimplementation can.

**babashka (`bb`) -- the SCRIPTING language.** All file rewriting, source
analysis and counting is bb. **No Python.** The friction is literal
backslashes in Fortran/regex payloads, where bb's reader needs care --
escape them properly, or write the replacement text to a file and splice
it, rather than switching languages.

bb is `sci`, a reimplementation, and is NOT authoritative for language
questions. It silently does not implement `Namespace.checkReplacement`'s
warning, which meant it agreed with clotran's wrong behaviour and then
with clotran's right behaviour, telling us nothing either time. `clj`
prints it; bb does not. Use bb to script, `clj` to decide.

Small-map print ORDER differs between them and neither is wrong; compare
values, not printed text, when order could vary.

**clojuredocs.org -- EXAMPLES, never authority.** Every function has a
page with community examples, and they are worth reading before
implementing one: people write down the edge cases a docstring omits,
and the shapes real code actually uses. `make-array` is the kind of
thing to look up there before guessing.

It is NOT an oracle. The examples are user-contributed and some were
written a decade ago against an older Clojure. Anything taken from it
gets re-run through `clj` before it becomes a test or a decision --
same rule as bb: read it for ideas, ask `clj` what is true.

The page can also be thin where it matters. `make-array`'s arglists are
there, but the examples were not, and nothing on the page says whether
`(make-array Integer/TYPE 2 3)` is one flat buffer or an array of
arrays. Two lines of `clj` did:

    (class (make-array Integer/TYPE 2 3))   ;=> [[I  -- nested
    (alength (make-array Integer/TYPE 2 3)) ;=> 2   -- the OUTER length

So the order is: clojuredocs to find out what to ask, `clj` to find out
the answer.

**Do this per FUNCTION, before implementing it, and test VALUES.**
The reader's number patterns went in having checked 29 literals
against `clj` -- every shape, no values -- and `(* 2.0 3)` was
answering 0 the whole time, because `+`, `-`, `*`, `quot` and `rem`
read the integer field and ignored a real operand entirely. A form
being ACCEPTED is not the check; the answer being right is.

Reading the page first is what turns up the cases you would not
invent. Two came straight from the docstrings: `(/ x)` with one
argument is `1/numerator`, not identity, and `*` THROWS on overflow
rather than wrapping. Neither was on any list of mine.

One practical limit: the community examples render with JavaScript,
so a plain fetch returns the docstring and signatures and not the
examples. The docstring is still worth the fetch, and `clj` supplies
the values either way.

**`~/jborden/clojure`** -- a clone of `clojure/clojure` pinned to
the `clojure-1.12.0` tag (`d4bb93f0`), the SAME release as the vendored
`core.clj` and the one `clj` runs. Cite file and
method. Reading the Java of one version while running the core.clj of
another is the same mistake as citing memory, and it nearly happened:
the clone was first taken three hunks newer than what we run.

**`~/jborden/clojurescript`** -- pinned to `b45dff9f`. A second
implementation of the same language on a completely different host. Not
a porting source: it is how we tell which parts of `clojure.lang.*` are
the LANGUAGE and which are JVM artifacts. If ClojureScript writes
something in Clojure, it is not host-bound and our putting it in Fortran
is a choice we should be able to justify. If ClojureScript cannot write
it in Clojure either, it is a real seam. And if ClojureScript does not
have it at all -- `re-matcher`, `re-groups` -- it was never Clojure, it
was Java showing through. `SEAMS.md` carries the argument.

## Never edit vendored source

`src/clj/clojure/**` is Clojure's, `src/c/icu/**` is ICU's,
`test/clj/clojure/**` is Clojure's test suite. All verbatim. If clotran
cannot load one, that is clotran's bug -- the whole point is that these
files run as written.

Each vendored tree has a `PROVENANCE.md` saying where it came from, at
what commit, and what is deliberately absent. Read it before touching
the tree.

**Adding a vendored file can be a breaking change.** core.clj says
`(load "core_proxy")` and `clotran` skips that by name. An
evaluator that instead relied on the file simply not being there broke
`defprotocol`, `extend-protocol`, `satisfies?` and `into` the day it
was vendored -- a red crosscheck from adding files and changing no
code. Skip by name, never by absence.

## Report scorecards, not bug counts

Three measures, each named with its denominator:

| scorecard | what it is |
|---|---|
| **our tests** | `test/f/*_test.f90` (the Fortran host -- GC, reader, printer, evaluator), `test/clj/language_test.clj` (host checks with core.clj loaded) and `scripts/oracle` (`test/clj/oracle.clj` through `clj` AND clotran, values compared). A GATE, not a grade: 100% or do not commit. |
| **the language suite** | `test/clj/derived/`, DERIVED from Clojure's own tests by `scripts/derive-tests`: the deftests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency). `scripts/run-clojure-tests-parallel test/clj/derived` runs it. Never edit the derived files; re-run the script. The 67 vendored namespaces still run verbatim with no argument, for reference. |
| **libraries loading** | how many of Clojure's own libs `(require ...)` succeeds on. |

State what the denominator excludes. A namespace that crashes before
reporting contributes zero assertions, so a pass rate is over assertions
that EXECUTED, not assertions that exist -- say so rather than letting
the number flatter. "Bugs fixed" is not a measure; it says nothing about
how close the thing is.

Not every good change moves a scorecard. A bug that corrupts
`clojure.core` globally is worth fixing whether or not the suite can see
it -- but say plainly that the number did not move, rather than dressing
it up.

## Tools that exist

- `scripts/split-forms <file.clj> [outdir] [start]` -- splits a Clojure
  file into one file per top-level form. `load_file` aborts on its first
  error, so `clotran-bin core.clj` answers exactly one question; the
  ARGUMENT LIST does not abort, so
  `./clotran-bin core.clj forms/*.clj` reports every failure in one pass.
  This is how "the wall is form 656" became "5 forms fail and 63 behind
  them already work".
- `scripts/audit-host` -- every host class and member the loaded
  Clojure mentions. `src/f/hosttable.inc` is the JVM surface as data;
  a member the audit does not find has no business being a row.
- `scripts/run-clojure-tests` -- Clojure's own suite, one namespace per
  run so a hard failure cannot hide the others.
- `scripts/oracle` -- the differential test. Every form in
  `test/clj/oracle.clj` runs through `clj` and through clotran and the
  values are compared, so no expected value is ever typed in by hand.
  `(expect-diff "DEVIATIONS n")` before a form says it MUST differ.
  When you make something work, add the form there, not a hand-typed
  check: 14 of the 477 hand-typed expectations turned out to be
  clotran's answer, not Clojure's.
- `scripts/bench` -- the same forms timed on a warmed JVM (`clj`) and on
  clotran, with the ratio. Speed claims cite this, not a feeling.
- `make crosscheck` -- the gate.

## Gotchas that have cost real time

- **`make crosscheck` runs in two copies** (`XC_DIR/flang`,
  `XC_DIR/gfortran`, under the temp directory): it copies the sources,
  then cleans, builds and tests both compilers there AT ONCE, each with
  -j4, about 95 s. Building or running `./clotran` in the working tree
  meanwhile is safe. An EDIT made after the copy is not in the verdict
  -- the gate judges the tree as it was when it started. `make -j test`
  runs the checks side by side in the working tree; a new check gets a
  `check-*` target and writes only under build/. (A
  crosscheck interrupted between its halves used to leave flang's
  `.mod` files for gfortran to choke on; `build/.built-with-<fc>` now
  makes a compiler change empty the directory first.)
- **The gate's verdict is the `EXIT` line in its log.** Run it as
  `(make crosscheck > log; echo "EXIT $?" >> log)` and commit only on
  `grep -q '^EXIT 0' log`. A wrapper's or a background task's exit code
  is not the gate's; two commits were made on a red gate that way.
- **Instrument before theorising.** An hour went into an elaborate
  name-resolution theory that one `print` statement disproved in a
  single run. If there is a testable claim, test it.
- **A silent wrong answer is worse than a crash.** `(swap! a conj x)`
  returned the unchanged value instead of erroring; syntax-quoted map
  literals answered `{}` instead of failing. Both survived a long time
  because they looked plausible. Prefer the check that would catch a
  wrong answer, not just an exception.
- **Torture mode catches what the plain pass cannot.** `test/f` runs
  both; a GC rooting bug shows up only under stress. Two allocations
  passed as arguments to one call means the second can collect the
  first -- put each on the shadow stack first.

## Committing -- the stopping-point workflow

**At every stopping point:**

1. Make sure `make crosscheck` is green. It is the gate. A red
   crosscheck means nothing gets staged, and "my change works" is not a
   substitute -- that mistake has been made here, reporting success from
   targeted tests while the gate was failing.
2. `git add` exactly the files that belong in this commit.
3. Show `git status --short` so the scope is visible.
4. Give a **one-line** commit message.
5. **Stop and wait for review.** Do not run `git commit`, do not push,
   do not start the next task.

James runs `git commit`. He may change the message, unstage something,
or say no -- which is the point of stopping.

Commits are atomic. Two unrelated changes get staged and described
separately, one after the other, not bundled because they happened to
land in the same session.

Say plainly what a change does NOT do. If the scorecard did not move,
say so rather than dressing it up; a bug that corrupts `clojure.core`
globally is worth landing whether or not the suite can see it, but the
claim has to match the evidence.

## The documents

- `README.md` -- what clotran is, what works, what does not. Its examples
  are verified output, not aspiration. Keep it that way.
- `DEVIATIONS.md` -- every place clotran does something real Clojure does
  not, why, and what removing it would take. **A deviation with no entry
  here is a bug.**
- `SEAMS.md` -- the other question: what must be native versus what we
  merely chose to make native, with ClojureScript as the control group.
  Not the same ledger as DEVIATIONS; do not mix them.
- `PACKAGES.md` -- the package system: what a package is, the core
  packages we ship, the planned ones, and the vendoring rules (pinned by
  sha256, private prefix, never a system package manager).
- `PLAN.md` -- what we are about to build, what we decided not to, and
  why, so decisions are not re-argued from scratch. Contains the
  "Should we JIT?" decision record.
- `NOTES.md` -- design history and why things work the way they do.
