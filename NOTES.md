# Implementation notes

Working notes on decisions and gotchas, so the reasoning doesn't only
live in conversation history. Update this as new decisions get made.

## What this actually is

A Clojure for Fortran. The `mal` (Make-A-Lisp) test suite is scaffolding
to bootstrap and validate correctness incrementally -- it is not the
project's identity. Nothing should be named or described as "mal";
naming mirrors real Clojure instead (see below).

## The actual goal: composable QM/MD pipelines

The point of building a real Clojure isn't the language for its own
sake -- it's to write quantum mechanics and molecular dynamics pipelines
as composable, readable steps instead of one giant imperative loop.
Concretely: `(-> mol setup-parameters run-qm extract-missing-params
rerun-qm)`, where each step is a function over a molecule/state value,
and the pipeline reads as what it does instead of being buried in
control flow. James has hit this exact wall before -- existing Fortran
scientific codes (e.g. ChemSol, a solvation-energy program he co-wrote)
are usually one big loop where it's hard to tell what's actually
happening.

`ChemSol` (`~/jborden/ChemSol/src/chemsol.f90`) is the concrete first
target: it's a good example because the computation is *already*
factored into separate callable units (`readopt`, `dg_ld`, `solvout`,
`entropy`) -- the pipeline shape already exists. What makes it
unreadable as a pipeline is that each function takes a sprawling
positional argument list instead of one cohesive state (`dg_ld` alone
takes ~30 arguments) -- that's an argument-marshaling problem, not a
rewrite. The plan: wrap each such function as a native builtin (unpack
a mal hash-map into ChemSol's positional args, call the real,
unmodified Fortran routine, repack the outputs into a new hash-map),
so `(-> mol readopt dg-ld solvout)` calls real ChemSol code. This is
exactly why the core-namespace design (symbol -> native adapter,
uniform `(args) -> value`, independent of how the adapter is
implemented inside) was worth getting right early -- adding a wrapped
external library function should look exactly like adding any other
builtin.

Longer-term: other compiled-in scientific packages (QM codes, weather
models, ...) the same way, each exposed as ordinary callable functions
in the language. Threading (`->`) doesn't need macros to build now --
it's a small special form (like `def!`/`let*`), and later can become a
real macro without changing how it's used once macros exist.

## Real namespaces, not a flat global env -- and eventually real .cljc

James wants Clojure's actual namespace system (`clojure.lang.Namespace`),
not mal's single flat global env, built properly rather than deferred:
it's genuinely one of Clojure's better ideas, and it's what will let
this project cleanly separate "our own Fortran-native primitives" from
"ported Clojure library code" from "user code" -- three different
namespaces, not one bag of symbols. The longer-term idea this unlocks:
real Clojure library source (`.cljc` files, which are meant to be
portable across JVM/JS/etc. already) could eventually be loaded more
or less as-is against this implementation, once enough of the language
exists underneath it, rather than reimplementing library code by hand.
This is why native builtins live in a namespace literally named
`clojure.core` (see below) -- so a ported `.cljc` file that assumes
`clojure.core` already has `first`/`cons`/`+`/... just works.

**What's actually still missing before that's real** (not close yet,
worth being honest about):

1. **Reader completeness.** Collection literals are mostly there, but
   real `.clj`/`.cljc` source leans on metadata (`^{}`), regex literals
   (`#"..."`), char literals (`\a`), `#(...)` anonymous-fn syntax, `#_`
   discard, and -- specifically for `.cljc` -- reader conditionals
   (`#?(:clj ... :cljs ...)`). That last one matters most for the
   "pull `.cljc` directly" goal: this needs its own feature key
   (something like `:cljf`) rather than pretending to be `:clj`, since
   real JVM-specific branches won't run here anyway.
2. **Macros (step8) plus a self-hosted core.** Most of what makes
   `.clj` source look like `.clj` -- `defn`, `defmacro`, `cond`,
   `->`/`->>`, destructuring in `let`/`fn` args, multi-arity fns --
   isn't special forms, it's macros built on the primitives, usually
   bootstrapped in Clojure itself early in `clojure.core`. A
   third-party library file assumes all of that already exists. So
   realistically the gate isn't "macros done" but "our own
   `core.clj`-equivalent bootstrap exists" -- a point after step8, not
   at it.
3. **Depth of `clojure.core` actually needed.** Real library code
   transitively touches a lot: the sequence abstraction (`lazy-seq`,
   `ISeq`), protocols/multimethods, real hash maps/sets at scale,
   exception handling, `apply`, the higher-order seq functions. Very
   few real files are self-contained enough to dodge all of that.

## Toolchain: gfortran builds it, flang is the correctness oracle

Both are pinned (`Makefile`: gfortran 16, flang 23.1) and both run
before every commit -- `make crosscheck`. The roles differ.

**gfortran is the default build, for speed.** Measured on the identical
`cons_value`: a scalar copy is 13.7 ns under gfortran and 488 ns under
flang; a symbol 26.4 vs 576; a list 66.4 vs 740. End to end that is a
**4.5 s bootstrap against 30 s**, same source and the same results.
That 6.7x is paid on every edit-test cycle, so it is the daily driver.

Note what this says about PLAN.md step 3's premise. The GC exists
partly because "one `cons_value` copy costs 497 ns" -- and that number
is *flang*, not Fortran. The compiler-independent reason stands on its
own and is the real one: **refcounting cannot collect cycles**, which
is why clotran leaks closures today.

**flang is the oracle, and is not optional.** On every actual compiler
bug this project has hit, flang came out ahead, and its diagnostics
have twice caught real mistakes here that gfortran accepted silently at
`-Wall -Wextra` (two missing `RECURSIVE` markers among them).

**And gfortran currently fails things flang passes.** On the upstream
Clojure suite, a gfortran build crashes `clojure.test-clojure.
multimethods` every time and `clojure.test-clojure.logic`
*intermittently* -- 163 assertions under flang against 51 or 161 under
gfortran depending on the run. An intermittent crash under one compiler
and not another is the signature of undefined behaviour in *this* code
that flang's codegen happens to mask, not of a gfortran defect. So it
is a clotran bug, it is tracked in PLAN.md step 4a, and until it is
found gfortran is the fast build rather than a trustworthy one.

When something looks like a compiler quirk rather than a bug here,
building with both and comparing tells them apart -- that is what the
second compiler is for, and the split above is a live example of it
working. Don't contort the source to route around a quirk in either
one: document it here and move on, unless the fix is free.

## Oracles: gfortran for the compiler, babashka for the language

Two independent oracles, for two different kinds of "is this right?".

**gfortran cross-checks flang** -- see the toolchain section above.

**babashka cross-checks the LANGUAGE.** `scripts/gc-oracle` evaluates
each expression in `test/clj/gc_oracle.clj` with both `bb` and
`clotran-gc` and diffs the printed result. Memory is not a
specification: several semantics that felt obvious are not, and the
oracle settles them without argument --

- `(= (list 1 2) [1 2])` is **true**; a list and a vector of the same
  elements are equal, because both are sequential.
- `(str)` is `""`, not nil.
- `(conj (list 2) 1)` is `(1 2)` -- conj prepends to a list and
  appends to a vector.
- a map prints with commas: `{:a 1, :b 2}`.

A difference is not automatically a bug: usually it is a feature the
GC evaluator does not have yet, which makes the diff a todo list
rather than a failure. Currently 40/40 agree.

For clotran-bin itself the equivalent oracle is Clojure's own test
suite (below), which is stronger; `gc-oracle` exists because the new
stack cannot run that suite yet.

## Testing: unit tests are ours, test/regression/ is borrowed

`test/f/*.f90` are this project's own unit tests, one file per
Fortran module -- run with `make test`, no external tooling.

`test/regression/*.mal` are the official per-step mal test suites (step2
through stepA) plus their small load-file/slurp fixtures, carried
over from the mal-based bootstrap project because they're still
genuinely useful regression coverage of real Clojure-ish behavior,
not because this project depends on mal. Their `load-file`/`slurp`
paths were rewritten from mal's own `"../tests/x.mal"` convention
(which only works from inside mal's own repo layout) to plain
same-directory filenames, since these fixtures now live together in
one directory of their own.

Running them still means using mal's `runtest.py` (Python), invoked
from *outside* this repo against the raw interpreter, `clotran-bin`
-- not `clotran`, the rlwrap-wrapping launcher (see "A launcher
script, not a vendored library" below) -- e.g. from this repo's root:

```
python3 ~/jborden/mal/runtest.py --deferrable --rundir test/regression \
    step9_try.mal -- ../../clotran-bin
```

Deliberately not vendored into this repo (no Python in a Clojure-on-
Fortran project).

**Eventually these should become real, native tests -- not stay a
permanent mal-shaped fixture directory.** Two things block that
today: no assertion/test macros exist yet in the language itself
(no `deftest`/`is`, not even a bare `assert` builtin), and no native
runner replaces `runtest.py`'s job (walk a file, run each form,
compare against the `;=>` line, tally pass/fail/soft-fail). Once
both exist, porting means rewriting each fixture's mal-specific
constructs (`defmacro!`, `try*`/`catch*`) to real Clojure syntax and
turning each `form` / `;=>expected` pair into `(is (= expected form))`
or similar -- mechanical per-file, but real work across ~700 cases,
not a quick pass. Not started; `test/regression/` is the honest
interim name for what's there until it happens.

## The REPL launcher: mirrors clj, not lein

`clotran` (the thing you actually run) is a thin shell script,
`scripts/clotran`, wrapping the raw interpreter `clotran-bin` --
not line-editing code baked into the Fortran binary itself. This
mirrors real Clojure's own `clj` deliberately, not `lein repl`: `clj`
is *not* self-contained either -- its installed script (read
directly, not just described) does exactly this:

```sh
if type -p rlwrap >/dev/null 2>&1; then
  exec rlwrap -m -r -q '\"' -b "(){}[],^%#@\";:'" "$bin_dir/clojure" "$@"
else
  echo "Please install rlwrap for command editing or use \"clojure\" instead."
  exit 1
fi
```

`lein repl` *does* achieve genuine self-containment, but only because
it bundles JLine (a Java library) on the classpath -- there's no
equivalent "just add a jar" move for a native Fortran binary; the
honest equivalent would be vendoring a small C line-editor (e.g.
linenoise) via `iso_c_binding`. That's a real, buildable option
(confirmed: neither flang nor gfortran compiles `.c` directly, but
`cc`/`clang` -- already a transitive dependency of having either
Fortran compiler at all -- compiles it to a `.o` that either
compiler's own link step accepts with no special handling) but it's
more machinery than real Clojure itself uses, and duplicates what
`rlwrap` already does. Given the project mirrors real Clojure
directly wherever the two diverge, matching `clj`'s actual design
(external `rlwrap`, automated so the user doesn't have to remember to
type it) was the right call over inventing something heavier.

`scripts/clotran` uses the exact same rlwrap flags `clj` does (`-m`
multi-line, `-r` remember typed words for completion, `-q`/`-b` tuned
for Lisp syntax rather than shell syntax) rather than guessed-at
ones. One deliberate deviation: `clj` exits with an error if `rlwrap`
is missing (it assumes you know to use `clojure` directly instead);
`scripts/clotran` warns and still runs `clotran-bin`, since there's
no equally well-known bare alternative to point someone at yet.

## Importing real clojure/core.clj, not writing our own

The plan is to literally load the actual upstream `core.clj` (~8,400
lines), not hand-write a fresh core library that merely matches real
Clojure's behavior. `src/clj/clojure/core.clj` stays byte-for-byte
pristine forever -- not even additively patched with reader
conditionals -- because real core.clj has never had any: `.cljc` and
its `#?(:clj ...)` reader-conditional convention weren't introduced
until Clojure 1.7 (2015) and are used by later, independently-written
cross-host *libraries* (`clojure.spec.alpha` and similar), never by
the JVM's own `core.clj` or ClojureScript's own `cljs.core` -- those
two are separately, independently hand-written files that happen to
mirror each other's API, not one core mechanically deriving the
other. `src/clj/clotran.clj` is this project's own equivalent of that
relationship: a small, separate file loaded FIRST (before core.clj,
not after -- see its own header for why), populating just the
`clojure.lang.*` interop surface (`clojure.lang.RT`,
`clojure.lang.PersistentList`, `clojure.lang.Util`, a handful of
`instance?` pseudo-classes) that real core.clj's own bootstrap-era
definitions (`cons`, `list`, `fn`, ...) call into from their very
first few forms -- grown one entry at a time as walking further into
core.clj turns up the next thing it needs, never by editing core.clj
itself.

Getting even the earliest lines of core.clj to parse and run at all
required adapting this project's own reader/evaluator to handle what
real bootstrap Clojure source actually looks like -- confirmed
empirically against the real file, not assumed:

- **`fn*` needed an optional self-reference name** (`(fn* name
  [params] body)`), used throughout core.clj's own bootstrap (`(fn*
  cons [x seq] ...)`) for self-recursion without an outer `def`.
  Bound via a throwaway env layer set to the closure only after it's
  built (`env_set` mutates the shared node in place).
- **`defmacro` had the same silently-drops-extra-body-forms bug `fn*`
  had before** -- same fix, factored into a shared `wrap_body` helper.
- **`^META FORM` now attaches META directly to FORM's own metadata,
  never evaluated** -- real Clojure's actual reader behavior, not
  mal's (and this project's former) `(with-meta FORM META)`, an
  evaluated call. This matters because `def`/`fn*`'s name position is
  never evaluated at all (same as real Clojure): `(def ^{:doc "..."}
  x 1)` needs `^{:doc "..."} x` to still read as the bare symbol `x`
  with metadata riding along invisibly, not an unevaluated
  `(with-meta x {...})` list sitting where `def` expects a symbol --
  and nearly every def in core.clj carries doc/arglists metadata this
  way. Confirmed the reader change didn't regress anything by
  checking it against real Clojure itself first (`clojure -e`), not
  assumed.

  This one change **temporarily** breaks two `test/regression/
  stepA_mal.mal` soft-fails (`(meta f-wm2)` where `f-wm2` is `(def!
  f-wm2 ^{"abc" 1} (fn* [a] (+ 1 a)))`): mal's own convention
  auto-propagated a value-position `^META` onto the evaluated result
  because it was really an evaluated `with-meta` call underneath. Real
  Clojure does NOT do this automatically -- it only works because the
  real `fn` macro explicitly copies `(.meta &form)` onto the `fn*` it
  builds (confirmed directly: `(meta ^{"abc" 1} (fn [a] a))` returns
  the metadata in real Clojure only because `fn` does this itself, not
  because evaluating a form transfers its reader metadata for free).
  This project doesn't have a real `fn` macro yet (only bare `fn*`) --
  once core.clj's own `fn` is imported and does the same copy-through,
  these two tests should pass again on their own.

Bootstrapping even `first`/`next`/`rest`/`conj` (~line 90 of ~8,400)
needed one more real feature: **multi-arity `fn*`**
(`(fn* name? ([p1] b1) ([p2] b2) ...)`), since real `conj`'s own
bootstrap definition has 4 arity clauses (0, 1, 2, variadic). Dispatch
is by argument count at *call* time (`select_clause` picks the
matching clause, checked against both apply paths -- the tail-call
fast path inside `eval_form`'s trampoline and the non-tail
`apply_closure`, the same two places every closure-calling fix in
this project has needed both times), not rewritten into a single
dispatch body at parse time -- one runtime closure shape either way.
A fixed-arity clause matching exactly always wins over a variadic one
that would also accept the same count (confirmed against real
Clojure's own arity resolution order, not assumed).

Detecting multi-arity syntax needed care: this project (like mal)
also allows a single arity's params to be written with parens,
`(fn* (a b) body)`, not just `[a b]` -- so "is the thing after the
name a list?" isn't enough to mean "multi-arity clauses", since
`(a b)` is itself a list. The real test: a clause's own first element
is always a params collection (vector or list), never a bare symbol
(no destructuring, so every real single-arity param is a symbol) --
checked one level deeper, not just at the top.

**Not doing yet, deliberately deferred**: `let`/`loop`/`fn`'s real
bootstrap definitions use the `&form`/`&env` macro-calling convention
(the compiler auto-supplies the raw calling form and lexical
compile-env as a macro's first two arguments) -- this project's
macros don't get these auto-supplied at all. `let`/`loop`'s own
bootstrap bodies never actually reference `&form`/`&env` (only bind
them, unused), so dropping those two params entirely is a safe,
faithful patch, buildable with what already exists (`defmacro`,
`cons`). Real `fn`'s bootstrap *does* use `&form`'s metadata (for the
copy-through mentioned above) -- patched `fn` skips that one behavior
rather than building real `&form`/`&env` support now. Destructuring
in `let`/`fn` params is also not built -- nothing needed by the file
so far has required it, but real Clojure code leans on it constantly,
so it's a near-certain future need, not a one-off skip.

**The actual file is now vendored in, and the bootstrap points at
it** (`src/clj/clojure/core.clj`, mirroring the upstream `clojure/
clojure` repo's own path -- verbatim, no edits yet). This is a
deliberate, temporary regression, not an oversight: the file can't
actually load yet (further gaps below), so `not`/`cond` -- and
everything depending on them -- are broken until enough of it is
ported. Confirmed exact scope: `eval_test` goes from all-green to 7
failures (`not`, `cond`, and the two tests that incidentally use
`cond`), `test/regression/step8_macros.mal` from 1 to 14 failing,
`step9_try.mal` from 0 to 2. Chosen deliberately over keeping a
separate always-working placeholder file, so the actual, current
state of the real import is never obscured by a stand-in.

A real, load-bearing bug surfaced getting even this far: attempting
to load the file crashed on startup. Root-caused via a full lldb
backtrace (not guessed at) to `LispReader.f90`'s tokenizer -- `cur =
cur // expr(i:i)`, growing an allocatable string one character at a
time to read a string literal or symbol, is both O(n^2) and a real
crash for long enough input (here, a multi-line docstring), hitting
the exact reallocating-assignment fragility already in this file's
gotchas catalog, just for a plain string instead of a `cons_value`
array. Fixed by scanning for each token's end first and slicing the
source once -- unrelated to core.clj specifically, a real bug any
sufficiently long input could have hit.

Immediately past that, real forms (not truncation artifacts) hit a
**third substantial gap: no set-literal syntax or set type at all**.
`#{2}` (here in an inert `:inline-arities` metadata hint) was
misread as bare symbol `#` immediately followed by hash-map `{2}`,
which then failed on odd element count. **Now built**: `TAG_SET`
reuses the exact same `array_map_t` backing as hash-maps -- every
element mapped to itself -- the direct structural mirror of how real
Clojure's own `PersistentHashSet` wraps a map internally, so `count`/
`get`/`contains?`/`conj`/`seq`/`=` all extend for free by adding one
more `case` alongside the existing `TAG_HASHMAP` one, wherever one
already existed, rather than a parallel implementation. New:
`hash-set`, `set?`, `disj` (mirrors `dissoc`, same underlying
`array_map_dissoc`). `conj` on a set adds (dedup); `seq` gives
elements directly, not `[k v]` pairs like a map's seq does.

That in turn exposed a **fourth gap: `#(...)` anonymous-fn literal
syntax**, also unsupported (`#(str ", " %)` inside a real function
body, not just metadata this time). Built properly: bare `%` means
`%1`, an explicit `%2`/`%3`/... implies the lower-numbered ones are
also params even if unused, `%&` is the rest-arg -- every case
checked against real Clojure's own macroexpansion first (`clojure -e
'(macroexpand ...)'`), not guessed. Real Clojure gensyms fresh
internal names for these; using the literal `%1`/`%2`/`%&` symbols
directly as both the param names and what the body already
references is simpler and just as correct here, since nothing
outside one `#(...)` body could reference them anyway -- but bare `%`
still needs rewriting to `%1` in the body (a recursive walk over just
lists and vectors; a `%`-reference nested inside a `{}`/`#{}` literal
within one `#(...)` body is vanishingly rare and not handled).
Nesting (`#(...)` inside another) isn't checked for or rejected the
way real Clojure does -- just not handled correctly, a low-risk gap
since nothing here writes nested ones.

A **fifth**, smaller one: `#'sym` (real Clojure's `(var sym)`
shorthand). No separate Var type exists here (macro-ness itself is a
flag on the closure, not Var metadata, for the same reason -- see
"Naming" below), so this reads as `(quote sym)` instead: the closest
sensible reader-level behavior without inventing Var semantics, not
a faithful stand-in for what `(var sym)` actually returns.

None of `#{`, `#(`, nor `#'` merge into a single token the way `#?`
does (`?` is an ordinary character so `#?` merges naturally; `{`,
`(`, `'` are all special characters that break the merge) -- `read_form`
peeks at the next token instead of relying on the tokenizer to hand
it a combined one.

**A second real, load-bearing performance bug, found from actually
noticing the REPL felt hung** (17+ seconds before the first prompt,
reported directly, not something the existing test sweep caught):
`read_items`, which reads the contents of any collection literal,
pre-sized its `items` array as "however many tokens are left in the
*entire remaining file*" -- a bound that's always safe but almost
never tight, and `read_items` runs once per collection literal,
including every nested one (a `defn`'s params vector, a metadata
map, ...). A file with hundreds of small nested collections spent
nearly all its time allocating (and mostly discarding) one huge
array per collection. Confirmed as the actual cause by isolating each
stage (`slurp` alone: instant; `str`-concatenating the wrapped
source: instant; tokenizing the whole file to read just its first
top-level form: instant; only reading the *whole* file wrapped in one
`(do ...)`, which recurses through hundreds of nested literals, was
slow) rather than assumed from the tokenizer fix already made.
Fixed by growing `items` geometrically (doubling, via `move_alloc`,
not assignment) from a small start instead of one large upfront
guess -- 17s down to 0.5s end to end.

Last reader gap hit: `#"pattern"` (regex literals -- `#(str ", "
%)`-adjacent, used e.g. in `*clojure-version*`'s own definition). No
regex engine exists here at all (`re-pattern`/`re-matches`/`re-find`/
`re-seq`, its own type -- a genuinely separate, substantial feature,
not attempted). Read as a plain string instead, purely so the reader
doesn't choke; code that actually calls a regex function on one will
fail there, honestly, not silently here. Taken **raw**, not through
the ordinary string escaper: a regex's own `\d`, `\s`, `\.`, etc. must
keep their literal backslash, unlike a normal string's escapes --
confirmed against real Clojure first (`#"\d+"` is a 3-character
pattern, backslash included, not 2), not assumed.

**With that, all 726 top-level forms in the real, complete
`core.clj` now parse successfully** -- the only remaining error
loading it is `'ns' not found`, evaluating the very first form.
Every reader-level gap found this way (`#{`, `#(`, `#'`, `#"`, the
tokenizer crash, the `read_items` slowness) is fixed; what's left is
entirely at the evaluation level: a real `ns`, then `let`/`loop`/`fn`
(dropping the unused `&form`/`&env` params, per the plan already
written up above), then whatever surfaces past that.

**`ns` is built**: `(ns name & _clauses)` switches `*ns*`, creating
it if new -- `name` is never evaluated (same as `def`'s name
position; `^{...}` metadata rides along invisibly on it the same
way). A real, useful primitive on its own merits, not a one-off for
this file -- core.clj's own single `ns` form has no `:require`/
`:import` (it IS the root namespace), so clauses after the name are
silently ignored for now; that's genuinely future work for this
project's own multi-namespace code, not something this file needs.
Moved the bootstrap's failure point from `'ns' not found` to `'.'
not found` -- the next real blocker, `list`'s own `(. clojure.lang.
PersistentList creator)`, exactly as expected.

The REPL prompt now shows the real current namespace (`user=>`,
`foo.bar=>`, ...) instead of a hardcoded `user> ` -- matching real
Clojure's own REPL exactly, and incidentally makes `ns`/`in-ns`
switches visible while working through this file. Confirmed this
doesn't break the official mal test harness's prompt-matching regex
(`[^\s()<>]+> `, generic enough to match either form) before relying
on it, not assumed.

## Value representation: cons_value, not class(*)

`cons_value` (`Values.f90`) is a concrete tagged-union type (an integer
tag plus one field per variant: int/real/bool/string/symbol/keyword/
list/vector/hashmap). It is deliberately **not** `class(*)`
(unlimited polymorphic).

Why: `class(*)` never dispatches to a dynamic type's own
`assignment(=)`/`FINAL` on *any* copy path -- plain assignment,
`allocate(x, source=y)`, even `class(*) = class(*)` assignment all do a
raw component-wise copy regardless of the runtime type. Confirmed with
targeted repros; this is fundamental to how Fortran resolves defined
assignment (compile-time, by declared type), not a bug. A concrete type
doesn't have this problem: `cons_value_assign` genuinely dispatches
per-tag at runtime via `select case`.

## Refcounting pattern (PersistentList/PersistentVector/PersistentArrayMap)

Each persistent structure has its own node type plus a thin refcounted
handle (`cons_ref` / `node_ref` / `array_map_ref`): `assignment(=)`
bumps the refcount on copy, `FINAL` drops it and frees at zero. Rules
that took real debugging to pin down, confirmed identically on both
compilers (so: real Fortran behavior, not compiler bugs):

- Both `FINAL` and `assignment(=)` must be `impure elemental`, not just
  scalar. A plain (non-elemental) one silently no-ops for a whole array
  (`deallocate(array_of_x)` frees nothing; `arr2 = arr1` doesn't bump
  refcounts, it raw-copies pointers) -- it only fires for a single
  scalar instance.
- A type that *embeds* one of these handles (e.g. `vec_t` embeds
  `node_ref`; `cons_value` embeds `cons_ref`/`vec_t`/`array_map_t`) must
  define its own `assignment(=)` that assigns each such component by
  hand. Default whole-struct assignment does not cascade into an
  embedded component's own `assignment(=)`.
- Never assign into a not-yet-allocated array of one of these types
  (`arr = other_arr` where `arr` starts unallocated) -- the combination
  of auto-reallocation and impure elemental `assignment(=)` crashes on
  both compilers. Always pre-allocate the target first (a real
  `ALLOCATE` statement), then assign into it -- or write a subroutine
  with an `intent(out)` allocatable array argument that allocates
  internally, rather than a function whose result gets assigned.
- Include a self-assignment guard in `assignment(=)`
  (`if (associated(lhs%ptr, rhs%ptr)) return`) before releasing the
  LHS -- otherwise self-assignment frees the object out from under
  itself.
- This only works because the graphs are acyclic (list cells, trie
  nodes point only toward leaves/tails). Plain refcounting leaks on
  cycles; there are none here.

### Mutually-recursive types live in one module

`cons_value` needs to hold a list/vector/map; a list cell needs to hold
a `cons_value`; same for the vector-trie node and the array-map node.
Fortran can only forward-reference a not-yet-defined type via an
`allocatable` or `pointer` component, and only *within the same
module* -- not across a `use` boundary. That's why `Values.f90` holds
all of these type definitions together, while every operation on them
(`PersistentList.f90`, `PersistentVector.f90`, `PersistentArrayMap.f90`,
`RT.f90`) lives in its own file and just `use`s the types.

## Big-O: matching real Clojure's own guarantees, not just its behavior

Getting the right *answer* isn't the same as getting there the way real
Clojure does -- Rich Hickey's own data structures are chosen precisely
for their asymptotic behavior, and silently falling back to a slower
shape defeats the point of mirroring them. Two real gaps, found by
deliberately auditing every structure against what real Clojure
actually guarantees (not just what our own tests happened to cover):

- **Every map/set (and, since they reuse the same backing, every
  namespace's own bindings and every lexical env frame) was
  `PersistentArrayMap`-only** -- a flat, linear-scan array, correct for
  real Clojure's own small-map tier (<=8 entries, confirmed against the
  real `clojure` CLI) but never promoted beyond it. `clojure.core`
  alone holds 700+ bindings once `core.clj` finishes loading, so this
  wasn't a corner case: interning the k-th definition cost O(k) (full
  array copy-on-write), making the whole load O(n^2) in its own
  definition count -- the exact shape of bug this project already hit
  twice before at the reader/tokenizer level, just one layer up.
  Fixed with a real HAMT (`PersistentHashMap.f90`): same 32-way
  branching trie algorithm as `PersistentVector.f90`, keyed on hash
  bits instead of a sequential index, promoting past 8 entries (never
  demoting back, matching real Clojure exactly) via
  `PersistentArrayMap.f90`'s `array_map_assoc`/`array_map_dissoc` --
  every existing caller (`RT.f90`, `Namespace.f90`, `Env.f90`,
  `Eval.f90`, `printer.f90`) gets the fix for free through the same
  `array_map_t`/`array_map_*` API, no changes needed on their end.
  Deliberate simplifications, both real Big-O tradeoffs against
  upstream, not correctness gaps: every node is a full 32-slot array
  rather than real Clojure's bitmap-compressed sparse array (same
  O(log32 n), a higher constant memory factor per node); a promoted
  map's own iteration order is hash order, not insertion order --
  which is not a simplification at all, it's what real Clojure's own
  `PersistentHashMap` actually does (only `PersistentArrayMap`
  preserves insertion order upstream too).
- **Vector `rest`/`next`/`seq`/`cons` eagerly rebuilt a fresh list by
  calling `nth` once per remaining element** -- O(n log32 n) to walk a
  whole vector instead of real Clojure's O(1)-to-start chunked seq
  (still bounded, not the unbounded-per-call blowup it might look like
  at a glance, since every step after the first walks the resulting
  *list*, not the vector, at real list speed -- but a real, avoidable
  gap regardless). Fixed by replacing the n-`nth`-calls approach with
  a single O(n) in-order trie walk (`RT.f90`'s `vector_to_list`,
  visiting each leaf node's whole `items(:)` run at once). `assoc` on a
  vector was simply unhandled entirely -- `RT.f90`'s `assoc` unconditionally
  built a hashmap regardless of `coll`'s actual type -- even though the
  correct O(log32 n) path-copy machinery (`node_assoc`) already existed
  in `PersistentVector.f90`, just never wired up as `vector_assoc`.
  Not fixed (a real, currently-accepted gap, not an oversight): vector
  `rest`/`next`/`seq` still materialize the whole remaining list
  eagerly rather than lazily/chunked -- same total work a fully-forced
  real Clojure lazy seq would do, just performed up front instead of
  incrementally. Revisit with a real chunked-seq/ISeq abstraction if
  that eagerness is ever actually observed to matter.
- Map/set keys still only compare by scalar/text equality
  (`value_equal` in `Values.f90`) -- a vector, list, or map used as a
  map/set key doesn't hash or compare the way real Clojure's deep value
  equality would. Pre-existing (not introduced by the HAMT work above,
  and not made any worse by it: a compound key still just always
  collides into the same hash bucket, linear-scanned by the same
  under-powered `value_equal`). Left alone for now -- a real, scoped
  gap, tracked here rather than fixed as a side effect of unrelated work.

## Fortran gotchas catalog (for next time)

- `class(*)` copy semantics: see above. (Historical: this is also why
  strings used to be wrapped in a `cons_string` type rather than stored
  as bare `class(*)` -- gfortran's built-in copy helper crashed on a
  zero-length `character` as a polymorphic dynamic type. Moot now that
  `class(*)` is gone from the value representation, but a real,
  reproducible gfortran bug, confirmed absent on flang.)
- `impure elemental` needed on both `FINAL` and `assignment(=)` to
  cover arrays, not just scalars -- see refcounting pattern above.
- Auto-reallocating array assignment + impure elemental
  `assignment(=)` crashes on both compilers -- pre-allocate first.
- Default struct assignment doesn't cascade into an embedded type's own
  `assignment(=)` -- the wrapping type needs its own.
- A function-result component access chained inline
  (`some_function(x)%field`) fails to compile on flang (works on
  gfortran). Assign the function result to a variable first, then
  access the field.
- gfortran-only: chaining two calls to the same *recursive,
  deferred-length-character* function inside one concatenation
  expression corrupted memory (stray NUL bytes) -- e.g.
  `str = str // pr_str(k) // " " // pr_str(v)` inside a recursive
  `pr_str`. Fixed by materializing each call into its own variable
  first (`printer.f90`, `pr_hashmap`) -- and that fix is also just
  clearer code, not a pure workaround, which is why it was worth taking
  despite the gfortran-only policy above.
- **`.and.`/`.or.` don't guarantee short-circuit evaluation**, unlike
  C's `&&`/`||`. `associated(l%ptr) .and. allocated(l%ptr%cdr)`
  dereferenced the null `l%ptr` anyway and segfaulted (confirmed on
  both compilers, `PersistentList.rest` on an empty list -- found by
  mal's own step8 deferrable tests, not caught until then). Fix:
  sequential guard-clause `if (.not. ...) return`s, not a combined
  `.and.`, whenever the second condition depends on the first being
  true to be safe to evaluate at all. (This is a purely lexical/
  compile-time nesting question, not runtime recursion depth --
  unrelated to the TCO/stack-depth concerns elsewhere in this file.)

  Third instance, found much later in `eval_instance_call`:
  `target%tag == TAG_KEYWORD .and. names_a_class(target%str_val)`
  passed an **unallocated** `str_val` as an actual argument for every
  non-keyword target. flang read whatever was there and carried on;
  gfortran's `-fcheck=all` named it exactly. Three occurrences now, all
  the same shape -- a tag test guarding a use of the payload that only
  that tag allocates. Treat any `%tag == ... .and. <uses payload>` as a
  bug on sight.
- **gfortran defaults to Fortran 2008, where a procedure not marked
  `RECURSIVE` may keep its locals in STATIC storage.** F2018 made every
  procedure recursive by default and flang follows it, so this source
  is written against semantics gfortran does not have by default.
  Re-entering such a procedure silently overwrites the outer
  invocation's variables.

  It hides well: gfortran rejects *direct* recursion at compile time,
  so only INDIRECT recursion slips through -- and an evaluator is
  mutually recursive everywhere (`eval_form` -> `eval_let_head` ->
  `eval_form`), as is refcounting (`release` -> `deallocate` -> `final`
  -> `release`). The corruption surfaced far away, as SIGTRAP inside
  `malloc` at an unrelated `allocate`.

  Fix: `-frecursive` (in the Makefile, gfortran only), which forces
  locals onto the stack. `-std=f2018` does **not** enable it, checked
  on gfortran 16. Marking procedures by hand was rejected: it is one
  build-level property, not ~200 annotations, and a half-annotated
  codebase is worse than none.

  **`-fcheck=all -fbacktrace` is the first thing to reach for** on any
  memory-shaped crash here. It named all of this; the raw crash named
  nothing.
- gfortran-only: a derived type with an allocatable component of *its
  own type*, once a `FINAL` procedure is involved, corrupts a type
  descriptor -- crashes with a null function-pointer call inside
  gfortran's generated finalization code, confirmed with a minimal
  isolated repro outside this codebase (flang runs it correctly).
  Found via `with-meta`/`meta`'s metadata field. Fix isn't a gfortran
  contortion: use the same pointer-based refcounted box this codebase
  already uses for every other recursive/shared structure
  (`meta_ref`/`meta_node`, mirroring `atom_ref`/`atom_node`) instead of
  embedding the value directly -- correct and clearer on both
  compilers regardless. **Confirmed this isn't specific to direct
  self-embedding**: `closure_t` holding an allocatable *array* of
  `cons_value` (for multi-arity `fn*`'s extra clauses) hit the exact
  same gfortran crash, even though the recursion is indirect
  (`cons_value` -> `closure_t` -> array-of-`cons_value`) and it's an
  array, not a scalar. Same fix, same box-behind-a-pointer pattern
  (`arity_clauses_ref`/`arity_clauses_node`).
- gfortran-only: a **fixed-size** array component (`type(t) :: x(N)`,
  not `allocatable`) of a self-referential struct also corrupts
  finalization, distinct from the allocatable-component bug above --
  found via `hamt_node`'s `slots(BRANCH)` (each slot embeds a
  `hamt_ref` pointing back to another `hamt_node`): gfortran's
  auto-generated finalizer for the whole node crashed inside a nested
  `cons_value` finalizer, even though every slot had already been
  released by hand first (flang ran the identical code fine). `vec_node`
  never hit this because its own self-referential array (`children(:)`)
  was already `allocatable`, not fixed-size -- making `hamt_node%slots`
  allocatable too (pre-allocated to exactly `BRANCH` right after
  creating the node, so nothing about its behavior actually changes)
  fixed it on both compilers.
- **Automatic reallocation on array assignment (`x = expr`) cannot be
  trusted for an array whose element type has `assignment(=)`**
  (confirmed on flang; unlike the "pre-allocate first" note above,
  this one silently produces the WRONG SIZE rather than crashing, so
  it's easy to miss). Confirmed for three distinct shapes, all with
  `cons_value` (which has its own `assignment(=)`) as the element
  type: (1) `x = some_pointer%ptr%allocatable_array` -- allocated `x`
  to size 0 regardless of the source's real size; (2) `x = f(...)`
  where `f` is an ordinary function returning an allocatable array,
  assigned into a fresh, entirely unrelated variable -- same silent
  size-0 result; (3) `x = x(1:n)` (self-slice to shrink a growable
  buffer) -- silently left `x` at its old, oversized shape instead of
  shrinking it. All three were found chasing the exact same visible
  symptom (`(hash-map "a" 1 "b" 2)` printing `{}`), and none of them
  are about self-assignment or `impure elemental` -- a plain, distinct
  target variable receiving an ordinary function's result was already
  enough to trigger it. Fix, applied uniformly: never rely on
  reallocate-on-assignment for this element type -- `allocate(x(n))`
  explicitly first (matching the size you're about to write), then
  assign element-by-element into the already-correctly-sized array
  (`PersistentArrayMap.f90`'s `array_map_entries`, `PersistentHashMap
  .f90`'s `node_assoc`/`node_dissoc`/`hamt_entries`). Where the
  *caller* needs the array back, prefer a subroutine with an
  `intent(out), allocatable` argument over a function returning one --
  argument association isn't assignment(=) and isn't affected (the
  same pattern `LispReader.f90`'s `read_items` already used).

## Naming: mirrors real Clojure directly

For 1:1 comparison against the real thing, not our own invented names:

| Clojure | here |
|---|---|
| `clojure.lang.PersistentVector` | `PersistentVector.f90` |
| `clojure.lang.PersistentList`/`Cons` | `PersistentList.f90` |
| `clojure.lang.PersistentArrayMap` | `PersistentArrayMap.f90` |
| `clojure.lang.RT` | `RT.f90` (the generic, type-dispatching layer) |
| `clojure.lang.Atom` | `Atom.f90` |
| `clojure.lang.Namespace` | `Namespace.f90` |
| `clojure.lang.LispReader` | `LispReader.f90` |
| `first`, `rest`, `next`, `cons`, `conj`, `nth`, `count`, `seq`, `get`, `assoc` | same names, verbatim |
| `vector?`, `list?`, `seq?`, `map?` | `vector_p`, `list_p`, `seq_p`, `map_p` (Fortran identifiers can't hold `?`; `_p` is the old Lisp predicate-suffix convention) |
| `with-meta`, `hash-map` | `with_meta`, `hash_map` (Fortran can't do `-` in names either) |

`cons_value` has no Clojure equivalent to mirror -- Java's `Object` plus
`instanceof` already gives Clojure free dynamic dispatch, which is
exactly what `class(*)` was trying (and failing) to give us here.
`closure_t` is the same kind of exception: real Clojure compiles each
`fn*` to its own JVM class rather than using one generic closure
struct at runtime, so there's no name to mirror -- interpreting instead
of compiling needs an explicit params/body/env representation that
Clojure's own implementation never has to build.

## Deliberate scope decisions (not oversights)

- **`seq` is eager, not lazy.** Real Clojure's `(seq vec)` is a lazy
  view that walks the trie on demand. This builds an actual list up
  front instead. True laziness (`lazy-seq`, infinite sequences) needs
  to defer *evaluation of arbitrary code*, which needs an evaluator and
  an environment to capture -- neither exists yet. Revisit once
  eval/env do.
- **Hash-maps are `PersistentArrayMap` (flat, linear-scan), not a real
  hash trie.** This matches real Clojure, which does the same thing for
  maps up to 8 entries and only switches to `PersistentHashMap` beyond
  that. Every map here is small for now. Build a real HAMT
  (`PersistentHashMap.f90`) when something actually needs a large map.
- **No garbage collector.** Reference counting is hand-built and
  validated per structure (see above), not automatic. This is why the
  refcounting rules above matter so much -- there's no safety net
  behind them.
- **No `IFn`-style polymorphic dispatch for callables.** Fortran can
  express an interface (an `abstract` type with a `deferred`
  type-bound procedure), but plugging it into `cons_value` would need
  a `class(ifn_t)` component -- polymorphic, the same shape as the
  abandoned `class(*)` value type, with the same broken copy/refcount
  dispatch. `apply_fn`'s `select case` over builtin/closure/
  keyword/map/vector is the behavioral equivalent of `IFn.invoke`,
  compiled as a switch instead of a vtable -- but it's a *closed*
  switch: unlike real `IFn`, a library can't make its own type callable
  by implementing an interface, only types this project already knows
  about dispatch. Real risk for pulling in `.cljc` code that defines a
  custom `IFn` type (rare but real); not a risk for the far more common
  cases (fns/keywords/maps/vars/multimethods). The fix isn't a
  parallel mechanism bolted on now -- it falls out of building
  protocols/multimethods properly later: that's already a
  namespace-level open dispatch table (type -> implementation, which
  is what protocol dispatch compiles down to even in real Clojure),
  so `apply_fn` gains one more case that consults that same registry
  for a type's `invoke` impl. Open callable dispatch as a side effect
  of protocols, not a second polymorphism mechanism.
- **No separate `clojure.lang.Var` indirection.** A namespace
  (`Namespace.f90`) stores its own bindings as symbol -> value
  directly (an `array_map_t`, same shape as `Env`'s bindings), not
  through a first-class Var object per binding. Real `Var` exists for
  metadata, `#'foo`, and thread-local dynamic (`binding`) rebinding --
  none of which this project needs yet. Build it once something does;
  it won't change how namespaces themselves work.

## Real numbers are real(8), not `real`

`cons_value%real_val` is `real(dp)` where `dp = kind(1.0d0)` (double
precision), not the bare default `real` (single precision) it started
as. Every real scientific Fortran library -- ChemSol included, 116 uses
of `real(8)` in one file -- works in double precision throughout;
silently truncating to single precision at the value-type boundary
would be a real, if quiet, correctness bug the first time a native
function got called. Fixed before any native interop was wired up, not
after. The reader also gained actual real-literal parsing
(`looks_like_real`/`parse_real` in `LispReader.f90`) -- mal's own spec
only has integers, but native interop needs real literals to exist at
all.

## ChemSol interop: confirmed feasible, deliberately not built yet

Spiked as a proof of concept mid-session: a `ChemsolAdapter.f90`
wrapping `entropy` from ChemSol (`~/jborden/ChemSol/src/chemsol.f90`,
compiled by path) as an ordinary callable builtin, unmodified.
`(entropy 18.0)` called the real Fortran function and returned `8.43`
(kcal/mol), identically on both compilers -- so the core idea is
validated. Deliberately reverted, not kept: mal tests come first: the
ChemSol pipeline (see "The actual goal" above) is a goal for *after*
mal passes, not a parallel effort. The `real(dp)` precision fix and
real-literal parsing above were kept regardless -- those aren't
ChemSol-specific, they're "the language has a real-number type," same
as Clojure's `Double`.

One design point worth keeping in mind for when this resumes: Fortran
libraries use many different kinds (`real(4)`, `real(8)`, `integer(8)`,
...), but that doesn't mean `cons_value` needs to enumerate them --
exactly one canonical real type and one integer type is the right
amount, same as any language calling into C/Fortran (Python's `float`
is always a C `double` regardless of what a wrapped library uses
internally). Kind conversion belongs in each function's adapter, not in
the core value type. Once there are enough native functions to wrap
that hand-writing adapters gets tedious, a small generator reading a
library's real signatures and emitting the marshaling code (the
`f2py`/SWIG pattern) is the right next tool -- not a different
architecture, just less boilerplate per function.

## Native interop values: a `TAG_NATIVE` cons_value case, validated

ChemSol's own routines are scalar in, scalar out -- "one canonical
real + one canonical int, kind conversion per-adapter" (above) covers
it completely. Not every library will: something like a hypothetical
`mathblas` (a matrix/vector type) or a solver that hands back a handle
you're meant to hold and pass into a *later* call needs Clojure code
to carry an actual Fortran derived-type value as a first-class value
-- put it in a vector, hold it in a var, pass it to another function,
maybe even into a *different* library's call -- without clotran ever
needing to understand its internals. Every value up to now had to be
one of clotran's own known tags; there was no way to represent "an
opaque Fortran object" at all. This is the missing case, and it
belongs on `cons_value` itself (a new tag, e.g. `TAG_NATIVE`), not
bolted onto Var -- real Clojure's Var is just a mutable box holding an
ordinary `Object` reference, the same slot every value uses (locals,
vector elements, map values, ...); nothing about holding an interop
object is Var-specific there, so it shouldn't be here either.

Validated in isolation first (`test/f/native_test.f90`, both
compilers), before touching `cons_value`:

- The payload is a `class(*), pointer`, not `type(c_ptr)` --
  `iso_c_binding` was flagged as a real prior pain point, and it's not
  actually needed: ChemSol and any other realistic target here are
  real Fortran, not a C ABI, and a native Fortran pointer already
  crosses that boundary. Scalars of odd kinds (`real(4)`,
  `integer(8)`) and a derived-type struct both round-trip exactly
  through it via `select type`.
- **Pointer, not allocatable, matters**: intrinsic structure
  assignment on a `pointer` component does pointer association (copy
  the reference) and never invokes `assignment(=)`/`FINAL` on the
  target -- sidesteps the "class(*) allocatable doesn't dispatch
  defined assignment" gotcha from earlier, and is also the *correct*
  semantics: Java object references alias on assignment, they never
  deep-copy, and this matches that exactly.
- **Confirmed, concretely, a sharper version of the `closure_t_assign`
  warning** ("default struct assignment doesn't cascade into an
  embedded type's own defined assignment"): a brand-new host struct
  embedding a `cons_value`, with no `assignment(=)` of its own,
  crashed the moment a naive copy went out of scope
  (`DEALLOCATE of a pointer that is not the whole content of a pointer
  ALLOCATE` -- both copies thought they owned the only reference to
  the same cons cells, so both tried to free them). Demonstrated
  safely afterward the same way `rc_test.f90`'s `holder_naive` does
  (a leaked, never-dereferenced pointer copy), then fixed the proven
  way: an explicit `assignment(=)` forwarding field-by-field, same
  pattern as `closure_t_assign`. **Rule, not a suggestion**: any new
  host type that embeds a `cons_value` (or any other clotran ref type)
  needs its own explicit `assignment(=)` -- Fortran's default is not
  reliable here on this project's compilers, full stop.
- Arbitrary nesting in both directions works: a clotran value (map/
  vector, once `TAG_NATIVE` is real) holding a native struct as a
  leaf, a native struct holding a real clotran string as one of its
  own fields, and a native struct built from *another* native struct
  (native-in-native) -- all round-tripped through three levels of
  `select type` traversal.

**How this shapes the future adapter generator** (the `f2py`/SWIG-
style tool above): it isn't one marshaling strategy per library, it's
two, chosen per argument/return value from the library's own real
signature -- a scalar of some kind (box/unbox + kind convert, no
`TAG_NATIVE` involved) versus a derived-type value (wrap/unwrap via
the native pointer). For the latter, the native tag will need to
carry a type identity alongside the raw pointer (a name/descriptor,
not just a bare `class(*)`), so `instance?`/`type` can tell a
`mathblas.matrix` apart from a `chemsol.something` -- otherwise a
value from one library's adapter could be handed, unchecked, to a
routine expecting a different library's type. Same idea as the
existing `Integer`/`Long`/etc. pseudo-classes `instance?` already
matches against, just for real Fortran-object identity instead of
clotran's own built-in kinds. Not implemented yet -- `cons_value`
itself doesn't have the tag yet, this section records the validated
plan and the concrete gotcha to avoid when it's added.

## Real Vars: `TAG_VAR`, reusing `atom_ref` wholesale

A namespace's own bindings used to be plain `symbol -> value`, with a
comment noting Var (metadata, `#'foo`, thread-local dynamic bindings)
wasn't built because nothing needed it yet. Something did: `(var sym)`/
`#'sym` used to read as a bare symbol (or `(quote sym)`), a
placeholder documented as "not a faithful stand-in for what `(var
sym)` actually does" -- and real core.clj's own bootstrap turned out
to already depend on the real thing (`(. (var defn) (setMacro))`,
right at the start of `defn`'s own definition).

**Deliberately NOT a new Fortran type.** A Var's root binding is
structurally identical to what `atom_ref`/`atom_node` (Values.f90)
already is: "one genuinely mutable slot, shared by reference." Rather
than a parallel `var_ref`/`var_node`, `TAG_VAR` reuses `atom_val`
(the existing field) outright -- `Atom.f90`'s `atom_new`/`atom_deref`/
`atom_reset` don't check the tag, only whether `atom_val` is
allocated, so they work unmodified for a Var's root too. `str_val`
(also already on `cons_value`) holds the qualified `ns/name` for
printing (`#'user/foo`). Zero new types, zero new assign/finalize/
refcount code -- `cons_value_assign`/`cons_value_release` already
handle `atom_val` generically. The only real difference between
`TAG_ATOM` and `TAG_VAR` is behavioral, not structural: a symbol
resolving to a Var auto-derefs transparently (matching real Clojure --
you don't `@`/`deref` a Var to use it); an atom never does.

`Namespace.f90`: `ns_intern` (def!'s job) now mutates an existing
Var's root in place (`atom_reset`) rather than replacing the map
entry, so identity survives redefinition -- `(let [v (var x)] (def! x
99) (var-get v))` sees `99`, matching real Clojure (anything already
holding a Var reference sees a later redefinition). `ns_get_own`/
`ns_resolve` transparently deref, so all 17 existing call sites in
Eval.f90 needed zero changes. Two new functions, `ns_get_own_var`/
`ns_resolve_var`, return the Var itself (unresolved) for `(var sym)`/
`#'sym`/`var-get`/`var-set`.

`Eval.f90`: `(var sym)` resolves a real Var instead of returning a
bare symbol (errors "Unable to resolve var" on a truly unbound name,
matching real Clojure); `#'sym`'s reader macro (`LispReader.f90`) now
expands to `(var sym)` instead of `(quote sym)`; `.get`/`.set` on a
`TAG_VAR` target (core.clj's own `var-get`/`var-set`) reuse
`atom_deref`/`atom_reset` directly; `.setMacro` (needed by `defn`/
`defmacro`'s own bootstrap, see above) gained a `TAG_VAR` case
mirroring the existing `TAG_SYMBOL` one, now mutating the Var
directly by identity instead of re-resolving by name.

**`binding`/`push-thread-bindings`/`pop-thread-bindings`: built, but
not exercisable end to end yet -- a separate, pre-existing gap blocks
it, not this work.** `atom_node` gained `dyn_stack` (a plain
`cons_value` array): `atom_deref` now checks its top before falling
back to the root, so a Var auto-derefs its dynamic value transparently
wherever it's already read (ns_get_own, `.get`/`var-get`, plain
`deref`). `Eval.f90` gained `push-thread-bindings`/
`pop-thread-bindings` as real builtins, plus a module-level flat stack
(`binding_stack_vars`/`binding_stack_frame_sizes`) recording exactly
which Vars each push touched, so pop undoes exactly that frame (nested
`binding` on the same Var restores correctly). `ponytail`: one global
stack, not real per-thread storage -- single-threaded today. Real
Clojure's bindings are thread-local, so this and `dyn_stack` both
become per-context when concurrency lands; see PLAN.md, which now
records Clojure's own STM model rather than the Rust-inspired one
originally sketched here.

Along the way, found and fixed a real, independent bug real `binding`
needs regardless of any of the above: `eval_try` never actually ran a
trailing `(finally ...)` clause when the body errored (it wasn't
recognized as its own clause at all -- just evaluated as an ordinary
body form, which the error-triggered early exit skipped entirely).
Real `binding` expands to exactly `(push-thread-bindings ...) (try
body (finally (pop-thread-bindings)))`, so an unhandled error inside
`binding`'s own body used to leak the pushed frame forever. Fixed:
`finally` is now its own recognized trailing clause (after an optional
`catch`), always runs -- even with no catch, even when the body
errored -- and its own error (if it has one) masks whatever the
try/catch above produced, matching real Java/Clojure `finally`
semantics. Verified directly (`(try (throw ...) (finally (swap! log
...)))` -- log shows the cleanup ran).

**Getting real `let`/`loop`/`fn`/`binding` working meant clearing a
chain of independent bugs, each one hidden behind the last.** The
symptom never changed (`let` "requires an even number of forms"); the
cause moved every time one was fixed. In order:

1. **The flat dot form.** `(. target member args*)` is legal Clojure,
   equivalent to `(. target (member args*))`, and core.clj uses it in
   59 places -- every bit operation among them (`bit-and` is literally
   `(. clojure.lang.Numbers and x y)`). `eval_dot` treated a
   bare-symbol member as field access ALWAYS and silently dropped the
   trailing args, so `(bit-and 4 1)` returned the `and` field itself
   (`#<builtin bit-and>`) instead of 0. That made `even?` return false
   unconditionally, which made `assert-args` reject every bindings
   vector, which broke `let`/`loop`/`binding`/`if-let`/... all of it,
   from one missing syntax form. (Two days of "corruption" hunting
   before noticing real core.clj's source simply says what it says.)
2. **`pre_expand` on `eval_fn` was the wrong hook.** `def` runs once
   per definition; `eval_fn` runs once per closure VALUE constructed,
   including every throwaway closure a macro builds mid-expansion
   (`destructure` alone builds two per call). Freezing there re-did the
   whole expansion every time, and expanding builds more closures, so
   it compounded until bootstrap stopped finishing (confirmed on a
   sampled stack: pre_expand -> eval_fn -> pre_expand -> ...). Moved to
   `eval_def`, which is once per definition -- what a real compiler
   does anyway, and the same freeze.
3. **`pre_expand` skipped vectors entirely.** Anything not a list
   returned unchanged, so every `let*`/`loop*` BINDINGS VECTOR went
   unfrozen -- and binding inits are ordinary code. core.clj's own
   `drop` kept a raw `(fn [n coll] ... (and (pos? n) s) ...)` in its
   `step` binding, so calling `drop` re-expanded `and` at runtime ->
   `let` -> assert-args -> destructure -> partition -> `drop`, forever.
   pre_expand now walks vectors like lists.
4. **Set literals didn't evaluate their elements.** `#{'&}` held the
   FORM `(quote &)` rather than the symbol `&`, so `destvec*`'s own
   `(some #{'&} b)` rest-arg test never matched and `[params & body]`
   destructuring silently dropped its bindings (a `seq__NNN` bound
   nowhere). Vectors and maps already evaluated; sets were missed.
5. **Sets weren't callable.** `(#{'&} x)` is a membership lookup in
   real Clojure, and core.clj's own destructuring relies on it.
6. **An empty `& rest` bound `()` instead of nil.** Real Clojure binds
   nil, and core.clj nil-puns rest args constantly (`(nil? oldform)`,
   `(when more ...)`) -- an empty list is TRUTHY, so every one of
   those took the wrong branch.
7. **`first`/`rest` only handled lists and vectors.** Real `RT.first`
   is `seq(x).first()`. `(first {:a 1})` returned nil, so map
   destructuring called `(.getKey nil)`.
8. **`lazy-seq` did nothing.** It expands to `(new clojure.lang.LazySeq
   (fn* [] ...))`, and `eval_new`'s generic passthrough handed the
   thunk straight back -- so `map`, `filter`, and every other lazy
   function evaluated to `#<fn>`. Now forced (see the ceiling below).
9. Smaller, same flavour: `.toString`/`.getNamespace`/`.startsWith` and
   friends; a real `StringBuilder` (core.clj's multi-arg `str` builds
   one); two-arg `(keyword ns name)`/`(symbol ns name)`; `bit-*`,
   `quot`/`rem` and the shifts as natives; `RT/nextID` for `gensym`;
   `*ns*` as a real Var; `PersistentHashMap/create` taking ONE seq of
   keyvals rather than varargs (it was making the whole seq a single
   KEY, which is what the long-standing flaky `hash-map` crash
   actually was -- gone now); and a general rule that a bare
   `clojure.lang.*` name resolves to the keyword of the same name
   instead of being enumerated by hand in clotran.clj one at a time.

Result: `let`, `loop`, `fn`, `defn`, sequential destructuring
(`[a b & c]`), associative destructuring (`{:keys [...]}`, `{x :x}`),
variadic fns, `map`/`filter`/`reduce` all work, and core.clj loads
with no warning. `eval_test` went 94/103 -> **167/169 on both
compilers**, with no crash anywhere (previously it aborted partway).
The two that remain both need `*out*` (`with-out-str`/`pr-str`), which
is real output redirection and hasn't been built.

One test-hygiene bug worth noting, since it hid several others: check
25g deliberately shadows `clojure.core/first` and never put it back,
so every later check ran against a broken `first` -- which is what
made `disj`, `%&` and the Var printing checks "fail". It restores it
now.

## Real lazy seqs: TAG_LAZYSEQ

Fortran has no notion of a deferred value, so this is built the same
way clojure.lang.LazySeq is: a node with three states -- not yet run
(holding the thunk), run and produced a first/rest pair, or run and
produced nothing. `lazy-seq` expands to `(new clojure.lang.LazySeq
(fn* [] body...))`, so eval_new just builds one of these and runs
NOTHING.

**Realization is memoized, and that is where the big-O lives.** A cell
flips state exactly once and keeps the result, so:

| operation | cost |
|---|---|
| `(lazy-seq ...)` | O(1), nothing runs |
| `first` / `rest` / `next` | O(1) -- realizes that one cell |
| `nth s i` | O(i), realizes i+1 cells -- never the whole seq |
| `count` | O(n), realizes all of it (same as real Clojure) |
| walking the same seq again | free -- already realized |

Without the memoization, a nested lazy seq (`map` over `map` over
`filter`...) would re-run each generator per step and go exponential;
with it, a full walk is O(n) and `(take 5 (iterate inc 0))` costs five
steps no matter how infinite the underlying seq is.

Three pieces made it fit:

- **RT can't call a closure** (it sits below Eval), so Eval hands its
  forcer down at startup: `rt_set_lazy_forcer(force_lazy)`. RT's
  seq/first/rest/next/count/nth force through that pointer.
- **`cons` onto a lazy seq must not realize it.** A `cons_cell`'s cdr
  is a `cons_ref`, so it simply cannot hold an unrealized rest -- and
  `repeatedly` is literally `(lazy-seq (cons (f) (repeatedly f)))`, so
  a cons that forced its tail would never terminate. `cons` onto a
  lazy seq therefore builds an already-realized lazy node (head + any
  tail) instead, which is exactly real Clojure's `Cons` over an ISeq.
- **A seq in code position is a form.** `list*`/`concat` are lazy, so
  macro expansions now routinely come back as lazy seqs; eval_form
  realizes those into a list and evaluates them, the way real
  Clojure's compiler analyses any ISeq.

`range`/`iterate`/`repeat`/`cycle` are each a Java class in real
core.clj (`clojure.lang.LongRange/create` and friends). They're
written out in clotran.clj over the same `(new clojure.lang.LazySeq
(fn* [] ...))` primitive -- longhand, because clotran.clj loads before
core.clj defines the `lazy-seq` macro. All of them are genuinely
infinite: `(nth (range) 7)`, `(take 3 (repeat :x))`, `(take 4 (cycle
[1 2]))` all terminate.

Realizing a cell drops its thunk (`node%thunk = nilv`), so a realized
seq doesn't retain the closure that generated it -- the same "don't
hold onto the head" hygiene real Clojure needs.

**Two more real bugs fell out of getting `binding` to work on top of
this**, both of which had been quietly wrong for a long time:

- `let*` took only its FIRST body form. Real Clojure's `let*` has an
  implicit `do`; mal's takes exactly one form, and that's what this
  had inherited. So `(let [] (side-effect) x)` evaluated to the side
  effect, not `x` -- which is precisely how `binding` lost its body
  value, since `binding` expands to `(let [] (push-thread-bindings
  ...) (try body (finally (pop-thread-bindings))))`.
- Syntax-quote was namespace-qualifying `finally` (and `recur`,
  `throw`, `set!`), so `binding`'s expansion carried a
  `(user/finally ...)` clause that eval_try didn't recognize as a
  finally at all -- the pop never ran and the binding leaked.

With both fixed, `binding` is real: the body sees the bound value,
functions called from inside see it, the root is restored on the way
out, and nested bindings unwind one level at a time. Still one global
stack rather than per-thread -- there are no threads yet; see the
concurrency note.


## Getting `defn`/`let`/`loop` to actually work against real core.clj

Getting past `defn`'s own bootstrap (previously it silently failed to
bind at all) needed several more real fixes, found by walking further
into core.clj than before rather than by inspection:

- **Load order: `clotran.clj` must load *before* `core.clj`, not
  after.** core.clj's own bootstrap-era `cons`/`list`/`fn` call
  straight into `clojure.lang.RT` from their very first few forms,
  long before the file finishes -- loading it after meant every one of
  those calls failed for the entire rest of the file (a warning at
  startup, easy to miss the real cause of).
- **`(. Class member)` (bare-symbol field access) vs `(. Class
  (member))` (a real, parenthesized 0-arg method call) look identical
  once args are both empty** -- `eval_static_call` used to guess by the
  found value's own tag (assume a builtin/fn value must mean "call
  it"), which broke `clojure.lang.PersistentList`'s own `creator`
  field (a bare-symbol field that just *holds* an IFn, never meant to
  be invoked on the spot -- `list` itself came out `()` instead of the
  builtin). Fixed by passing the shape (bare symbol vs parenthesized)
  down as an explicit flag instead of inferring it from the value.
- **`defmacro`/`defn` both need to skip an optional leading docstring
  and/or metadata map before the params vector** (`(defmacro name
  "doc"? {attrs}? [params] body)`) -- confirmed against real
  `clojure`'s own `defmacro`/`defn` source, which do exactly this
  before ever binding params. Without it, the docstring itself gets
  mistaken for the params vector, and the *real* params vector ends up
  evaluated as an ordinary body form (its own symbols looked up as
  values) instead of bound as parameter names -- broke `let`, `cond`,
  and every other core.clj macro that carries a docstring.
- **Multi-arity `defmacro`** (`(defmacro name ([p1] b1) ([p2] b2)
  ...)`, same clause shape multi-arity `fn*` already had) -- real
  core.clj's own `or`/`and` are defined exactly this way; the
  `defmacro` special form only ever parsed a single params vector,
  silently misreading the whole first clause as params.
- **`loop*`/`recur` had never actually been implemented** -- a real,
  previously-invisible gap (mal's own borrowed test suite never
  exercises `loop`, only named self-recursive `fn*`). Implemented by
  reusing the exact tail-call machinery `fn*`'s own `recur` already
  has: `loop*` builds an ordinary `TAG_FN` closure (params = the
  binding names, body = the loop body, env = the loop's own env) bound
  to the symbol `recur`, so `(recur args...)` inside the body is just
  an ordinary call into that closure -- no separate loop-specific
  tail-call path needed.
- **`new`/`(Class. args...)`** -- neither existed. `new` evaluates and
  returns its first constructor arg (matching how `throw`/`catch`
  already treat any value as throwable regardless of a real type --
  covers the common `(new SomeException "msg")` shape), with
  `clojure.lang.Atom` specifically constructing a real atom.
  `(Class. args...)` is reader/eval-time sugar for `(new Class
  args...)`, rewritten the same way `.method` sugar already is.
- **A real, previously-latent HAMT bug**: `node_assoc`/`node_dissoc`'s
  own path-copy did `new_node%slots(:) = old%slots(:)`, a bulk array
  assignment of `hamt_slot` -- a type with no `assignment(=)` of its
  own, so Fortran falls back to default derived-type assignment, which
  silently mishandles `bucket_keys`/`bucket_vals` (allocatable arrays
  of `cons_value`, which *does* have one) one level down -- the same
  "automatic reallocation on array assignment cannot be trusted"
  gotcha already catalogued above, just one level deeper than where it
  was first found. Invisible for the HAMT's own unit test (small
  int/string values); corrupted real closures once `*ns*` itself
  (namespaces are backed by this same HAMT past 8 entries) grew large
  enough to promote. Fixed the same proven way: `copy_slot` copies
  every field explicitly, bucket arrays pre-allocated to size first.

**Fixed: `assert-args` vs `let` (was a known limitation, now a real
fix, not just a mitigation).** Real core.clj's own `assert-args` (used
by `let`, `loop`, `binding`, `if-let`, and others to validate their
bindings vector) has, in its own source, `~(let [more (nnext pairs)]
(when more (list* \`assert-args more)))` -- a self-recursive reduction
that uses `let` internally. This is completely inert in real Clojure:
the compiler resolves `let` to a specific Var *once*, at the time
`assert-args` itself is compiled (while `let` is still its own simple
bootstrap version, long before core.clj redefines it), and that
resolution is permanent, regardless of `let` being redefined later in
the same file. clotran has no such compile-time Var model -- every
macro call is resolved fresh, dynamically, by name, every single time
it runs (which is otherwise exactly correct and is what the rest of
this project relies on). Once `let` becomes the real, validating,
destructuring macro (core.clj redefines it partway through the file),
`assert-args`'s own internal `let` usage starts resolving to *that*
`let` -- which validates its own bindings via `assert-args` again --
genuine, unbounded mutual recursion, confirmed via lldb (a stack that
grows without ever repeating a shorter cycle, not merely deep).

The real fix: `pre_expand` walks a macro (or, now, a `fn*`/`fn`/`defn`)
body ONCE, right after it's built, expanding every nested macro call
it finds in actual code position using `*ns*` as it stands *right
now* -- mirroring real Clojure's compile-time Var resolution without
needing a real compiler or a Var object. `assert-args`'s own internal
`let` usage gets frozen this way at `assert-args`'s own `defmacro`
time (while `let` is still the simple bootstrap version), so it never
sees the later, real, validating `let` at all -- the mutual recursion
never starts. This isn't the "freeze the structure, lose track of
which env free variables resolve in" approach that was tried and
rejected earlier (see git history): `pre_expand` only ever substitutes
in the *unevaluated* expansion of a nested macro call (a purely
syntactic rewrite -- the nested call's own free variables ride along
in the substituted AST and resolve normally, later, wherever that AST
ends up actually running), never evaluates anything early or captures
an env. Applied unconditionally to every `defmacro` body (an earlier
attempt gated this to only `assert-args` by name, which worked but
was strictly narrower for no real benefit, since expanding a nested
macro call this way is always safe).

Fixing `assert-args`/`let` directly surfaced the same problem one step
removed: `integer?`/`even?` are ordinary `defn`s (not macros) whose
body calls `or` (a macro) internally; without freezing that too, every
call to `integer?`/`even?` re-resolves `or`'s own internal `let` fresh
against `*ns*` as it stands *then* -- the real `let`, once it exists --
reintroducing the identical mutual recursion one level removed. Fixed
by applying the same `pre_expand` to `eval_fn`'s own clause bodies
(`fn*`/`fn`, and so every `defn`), not just `defmacro`'s.

`eval_macro_head`'s own macro-expansion depth cap (see below) turned
out to guard only ITS OWN internal recursion, not `pre_expand`'s --
`pre_expand` calls `eval_macro_head` once per nested macro call it
finds and then recurses on the result itself, a second, independent
recursion on top of the first, so the same cap now wraps that outer
loop too (same shared counter, same 60-deep threshold, same "leave it
unexpanded and let normal per-form tolerance pick it up" fallback
instead of erroring).

While implementing this, a real, independent, previously-undiscovered
bug turned up in the same area: `eval_macro_head` never did
multi-arity dispatch at all -- it always bound params/evaluated the
body of the PRIMARY (first) clause, regardless of the actual call's
arity, the same bug ordinary `fn*` calls would have if `apply_closure`
didn't call `select_clause`. Real core.clj's own `or`/`and` are
multi-arity `defmacro`s (`([] nil) ([x] x) ([x & next] ...)`), so
every call to either one that didn't happen to match the 0-arg clause
silently ran the WRONG body -- this alone made `or`/`and` (and so
`integer?`/`even?`, both `or`-based) always return `nil`. Fixed by
having `eval_macro_head` call the existing `select_clause` helper,
same as `apply_closure` already does.

**Remaining safety net**: `eval_macro_head` (and now `pre_expand`'s
own outer loop, see above) still caps nested macro-expansion depth
(currently 60) as a hard safety net -- purely to turn what would
otherwise be a real Fortran stack overflow (a crash) into a catchable
`eval_error` ("macro expansion too deep"), for whatever mutually-
recursive macro pair turns up next that this project hasn't found and
frozen yet.

## Characters, `#_`, multimethods, and the printing stack

Four more pieces core.clj genuinely needs, found the same way as the
rest -- by walking further into the file, not by inspection. Together
with `reduce` they took core.clj's own load from 57 failing forms
to 16.

**`TAG_CHAR`** is a real type, not a one-character string. Real
Clojure's `\a` is a `java.lang.Character` and `(= \a "a")` is false,
so a tag of its own is the only faithful representation; reusing
`str_val` (length 1) means equality and hashing fall straight out of
the existing string handling, with no new code beyond adding
`TAG_CHAR` to a case list in three places. `seq` over a string now
yields characters, matching real Clojure. The reader takes the
character after `\` unconditionally (so `\(`, `\"` and `\/` all read)
and then keeps any regular characters after it, which is what makes
the named forms (`\newline`, `\space`, `\tab`, `\return`, `\formfeed`,
`\backspace`) stay one token. `\uNNNN`/`\oNNN` aren't supported --
nothing in core.clj uses them, and an honest reader error beats a
half-decoded character.

**`#_`** (discard) reads the next form, throws it away, and returns
whatever follows -- so it works mid-collection, mid-arglist and at top
level alike. The one wrinkle is tokenizing: `#` has to stay an
ordinary character so an auto-gensym's trailing `#` (`x#`) doesn't
split off, which means `#_2` would otherwise lex as a single symbol.
The regular-character run cuts `#_` back off explicitly -- the only
place `#` leads rather than trails.

**`TAG_MULTIFN`** is `clojure.lang.MultiFn`: what `defmulti`
constructs and `defmethod` mutates. Same "reuse `atom_val` as the one
mutable box" pattern as `TAG_VAR`, holding a map of `{:dispatch fn
:default dv :methods {dv -> fn}}` -- a multimethod really is a value
plus one genuinely mutable table, and every holder of the multifn has
to see a later `defmethod`, which is exactly what mutating the shared
box gives. Dispatch is exact match, then `:default`. Real Clojure also
walks the global hierarchy (`isa?`) and consults `prefer-method`;
neither is here yet, so a derived dispatch value won't find its
parent's method.

Two syntax-quote bugs surfaced only once multimethods existed, both
about qualifying symbols that shouldn't be qualified:

- **A member name never carries a namespace.** `defmethod` is
  `` `(. ~multifn addMethod ...) ``, and syntax-quote qualifies every
  bare symbol it sees -- including `addMethod`, which arrived here as
  `user/addMethod`. Real Clojure's compiler ignores that namespace for
  exactly this reason (`HostExpr` only ever munges the name part), so
  `eval_dot` strips it too now. That is why real Clojure's own
  `defmethod` works at all.
- **A class name survives syntax-quote untouched.** `defmulti`'s
  template contains `` `(new clojure.lang.MultiFn ...) ``; real
  Clojure resolves that symbol through the compiler, where it names a
  class, not a var in the current namespace. Without an import table
  the reachable approximation is Java's own naming convention (dotted,
  or leading capital), which is what core.clj's templates rely on.
  Before this, that form fell through `eval_new`'s generic passthrough
  and every multimethod evaluated to the *string* of its own name.

Also fixed alongside: `..` was being caught by the `.method` interop
sugar (any symbol starting with `.`), so `root-resource`'s
`(.. (name lib) (replace \- \_) ...)` never reached core.clj's own
`..` macro.

**The printing stack** (`pr`/`prn`/`println`/`pr-str`/`with-out-str`)
now works end to end. It bottoms out in `(. *out* (append s))`, so:
`*out*`'s default binding stays nil, meaning the console itself, and
`.append`/`.write`/`.flush` on nil write straight to stdout;
`java.io.StringWriter` is the same object as `StringBuilder`
(`TAG_STRING_BUILDER`), which is what lets `with-out-str` bind `*out*`
to one and read it back with `(str s#)`. `(class x)` answers the
keyword naming the type rather than a `java.lang.Class` -- what it's
actually used for here is `print-method`'s own dispatch function and
error messages.

The last link is that real Clojure's `print-method` methods all live
in `core_print.clj`, which core.clj `(load "core_print")`s and which
isn't ported -- leaving the multimethod with no methods at all, so
every print call failed on dispatch. `eval_core_bootstrap` installs
one `:default` method delegating to the native printer. It goes there,
not in `clotran.clj`, because that file loads *before* core.clj, where
the `defmulti` itself lives.

**Where core.clj's remaining 16 failures are.** `CLOTRAN_DEBUG_LOAD=1
./clotran-bin` lists them -- that's the project's running coverage
number, so it's an environment variable rather than a patch applied by
hand each time. Seven are `(load "...")` of the other upstream core
source files (`core_print`, `core_deftype`, `core/protocols`, `gvec`,
`genclass`, `core_proxy`, `uuid`): none ported yet, and
`genclass`/`core_proxy` are JVM bytecode generation that never will
be. Five are `defprotocol`/`extend-protocol`/`deftype` and the
`Eduction` type that depends on them. The rest are
`clojure.lang.RT/baseLoader`, `Thread/currentThread` reached through
`getContextClassLoader`, and `(require 'clojure.java.io)` --
classloaders and host I/O.

## Loading the OTHER upstream core files: `RT/load` and core_print.clj

core.clj isn't one file. Six lines in the middle of it are `(load
"core_print")`, `(load "core_deftype")`, `(load "core/protocols")`,
`(load "gvec")`, `(load "genclass")`, `(load "core_proxy")`, and every
one was failing -- which is where most of the remaining failures were
concentrated, since everything those files define (`defprotocol`,
`deftype`, and all of `print-method`'s methods) went missing with them.

`(load "core_print")` reaches the host as `(clojure.lang.RT/load
"clojure/core_print")`: core.clj's own `load` builds a classpath-
relative path out of `root-directory` and strips the leading slash.
There is no classpath here, so `RT/load` maps that straight to a file
under `src/clj` (`clotran.native/resource-path` resolves it against the
executable, the same rule the bootstrap's own loads use).

Getting `root-resource` to produce that path at all needed two fixes,
both of which had been silently wrong:

- **`..` was being read as a constructor.** `(ClassName. args)`
  rewrites to `(new ClassName args)`, and the test for it was "the name
  ends in a dot" -- which `..` does. So `(.. x (m a) (m b))` quietly
  evaluated to `x` instead of chaining, with no error at all. `..` now
  escapes both that rewrite and the `.method` sugar.
- **`.replace` (the char/char overload) didn't exist**, which is what
  `root-resource` uses to turn `clojure.core` into `clojure/core`.

With those, **core_print.clj is real upstream source, loading and
running unmodified** -- all ~40 `defmethod`s, the `prefer-method`
calls, `print-sequential`, `*print-length*`/`*print-level*` -- and it
replaces the single `:default` method the previous pass installed as a
stand-in. Reaching it turned up a pile of genuine gaps, each fixed
where it belonged rather than papered over:

- **`nth` ignored its not-found argument**, and `(nth nil 0)` threw
  instead of answering nil. Not cosmetic: destructuring compiles to
  `(nth v 0 nil)` for every position it binds, so `(let [[a b] nil]
  ...)` threw, and with it every core.clj form that destructures a
  possibly-nil value. It was also the real cause of the long-standing
  `for`/`condp` "nth: index out of bounds".
- **`set!`** was listed as a special form but never implemented. It
  writes the innermost dynamic binding if one is in effect, else the
  root (`var_set`). Real Clojure refuses set! on a Var with no thread
  binding; clotran has no threads, so the root is the honest place for
  it to land.
- `vec` (`LazilyPersistentVector/create`), `.charAt`, `String/format`
  (the `%s %d %x %n %%` subset core.clj actually uses), `hash`
  (`Util/hasheq`, and `System/identityHashCode`, since there is no
  object identity separate from value here), `to-array`, `.isNaN`,
  `.isArray`, `.getClass`, and `Double/POSITIVE_INFINITY` /
  `NEGATIVE_INFINITY` as real IEEE values via `ieee_arithmetic` rather
  than a `huge()` stand-in, so a computed infinity really does compare
  equal.

## Multimethod dispatch over host types: the hierarchy is declared, not reflected

core_print.clj dispatches `print-method` on *interfaces* --
`clojure.lang.ISeq`, `java.util.Map`, `Object` -- and leans on
`prefer-method` to break ties. Exact-match dispatch can do none of
that, so multimethods needed the rest of their semantics.

What the JVM gets from `Class.isAssignableFrom` has to come from
somewhere else here, and the cheap answer turned out to be the right
one: **class names are keywords** (`(class [1])` is
`:clojure.lang.PersistentVector`, and a bare class name in source
evaluates to the keyword of the same name), so the relationships
between them can live in the same global hierarchy `derive` already
maintains. `src/clj/clotran_types.clj` declares that hierarchy -- and
because it is declared with real `derive`, clojure.core's own `isa?`,
`parents`, `ancestors` and `prefer-method` work on host types
unchanged. The host owes only the lookup.

Dispatch now mirrors `MultiFn.findAndCacheBestMethod`: exact match,
else every method key the dispatch value `isa?`, with `dominates`
(`prefers` OR `isa?`) picking the winner and a genuine tie being an
error rather than an arbitrary choice. `dominates` falling back to
`isa?` is what keeps a catch-all `Object` method from making every
dispatch ambiguous. `prefers` recurses through `(parents x)` and
`(parents y)`, same as MultiFn.java: core_print.clj prefers `ISeq` over
`java.util.Collection` and never mentions `java.util.List`, yet a list
matches both the `ISeq` method and the `java.util.List` one, and the
preference only reaches the latter through `List`'s parent
`Collection`.

Two smaller decisions fell out of this:

- **`java.lang` is the implicit package**, so `Double` and
  `java.lang.Double` are one class -- and core_print.clj really does
  use both spellings, sometimes for the same type. As keywords those
  would be different dispatch values, so one spelling wins: the bare
  one (`class_keyword_name` strips the prefix), since it is what the
  source mostly writes and what reads best out of `(class x)`.
- **Any unresolved class-shaped name evaluates to its own keyword**,
  not just `clojure.lang.*` as before -- `Object`, `java.util.Map`,
  `Throwable`. The test is Java's own naming convention (dotted, or
  leading capital), the same one syntax-quote uses. The cost is that a
  mistyped capitalized symbol reads as a keyword instead of erroring;
  the alternative is failing every host-class reference in core.clj.
  This also retired the hand-written list of `(def clojure.lang.ISeq
  :clojure.lang.ISeq)` forms clotran.clj used to carry.

`ponytail`: dispatch is linear over the method table on every unmatched
value, where real Clojure memoizes the winner. A cache cleared by
addMethod/removeMethod is the upgrade if a hot multimethod shows up.

**Where core.clj's remaining 14 failures are** (`CLOTRAN_DEBUG_LOAD=1
./clotran-bin` lists them): five are the still-unported sibling files,
of which `genclass` and `core_proxy` are JVM bytecode generation that
never will be; five are `defprotocol`/`extend-protocol`/`deftype` and
the `Eduction` type built on them, all waiting on core_deftype.clj; the
rest are `clojure.lang.RT/baseLoader`, `Thread`'s context classloader,
and `(require 'clojure.java.io)` -- classloaders and host I/O.


## Protocols, and resolving symbols in the namespace they were written in

`core_deftype.clj` is vendored and runs: `defprotocol`,
`extend`/`extend-type`/`extend-protocol`, `satisfies?`, `extenders`.
Dispatch goes through upstream's own `emit-method-builder`, including
its `MethodImplCache` call-site cache -- no rewriting, because a
protocol is already the shape clotran has: a table keyed by type, which
is exactly what the multimethod work built. `deftype`/`defrecord`/
`reify` still need the `deftype*` compiler special form and are not
here yet.

**Why protocols are the right seam for Fortran interop.** Fortran's own
polymorphism (an abstract derived type with deferred type-bound
procedures, dispatched through `class(t), pointer`) is *closed*: the set
of implementors is fixed when the program is compiled, and there is no
runtime reflection to ask an object what it implements. A protocol is
*open* -- `extend-protocol` on a type you do not own, after the fact, is
the whole point. So the two are opposite ends of one bridge rather than
alternatives:

| Fortran | clotran |
| --- | --- |
| abstract type + deferred TBP | a protocol -- the natural import target |
| each concrete extending type | one `extend` registration |
| `class(t), pointer` dispatch | inside the generated shim; clotran just calls it |
| `generic ::` | a generated argument-dispatching fn, NOT a protocol |
| `interface` block | input to the generator (argument kinds, for marshalling) |

The protocol works as the seam precisely because it is open: a table in
clotran can hold entries that call into Fortran vtables, where a Fortran
vtable can never hold an entry that calls back into clotran. Traffic is
one-way by design -- a Fortran object rides in clotran as a
`class(*), pointer` (see the native interop section), and a clotran
`deftype` is deliberately NOT passable to Fortran, since a Fortran
derived type is a compile-time thing. Doing that in reverse would mean
generating and compiling Fortran at runtime, i.e. a JIT.

### Free symbols resolve in the DEFINING namespace

Vendoring `core/protocols.clj` immediately broke `reduce`, and the
reason turned out to be the biggest single correctness gap left in the
evaluator: a function's free symbols were resolved against whatever
namespace happened to be *current when it ran*, not the one its source
was written in. `clojure.core.protocols/seq-reduce` could not find its
own `internal-reduce` once called from `user`. Real Clojure resolves
symbols when a form is compiled, in the namespace being compiled.

clotran has no compile step, so the defining namespace rides on the
closure's own env frame (`env_node%ns_name`, set by `eval_fn` and
`eval_defmacro`, read by `env_defining_ns`). On the env rather than on
`closure_t` deliberately: a tail call reuses the trampoline instead of
returning through `apply_closure`, so a call stack of namespaces would
be wrong, while the env chain is already exactly right. `eval_fn`
inherits the *enclosing* frame's namespace rather than reading
`*ns*` -- a fn built while another namespace's function is running
(`clojure.test/test-vars` builds several) belongs to the namespace whose
source it was written in.

Three more things had to follow the same rule: `(var x)`, `set!`, and
syntax-quote's own qualification. That last one has a second part --
`` `temp/do-template `` has to expand its ALIAS to the real namespace at
read time, because the expansion is evaluated wherever the macro was
called from, where that alias does not exist. `clojure.test`'s `are`
emits exactly that.

This also silently fixed a mystery: several `eval_test` checks passed in
the REPL but failed inside the suite, because an earlier check
(deliberately) shadows `first` in `user`, and core.clj's own functions
were picking up the shadow.

## Running real Clojure's own test suite

`test/clj/clojure/test_clojure/` holds test files vendored from
clojure/clojure, run by `scripts/run-clojure-tests`. This is the
conformance number that matters: the hand-written checks in
`test/f/*_test.f90` belong to the *host* -- refcounting, native interop,
the Fortran gotchas catalog -- which upstream cannot test, and language
semantics are much better judged by Clojure's own assertions than by
ours. Expect `test/f/eval_test.f90` to shrink as upstream coverage grows.

Getting there needed `clojure.test` itself (vendored, with
`clojure.template`/`walk`/`string`/`stacktrace`), and:

- **`unescape_string` was O(n^2) and crashed on a long string** -- the
  same reallocating-assignment fragility the tokenizer was already
  rewritten for, just in the reader's other half. clojure/test.clj's ns
  docstring is ~7KB and hit it exactly. It now sizes a buffer once and
  slices.
- **Real Var metadata** (`atom_node%var_meta`, shared by reference like
  the root), and `def` transferring the name symbol's metadata onto the
  Var -- *evaluated*, as real Clojure's compiler does, since `deftest`
  attaches its `:test` function as a syntax-quoted form. Without this
  `run-tests` found zero tests. Metadata that will not evaluate is kept
  raw rather than failing the `def`: core.clj attaches `:inline` fns to
  definitions made long before the machinery those forms need exists.
- **`ns` handles its library clauses** (`:require`/`:use`/`:import`/
  `:refer-clojure`) by calling the functions the real macro would.
  Delegating to core.clj's own `ns` macro was tried and reverted --
  core.clj loads its sibling files through `ns` forms at a point where
  that macro's expansion needs machinery that is not up yet.
- **Namespace aliases** (`ns_node%aliases`, `.addAlias`), `refer`
  binding the *same* Var rather than a copy of its value, `ns-map` via
  `.getMappings`, and `Var`'s `.ns`/`.sym`/`.isPublic`/`.isMacro`.
- **`case*`**, the special form `case` compiles to. Implemented as a
  scan of its `{hash [test-constant then-expr]}` table rather than a
  jump table: `case` is correct, just not faster than `cond`. It has to
  be a special form, not a function, because only the branch that
  matches may be evaluated.
- Refs and `dosync` as an Atom and "just run the body" -- there is no
  STM and nothing to coordinate with yet. This is the second placeholder
  waiting on the concurrency model (`binding`'s thread-local stack is
  the first); both should be revisited together.

**A Fortran gotcha worth its own line**: `.and.` does not short-circuit.
Writing `head == "ns" .and. .not. resolves_to_macro("ns", macro_val, env)`
called `resolves_to_macro` for *every list form in the program*, and its
`intent(out)` argument clobbered the macro being expanded. Nested `if`s,
not compound conditions, whenever an operand has a side effect.

**Known open**: `clojure.test-clojure.for` sends the evaluator into an
infinite loop, so `scripts/run-clojure-tests` runs each namespace under
a watchdog. Java array interop (`into-array`, `RT/seqToTypedArray`) is
the largest single source of remaining errors in the upstream files.


## Startup: a macro expanded at every call, not once

Startup had drifted to 46s, and the per-file split (`CLOTRAN_DEBUG_LOAD=1`
now reports read and eval time per file) put it somewhere surprising:
reading all ~11,000 lines of Clojure costs 0.2s, while
`clojure/core/protocols.clj` -- sixteen forms -- cost 16 seconds, and
`clotran_types.clj`'s ninety `derive` calls cost nine.

The cause was one line in `pre_expand`. A macro that builds its
expansion with `map` or `for` hands back **lazy seqs, not lists**, and
real core.clj's own `fn` assembles its clause list exactly that way.
`pre_expand` treated "not a `TAG_LIST`" as "not code" and returned such
forms untouched, so:

    (def g (fn* ([] (let [a 1] a))))   ; typed literally -> frozen
    (defn g []      (let [a 1] a))     ; via the fn macro -> NOT frozen

Every `defn` in core.clj kept the macro calls in its body raw, and
re-expanded them on **every single call**. A `let` inside a function
cost 21ms instead of the 0.9ms its `let*` costs -- macroexpansion, with
`destructure` and everything under it, re-run per invocation. Teaching
`pre_expand` to realize a lazy seq and walk it fixed all of it:

| | before | after |
| --- | --- | --- |
| bootstrap | 46s | 28s |
| bootstrap + `clojure.test` | 53s | 33s |
| `(let [a 1 b 2] (+ a b))` in a defn, per call | 21ms | 0.9ms |
| `clojure/core/protocols.clj` | 16.0s | 2.5s |
| `clotran_types.clj` | 9.2s | 0.9s |

It also fixed `clojure.test-clojure.for`, which had been written off as
an infinite loop in the evaluator. It was never looping -- it was
re-expanding `for`'s own machinery on every iteration. With the fix it
runs: 17 tests, 47 assertions passing. (`:when`/`:while` additionally
needed `peek`/`pop`.)

What remains is the real compile step: ~19s of core.clj's own
macroexpansion, done once per launch. Caching the frozen forms is the
next move if this needs to get faster, and it is not free -- `pr_str`
does not round-trip metadata, so a naive text cache would silently drop
`^:dynamic`.

## Arrays are real Fortran arrays

`into-array`/`aget`/`aset`/`alength` are the largest single source of
errors in the upstream test files, and the JVM answer -- an
`Object[]`, or a nest of them for more than one dimension -- is the
wrong thing to copy here twice over: it is a foreign abstraction, and
it discards the one capability this host has that the JVM does not.

A clotran array (`TAG_ARRAY`, `NativeArray.f90`) is a genuine Fortran
array. `(into-array [1.0 2.0 3.0])` produces a contiguous `real(8)`
buffer that a Fortran library can be handed **by reference, with no
copy and no marshalling** -- which is the whole point of the project.

Generic over kind and over rank, each for its own reason:

- **Kind**: the payload is `class(*), allocatable :: buf(:)`, allocated
  with an explicit type-spec (`allocate(real(8) :: buf(n))`) and read
  back through `select type`. One type covers real(8), real(4),
  integer(4), integer(8), complex(8), logical -- the same mechanism
  `native_test` already validates for scalars and structs. `"value"` is
  the escape hatch for an array of clotran values, which is what plain
  `(into-array [:a "b"])` needs.
- **Rank**: one rank-1 contiguous buffer plus a shape vector, with the
  index arithmetic done in `linear_index`. Rank is part of a Fortran
  *type declaration*, so a derived-type component cannot be declared
  "any rank" -- doing the arithmetic here is what makes every rank work
  instead of a hand-written case per rank. The order is column-major,
  Fortran's own, so the buffer is bit-identical to what a Fortran
  routine expects and `(vec a)` reads in memory order.

Lower bounds are stored per dimension. Fortran arrays may start at any
index, so there is no translation layer and no off-by-one convention:
a Clojure-facing array is simply allocated from 0 (what `aget`
promises), and an imported Fortran array can keep whatever bounds it
was declared with.

One visible difference from the JVM, and `clotran_types.clj` is where
it shows. On the JVM a multi-dimensional array is an array of arrays,
so core.clj's `aget` recurses (`(apply aget (aget a i) idxs)`). A
Fortran array is genuinely rank-N, one block, so the indices apply
together: `(aget m 1 2)` is a single indexed read rather than two.
`aget`/`aset`/`alength`/`make-array`/`into-array` are redefined there
for that reason.

Arrays are ordinary values otherwise: `seq`, `count`, `first`, `vec`
and `map` all work, `(class a)` answers `:clotran.native.real8-array`,
and every element kind is `derive`d under `:clotran.native/array` so a
multimethod or protocol can dispatch on it. `aset` mutates in place --
an array is a mutable slot shared by reference, as it is in Clojure.

Not yet: passing one of these to an actual Fortran procedure. The
storage is deliberately ready for it (contiguous, column-major, of a
declared kind), and the binding generator described under protocols is
what will emit the call.


## Source positions: where a form came from

Every list form records the line, column and file it was read from, and
where it ENDS. Errors now say `(/path/file.clj:6:3)` instead of nothing
at all, which is the first half of the debugger in PLAN.md and was
overdue on its own -- an error with no location is painful to chase,
and we spent real time on exactly that.

Three design choices worth recording:

**Positions live on the `cons_cell`, not as metadata on every value.**
Real Clojure attaches `:line`/`:column` as form metadata, which means a
map allocation per form; over ~11k lines of bootstrap that is a lot of
maps, and only list forms are ever what an error or a stack frame
points at. Three integers on the cell cost nothing to copy and survive
the value-representation change planned in PLAN.md, because cons cells
stay heap nodes either way. `(meta form)` synthesises
`{:line :column :end-line :end-column :file}` on demand, so core.clj's
own `(meta &form)` -- which `fn` uses -- still works.

**End positions, not just start.** Line-only positions give a
gdb-style debugger; start-and-end give sexp-level highlighting, which
is what makes CIDER's debugger pleasant. The reader already knows where
the closing paren is, so recording it now is free and retrofitting it
later would not be.

**Positions are carried through macro expansion.** `pre_expand` and the
macro machinery rebuild lists constantly (`make_list`), and the first
version dropped the position every time -- so every form inside a
frozen `defn` body had none, which is every form that matters.
`carry_position` copies it onto the rebuilt form. A form genuinely
built by a macro (rather than rebuilt) still has no position of its
own, and inherits the enclosing read form's, which is the location a
user can act on.

Two Fortran gotchas for the catalog:

- `character(len=:), allocatable :: files(:)` -- assigning `""` to a
  deferred-length allocatable **array** reallocates it to length zero,
  so every path stored afterwards read back blank. Fixed-length
  elements instead.
- The tokenizer has to advance its line counter *through* a string
  token, not just at whitespace: every docstring in core.clj spans
  lines, and without that every form after the first docstring reported
  the wrong line.


## Concurrency: the direction, and what already blocks it

Recorded here because the intent changed. Earlier notes said the
concurrency model would be "Rust-inspired, not a JVM-thread port";
the decision is now **Clojure's own model** -- immutable values,
explicit mutable references (atoms, refs, agents), and STM for
coordinated change. The reason is that Clojure's model is built on
persistent immutable data structures, which clotran already has, so it
fits what exists rather than fighting it. PLAN.md carries the
sequencing; this section records the constraints that are already
visible in the code.

**Ordering: the GC comes first.** Refcounting across threads means
atomic increments on every value copy, which makes the 497ns copy cost
worse and is then thrown away. STM is built directly on the value
representation (a ref holds a value; a transaction snapshots and
compare-and-swaps it), so building it before the representation
changes means building it twice. And a collector written
context-parameterized takes a second thread almost for free, where one
written single-threaded and retrofitted with safepoints is a redesign.

**What is implicitly single-threaded today.** These are module-level
globals that are really "the current thread's state", and they need to
become fields of one context type -- cheap now, a rewrite later:

- `Eval.f90`: `has_error`, `last_error_value`, `gensym_table`/
  `gensym_count`/`gensym_counter`, `here_line`/`here_col`/`here_file`,
  `macro_expand_depth`
- `LispReader.f90`: `has_error`, `last_error`, `current_file`
- `Namespace.f90`: `current` -- this is `*ns*`, which real Clojure
  makes thread-local
- `Atom.f90`: a Var's `dyn_stack`, and the `binding` frame stack --
  thread-local in real Clojure, one shared stack here

**The substrate is an open question, not a decision.** Fortran's
options are OpenMP (supported by both compilers, gives locks and
atomics, but fork-join around parallel regions rather than long-lived
workers), pthreads through `iso_c_binding` (fully general, but Fortran
runtime thread-safety is compiler-dependent -- and flang's runtime is
already measured as the dominant cost, so assuming it is reentrant
from a raw pthread is a large assumption), or coarrays (the wrong
model: images have separate memory, SPMD rather than shared). This
gets settled by a spike -- can two OpenMP threads each run an
independent clotran evaluation without corrupting flang's runtime --
not from the armchair, and not until the GC is done.

**Two things that will not come free:**

- **core.async.** The `go` macro is a CPS/state-machine transform that
  depends on `tools.analyzer`, and the impl namespaces use Java
  executors and locks. The macro layer is portable in principle, the
  runtime under it is not, and `go` is among the hairiest macros in the
  ecosystem. The blocking operations (`chan`, `>!!`, `<!!`, `thread`)
  are the attainable target; `go` is not.
- **Interop thread-safety.** Many Fortran libraries are not thread-safe
  -- module-level `save` variables, COMMON blocks, shared workspace
  arrays. BLAS is usually fine; legacy scientific code frequently is
  not. The binding generator will need a per-library thread-safety
  declaration and to serialize calls into the unsafe ones. Separately,
  a `native_array` is shared MUTABLE memory, which STM does not cover
  at all: a ref protects the reference, never the array's contents.
  That semantic gap needs a decision before agents exist.


## Metadata: the reader was the broken half

`pr-str` under `*print-meta*` already worked -- core_print.clj's own
`print-meta` does it. The real gap was that the READER never normalised
metadata shorthand, which real Clojure's LispReader does:

    ^:kw form    -> {:kw true}
    ^Type form   -> {:tag Type}
    ^"str" form  -> {:tag "str"}
    ^{...} form  -> as written

Storing the shorthand raw is not a cosmetic difference. `^:private foo`
produced the bare keyword `:private`, so every `(:private (meta v))`
and `(:dynamic (meta v))` test in core.clj was looking a key up in
something that is not a map, and `print-meta` skipped it because
`(count m)` on a keyword answers nothing. `defn-`'s own
`(assoc (meta name) :private true)` was assoc-ing onto a keyword.

Normalising it immediately woke up code that had never run: `defn`'s
`resolve-tag` (core.clj:243) inspects `(:tag m)` and, finding one for
the first time, called `clojure.lang.Compiler$HostExpr/maybeSpecialTag`
and `maybeClass`. Both are shimmed in clotran.clj to answer nil --
there are no classes here, so `defn` leaves the tag exactly as written,
which is right, since a type hint is advisory. Bootstrap failures went
9 -> 25 on the change and back to 9 with the shims.

Also fixed while here: a READER error was being tagged with the
EVALUATOR's current position, so a malformed form typed at the REPL got
reported at whatever line of core.clj happened to be evaluated last --
worse than no location at all. Reader errors now raise without one.


## Native buffers in a GC pool

Everything about the interop story depends on one property: a buffer
handed to a Fortran library must not move, and the library must write
into OUR memory rather than a copy. Before committing the value
representation to the collector, that was probed directly on both
compilers rather than assumed.

**A buffer must be a POINTER component, never allocatable.** This is
the finding that matters. A `class(*), allocatable` component of a
pool node is *copied* when the pool grows -- the collector's own
`grow_*` does an element-wise copy into a larger array, and copying a
node with an allocatable component reallocates it. Measured on flang
and gfortran alike: the address changes. That would mean an unrelated
allocation, anywhere, silently invalidating a pointer a Fortran library
is holding -- exactly what choosing a non-moving collector was meant to
prevent. With `class(*), pointer, contiguous` the node copy shares the
target and the address survives (verified across three pool growths).

**A library must be handed the whole buffer, never a slice.** Passing
a contiguous whole buffer through an old-style `a(*)` dummy -- the
shape BLAS and legacy scientific code declare -- makes no copy on
either compiler: the callee's address equals ours and its writes are
visible through the heap afterwards. A *strided slice* is copied.
Correctness survives (copy-in/copy-out), but the copy is silent, and a
library that retained the pointer would be left holding a temporary.
So the rule is a rule, not a preference.

Also verified: `c_loc` works on the buffer, for a future C-level
hand-off from the binding generator; arbitrary kinds work
(`integer(2)` as well as `real(8)`); zero-length buffers are fine; and
deallocating once through the pointer after several growths is clean,
because Fortran does not auto-deallocate pointer components, so
discarding the old pool array cannot double-free.

One consequence worth naming, because it is a hole rather than a
detail: a native buffer is a LEAF to the collector -- it holds Fortran
scalars, and there is nothing in it to trace. NativeArray's `:value`
kind currently stores `cons_value` elements, which under a tracing
collector would mean values an array still holds looking unreachable
and being swept. Those arrays belong in the value-run pool instead,
where they are traced for free; they never go to a Fortran library, so
they never needed a stable address. Native buffers then hold only
Fortran scalar kinds, which makes the leaf property an invariant.

### Gotcha: flang cannot pass an internal procedure as a callback

Found while testing the above, and it is a landmine well beyond arrays.
Passing a *module* procedure as an actual argument to a dummy procedure
works on both compilers. Passing an **internal** procedure -- one
contained in a program or subroutine, using host association --
**segfaults under flang** on macOS/ARM64 (Homebrew flang 23.1.1),
executing from a stack address, which is a trampoline that the
platform's W^X rules will not run. gfortran handles it.

    call take_callback(module_proc)     ! fine on both
    call take_callback(internal_proc)   ! flang: SIGSEGV

Consequences: any callback in clotran must be a module procedure. The
existing `rt_set_lazy_forcer` already is. The binding generator's
"hand the typed buffer to a routine" pattern is viable *because*
generated code lives in a module -- but the constraint has to be
written into the generator, not discovered later.


## Status

Steps 1-6 pass official required tests on both compilers (117/117,
12/12, 30/30, 84/84, 8/8, 31/31): read/print, eval/apply, def!/let*
with real lexical scoping, if/do/fn*, TCO, and read-string/eval/slurp/
load-file/atoms. `cons_value` gained `TAG_FN` (a closure: params/body/
captured env) in step4 and `TAG_ATOM` (`Atom.f90`, mirrors
`clojure.lang.Atom` -- one genuinely mutable slot, shared by reference
like Env) in step6. `eval_form` (`Eval.f90`) is a loop, not a plain
recursive walker: if's chosen branch, do's last form, let*'s body, and
calling a closure all rebind ast/env and loop instead of recursing, so
10000-deep (mutual) tail recursion runs in constant Fortran stack --
the point of step5.

Step7 (quoting) passes 40/45 official tests, on purpose not 45/45 --
see below. Globals moved from a flat env into real namespaces
(`Namespace.f90`, mirrors `clojure.lang.Namespace`): native builtins
live in `clojure.core`, `*ns*` starts as `user` and auto-refers
`clojure.core`, and `def!`/symbol lookup/`eval`/`load-file` all go
through `ns_resolve`/`ns_intern` now instead of the env chain -- the
lexical env (`Env.f90`) is purely for let*/fn* locals again. `in-ns` is
the new primitive this needs (real Clojure's `ns` macro, with
:require/:import, waits for step8 macros). quasiquote/unquote/
splice-unquote are real syntax-quote, not mal's simplified version:
a bare symbol gets namespace-qualified (`+` -> `clojure.core/+` from
`user`, using which namespace `ns_resolve` says actually owns it, not
just the current one), a symbol ending in `#` auto-gensyms (consistent
within one quasiquote call), and a quasiquoted vector stays a vector
(mal's own reference impls produce a list here -- a known, TODO-marked
gap in mal's own test suite this project doesn't inherit). This is why
step7 is 40/45 and not 45/45: the 4 failures are mal's test file
asserting the OLD unqualified-symbol behavior (e.g. `` `a `` => `a`),
which is exactly the divergence intended -- not a bug. `concat` is a
new builtin; the 5th failure is `str`, still deferred from step4.

Step8 (macros) passes 13/14 official tests. `defmacro` uses real
Clojure's own syntax (`(defmacro name [params] body)`, not mal's
`(defmacro! name (fn* (params) body))`) -- a macro is `TAG_MACRO`, the
same `fn_val` closure shape as `TAG_FN`, just dispatched differently:
unevaluated argument forms in, its result evaluated again (tail, so a
recursive macro gets TCO -- `cond` recurses through arbitrarily many
clauses without overflowing). Macro-ness is checked via `*ns*` only,
never the lexical env, matching real Clojure (macros are Var metadata,
never lexically bound). `defmacro!` is *also* recognized -- purely a
mal-test-suite compatibility shim (evaluates its second argument,
typically `(fn* ...)`, and re-tags the result `TAG_MACRO`), not
meaningful Clojure; kept alongside real `defmacro`, not instead of it.
`cond`/`not` are the first bootstrapped-in-this-language core pieces
(`eval_core_bootstrap` in `Eval.f90`, evaluated into `clojure.core` at
startup) -- written using defmacro/quasiquote/if/first/rest/empty?,
not native Fortran, exactly like real clojure.core's own `cond`. The
one remaining failure is `macroexpand`: real Clojure's is an ordinary
function (its argument evaluated normally, so callers quote the form
themselves, `(macroexpand '(unless2 1 2 3))`), not a special form like
mal's (`(macroexpand (unless2 1 2 3))`, no quote) -- built the real way
on purpose, per the standing "we mirror Clojure directly" rule that
already governs everything else, not something to alias like
`defmacro!`.

Also fixed as part of this: explicitly namespace-qualified symbols
(`ns/sym`) now resolve directly in that one namespace (`ns_resolve` in
`Namespace.f90`), no auto-refer fallback -- needed for `cond`'s own
self-reference (quasiquote qualifies it to `clojure.core/cond`) to
actually run when the macro is invoked from any namespace, not just
the one it's defined in. `/` itself (the division symbol) is the one
exception, never split.

**Fixed: `(rest (list))` segfaulted** (`rest` of an empty list). Found
by step8's own deferrable tests; confirmed to predate step7/8 entirely
(reproduced unmodified against the step6 commit), just never exercised
until then. Root cause: non-short-circuit `.and.` in
`PersistentList.rest` dereferencing a null pointer -- see the gotchas
catalog above.

Step9 (try/catch) passes 29/29 official required tests, no
divergence needed at all this time. `try`/`catch` are real Clojure's
own names (`try*`/`catch*` also recognized, same as `def!`/`def`) --
only one catch clause, catching anything (no exception-class matching:
we have no class hierarchy to match against). The error state
(`has_error`/`last_error_value`) now holds a real `cons_value`, not
just a string -- `(throw x)` can throw *any* value (a hash-map, a
list, ...), and internal errors (symbol not found, etc.) wrap their
message as a `TAG_STRING` so they're caught exactly like a real
`throw` would be seen. `throw` is an ordinary builtin (not a special
form): its argument is evaluated normally, which is exactly what
makes it usable as a first-class function (`(map throw (list "err"))`
-- a real mal/Clojure test case, and it works). This finally fixed the
`nth` out-of-bounds gap flagged earlier: `nth` now calls `eval_error`
on an out-of-range index, which is catchable the same way any other
error is. Also added: `apply`, `map` (eager, same as the rest of this
project's seq handling), and `symbol?`/`nil?`/`true?`/`false?`.

Step9's own (not-required) test file now passes in full too, 129/129:
hash-map ops (`hash-map`, `contains?`, `keys`, `vals`, `dissoc`),
`symbol`/`keyword` constructors, `sequential?`/`vector?`/`map?`, and
`str`/`pr-str`/`println` (finally using the "non-readable" printer
mode deferred back at step4 -- `pr_str` grew an optional `readable`
argument, threaded through `pr_seq`/`pr_hashmap`, defaulting to
readable so every existing call site is unaffected; only `TAG_STRING`
differs between the two modes).

Running that full suite exposed two real bugs, both fixed: `assoc`
was not variadic (`case ("assoc")` only applied the first key/value
pair, silently dropping the rest -- now `builtin_assoc` loops over
every pair); and `RT.equiv` had no `TAG_HASHMAP` case at all, so any
two maps compared unequal, even `(= {} {})` -- now compares count
first, then every key of `a` via `array_map_contains`/`array_map_get`
against `b`, recursively `equiv`-ing values (order-independent, as
map equality should be).

StepA passes 3/3 official required tests: `readline` (writes a
prompt, reads one line, `nil` at end of input) and `*host-language*`
(bound to `"Fortran"`). Fixed as part of this: the REPL driver
(`step2_eval.f90`, shared by steps 2-9) used to loop forever
re-prompting after stdin closed, eventually crashing -- it never
checked for real end-of-file, only end-of-record (a normal line
terminator), and both give a negative `iostat` from a non-advancing
read. `mal_readline.readline` (`readline.f90`) now returns an explicit
`at_eof` distinguishing the two (checking for `iostat_end`
specifically), and every driver (`step0_repl`, `step1_read_print`,
`step2_eval`, and so everything built on it) stops cleanly on real
EOF instead of recursing forever. This is also exactly what lets the
mal-level `readline` builtin return `nil` at end of input rather than
looping or erroring.

**Self-hosting: mal's own mal-in-mal reference interpreter now boots
and runs correctly on top of this implementation** -- validated in
the original mal-based bootstrap repo. That reference interpreter's
own source (`mal/stepA_mal.mal`, `env.mal`, `core.mal`) wasn't
carried over the migration to this repo -- it was a one-time
validation exercise, not something this project runs routinely -- but
the official per-step *test* files (`test/regression/step2_eval.mal` through
`stepA_mal.mal`, plus the small fixtures they load) were, since they
remain genuinely useful regression coverage; see "Testing" below for
how they're run. Arithmetic, closures, map/apply, defmacro and
macroexpand all worked through the extra interpretation layer. Getting
there needed seven more builtins mal-in-mal's own `env.mal`/`core.mal`
require that weren't needed for anything up to here: `number?`,
`string?`, `fn?`, `macro?`, `seq`, `time-ms`, and `with-meta`/`meta`
(real metadata -- attaches to any value, doesn't affect equality,
`with-meta` returns a new value sharing the original's structure
without mutating it, exactly like real Clojure's IObj/IMeta). Chasing
these down (and then actually running the self-hosted REPL) also
exposed and fixed three real bugs the required test suites hadn't
reached: `conj` wasn't variadic (same shape as the earlier `assoc`
bug -- now `builtin_conj` loops left to right, matching real
Clojure's `(conj coll x y z)` = `(conj (conj (conj coll x) y) z)`);
`seq` had no `TAG_STRING` case (`(seq "abc")` now gives `("a" "b"
"c")`, one-character strings, same as real Clojure); and `load-file`
joined a slurped file's contents with `" nil)"` (a space) rather than
a newline before the closing paren, so a file ending in a `;;`
comment with no trailing newline of its own silently swallowed
`nil)` into that comment, breaking the read -- real mal's own
`load-file` uses `"\n" // "nil)"` for exactly this reason, now
matched. Fixing this also took step6 from 46/60 to a clean 60/60 and
stepA's own test file from 30/108 to 108/108.

Building `with-meta`/`meta` also surfaced a genuine gfortran
compiler limitation, caught by a gfortran-only segfault (a null
function-pointer call inside gfortran's own generated finalization
code) that flang never hit: a derived type cannot hold an allocatable
component of *its own type* directly once a FINAL procedure is
involved -- confirmed with a 40-line isolated repro outside this
codebase entirely (gfortran crashes, flang runs correctly). The fix
wasn't a gfortran-only contortion, though -- it's the same pattern
this codebase already uses for every other recursive/shared structure
(`cons_ref`, `atom_ref`, ...): a small pointer-based refcounted box
(`meta_ref`/`meta_node`, mirroring `atom_ref`/`atom_node` exactly)
instead of embedding the value directly. Correct and clearer on both
compilers, not a workaround.

Self-hosting has a real depth ceiling, confirmed (not just assumed)
via lldb: a self-hosted, non-tail-recursive loop of a few hundred
levels segfaults with `EXC_BAD_ACCESS` writing near the stack
pointer, inside the Fortran runtime -- a genuine stack overflow, not
a bug. Each "step" of the self-hosted interpreter costs several real
host stack frames (EVAL -> eval-ast/cond -> apply -> the mal closure
body -> EVAL again), so depth that's fine natively (thousands, tail
calls aside) tops out in the low hundreds once doubled through
self-hosting. This is an expected, known characteristic of naive
(non-trampolined) self-hosting in any host language, not something
to engineer around here -- mal is a stepping stone, not the
destination.

**try/catch is not a general safety net the way it is on the JVM.**
It's the same `has_error`/`last_error_value` cooperative convention
every routine already checks (`if (has_error) return`) -- `try`/
`catch` just stops that propagation and binds the value instead of
letting it keep going. It can only catch what we've explicitly routed
through `eval_error`/`throw_value` (unbound symbol, `nth` out of
range, an explicit `(throw x)`). A genuine Fortran fault we haven't
instrumented (an unchecked out-of-bounds access, a null-pointer deref)
bypasses this convention entirely and kills the whole process -- no
Lisp-level `try` can intercept that, since the crash happens below
where our checking convention runs at all. That's exactly what the
`(rest (list))` bug earlier was: an uninstrumented native fault, fixed
at the Fortran root cause, not something try/catch could have masked.
Real Clojure gets "catches nearly anything" for free from the JVM
(`NullPointerException`, `ArithmeticException`, ...); we don't get
that for free -- every risky native operation (an index, a division,
a type assumption) needs its own explicit check calling `eval_error`
*before* raw Fortran runs into undefined behavior, an ongoing
discipline as more builtins get added, not a one-time cost.

**Idea for later: a real Fortran crash net, via a little C.** A small
C shim (`signal`/`sigaction` trapping `SIGSEGV`/`SIGFPE`/`SIGBUS`,
`sigsetjmp`/`siglongjmp` to unwind), called from Fortran through
`ISO_C_BINDING`, is a real and established pattern (SBCL and other
production Lisps do exactly this on POSIX). Would be a genuine
upgrade if built right. The catch: `longjmp` skips every Fortran
`FINAL` between the fault and the jump target, so none of our
refcounting runs for whatever was in flight -- best case those
objects just leak, worst case (a fault landing mid-mutation of one of
our own refcounts, which a hardware fault can do at any instruction)
a genuinely dangling pointer, not just a leak. That rules out using
this to make Lisp-level `(try ...)` safely resume after an arbitrary
native fault. What *would* be safe and worth building: a coarser net
at the outermost REPL loop only -- catch the fault there, print an
error, discard everything from that computation, and return to the
next prompt instead of the whole session dying, same spirit as a
crashed request not taking down a whole server process. Deliberately
not built yet (skipped for now, revisit if crashes during interactive
use become a recurring problem) -- but a real, concrete plan, not a
dead end.

**Idea for later: a real built-in debugger, SBCL-style, instead of
gdb.** gdb thinks in registers and raw memory; a Lisp debugger thinks
in the program's own terms -- exactly the gap James wants closed here.
Full SBCL parity (non-unwinding conditions, resuming a computation
mid-flight with a substituted value, `restart-case`) needs a
genuinely different, more sophisticated error model than what we
have: our `has_error`/`last_error_value` is unwind-based (closer to
Java's throw/catch), while Common Lisp conditions can be handled
*without* unwinding at all -- that's the real redesign, not an add-on.

But a meaningfully-scoped version is buildable now, with what already
exists: capture the `env_ref` active when an error goes uncaught (we
already thread `env` everywhere `eval_error`/`throw_value` fire; just
also stash it alongside `last_error_value`), and instead of printing
"Error: ..." and returning to the top-level prompt, drop into a
*nested* REPL running in that captured env -- inspecting and
evaluating expressions with the exact local bindings live at the
point of failure, until the user explicitly resumes. That's most of
the real value (thinking in the program's own terms) without needing
non-unwinding conditions at all. Multi-frame navigation (`up`/`down`
between call frames, like a real stack-frame debugger) is a step
beyond that -- Fortran's own call stack isn't introspectable from
inside the language, so it would need an explicit frame stack we
maintain ourselves (push/pop in `eval_form`), which is real work but
concretely buildable, not exotic. Different failure class than the
crash-net idea above (this is for graceful Lisp-level errors --
unbound symbol, wrong type -- the crash-net is for hardware faults);
complementary, not overlapping.

Not just a nice future user-facing feature -- gdb is a genuinely bad
fit for debugging *this exact codebase*, not merely suboptimal in
general. Its Fortran support has always lagged, and this project sits
right in its weak spots: `cons_value` is a tagged union with 7+
allocatable components where only one is ever meaningful at a time --
exactly the shape gdb prints worst (raw descriptor bytes for whatever
isn't allocated, when it doesn't refuse outright); our whole
refcounting/`FINAL` model is invisible to it (no concept of "this
fired because a refcount hit zero" -- exactly the class of bug this
project has actually hit); and flang/gfortran mangle module-procedure
names *differently*, so there's no stable, compiler-independent
symbol to even set a breakpoint on. Debugging the `(rest (list))`
crash even with lldb (gdb wasn't installed) only produced a raw
machine backtrace with flang-mangled frame names -- enough to find
it, but nothing semantic; a debugger that understood `cons_value`'s
tag could have said "this is `TAG_LIST`, empty" directly instead of a
hex dump. A real Lisp-aware debugger would be better tooling for
continuing to build this project itself, not just a feature for
eventual users.

Two different things worth distinguishing here, since they need very
different amounts of work. Lisp-level values (`cons_value`) need no
new Fortran-debugger work at all -- `pr_str` already knows how to
print them well; a home-grown Lisp debugger (above) just needs our
own REPL, not gdb. Our *backing* structures (`cons_cell`, `vec_node`,
`env_node`, `atom_node`, `ns_node`, `array_map_node` -- the raw
refcounted derived types) are the actually-invisible-to-gdb part
(raw hex for a pointer, garbage for an unallocated component), and
here there's a much cheaper path than writing a debugger from
scratch: both gdb and lldb support user-defined pretty-printers
(gdb's Python `gdb.printing`, lldb's Python scripting API) -- exactly
how C++'s STL containers or numpy arrays get readable printing
instead of raw struct dumps. A printer script for this project's own
small, closed set of types (show a `cons_cell` as `refcount=2,
car=<value>, cdr=<...>` instead of two raw pointers) would give real
introspection for the objects that actually matter here, riding on
gdb/lldb's existing (working) breakpoint/stepping machinery rather
than reimplementing it. What this is *not*: a general "better than
gdb for any Fortran program" tool -- matching gdb's DWARF parsing for
arbitrary derived types across compilers is a much bigger, different
undertaking and not the goal. Scoped to this project's own types,
though, it's real and achievable. Not started -- recorded because
these are real, worthwhile directions, not because either is
imminent.

**How this rhymes with the ChemSol adapter-generator idea (above) --
and why it's probably not the same tool.** Both ultimately need "read
a Fortran declaration well enough to automate something with it," but
the delivery differs enough that solving one doesn't hand us the
other for free. The debugger printer gets type-layout reflection for
free from gdb/lldb's own Python API (already reading DWARF for us --
we'd just format what it hands us). The adapter generator runs
standalone at build time against a target library's own source (or
module files), not inside a live debugger session, so it needs its
own (narrowly scoped -- just interface declarations, not the whole
language) parser or a lean on the compiler's module-file output.
Worth remembering they rhyme; not worth trying to design one unified
tool for both now.

Deliberately simplified vs. real syntax-quote: no nesting-depth
tracking, so a syntax-quote inside a syntax-quote doesn't get its own
gensym/unquote scope the way real Clojure's does -- rare in practice
(mostly matters for macros that write macros), revisit if something
needs it.

Next: step8 (macros, likely including a real `ns` macro over `in-ns`),
step9 try/catch, stepA mal-in-mal. ChemSol interop resumes once mal
passes in full (see the ChemSol section above for what's already
confirmed to work).

---

## The 3c-1 accessor migration

History, moved out of PLAN.md when it stopped being plan. The route it
belonged to -- retrofitting `cons_value` in place -- was superseded:
`clotran-gc` was built fresh on `gc_value` instead, and 3c-2/3d/3e now
apply only to `clotran-bin`, which is on its way out.

Kept because what each payload taught is still true, and the same
questions come back every time a hot path is touched: what an accessor
returning by value costs in refcount traffic, when a temporary is worth
it, and which shapes get SHORTER when you stop reaching through
`%ptr%` chains.

  - [x] **3c-1 `array_val`** (23 sites). Every real use was a
        `%array_val%ptr%...` chain -- the hardest shape, and it got
        *shorter*: `nd => array_node(v)` once per routine, then plain
        `nd%extents`. `array_is` collapsed to
        `associated(array_node(v))`, one test instead of the
        allocated-then-associated pair each site repeated. The only
        `%array_val` left in the tree is inside the accessors and
        inside the refcounting that 3e deletes, which is the end state
        every component is aiming at.
  - [x] **3c-1 `meta_val`** (35 sites). `meta_node` holds one
        `cons_value`, so the accessors are value-level:
        `has_meta`/`get_meta`/`set_meta`. Both five-line
        allocate-and-refcount blocks (`with-meta`, the reader's `^`)
        became one call, and `eval_def`'s doubly-nested
        allocated/associated guard flattened by two levels.

        `has_meta` is deliberately separate from "get_meta returned
        nil": `(with-meta x nil)` attaches nil, which is not the same
        as carrying no metadata, and `eval_def` branches on the
        difference. Collapsing them would have been a silent semantic
        change -- the kind this whole split exists to avoid.

        Metadata is where the unit tests are weakest relative to the
        risk (`:arglists`, `^:dynamic`, `deftest`'s `:test`), so this
        one was also checked against the upstream suite on the
        pre-change tree: 163/16/41, identical per namespace.
  - [x] **3c-1 `lazy_val`** (36 sites). `lazy_ptr` plus
        `new_lazy_node`. Every read site repeated the same three-level
        `allocated`/`associated`/`state` nest; each lost a level, and
        both constructors went from six lines of allocate-and-refcount
        to three.

        `lazy_ptr`, not `lazy_node`: the type is already called
        `lazy_node` and Fortran is case-insensitive, so a function of
        that name would be the same name -- the `GCT_`/`gc_cons` trap
        again.
  - [x] **3c-1 `atom_val`** (50 sites, 40 of them in `Atom.f90`).
        `atom_ptr` + `new_atom_node` + `share_atom`. Every routine in
        `Atom.f90` opened with the same `allocated`/`associated` pair;
        all of them now start `nd => atom_ptr(a)`, and the file no
        longer names the component at all.

        `atom_ptr` deliberately does **not** check the tag, unlike
        `array_node` and `lazy_ptr`. Five tags share this box --
        `TAG_ATOM`, `TAG_VAR`, `TAG_MULTIFN`, `TAG_REDUCED`,
        `TAG_STRING_BUILDER` -- because "one genuinely mutable slot,
        shared by reference" is the same storage for all of them and
        only the behaviour differs.

        `share_atom` exists because one call site must *share* the box
        rather than copy it, and the comment there recorded a real
        hazard worth keeping: the component has to exist before
        `assignment(=)` runs on it, since `atom_ref_assign` releases
        the old target first and releasing an unallocated component
        reads uninitialized memory.
  - [x] **3c-1 `vector_val`** (59 sites). The first payload that could
        *not* follow the pattern: the accessors live in
        **PersistentVector.f90**, not Values.f90, because reaching an
        element means walking the trie and Values cannot use that
        module -- the dependency runs one way only. So for vectors "the
        one place that knows the representation" is that file plus the
        type declaration in Values. Fine, and arguably the right home;
        worth knowing before 3c-2 assumes one file.

        `has_vector`, `val_vec_count`, `val_vec_nth`, `set_vector`,
        `val_vec_conj`, `val_vec_assoc`. Each absorbs the `allocated()`
        guard its callers repeated, so the common shape

        ```fortran
        if (allocated(v%vector_val)) then
           if (vector_count(v%vector_val) > 0) val = vector_nth(v%vector_val, 0)
        end if
        ```

        is now one line. `conj` and `assoc` lost their
        allocated/else/empty branches entirely -- an absent vector
        conjes onto the empty one, which is what `(conj nil x)` means.

        Residue: three `vector_to_list(...)` calls in RT.f90. That
        function is RT-private and walks `%root`/`%shift` directly;
        moving it into PersistentVector would need PersistentList,
        which PersistentVector does not use. Left deliberately, and
        small enough for 3c-2 to edit in place.
  - [x] **3c-1 `str_val`** (375 sites). Three read accessors, not one,
        because one would be slow: the commonest read is a comparison
        against a literal in `eval_form`'s dispatch, and routing those
        through a function returning `character(len=:), allocatable`
        would allocate and copy a string on the hottest path in the
        interpreter. So `str_is` compares in place, `str_len` measures,
        and `val_str` (a copy) is only for callers that genuinely need
        the text, where a copy was happening anyway. Plus `has_str`,
        `str_sub`, `set_str`.

        The real prize is not the refactor. Every text accessor treats
        an unallocated payload as empty instead of reading it, which
        makes 4a' bug 2 -- a non-short-circuiting `.and.` handing an
        unallocated `str_val` to a procedure -- **unrepresentable**
        rather than merely fixed.

        Two Fortran facts worth keeping: neither compiler accepts a
        substring of a function result (`val_str(v)(1:1)`), hence
        `str_sub`; and an internal `READ` needs a character *variable*,
        not an expression, so one call site keeps a local. Also
        `printer.f90`'s two helpers took `character(len=:),
        allocatable` purely to cope with an unallocated payload; they
        are plain `len=*` now.
  - [x] **3c-1 `list_val`** (158 sites). `has_list`, `val_lst`,
        `val_lst_first`, `val_lst_rest`, `val_lst_count`, `set_list` in
        PersistentList.f90 (the one-way dependency again), plus
        `list_cell` in Values.f90 for the reader's source positions --
        that one can live in Values because a `cons_cell` is declared
        there and no list walking is involved.

        **This migration changed 4a'' from intermittent to
        deterministic**, which is the most useful thing to come out of
        it. See 4a'' below.
  - [x] **3c-1 `map_val`** (108 sites). `has_map`, `val_map`,
        `set_map`, `val_map_count`, `val_map_get`, `val_map_contains`,
        `val_map_entries` in PersistentArrayMap.f90. The most regular
        of the six: `allocate`+assign pairs collapse to `set_map`, and
        `conj`/`assoc` lose their empty-map branches the way the
        vector ones did.
  - [x] **3c-1 `fn_val`** (74 sites, ~48 migrated). `has_fn`,
        `new_fn`, `fn_is_macro`, `set_fn_macro`, `fn_params`,
        `fn_body`, `set_fn_params`, `set_fn_body` -- field at a time,
        in Values.f90.

        Field accessors rather than a pointer to the `closure_t`
        because `fn_val` is ALLOCATABLE, not a pointer: returning a
        pointer would mean giving the dummy `TARGET` and relying on
        every actual argument being a target too. They are not, and a
        pointer to a non-target actual is undefined on return -- which
        is exactly the bug class 4a'' is about. Not while hunting it.

        **`%env` and the arity clauses (`%extra`) deliberately still
        name the component.** `env_new(f%fn_val%env)` is in
        `apply_closure`, the hottest path in the interpreter, and an
        accessor returning `env_ref` by value would add a refcount bump
        and a finalize per function call. `list_val` had just
        demonstrated what extra temporaries do to 4a''; paying that on
        every call for tidiness is not a trade worth making. 26 sites,
        all in Eval.f90, for 3c-2 to edit directly.

        **3c-1 is done.** What 3c-2 now has to touch: Values.f90,
        PersistentVector.f90, PersistentList.f90,
        PersistentArrayMap.f90, and ~29 residue sites in RT.f90 and
        Eval.f90 -- against 959 before.


---

## The GC: design and construction

Moved out of PLAN.md, which is for work not yet done. This is why the GC
and the data layer are the way they are, plus the `clotran-bin`
refcounting investigations (4a', 4a'') that die with that evaluator.

The investigations are kept for their method as much as their findings.
One of them corrects itself in place -- an earlier note claimed two
sampled runs had fixed a bug "permanently", and was wrong. Two samples
are not evidence of absence for a 1-in-6 bug.


**Read this before the sub-steps.** 3a and 3b happened. 3c-1 happened
(its log is in NOTES.md). **3c-2, 3d and 3e are SUPERSEDED and should not
be started.** They are a plan to retrofit `cons_value` in the ORIGINAL
evaluator; what actually happened is that `clotran-gc` was built fresh on
`gc_value`, which is that plan's endpoint reached by a different road.
The remaining sub-steps now apply only to `clotran-bin`, and retiring it
(Start here, item 6) deletes them outright. They are left in place only
because 4a'' below cites them.

- [x] **3a/3b.** `src/f/GC.f90` + `test/f/gc_test.f90`: typed pools
      with free lists, a value type with no allocatable components and
      no `FINAL`, non-moving mark-sweep with an explicit mark stack
      (not recursion -- a long list is a chain thousands deep), pool
      growth, torture mode, 24 checks. Nothing in clotran uses it yet.

      Two results worth keeping: a **cycle is collected** (6a/6b),
      which is what refcounting structurally cannot do and is why
      clotran leaks closures today; and building the test surfaced a
      real hole in the allocator's own API -- a freshly built value
      passed as an ARGUMENT is live but cannot have been listed as a
      root by the caller, since nothing references it yet, so
      allocation has to root its own arguments. `(cons (str ...) ...)`
      freed the string otherwise, and only under torture or at an
      unlucky heap size. Check 10a covers it and was confirmed to fail
      without the fix.
- [x] **3a'.** Generalised to hold clotran's data: 38 checks. clotran
      has ~15 node kinds (cons cells, trie nodes, array maps, HAMT
      nodes, closures, atoms, lazy seqs, metadata boxes, arity clauses,
      environments, namespaces), and one pool per kind would be fifteen
      near-identical allocators, free lists, mark arrays and trace
      routines. Underneath they are two shapes: a FIXED few value slots
      plus small integers (cons, closure, lazy, env, map, vector), or a
      VARIABLE-length run of values (trie children, map keys/vals,
      arity clauses, a Var's binding stack). So three pools -- object,
      value-run, text -- and an object's own `kind` says which it
      means. Adding a clotran type is a new `OBJ_` constant, not a new
      pool.

      `gc_check_heap` walks the whole heap asserting no live object
      references a freed or out-of-range slot; check 14a runs it under
      torture. That is the payoff of handles over pointers -- the heap
      audits itself, and corruption is caught where it happens rather
      than when a wild pointer is next dereferenced.

- [x] **3a''.** Native array buffers: INVESTIGATED, design settled.
      See "Native buffers in a GC pool" in NOTES.md for the probes.
      The rules the port must follow:

      1. A buffer is a `class(*), pointer, contiguous` component,
         **never `allocatable`**. Measured on both compilers: an
         allocatable component is *copied* when the pool grows, so the
         buffer's address changes -- which would defeat the entire
         point of a non-moving collector. A pointer component shares
         its target and the address survives.
      2. Hand a library the **whole buffer, never a slice**. A
         contiguous whole buffer is passed by reference with no copy
         (verified through an old-style `a(*)` dummy, the shape BLAS
         uses). A strided slice is silently copied -- correct by
         copy-in/copy-out, but a library that retained the pointer
         would hold a dangling temporary.
      3. A native node holds **only** pointer and small components. Any
         allocatable component is reallocated on pool growth, which is
         harmless for metadata but must never be where the buffer is.
      4. The wrapper roots the array for the duration of a call, so a
         collection mid-call cannot sweep the buffer out from under a
         library that is still writing to it.
      5. **Generated bindings must be module procedures.** flang
         segfaults passing an internal, host-associated procedure as a
         callback on macOS/ARM64 -- see the gotcha in NOTES.md.
      6. **A native buffer holds only Fortran scalar kinds, never
         clotran values.** The collector cannot see inside a native
         buffer -- it is a leaf, holding real(8)s and integer(2)s, not
         anything traceable. NativeArray's current `:value` kind stores
         cons_value elements, which under the GC would be a hole:
         values the array still holds would look unreachable and be
         swept. `:value` arrays move to the **vec pool** (a run of
         gc_value), which is traced for free and loses nothing, since
         a `:value` array is clotran data that never goes to a Fortran
         library and so does not need a stable address. That makes
         "a native buffer is a leaf" an invariant rather than a thing
         to remember.

      Note what is NOT changing: clotran references stay integer
      handles into pools, and the collector follows those. The Fortran
      `pointer` appears in exactly one place -- the buffer of a native
      array -- purely so its address is stable for foreign code.

      Confirmed on both compilers end to end: buffer survives three
      pool growths, a library sees our memory rather than a copy, its
      writes are visible through the heap, and `c_loc` works for a
      future C-level hand-off. Arbitrary kinds (`integer(2)` tested)
      and zero-length buffers are fine.

- [x] **3a'''.** Namespaces. Not a pool: tracing walks every slot
      regardless of kind, so `OBJ_NS` (name, bindings, aliases) and
      `OBJ_VAR` (root, meta, dynamic stack, name) are two constants and
      no new code. What namespaces genuinely needed is what they are
      the first case of -- a **global root**.

      Every other root so far is a root because a caller passed it. The
      namespace registry is a root because of where it lives: shared by
      every thread, so there is no context to thread it through, and
      alive until exit. So `gc_global_new/set/get` -- a slot, not a
      handle handed over once, since the registry's own handle changes
      each time it grows. The collector scans globals alongside the
      argument roots, and the split survives threading: global means
      shared by all threads, argument means owned by one.

      Checks 15a-15i, both compilers, the last two under torture with
      *nothing* on the stack -- 50 Vars kept alive across 50
      collections by registry -> namespace -> bindings alone. Verified
      to fail: with global scanning removed, 7 of the 9 fail.

      15d is the one that matters for semantics: `(def x 42)` after
      `(def x 41)` mutates slot 1 of the same `OBJ_VAR` and the handle
      is unchanged, which is what makes a closure built before a later
      `def` see the new value.
- [ ] **3c.** Value type: drop the nine allocatable components and
      `FINAL`; keep the inline scalars (`tag`, `int_val`, `real_val`,
      `bool_val`) so `v%tag` and friends keep working, and replace only
      the allocatable components with one handle.

      **It does not have to be one bang.** 959 sites name a component
      directly, but a census showed almost all of them pass the bare
      component to a module function; only ~48 reach through `%ptr%`.
      So split it:

      - **3c-1.** Add a payload accessor per component in Values.f90
        and migrate the call sites to it. Behaviour-preserving, the
        representation *unchanged*, so the full sweep stays green after
        every component. One commit each, smallest first.
      - **3c-2.** Swap the representation underneath the accessors.
        One file, and the only genuinely big-bang part left.

        3c-1 is worth doing whichever way the compiler question lands,
        so it does not need that decision first -- it makes the
        decision later and cheaper.

  - [x] **3c-1 is done** -- all ten payload accessors migrated, 959 call
        sites down to ~29 residue. The per-component log, which is the
        interesting part (what each payload taught us about temporaries,
        refcount traffic and the hot path), is in NOTES.md under
        "The 3c-1 accessor migration". It is history, not plan.


- [x] **3c-2, first slice: `str_val` is in the heap.** Two pieces of
      scaffolding made a single payload movable on its own:
      `gc_no_collect` (grow-only, because nothing roots anything until
      3d, so a collection would sweep live data -- check 16) and
      `gc_ensure_init` (so nine drivers need no `gc_init` call
      meanwhile). `str_val` became a bare handle into the string pool;
      the ref-level API keeps the is/len/text split so comparing a
      symbol to a literal still does not allocate.

      Not a win yet and expected not to be: gfortran 4.5s -> 5.3s,
      flang 30s -> 33s, RSS 93 -> 145 MB. The cost is `FINAL` plus the
      other eight components. Both compilers stay at 163/16/41.

- [ ] **3c-2, the rest -- and it is the same change as 3d.** A GC
      object's slots are `gc_value`. A `cons_value` cannot go in one
      while `cons_value` still has allocatable components, so a payload
      moves alone only if its backing node holds no clotran values.
      Checked, not assumed:

      | backing node | cons_value components |
      | --- | --- |
      | `cons_cell` | 1 (`car`) |
      | `vec_node` | 1 (`items`) |
      | `array_map_node` | 2 (`keys`, `vals`) |
      | `hamt_node` | via `hamt_slot`: key, val, buckets |
      | `closure_t` | 2 (`params`, `body`) |
      | `atom_node` | 4 |
      | `lazy_node` | 3 (`thunk`, `head`, `tail`) |
      | `meta_node` | 1 |
      | `native_array_node` | 0 -- except the `:value` kind |

      Text was migratable *because it is a leaf*: bytes, nothing
      traceable. The other eight are coupled to each other and to the
      value type, and the moment `cons_value` becomes a handle
      everything must be rooted or the first collection sweeps live
      data. So the remainder of 3c-2 and 3d are **one change**, which
      is the big bang this plan always said it was. `native_array` is
      the near-miss: a leaf apart from `:value` arrays, which 3a''
      rule 6 already moves to the vec pool.

- [ ] **3d.** Evaluator on the value stack.

- [x] **3d, groundwork: the value stack exists and is tested.** Built
      standalone against the collector, the same way the collector
      itself was built before anything used it. `vs_enter(n)` reserves
      a frame and returns its base, `vs_set`/`vs_get` address slots,
      `vs_leave(base)` pops; `gc_collect` scans every live slot
      alongside the globals.

      It lives in GC.f90, not beside the evaluator, because the
      collector must scan it and nothing else may -- which is what
      makes rooting by CONSTRUCTION rather than discipline: there is
      nowhere else to put a value.

      `vs_leave` clears on the way out, and that is not tidiness. A
      stale value left above the stack top is still traced and keeps
      dead data alive -- the characteristic leak of a stack collector.
      Check 17d is what pins it.

      Checks 17a-17j, both compilers: a frame's slots survive
      collection with no argument roots at all; leaving a frame makes
      its values collectable; the stack grows past its initial size
      without losing a slot; and 300 values rooted ONLY by the stack
      survive torture mode with the heap still passing its own audit.
      Verified non-vacuous -- with stack scanning removed, 5 of the 10
      fail.

- [x] **The data layer, built beside the old one.** Since the remaining
      payloads cannot move one at a time, the safe decomposition is not
      slicing the change but the pattern that has now worked three
      times here: build the new thing standalone, test it, wire it in
      last. `GC.f90` was built that way, so was the value stack, and so
      is this.

      **`src/f/GCVector.f90`** -- the same 32-way trie as
      `PersistentVector.f90`, with every reference a GC handle instead
      of a refcounted pointer. `gcv_empty/count/nth/conj/assoc`, path
      copying unchanged, sharing untouched children exactly as before.
      Nothing uses it yet.

      The vector went first on purpose: it is the most intricate
      structure in the layer, and it is where 4a'' lives. Check 6a is
      the point of the whole exercise -- a vector built with a
      collection at EVERY allocation, heap audit clean, every element
      intact. A premature free is not expressible under tracing:
      nothing decrements, so nothing can decrement too often, and a
      node is either reachable or it is not.

      Checks 1-6 (18 in all), both compilers: growth past one trie
      level (the push-down a 32-way trie gets wrong if mis-shifted),
      assoc leaving the original untouched, shared structure surviving
      collection, a vector rooted ONLY through the value stack
      surviving and then being collected when the frame is left, and
      the torture case above.

      **`src/f/GCList.f90`** -- the persistent list, same treatment.
      Count cached on the cell (i1) exactly as `cons_cell` does, so
      `count` stays O(1); the evaluator calls it constantly on argument
      lists. The empty list is a **singleton** registered as a GC
      global root, matching `PersistentList.EMPTY`: `()` must be
      identical to `()` everywhere, and `()` is a list rather than nil.

      Its test found a real bug in that singleton, which is the reason
      to write these checks rather than assume. `gc_init` clears the
      global-root registry, but the module's cached slot index survives
      it -- so after a re-init the "singleton" silently handed back nil
      and every `()` became a fresh object. `gcl_empty` now re-checks
      the slot instead of trusting the index (check 4c).

      Checks 1-5 (17 in all), both compilers: a 2000-cell chain rooted
      only through the value stack (which is also what proves the
      collector's explicit mark stack does not recurse into the real
      one), two lists sharing one tail object across a collection, and
      the torture case.

      **Open, and deliberately not invented at this stage: source
      positions.** `cons_cell` carries `count` plus five position
      integers; a GC object has `i1` and `i2`. Count took `i1`. The
      five remaining have to go somewhere before the switch, and the
      choice matters -- slots 3/4 of the cons object would mean an
      allocation per form, which is the exact cost the current design
      avoided on purpose (see `cons_cell`'s own comment). Packing them,
      widening `obj_node`, or accepting the allocation are all live;
      settle it before porting the reader.

      **`src/f/GCMap.f90`** -- the array map, and `gc_equal` in the
      collector to go with it, mirroring `value_equal` so the two
      representations agree during the migration: same tag and same
      scalar or text content, collections by identity. Deep equality
      for collection keys stays a separate decision rather than one
      made silently here.

      Text keys compare by CONTENT, not by pool slot, and check 4
      pins it: the same string allocated twice is two slots but one
      key. A map that got that wrong would quietly hold duplicates --
      the single most likely way to break a map on a pooled string
      representation.

      `dissoc` moves the LAST entry into the hole rather than shifting
      the tail, which is what Clojure's own array map does and is
      correct because a map is unordered; check 5c walks every other
      key afterwards, including the moved one.

      25 checks, both compilers. **Promotion to a hash trie past 8
      entries is not here** -- it arrives with the HAMT module, and
      until then this stays linear at any size. That is a performance
      gap, not a behavioural one: a linear map answers the same
      questions, slower.

      **`src/f/GCHamt.f90`** -- the hash trie the map promotes into,
      plus `gc_hash` in the collector, mirroring `PersistentHashMap`'s
      `hash_of`: same mix32, same FNV-1a over the text, same tag mixed
      in so `"a"` and `\a` do not collide. It has to agree with
      `gc_equal` or a trie stores one key twice, so text hashes over
      CONTENT exactly as gc_equal compares content.

      Collision buckets **reuse GCMap**: a set of keys sharing a
      32-bit hash is a small linear map, and a second linear scan here
      would be the same code twice.

      The collision path is forced with a REAL pair, not hoped for.
      Integers cannot collide -- mix32 is the Murmur finaliser, which
      is bijective -- so the test searches short strings for a genuine
      FNV-1a collision (open addressing, ~0.2s) and then checks both
      keys are stored, both read back, and replacing inside a bucket
      does not grow the count. A trie that drops one of a colliding
      pair looks perfectly healthy until the day it does not.

      22 checks, both compilers, including 3000 keys across several
      levels of splitting and the torture case.

      **`src/f/GCEnv.f90`** -- the lexical environment: a chain of
      frames, each a name -> value map, searched outward. Structure
      unchanged from Env.f90, including that `gce_set` MUTATES the
      frame rather than returning a new one (`def` and `let*` add to a
      frame a closure may already hold, and everything sharing it must
      see the binding). The walk is iterative rather than recursive:
      an env chain is as deep as the program's nesting and this is the
      hottest path in the interpreter.

      Check 5 is the one that matters, and it is the correctness half
      of why the GC exists at all. A named `fn` binds its own closure
      into its own frame so `recur` can find it -- closure -> env ->
      closure, a cycle. Refcounting never sees either side reach zero,
      so **clotran leaks one of these per named fn for the life of the
      process**. The check builds that cycle, confirms it really is
      one (5b follows the closure's env slot back to the frame), drops
      every reference, and 5d collects it. That is not a speed win; it
      is a class of leak disappearing.

      22 checks, both compilers, also covering shadowing across three
      frames, bound-to-nil counting as bound (which the evaluator needs
      to tell "no such local" from "a local holding nil"), inner
      bindings not leaking outward, defining-namespace inheritance, and
      torture.

      **Closure and atom need no module of their own.** Both are plain
      slot objects -- `OBJ_CLOSURE` (params, body, env, clauses; i1 =
      macro?) and `OBJ_ATOM` (value, meta, dyn stack) -- with no logic
      beyond `gc_obj`/`gc_slot`, which `gc_test` check 11 already
      covers and GCEnv check 5 exercises.

      **`src/f/GCAssoc.f90`** -- the map clotran actually uses: array
      map to 8 entries, hash trie beyond, one-way, matching Clojure.
      It is a THIRD module rather than logic inside GCMap, and that is
      forced rather than stylistic -- GCHamt already uses GCMap for
      collision buckets, so GCMap using GCHamt would be a module cycle
      Fortran rejects. The arrangement is better anyway: neither
      representation knows the other exists.

      Two subtleties the checks pin:

      - **Promotion copies entries POSITIONALLY, not via `get`.** A key
        bound to nil would be silently dropped by a copy that read
        values back, because `get` cannot tell "absent" from "present
        and nil". Check 4 is that key.
      - **Replacing a key in a full array map must not promote.** The
        count does not change, so the representation should not either
        (check 5).

      Writing this also exposed a **vacuous test of my own**, which is
      worth recording as the failure mode to watch for. `gca_dissoc`
      on a trie was a no-op because `gch_dissoc` did not exist, so the
      "stays a trie however small it gets" check passed by never
      shrinking the map at all. Fixed both ways: `gch_dissoc` is now
      implemented (with its own checks, 7a-7d), and the assoc check now
      asserts the count actually dropped, so it cannot pass vacuously
      again. A test that cannot fail is worse than no test, because it
      is counted as coverage.

      `gch_dissoc` deliberately does NOT collapse emptied nodes -- an
      empty child stays a child, a one-entry bucket stays a bucket.
      Correct but slightly wasteful; the collapse is where trie
      deletion gets subtle and nothing needs the space yet.

      **`src/f/GCPrinter.f90`** -- values back to text, written before
      the switch rather than after, for two reasons beyond eventually
      needing it. It is the first thing that walks EVERY structure in
      the new layer at once, so a representation mistake each module's
      own tests miss shows up here; and debugging the switch without
      being able to print a value would be miserable.

      It needed entry iteration, so `gch_entries` and `gca_entries`
      came with it -- filling caller-allocated arrays rather than
      taking a callback, because flang segfaults passing an internal
      procedure as one (NOTES.md).

      Check 5 is the one worth having: the SAME single entry is built
      first in an array map and then, by promoting and dissoc'ing
      everything else, in a trie -- and must print identically. A map
      that printed differently past 8 entries would be the
      implementation leaking into the language. Check 1f is the other:
      a double prints as `2.0`, not `2`, or it reads back as an
      integer, which is a round-trip failure rather than a cosmetic
      one.

      24 checks, both compilers, including a value rooted only by the
      value stack printing correctly after a collection (printing
      allocates as it walks, so the subject has to stay rooted).

      **`src/f/GCReader.f90`** -- text into the heap, and with the
      printer a genuine **round trip**: read a form, print it, get the
      input back. That is the strongest test this layer has. A reader
      and a printer can only agree if the thing between them actually
      holds what it was given, and it exercises every structure against
      real Clojure text rather than against values built by hand.

      41 checks, both compilers. The two that matter most:

      - **6a: a 60-element list round-trips under torture.** Reading
        allocates constantly, so a collection lands between two
        elements of a list far more often than it ever would in
        practice, and every partially built form has to stay rooted
        through it. Elements accumulate in a GC VECTOR rather than a
        Fortran array for exactly this reason -- a plain array of
        gc_value is invisible to the collector.
      - **Group 5: bad input is an error, not a half-built value.**
        Unclosed list, unclosed vector, odd map literal, stray closer,
        unterminated string -- and a good form afterwards clears the
        flag.

      Recursive descent straight over the buffer, with no token array:
      LispReader has one to record a line and column per token, and
      source positions are still the open question above, so this does
      not pretend to solve it.

      Deferred and listed rather than silently missing: metadata `^`,
      the discard macro `#_`, sets `#{}`, regex literals, syntax-quote
      expansion and auto-gensym. Those are reader macros layered on the
      core shapes, and the shapes are what needed proving.

      **`src/f/GCEval.f90`** -- a core evaluator, and the module that
      answers the question the whole port rests on: **does rooting by
      construction hold up under real evaluation?** Everything before
      it was data structures, where the roots are obvious. An evaluator
      is where they are not -- intermediate values live across
      recursive calls, every one of which can allocate and therefore
      collect.

      The answer is yes. Every check runs TWICE, once normally and
      once with `gc_torture` on, and the torture pass is the real one:

          (do (def fib (fn* [n] (if (< n 2) n
                                  (+ (fib (- n 1)) (fib (- n 2))))))
              (fib 10))   =>   55

      computed correctly with a collection at **every single
      allocation**, heap audit clean afterwards. Also under torture:
      lexical capture (`((mk 10) 5)` => 15), recursion through a def'd
      name, shadowing, and vector literals evaluating their elements.

      The rule the module documents and the tests enforce: a value that
      must survive an allocation lives in a value-stack SLOT, never in
      a Fortran local, because the collector cannot see locals. Each
      routine opens a frame, works in slots, and reads its result out
      before leaving.

      Scope is the core, deliberately, not the ~5400 lines of Eval.f90:
      quote/if/do/def/let*/fn*/loop*/recur/defmacro*/quasiquote/try*/
      throw, twelve primitives, closures, varargs, multi-arity.
      Missing and listed rather than silent: destructuring (a macro in
      core.clj, not evaluator work), namespaces, protocols, metadata.

      **Laziness**, which `map`/`filter`/`range` are all built on.
      `(lazy-seq* body)` captures the body in a no-argument closure and
      hands back an unrealised node; nothing runs until something asks
      for an element. Check 16e proves that directly -- a body that
      would `throw` constructs fine, and 16f shows asking does run it.

      Realisation is memoised on the node, so walking a seq costs O(1)
      per cell rather than re-running the thunk, and 16g takes the
      third element of an **infinite** seq, which without laziness
      does not terminate at all.

      Two structural notes:

      - **Printing forces.** A lazy seq has to be realised to print,
        but the printer sits below the evaluator, so the evaluator
        hands its forcer down -- the same dependency inversion
        clotran's `rt_set_lazy_forcer` already uses, and a MODULE
        procedure because flang will not take an internal one as a
        callback.
      - **`(cons x <lazy>)` cannot build a plain cons cell.** Its tail
        would have to be a realised list, and forcing there defeats the
        point, since `(cons n (from (+ n 1)))` is exactly how an
        infinite seq is written. It builds an already-realised lazy
        cell instead, head and tail in place, nothing forced. clotran's
        `RT.f90` has `lazy_cons` for precisely this reason; the tests
        found it the hard way (16g returned nil, 16h `(1 nil nil nil)`)
        before it was put back.

      **Namespaces and Vars** (`src/f/GCNamespace.f90`), which closes
      the `def` divergence: `def` now interns in the CURRENT NAMESPACE,
      so `(let [] (def x 1))` defines at the top level exactly as
      Clojure does (check 17b). Symbol resolution is lexical scope
      first, then the namespace, so a local shadows a Var rather than
      redefining it -- which is what makes `(let [map ...])` legal.

      The point of Vars, and check 17f: a Var is a stable box with
      IDENTITY, so `(def x 2)` after `(def x 1)` MUTATES the same Var
      rather than replacing it. A closure built before the
      redefinition therefore sees the new value -- which is what makes
      redefining a function at a REPL work while everything that
      already called it keeps working. `(var x)` returns the Var
      itself, undereferenced.

      ### A trap that bit three modules, now closed

      `gc_init` clears the global-root table, but a module's saved slot
      index survives it. Three separate modules hit this:

      1. GCList's empty-list singleton -- caught by check 4c, fixed by
         re-checking the slot.
      2. GCNamespace's registry -- `gc_global_set` on a stale index is
         silently a NO-OP (out of range), so the registry was never
         re-registered and every namespace lookup failed.
      3. GCEval's thrown value -- worse: a stale index that lands back
         IN range **overwrites another module's root**. `thrown_root`
         was clobbering the empty-list singleton.

      A bare integer cannot distinguish "my slot" from "someone else's
      slot that now has my number", so the fix is a `gc_root` handle
      carrying an index AND a generation, with the generation bumped by
      `gc_init`. `gc_global_keep` re-registers whenever the claim is
      stale. Every module holding a global root now uses it.

      Worth noting how this was found: not by reasoning, but because
      (2) made eight checks fail at once and (3) left exactly one
      failing that the isolated probe could not reproduce. The second
      one only appears when many `gc_init`s run in sequence, which is
      what a test suite does and a single program never would.

      **`try*`/`catch*`/`throw`, and a rooting point worth keeping.**
      `throw` carries a VALUE, not a message, and that value is held
      as a **GC global root** rather than a plain module variable. It
      has to be: between the throw and the catch, nothing else refers
      to it -- the frames that held it are unwinding -- so an ordinary
      variable would be a live value the collector cannot see, and a
      collection in that window would free the exception before its
      handler ran. Under torture that window is a guaranteed
      collection, and check 14d (throwing a list and counting it in
      the handler) is what proves it.

      An internal error is catchable too, and arrives as a **map**,
      `{:error "message"}`, not a bare string. A string would be
      indistinguishable from `(throw "x")`, so a handler that wants to
      re-raise anything it does not recognise would have no way to
      tell them apart. clotran's older evaluator uses a string here;
      this is a deliberate improvement on it rather than an accident
      of the port. Checks 14i/14j are that distinction.

      **What `catch` cannot catch: a Fortran runtime error.** Fortran
      has no exceptions and no stack unwinding, so a segfault, a failed
      `allocate`, an `error stop` or a trap inside a called library
      ends the process. There is no `try` around it, and that is not a
      gap in this evaluator -- it is the host.

      It matters beyond the REPL. The point of the project is handing
      arrays to real Fortran libraries, and a crash inside one of those
      takes the whole session with it, including whatever the user was
      computing. For the live-monitoring goal that is the difference
      between "the simulation blew up" and "everything you had is
      gone".

      Three things ARE catchable and should be, rather than being left
      to crash:

      - `allocate(..., stat=)` -- out of memory becomes a clotran error
      - `read(..., iostat=)` -- already used by the reader for numbers
      - IEEE flags via `ieee_arithmetic` -- overflow, divide by zero

      Anything else would need a C signal handler plus `longjmp`
      through `iso_c_binding`, which is exactly the fragile territory
      the README's ABI section is about, and is not worth it for a
      crash that has already corrupted the heap.

      ### Surviving a crash inside a called library

      This is the sharp end of it: if ChemSol segfaults, does the whole
      REPL go down, and everything the user had computed with it?

      **Threads do not help.** A segfault is delivered to the PROCESS,
      and threads share one address space -- a wild write in the
      library's thread lands in our heap. Even catching SIGSEGV on that
      thread leaves the damage done and possibly `malloc`'s lock held
      forever. Threads buy concurrency, not isolation. Worth stating
      plainly because it is an easy thing to assume otherwise.

      **A separate process does, and it is measured, not assumed.** A
      probe (`fork` + anonymous `MAP_SHARED` mmap, both through
      `iso_c_binding`) has the child write results into a shared buffer
      and then segfault. The parent survives, `waitpid` reports status
      11, and **the results written before the crash are readable**.
      So the REPL can report "the library died" as an ordinary clotran
      error and keep everything else.

      What makes this a good fit rather than a bolt-on: the collector
      is **non-moving** and native buffers are **contiguous with stable
      addresses** -- decisions already taken for zero-copy interop. An
      array can therefore live in shared memory and be handed to the
      child by offset, with no marshalling. The property that makes
      `dgemm` cheap is the same one that makes isolation cheap.

      Costs, honestly:

      - **`fork` and threads do not mix.** Only async-signal-safe calls
        are legal in the child, so this must happen before OpenMP
        starts, or through a persistent worker spawned early. That is a
        genuine tension with the concurrency step and needs settling
        there, not here.
      - **`fork` does not exist on Windows** -- which is the reason
        not to build on `fork` at all. See below.
      - A fork per call costs on the order of a millisecond -- nothing
        against a large `dgemm`, ruinous in a tight loop of small
        calls. So a **persistent worker** rather than fork-per-call.
      - Partial results are visible, which cuts both ways: you can see
        how far it got, and you can also read half-written garbage.
        The worker protocol has to say which.

      Shape to aim for: isolation is **opt-in per library** in the
      binding generator -- trusted libraries called directly, unknown
      or crash-prone ones through a worker. That is the same
      per-library declaration thread-safety already needs, so it is one
      annotation rather than two.

      ### Windows, without fork

      clotran must not require Linux or macOS, so nothing may depend
      on `fork`. It does not have to: we already wanted a **persistent
      worker** rather than fork-per-call for performance, and a worker
      needs SPAWN, not fork. Spawn exists everywhere.

      **The portable floor is standard Fortran, and it is measured.**
      `execute_command_line` is Fortran 2008 and exists on Windows.
      A probe runs a child that writes results to a file and then
      segfaults: the parent gets `exitstat = 11`, survives, and reads
      back everything the child managed to write. No C, no platform
      branches, nothing POSIX. Whether `exitstat` carries the signal
      or a Windows exception code is processor-dependent, but non-zero
      means "it died", which is the only thing that has to be portable.

      **The fast path is a small shim, not a different design.** The
      floor copies through a file; mapping that same file instead
      removes the copy. The two platform calls are direct analogues:

      | | POSIX | Windows |
      | --- | --- | --- |
      | map a file | `mmap` | `CreateFileMapping` + `MapViewOfFile` |
      | spawn | `posix_spawn` | `CreateProcess` |
      | crash status | `waitpid` / `WIFSIGNALED` | `GetExitCodeProcess` |

      Four functions behind one shim, and the design degrades: if the
      shim is missing on some platform, the standard-Fortran floor
      still works, just with a copy. On Linux the mapped file goes in
      `/dev/shm`, so it is RAM anyway.

      **And the interpreter is already portable.** Checked, not
      assumed: there is **no `bind(c)` or `iso_c_binding` anywhere in
      `src/f`**, and all eleven new GC-layer modules compile clean
      under `gfortran -std=f2018`. The only POSIX thing in the repo is
      `scripts/clotran`, a shell wrapper around `rlwrap` -- a
      convenience, not the interpreter. So Windows support is a
      packaging question rather than a porting one, and this decision
      must not be what breaks it.

      **Multi-arity.** The two shapes real Clojure has, told apart by
      whether the form after `fn*` is a vector or a list, which is
      exactly how the reader leaves them. Clauses live in slot 4 --
      the slot `OBJ_CLOSURE`'s comment already reserved -- with slot 1
      left nil, so "is this multi-arity" is one test rather than a
      flag. Clause selection prefers an exact arity and otherwise
      takes the first variadic one that fits; check 15g runs a
      two-clause function that `recur`s within one clause to sum 1..100.

      **Varargs** are one routine, `bind_params`, used by BOTH fn*
      application and recur -- so a variadic function can recur without
      the two disagreeing about arity. `&` collects the rest into a
      list, empty rather than nil when there is nothing left, which is
      what lets variadic core functions work without special-casing
      zero.

      **Macros and syntax-quote.** A macro gets its arguments
      unevaluated and its result is evaluated in the caller's
      environment; the check happens before the arguments are touched,
      which is the entire difference from a function (check 13c: a
      macro ignoring an unbound symbol, where a function would fail).
      Macro-ness lives on the closure, as clotran's own `is_macro`
      does -- real Clojure keeps it in Var metadata, and there are no
      Vars here. `quasiquote` expands to ordinary `cons`/`concat`
      calls, the same shape as clotran's `qq_expand`, which is why
      those two arrived as primitives with it.

      **`loop*`/`recur`, and why there is no general trampoline.**
      Clojure does not promise tail-call elimination; it promises
      `recur`, an explicit jump to the nearest enclosing `loop*` or
      `fn*`. So iteration lives in exactly those two places: each
      evaluates its body and, if the result is an `OBJ_RECUR`, rebinds
      its parameters and goes round again. Recursion depth is then
      bounded by the program's NESTING rather than its iteration count
      -- which is the guarantee the language actually makes. A general
      trampoline would be more machinery for a promise Clojure never
      made.

      `recur` is a VALUE (`OBJ_RECUR`, holding its evaluated arguments)
      rather than host control flow, because only the recur point
      knows how to rebind, and it is the thing that catches it.

      Check 8e is the one that matters: **100000 iterations**, which
      without rebinding in place is a stack overflow rather than a
      wrong answer. 8f sums to 50005000 the same way.

      **The torture pass then caught a real rooting bug in my own
      `qq_expand`**, and it is the exact mistake this design is meant
      to prevent, made anyway:

          sym = gc_sym("concat", ...)   ! a Fortran LOCAL
          inner = nth_of(...)           ! allocates -- can collect
          call vs_set(base + 3, sym)    ! too late

      The symbol was computed into a Fortran local, then something
      that allocates ran before it reached a slot. Under torture it was
      collected in that window and the accumulated tail went with it --
      every quasiquote returned just its head. The plain pass was
      perfectly green throughout. Fixed by storing each intermediate
      into its slot BEFORE anything that can allocate runs, which is
      the rule the module header already stated.

      That is the argument for torture mode in one example: rooting by
      construction makes the mistake *findable*, not impossible, and
      what makes it findable is collecting at every allocation.

      Check 8g caught a mistake in my own expectation, and is the
      better test for it: a closure built during the iteration where
      `i` is 1 must return **1**, not the loop's final 2. If `recur`
      mutated the frame in place instead of rebinding into a fresh
      one, it would return 2. Rebinding is what makes that right.

      The torture pass caught a real bug on its first run: `has_error`
      is module state and nothing cleared it, so once one check
      expected an error every later evaluation short-circuited.
      `gce_clear_error` is now the caller's job before a top-level
      eval -- it cannot be done inside `gce_eval`, which is recursive
      and would wipe an error raised deeper in the same evaluation.

      ### A host shim, NOT a core library

      `clotran-gc` (`src/f/gc_main.f90`) is a REPL over the new stack,
      and it loads `src/clj/host.clj` at startup.

      That file was briefly a small core -- map, filter, reduce, take,
      range, sort, merge, into, all written in Clojure -- and that was
      a mistake, caught in review. The argument against Fortran
      builtins was that real core.clj defines those in Clojure and the
      thesis is running that actual file. Writing our own versions is
      the same duplication one layer up: a second, different
      implementation that the real file replaces, and a confusing bug
      in the meantime wherever the two differ.

      So host.clj holds ONLY what core.clj cannot supply: the type
      predicates. Real Clojure asks `instance?` about
      `java.lang.String` and `clojure.lang.PersistentVector`; clotran
      has neither, so the host answers with `clotran-type` and the
      predicates are written over it. Three macros (`defn`, `fn`,
      `let`) come with them only because the predicates cannot be
      written without them -- scaffolding, and gone the moment the
      real core.clj loads.

      Its name was wrong too: `gc_core.clj` reads as part of the
      collector, when it targets the GC-backed evaluator and is not a
      core at all.

      **What the oracle measures, after the correction.** 59 of 86
      expressions agree; the 27 that differ name exactly what real
      core.clj must supply:

          <= > >= contains? dec distinct drop even? filter inc
          interpose into last map max merge min neg? odd? pos? range
          reduce reverse sort take vec zero?

      That is a better number than the 86/86 it replaced, because it
      measures the right thing: **how much of real core.clj the
      evaluator can already carry.** It closes by growing the
      evaluator, never by growing host.clj.
      ### Pointing it at the real core.clj

      `clotran-gc some.clj` now loads files named on the command line,
      so the real core.clj can be tried against this evaluator and the
      first error it reports IS the next thing to build. Two bugs of
      mine had to go first:

      - **The file loader was O(n^2).** It appended line by line, and
        each `//` builds a whole new string. On an 8371-line file that
        is not slow, it is indistinguishable from a hang. Now one
        `inquire(size=)` and one stream read. LispReader.f90 carries
        the same warning in two places; I repeated the mistake anyway.
      - **The reader could fail to advance.** core.clj opens with
        `^{...}`, the reader has no case for `^`, so it fell through to
        read_atom, produced an EMPTY token, and never moved `pos` --
        an infinite loop. A reader that can hang is far worse than one
        that errors, so an empty token is now an error naming the
        character it could not dispatch.

      With both fixed it fails in a second, usefully:

          load src/clj/clojure/core.clj: reader error:
            reader: no dispatch for '^'

      ### seq is the abstraction, and it was missing

      Caught in review, and correctly: the evaluator had no seq
      abstraction. Every operation dispatched on concrete type at its
      own call site --

          if (lazy) ... else if (list) ... else if (vector) ...

      repeated in first, rest, count, empty?, seq and second. That is
      not a style complaint: each chain was an independent chance to
      forget a branch, and one of them did. `rest` silently omitted
      vectors, which made `reduce` return its first element and `last`
      return its first -- both looking like arithmetic bugs.

      Two more consequences that had not been noticed:

      - `rest` on a vector COPIED the tail, so walking a vector was
        O(n^2) where Clojure's is O(1).
      - Strings and maps were not seqable at all. `(first "abc")` and
        `(first {:a 1})` both returned nil.

      **`OBJ_SEQ` is now a seq VIEW over an indexable collection** --
      slot 1 the source, i1 the index. `rest` bumps the index and
      shares the source, so it is O(1) and allocates one small object
      rather than copying. Lists and lazy seqs need no view because
      they ARE seqs, which is the same split real Clojure makes:
      PersistentList implements ISeq, PersistentVector does not and
      hands out a ChunkedSeq.

      **`to_seq` is now the only place that knows concrete types.**
      Adding a seqable type means teaching it and nothing else. first,
      rest, second, count, empty? and seq all go through it.

      Strings and maps came for free: `(first "abc")` is `\a`,
      `(first {:a 1})` is `[:a 1]` -- an entry, which is what lets
      destructuring walk a map. Nine new oracle cases, all agreeing
      with real Clojure; 68 of 95 now.

      One thing this does NOT change: the old evaluator (RT.f90) has
      the same per-type dispatch, which is where the shape was
      inherited from. It is not worth fixing there -- that code is
      being replaced -- but it is worth knowing the bug class existed
      in both.

      ### Should everything be built on seq? No -- Clojure does not

      Clojure keeps two layers, and conflating them would be wrong:

      - **collections** -- conj, assoc, get, nth, count: type-specific
        ON PURPOSE. `(conj [1] 2)` appends, `(conj (list 1) 2)`
        prepends, `(conj {:a 1} [:b 2])` assocs. That difference is
        the feature.
      - **sequences** -- first, rest, next, cons: uniform, over seqs.

      Only the second layer routes through `to_seq`. Measured rather
      than assumed: after the seq work, **3 of 32 builtins** still
      dispatched on concrete type -- conj, cons and nth -- so this was
      a three-function fix, not a refactor.

      `conj` stays type-specific (and gained the map case it was
      missing). `cons` and `nth` now go through seq, which is what
      real Clojure does: `(cons 1 "ab")` is `(1 \a \b)` and
      `(nth (range 5) 2)` is 2, neither of which has an index.

      **Two bugs this introduced, both instructive.**

      `(cons x ())` broke macro expansion. An empty tail seq's to nil,
      so cons took the not-a-list branch and built a lazy cell rather
      than a list -- and the evaluator only recognises a LIST as a
      form, so every macro returned its own expansion unevaluated.
      Three checks caught it immediately.

      `(cons n (from (+ n 1)))` then hung, because `to_seq` FORCES a
      lazy seq. Forcing there is not a slowdown, it is an infinite
      loop: building one cell realises the whole infinite seq. A lazy
      tail is now taken as-is and never seq'd.

      **And a flaw in how I was verifying.** That second bug showed up
      as a SEGFAULT under flang while gfortran looked clean -- because
      I was counting `FAIL` lines, and a crash prints none. The test
      had died, not passed. Check the **exit status**; a grep count
      cannot tell a clean run from a dead one. flang caught it purely
      because its stack gave out first.

      ### Metadata, and the reader now parses all of core.clj

      `OBJ_META` became a WRAPPER -- slot 1 the value, slot 2 the
      metadata -- rather than a field, because `gc_value` has no spare
      component (the point of it) and because symbol text is INTERNED,
      so metadata hung off a string-pool slot would apply to every
      `foo` in the program.

      The wrapper's cost is that consumers must see through it. That
      is contained by unwrapping in exactly one place: `gce_eval`
      evaluates the value inside, so metadata is invisible to every
      form that does not specifically ask. Only `def` and `meta` look.

      The payoff is the core.clj bootstrap working:

          (def ^{:macro true} m (fn* [a] (quote :expanded)))
          (m ignored)   =>   :expanded

      which is how let, loop and fn become macros at core.clj line 32,
      before defmacro exists.

      **Reader dispatch.** `#` is a dispatch character, not a symbol
      character, and treating it as the latter is not harmless:
      `#{1 2 3}` read as the symbol `#` followed by a three-element
      map, and the error was "map literal has an odd number of forms"
      -- nowhere near the cause. Added: `#_` discard (of the next
      FORM, not token), `#'` var, `#{}` sets, `#()` anonymous fns,
      `#""` regex literals.

      Sets are `OBJ_SET`, backed by a map from each element to itself
      -- what PersistentHashSet does -- but a distinct kind, so they
      print as `#{...}`, answer `:set`, count elements rather than
      pairs, and seq as elements rather than entries. The backing map
      is representation and stays hidden.

      `#()` takes its arity from the HIGHEST %n used, not the count:
      `#(+ %2 %2)` is a two-argument function. Parameter names are
      fixed rather than gensymed, so a body binding `p1` would shadow
      -- noted where it is written, and waiting on auto-gensym.

      **The reader now parses all 8371 lines of real core.clj.** It
      fails in evaluation instead:

          load src/clj/clojure/core.clj: 'ns' not found
            in form: (ns #<object>)

      which is the right kind of failure: a missing function rather
      than a syntax the reader cannot represent.

      One oracle case had to be dropped rather than fixed: set PRINT
      ORDER differs from Clojure's, and both are unordered, so the
      comparison was meaningless. Order-independent set facts are
      checked instead.

      ### Metadata: not lost, unported

      `clotran-bin` supports metadata fully -- `^`, `with-meta`,
      `meta`, Var metadata. `clotran-gc` does not yet. Checked:
      `(meta (with-meta [1] {:a 1}))` is `{:a 1}` on the old
      evaluator and `with-meta not found` on the new one.

      It is load-bearing rather than decorative, and core.clj proves
      it at line 32 with Rich Hickey's own comment:

          ;during bootstrap we don't have destructuring let, loop or fn
          (def ^{:macro true} let (fn* let [&form &env & decl]
                                    (cons 'let* decl)))

      Macro-ness IS `:macro true` in a Var's metadata; `defmacro` only
      sets it for you. So a reader that parses `^` and discards it
      produces a core.clj where nothing is a macro.

      That also narrows the design question below: what needs metadata
      first is the **Var**, and `OBJ_VAR` slot 2 is already reserved
      for it. `(def ^{...} name val)` may be reachable without solving
      metadata-on-any-value at all.

      ### The next blocker, and it is a real design question

      **Metadata cannot simply be dropped.** core.clj defines `let`,
      `loop` and `fn` as `(def ^{:macro true} name (fn* ...))` before
      `defmacro` itself exists -- so a reader that parses `^` and
      discards it produces a core.clj where nothing is a macro.

      But there is nowhere to put it. `gc_value` is {tag, ival, rval,
      ref} and deliberately has no spare component -- that is the
      entire point of the new representation. Worse for symbols: text
      is INTERNED, so two `foo` symbols share one string-pool slot,
      and metadata hung off that slot would apply to every `foo` in
      the program. Real Clojure has no such problem: a Symbol is an
      object with its own metadata, equal to but distinct from another
      `foo`.

      Options, none obviously right:

      1. **Wrap**: a metadata-bearing value becomes an `OBJ_META`
         holding {value, metadata}. Contained if unwrapping lives in
         one accessor, invasive if it does not -- every consumer must
         see through it.
      2. **Un-intern symbols**: give each its own object with a meta
         slot. Costs an allocation per symbol and makes symbol
         comparison a text compare rather than a slot compare, on the
         hottest path in the interpreter.
      3. **A side table** keyed by value identity -- which does not
         exist for interned text, so this reduces to (2).

      Settle before writing any of it. The old representation dodged
      this by giving every `cons_value` a `meta_val` component, which
      is exactly the nine-allocatable-component design being removed.

      Three bugs the bootstrap found that 266 unit tests had not:

      - **`rest` did not handle vectors**, so `(rest [1 2 3])` was nil
        and every seq walk over a vector stopped after one element.
        `reduce` returned its first element and `last` returned its
        first -- both looking like arithmetic bugs rather than a seq
        bug.
      - **A non-advancing `read` reports end-of-RECORD as a negative
        iostat**, exactly as end-of-file does, so the file loader
        stopped after line one and silently loaded nothing. Standard
        Fortran, easy to write, invisible without a diagnostic.
      - Auto-gensym (`sym#` in a syntax-quote) is missing from the
        reader.

      34 host primitives, and the split stays a dial rather than a
      wall: a primitive can move into Fortran when measurement says
      so. What must NOT happen is re-implementing core.clj in either
      language.

      **The new stack is now complete and proven end to end:** vector,
      list, array map, hash trie, promotion, environment, printer,
      reader, evaluator -- 21 suites green on both compilers. Real
      Clojure text is read, evaluated and printed entirely in the new
      representation, under a collector running at maximum paranoia. Closure and atom need no module of their
      own. What remains for 3c-2/3d is the switch itself: `cons_value`
      becomes a handle, the evaluator moves onto the value stack, and
      `Values.f90`'s old backing types go.
- [ ] **3e.** Retire `FINAL`-based refcounting; `rc_test` becomes a GC
      test. Finalizers survive only on the few heap nodes owning
      foreign resources, run once per object by sweep rather than once
      per copy.

Gate: `rc_test`, 226 `eval_test` checks and the upstream suite all pass
under torture mode. This is a branch, and it is genuinely big-bang at
step 3c.


---


Everything after this step is paid for by the edit-test loop, so make
the loop cheap before starting on the expensive steps.

- [x] **4a -- DONE.** `scripts/run-clojure-tests` drives `clotran-gc`
      with core.clj loaded. It did drop hard at first, which was the
      signal being asked for; see "Where we are" for the current numbers.
      Its summary-line parser also had to learn that maps print with
      commas now, which `clotran-bin` did not do.

      The original note: This is now the step that matters most: the suite is
      Clojure's own assertions over the real core.clj functions, where
      `scripts/gc-oracle` is 107 cases someone wrote by hand. Expect it
      to drop hard at first -- that is the signal being asked for.

      Two things it will force, both wanted:

      - **Retire `clotran-bin`.** ~9,300 lines of the original
        evaluator go once the suite passes on the GC one. That deletion
        is what the whole GC effort was for, and keeping two evaluators
        means every fix has to be considered twice.
      - **Startup cost becomes the bottleneck.** The runner launches a
        process per namespace, so ~40 namespaces x 1.68s is around a
        minute of pure loading per run. Annoying, not blocking -- but it
        is what finally makes 4c worth doing.

- [x] **4a'. The gfortran-only crashes.** Three real bugs, none of them
      a gfortran defect. Found with `-fcheck=all -fbacktrace`, which is
      worth reaching for first every time: the raw crash was SIGTRAP
      inside `malloc` at an unrelated `allocate`, and named nothing.

      1. **Missing Fortran 2018 recursion semantics.** F2018 makes every
         procedure recursive by default; flang follows it, gfortran
         still defaults to F2008, where a procedure not marked
         `RECURSIVE` may keep its locals in *static* storage. Re-enter
         it and the outer invocation's variables are overwritten.
         gfortran rejects *direct* recursion at compile time, which is
         why this hid for so long -- but an evaluator is mutually
         recursive everywhere (`eval_form` -> `eval_let_head` ->
         `eval_form`), and so is refcounting (`release` -> `deallocate`
         -> `final` -> `release`). Fixed with `-frecursive` in the
         Makefile, which is exactly flang's semantics. `-std=f2018`
         does **not** do it (checked on gfortran 16). Rejected marking
         ~200 procedures by hand: this is one build-level property, not
         an annotation per procedure.
      2. **Non-short-circuiting `.and.`** at `Eval.f90`'s
         `eval_instance_call`: `target%tag == TAG_KEYWORD .and.
         names_a_class(target%str_val)` evaluated the right operand for
         every target, passing an *unallocated* `str_val` as an actual
         argument whenever the target was not a keyword. Same trap as
         `resolves_to_macro`; fixed the same way, by nesting. flang read
         whatever was there and carried on.

      Those two fix the *deterministic* `multimethods` crash, and a
      clean run of the whole suite is 163/16/41 on both compilers.

      Correction: an earlier note here said they fixed `multimethods`
      "permanently". That was claimed on two sampled runs and is wrong.
      `multimethods` now fails the same way `logic` does -- sometimes,
      with the 4a'' signature below. Two samples are not evidence of
      absence for a 1-in-6 bug; take ten.

- [ ] **4a''. An intermittent use-after-free (~1 run in 6).** Hits
      whichever namespace happens to trip it -- `logic` and
      `multimethods` both do. Not the same class as the two above, and
      not fixed:

      ```
      node_ref_release -> cons_value_release -> cons_value_finalize
      Index '1' of dimension 1 of 'h...%children' above upper bound of 0
      ```

      What is established, by instrumenting `node_ref_release` to report
      any entry on a non-positive refcount:

      - The refcount read is **-675019966** -- garbage, not `0` or `-1`.
        So this is not a double-release of a live node; `h%ptr` points
        at memory that is no longer a `vec_node` at all. A `node_ref`
        outlived the node it referenced: a **missing increment**, not an
        extra decrement.
      - It is **not** a defined-assignment dispatch failure. The
        suspicion was `node_assoc`'s bulk slice copy
        (`new_node%children(1:n) = node_in%ptr%children(1:n)`) silently
        falling back to intrinsic assignment and skipping the refcount
        bump -- the same shape as the `hamt_slot` problem already in
        NOTES. Disproved with an isolated probe: both compilers
        dispatch to the elemental defined assignment, 4 calls for 4
        elements, slice and whole-array alike.
      - Every `_assign` *is* in the `assignment(=)` interface, and
        `cons_value_assign` does release the LHS before copying.
      - It is reached from `cons_value_finalize`, i.e. the compiler's
        own finalization, not from an explicit release.

      So the remaining candidates are the paths where a `node_ref` is
      copied WITHOUT defined assignment: function results, `intent(out)`
      dummies, and component finalization of the types that have no
      `FINAL` of their own (`vec_t`, `closure_t`) and rely on the
      standard cascading into their components.

      **Recommendation: do not root-cause this further.** Every routine
      in the failing path -- `node_ref_release`, `cons_value_release`,
      `cons_value_finalize` -- is deleted by 3e. Refcounting is the
      subsystem being replaced, and this is a bug *in the thing being
      thrown away*. The GC finds this class of fault deterministically
      (`gc_check_heap` under torture) where this takes six runs to
      reproduce once.

      It does not block 3c-1, which is a mechanical refactor with the
      representation unchanged. It is an argument for getting to 3c-2
      and 3e promptly rather than lingering in 4a.

      **Update, after 3c-1.** The migration made this fire much harder
      on gfortran. Measured over six runs after all six payloads:
      `multimethods` crashes **every** run, `logic` 2 of 6. gfortran
      never reaches 163 any more; its best is 161 and its worst 51.
      flang is unaffected at 163/16/41 every run, and both compilers
      pass all twelve unit suites.

      So the accessors are correct -- each is assign-then-return,
      refcount balanced, and the oracle agrees. What changed is that
      value-level accessors create more temporaries, so more refcount
      traffic goes through the broken path. A latent bug that fires
      reliably is more useful than one that fires sometimes, but be
      clear about the cost: on gfortran this went from unreliable to
      unusable on `multimethods`.

      With the deterministic repro, two more things are now known.
      Poisoning a `vec_node` instead of freeing it and checking for the
      poison on entry proves it exactly:

      - **A `vec_node` is released after it has already been freed**,
        and the second release arrives through `cons_value_release`'s
        explicit call, not through finalization. So two `cons_value`s
        hold a `vec_t` pointing at the same node with only one
        increment between them: a missing increment, confirmed, not an
        extra decrement.
      - **It is not the copy-in/copy-out hazard.** The obvious suspect
        was `call node_ref_release(v%vector_val%root)` -- an
        `intent(inout)` actual whose type has a `FINAL` -- nulling a
        copy while the original stayed pointing at freed memory.
        Dropping the explicit release and relying on `deallocate`'s
        cascade changes nothing. Disproved.

      Also ruled out: AddressSanitizer. The gfortran build runs `logic`
      to completion under ASan with no report at all, because its
      allocator does not recycle the freed node into the path that
      trips it. `-fcheck=all` says nothing either -- a dangling pointer
      is invisible to bounds and recursion checks.

      **Every compiler-mechanism hypothesis is now eliminated.** Each
      was checked with an isolated probe on BOTH compilers, and all
      four behave correctly:

      | suspected mechanism | verdict |
      | --- | --- |
      | bulk slice assign skipping defined assignment | correct, 4 calls for 4 elements |
      | array constructor copying a ref without a bump | correct, refcounts balance |
      | function result of a type whose *component* has the FINAL (`vec_t`'s exact shape) | correct, one finalize of the temp |
      | copy-in/copy-out on `intent(inout)` with a FINAL | not it -- removing the explicit release changes nothing |

      That matters more than any single one of them: **the bug is in
      this codebase's own logic, not in a compiler behaviour we
      misunderstood.** It is findable by reading the code that shares a
      `vec_t` between two `cons_value`s, and it does not need another
      compiler experiment.

      **There is now a minimal repro: `test/clj/uaf_repro.clj`.** It
      runs in seconds instead of a 30-second suite sweep, crashes ~6
      runs in 8 on gfortran, and is deterministic under the poison
      instrument its header describes. It was reduced from
      `multimethods`' `methods-test`, and **it crashes identically on a
      tree with the 3c-1 accessors stashed** -- which is the proof that
      3c-1 exposed this rather than caused it.

      Two facts the reduction handed over:

      - **The bare forms do not crash.** `defmulti`/`defmethod`/
        `remove-method`/`methods`/`into #{}` at the top level are fine.
        It needs `deftest`/`testing`/`is` around them -- i.e.
        clojure.test's *dynamic bindings* and its report machinery.
        That points at the `binding` stack (`atom_node%dyn_stack`, an
        allocatable array of `cons_value` grown and shrunk with
        `move_alloc`) rather than at vectors, even though a `vec_node`
        is what dies.
      - **The corruption and the crash are in different places.** The
        fault is a stale `node_ref`; the SIGTRAP lands later at an
        unrelated `allocate` in `node_assoc`. Reading the backtrace
        alone was never going to find this, which is why the poison
        instrument matters.

      **Mitigated, not fixed: `node_ref_release` no longer frees.**
      Leaking the `vec_node` makes the premature free harmless, and the
      measured cost is small -- bootstrap RSS 93 MB against 84 MB,
      about 10%. In exchange gfortran goes from "multimethods crashes
      every run" to **163/16/41, identical to flang**, three runs in a
      row, with every unit suite green on both compilers.

      That trade is worth taking because gfortran is the default build
      and the one most people will use, and because step 3e deletes
      this refcounting outright: the GC frees these by tracing, so the
      missing increment stops mattering rather than needing to be
      found. Ceiling: a long-running process building many vectors
      grows without bound. If 3e slips, fix the bug instead -- the
      repro plus the poison instrument finds it in one run.

      **Bisect: attempted, and it does not isolate this.** Two things
      worth recording so nobody repeats them:

      - The first run was invalid. The harness accepted any commit that
        printed a `:type :summary`, but the bisect-specific repro used
        fully-qualified `clojure.test/deftest`, which does not register
        a test -- every commit ran **0 assertions** and looked "good".
        It accused a docs-only commit, which is what gave it away. A
        bisect harness has to assert that the test genuinely ran, not
        merely that it finished.
      - With a correct harness (force `FC=gfortran` and `-frecursive`
        at every commit, since older trees default to flang and
        pre-date that fix; require `Ran N tests containing M
        assertions` with M > 0), **every commit back to `a3bb429` is
        bad** -- 22 commits, and further back the repro cannot even be
        expressed because `:refer` did not exist yet. The bug predates
        the earliest commit that can express it. It is old code, not a
        regression, and bisect has nothing to bracket.

      Correction to an earlier note here: this entry previously said
      "pre-existing" on the strength of stashing `src/f` and rebuilding.
      That test was worthless -- 3c-1 was already committed, so the
      stash removed nothing relevant. The conclusion happens to be
      right, but the evidence for it is the bisect above (`931c93a`,
      which predates every accessor commit, is bad), not that stash.

## `deftype*`: four bugs behind one special form

The special form itself was the easy half. Of the five things that had
to change to make `(deftype Point [x y] ...)` work, four were bugs that
had been in the tree the whole time, invisible because nothing had ever
asked the question.

**A type is not a class.** Clojure generates a JVM class; ClojureScript
generates a JavaScript constructor; both host compilers have a case for
`deftype*` (cited in SEAMS.md). clotran generates nothing. A type is an
object holding a name, its field names, a map from method-name keyword
to closure, and a vector of the class keywords it claims to implement.
That is enough because `instance?` is the only question anything asks of
a type, and `find-protocol-impl` asks it first:

    (defn find-protocol-impl [protocol x]
      (if (instance? (:on-interface protocol) x)
        x
        ...))

A list of names answers that. A hierarchy would let us answer it for
names nobody declared, and nothing needs that yet.

**Method bodies see fields as plain names.** On the JVM they are real
fields on a real class, so `(area [this] (* w h))` compiles to field
loads. Here the clause is rewritten at definition time to

    ([this] (let* [w (. this -w) h (. this -h)] (* w h)))

which needs no evaluator support beyond field reads. The one subtlety:
a field whose name a PARAMETER also uses is left out of that `let*`,
because the parameter is bound outside it and binding the field too
would shadow the argument the caller passed. Clojure resolves that the
other way round, the parameter winning; skipping is how this gets the
same answer with the bindings in the wrong order.

**The global root table was exactly full.** Eight slots, and eight
claimed: `thrown`, `global_env`, `gensym` and `binding_stack` in
GCEval, `registry`, `current` and `ns_var` in GCNamespace, and
GCList's `empty`. The type table was the ninth, and `gc_global_new`
answered by returning index 0 and shrugging. `gc_global_keep` then
stored nothing, `gc_root_live` stayed false, and the table was swept on
the next collection -- so a type defined one moment was "no such class"
the next.

The comment above `gc_global_keep` already warned about the *stale
index* version of this failure, having bitten three modules.

The first fix was to raise the constant and make exhaustion an
`error stop`. That was the wrong shape: it kept a limit in `GC.f90`
that has to be maintained in step with `type(gc_root), save ::`
declarations in other files, and 32 is no more principled than 8, only
further away. The table is now GROWABLE and there is no number at all.

It stays small on its own. Every root is a module-level singleton --
nine today -- and nothing claims one per object: a million deftypes
live inside the one `types_root` map, a million namespaces inside
`registry_root`. So it doubles once, at startup, and never again. The
grow path preserves slot INDICES rather than addresses, because that is
what modules hold across calls -- a copy landing at a different offset
would silently swap two modules roots, which `gc_test` 18c checks by
claiming 200 and reading every one of them back after a collection.

**`(str *ns*)` printed the wrapper.** `namespace-munge` is literally
`(.replace (str ns) \- \_)`, so what `deftype` built its class name
out of was `#<ns clojure.core>.Point`. `Namespace.toString` is the
NAME -- `clj` confirms `(str *ns*)` is `"user"`.

The first fix keyed the PRINTER on `*print-readably*`: bare name for
print, `#<ns ...>` for pr. That got the one case that was asked about
right and three others wrong, because that is not the axis Clojure
splits on. Measured against `clj`:

    (str *ns*)        "user"                       <- toString
    (print-str *ns*)  "#object[...Namespace... user]"  <- still the object form
    (str [*ns*])      "[#object[...Namespace...]]"     <- and nested too

So `print` is NOT the bare name, and a namespace inside a collection
is not either -- a collection's `toString` prints its elements rather
than calling `toString` on each. The split is `toString` against
everything else, not readable against not.

It belongs in `.toString`, which is where `str` actually goes:
core.clj's `str` is `(. x (toString))`. `to_string_text` is that one
place, shared by the host member and the base-env `str` builtin so
the two cannot drift, and it already had the same shape for a
StringBuilder and a Pattern -- host objects whose text is their own
rather than their print form. A namespace is the third.

What is still wrong is `pr` of a bare namespace, and DEVIATIONS 21
says why it cannot be reached from here: Clojure gets `#object[...]`
from `print-method Object`, which needs `String/format` and an
identity hash clotran has no stable answer for.

**A macro's expansion is a lazy seq, not a list.** `eval_dot` decided
"is this `(. x (m a))` or `(. x m)`" with `gcl_is`, which is true only
for `OBJ_CONS`. `emit-method-builder` assembles its dot form with
syntax-quote, so what arrives is a lazy cell, `gcl_is` was false, and
the `(area)` list was read as a member NAME -- "`.` needs a member
name", on every protocol method dispatched through its interface.
`gce_eval` already realises a seq before treating it as a call, for
exactly this reason and with a comment saying so; `eval_dot` had never
learned it. The member name also needed `strip_meta`: a protocol sig
keeps its metadata through `defprotocol`, and `emit-method-builder`
splices that symbol in verbatim.

**What it did not move.** Neither scorecard. Clojure's own suite went
653 -> 655 passing assertions, and the 14 libraries that load are the
same 14: the three vendored libs that use `deftype` or `reify`
(`core/reducers`, `reflect/java`, `pprint/pretty_writer`) each fail on
something else first -- `clojure.lang.Delay`, a `0x0001` literal, and
`PersistentStructMap`. What moved is core.clj, 691 -> 707 forms, and
the fact that `deftype` and `reify` exist at all. `defrecord` still does
not: it expands through `letfn`, so it waits on `letfn*`.

## `letfn*`, and the four bugs that stood between a record and working

`letfn*` itself is `let*` with one difference: every name is in scope in
every init, so the functions can call each other. Compiler.java's
LetFnExpr calls that "pre-seed env (like Lisp labels)" -- it registers
all the locals before analysing any init. Here that is one frame, seeded
with every name bound to nil, and each init evaluated in that same frame
so a closure built by an earlier init captures the frame a later one is
about to fill. Twenty lines.

What it cost was the rest of this entry, and none of it was about
`letfn`. `defrecord` expands through `letfn`, so landing the special
form turned `defrecord`'s loud failure into a working definition with
SILENT wrong answers behind it:

    (:a p)                  ;=> nil   (want 1)
    (count p)               ;=> 0     (want 2)
    (= (->P 1 2) (->P 1 2)) ;=> false (want true)

Which is the trade this project refuses to make. `(.valAt p :a)` already
answered 1 -- core_deftype.clj's methods were there and correct -- so
nothing needed reimplementing; the generic operations simply never
asked.

**The operations now offer an instance its own method first.** `get`,
`count`, `seq`, `assoc`, `keys`, `vals`, `contains?`, `dissoc` and `=`
each check for a declared method before falling through to the map
layer. That is what an interface IS here: there is no class to test, so
"implements ILookup" means "declares valAt", and records work through
Clojure's own vendored code rather than a second implementation in
Fortran. A plain deftype declares none of them and still reaches the old
path.

**`identical?` was wired to `=`.** `Util/identical`, `Util/equiv` and
`Util/equals` all mapped to the `=` builtin, so `(identical? [1] [1])`
was true where Clojure says false. Wrong on its own, and fatal once a
record's `equiv` could be reached: that method opens with
`(identical? this other)`, so `=` called `equiv`, which called `=`.
Printing a record segfaulted, and `lldb -b -o run -o bt` named
`gc_equal` in one line after several wrong guesses -- the lesson from
the gotchas list, learned again.

The replacement compares by TEXT for strings, symbols and keywords
rather than by pool slot, because clotran does not intern text while the
JVM interns those three. Ref equality made `(identical? :a :a)` false,
and a record's equiv compares `(identical? (class this) (class other))`
-- exactly two keywords of the same name.

**`(symbol "a.b.C/create")` dropped the qualifier,** answering `create`.
It used `name_part`, which is what `name` wants and the opposite of what
`Symbol.intern(String)` does: that splits on the slash and sets both
halves. Every form built as `(~(symbol (str classname "/create")) ...)`
therefore lost the class it was calling, which is how defrecord's
`map->Name` factory came out as `(create m)`.

**Multimethod dispatch did not know a deftype's declared interfaces.**
`print-method` has a method on `clojure.lang.IRecord`; a record
dispatches as `:clojure.core.P`; nothing connected the two. So dispatch
fell to `:default`, which asks `(instance? clojure.lang.IObj o)` -- which
a record IS, since IObj is in its `:implements` -- and re-entered
`print-method` on the same object. `host_super` now reads a type's own
interface list, and the walk is 24 deep rather than 4, because a record
declares a dozen where a built-in type declares two.

**Record constructors have three arities,** and the rule is stated
exactly in Compiler.java: trailing fields named `__meta`, `__extmap`,
`__hash` or `__hasheq` are counted into `altCtorDrops`, and when that is
non-zero the class gets one ctor dropping all of them and one dropping
the last two. The omitted fields are filled ACONST_NULL, ACONST_NULL,
ICONST_0, ICONST_0 -- and the zeros matter, because core_deftype reads
them back as `(if (zero? __hasheq) ...recompute... __hasheq)`, which a
nil would not survive. A plain deftype has no such fields, so its arity
check stays exact.

**What this exposed, and what it took to fix: sequential equality.**
The new suite's first run answered false for
`(= (map inc [0 1]) [1 2])`. `seqable` was `gcl_is(v) .or. gcv_is(v)`
-- list or vector -- so a LAZY SEQ was not sequential and fell through
to identity. Anything built by `map`, `filter`, `range` or
`map-indexed` is a lazy seq, so comparing one against a literal vector
was silently wrong, which is most of what a test does.

Both references ask a different question and use a different method:

    ASeq.equiv        obj instanceof Sequential || obj instanceof List
                      this instanceof Counted && obj instanceof Counted
                        && count() != count()        -> false
                      then walk with RT.seq / .next()

    equiv-sequential  (sequential? y)
                      (and (counted? x) (counted? y)
                           (not (== (count x) (count y))))  -> false
                      then (loop [xs (seq x) ys (seq y)] ...)

Two things fall out of that. The test is SEQUENTIAL, not
list-or-vector -- which is why a set and a bare string stay unequal to
a vector while `(seq "ab")` does not. And the count is a SHORTCUT
taken only when BOTH sides are counted, because counting a lazy seq
realises it and an infinite one never finishes. Counting first, which
is what this did, cannot be repaired by adding lazy seqs to the
predicate: `(= (range) [1 2])` has to return, and in Clojure it does
precisely because nothing asks for a count.

So `deep_equal` now walks, and takes a `roots` argument because
walking allocates where indexing did not -- forcing a lazy cell, and
taking the rest of a vector view. Stripping metadata at entry came
with it: the wrapper used to reach the sequential test and answer
false, so `(= (with-meta [1 2] {:a 1}) [1 2])` was false where Clojure
says true.

ClojureScript writes all of this in Clojure, so it is bucket B and
not a seam: ours being in Fortran is a choice.

This is the change that moved the suite. `=` is in every assertion
Clojure's tests make, so getting it wrong for lazy seqs suppressed
passes everywhere:

| | before | after |
| --- | ---: | ---: |
| passing assertions | 655 | 681 |
| failures | 199 | 175 |
| errors | 231 | 237 |
| tests reporting | 190 | 193 |
| namespaces with a pass | 17 | 18 |

The errors went UP by six, which is the honest shape of it: an
assertion that used to compare false and stop now gets further and
hits the next missing thing. Thirteen namespaces still crash before
reporting, unchanged.

**And a gap this closed.** `test/f` runs against the BASE environment,
with no core.clj, so none of the above could be tested there: records
were verified by hand against `clj` and nothing would have caught a
regression. `test/clj/language_test.clj` is a language-level suite `make
test` now runs, greping for a final PASSED marker so that a crash
part-way through fails the gate too. Checked by breaking an assertion
and confirming `make test` stops.

## `require` lost its `:refer` to a metadata wrapper

`(:require [clojure.test :refer :all])` interned nothing, so whole test
files died on their first `(deftest ...)`. `refer` itself was fine --
`(refer 'clojure.string :only '[join])` worked -- and so were
`select-keys`, `mapcat` and `apply`. The break was one expression:

    (:refer filter-opts)   ;=> nil, even though filter-opts is {:refer [join]}

`load-lib` guards the whole thing with
`(when (or use (:refer filter-opts)) ... (apply refer lib ...))`, so a
nil there means `refer` is never called at all. And `filter-opts` comes
from `select-keys`, which ends `(with-meta ret (meta map))`.

`apply` strips metadata from the thing being CALLED, so
`((with-meta {:a 1} m) :a)` was 1 and `get` was 1 -- only a keyword
applied to a wrapped map was wrong, because the ARGUMENT was never
stripped and the lookup happened in the wrapper. One `strip_meta`.

**Sets were never equal to each other either.** `(= #{1 2} #{1 2})` was
false: `deep_equal` handled instances, sequentials and maps, and a set
fell past all three to `gc_equal`, which compares pool slots. Both
references spell it the same way -- other must be a set, counts must
match, every element contained -- `APersistentSet.equiv` and
`PersistentHashSet`'s `-equiv`.

**What each was worth, measured.** These landed together and pull in
opposite directions, which is worth recording because the crash count is
the more tempting number to quote:

| | crashes | tests | pass | fail | error |
| --- | ---: | ---: | ---: | ---: | ---: |
| before | 13 | 193 | 681 | 175 | 237 |
| after `:refer` | 8 | 196 | 681 | 175 | 269 |
| after set `=` | 8 | 196 | 756 | 100 | 269 |

The `:refer` fix freed five namespaces from crashing and moved the pass
count by ZERO -- they went straight to erroring on the next missing
thing, which is why the errors rose by 32. Set equality touched no
namespace's ability to load and converted 75 failures into passes on its
own. A namespace leaving the CRASHED column is not the same as a
namespace passing anything, and the two are worth reporting separately.

**And one deviation this wrote down rather than fixed.** A collection
used as a map KEY or a set ELEMENT matches by identity, so
`(get {[1] 2} [1])` is nil and `(= #{[1]} #{[1]})` is false while
`(= {:a [1]} {:a [1]})` is true. Values go through `deep_equal`; finding
the key goes through `gca_get`, which is `gc_equal` on pool slots.
`gc_equal` already called this a separate decision -- DEVIATIONS 22 is
that decision written down, and fixing it means hashing collections
structurally so equal vectors reach the same HAMT bucket at all.

## The last sixteen forms: core.clj loads completely

`core.clj` had stopped somewhere for the whole life of this project.
It no longer does -- 724 of 724 -- and the two remaining walls are worth
recording because the first one lied about where it was.

**Form 708 named the wrong thing.**

    (try (load-data-readers) (catch Throwable t (.printStackTrace t) (throw t)))

The reported error was `no such member: map.printStackTrace`, so the
obvious move is to implement `.printStackTrace`. That would have changed
NOTHING: the handler re-throws, so the form fails either way. The error
named the HANDLER because the handler is what failed second;
`load-data-readers` is what failed first.

It failed on `(.. Thread currentThread getContextClassLoader)` answering
nil -- correctly, clotran has no classloader -- and then `.getResources`
on that nil, plus `enumeration-seq`. Both now answer EMPTY rather than
failing, which is not a stub: a host with no classpath genuinely has no
`data_readers.clj` files to find, so the empty enumeration IS the right
answer. `reduce` over nothing leaves the mappings alone, nothing throws,
and the form succeeds.

**Form 711 was `ArrayBlockingQueue`, and `Delay` behind it.** A delay is
a new object kind -- thunk, cached value, forced flag -- because
`delay` in core.clj is literally
`(new clojure.lang.Delay (fn [] body))`, and OBJ_LAZY could not stand in
for it: that caches a first and a rest and its forcing expects a seq.
The queue is a mutable box holding a vector, capacity accepted and
ignored, because a bound exists to make a producer wait and nothing here
waits.

**What the tail was worth.** `update-vals`, `update-keys`, `parse-long`,
`parse-double`, `parse-boolean`, `NaN?`, `infinite?`, and `delay` /
`force` / `realized?`. `clojure.core.reducers` also loads now, which
had been waiting on `Delay` -- libraries 14 -> 15.

**Two things this nearly got wrong.**

`Double/valueOf` pointed at the `double` CAST made `(parse-double "1.5")`
answer `0.0`, because `num_dbl` of a string is zero rather than an
error. A silent wrong answer, and worse than the missing member it
replaced. It needs a string PARSE, which is what `B_DBLVALUE` is.

And `parse-long` is written around a TYPED exception:

    (try (Long/valueOf s) (catch NumberFormatException _ nil))

`fail` produces `{:error "..."}`, an ordinary map, and `catch_matches`
only lets `Throwable` and `Exception` catch one of those -- so the
failure escaped the function whose entire purpose was to contain it, and
`(parse-long "x")` was an error instead of nil. `fail_as` throws a named
class for the handful of places core.clj reads an exception TYPE as an
answer.

**`tap>` is the one thing in the tail that still does not run.** It
forces a delay that constructs a `Thread`. That is a real seam, not a
missing member, and it fails loudly.

**What it did NOT move much.** The suite went 756 -> 766 passing, and
111 failing against 100 -- more tests reach further and some of them
then fail. Namespaces with a passing assertion, 18 -> 19. The number
that moved is core.clj itself, 707 -> 724, and the seven functions that
now exist.
