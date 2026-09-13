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

## Toolchain: flang is primary, gfortran is a cross-check oracle only

Pinned to flang 23.1 (`Makefile`), not gfortran. On every actual
compiler bug this project has hit, flang came out ahead, and its
diagnostics have twice caught real mistakes in this code that gfortran
missed silently even at `-Wall -Wextra`.

gfortran stays installed for cross-checking: when something looks like
a compiler quirk rather than a bug in this code, building with both and
comparing tells them apart. **This does not make gfortran a second
target.** If a gfortran-only bug ever needs uglier or more convoluted
code to route around, the right call is to document it here and move
on -- not contort the source for a compiler this project deliberately
didn't pin to. Only take a fix if it's free (the same or clearer code
regardless of the bug); don't chase gfortran quirks as a default habit.

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
