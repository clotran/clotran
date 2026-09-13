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
from *outside* this repo against `bin/clotran` -- e.g. from this
repo's root:

```
python3 ~/jborden/mal/runtest.py --deferrable --rundir test/regression \
    step9_try.mal -- ../../bin/clotran
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
  compilers regardless.

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
