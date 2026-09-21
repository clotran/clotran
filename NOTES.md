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
was a clotran bug -- three of them, in the refcounted evaluator since
deleted, none a gfortran defect -- and until they were found gfortran
was the fast build rather than a trustworthy one.

When something looks like a compiler quirk rather than a bug here,
building with both and comparing tells them apart -- that is what the
second compiler is for, and the split above is a live example of it
working. Don't contort the source to route around a quirk in either
one: document it here and move on, unless the fix is free.

## Fortran gotchas catalog (for next time)

- `class(*)` copy semantics: see above. (Historical: this is also why
  strings used to be wrapped in a `cons_string` type rather than stored
  as bare `class(*)` -- gfortran's built-in copy helper crashed on a
  zero-length `character` as a polymorphic dynamic type. Moot now that
  `class(*)` is gone from the value representation, but a real,
  reproducible gfortran bug, confirmed absent on flang.)
- `impure elemental` needed on both `FINAL` and `assignment(=)` to
  cover arrays, not just scalars.
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
  same pattern the reader's `read_items` already used).

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
one: **class names are keywords** (a bare class name in source
evaluates to the keyword of the same name), so the relationships
between them can live in the same global hierarchy `derive` already
maintains, and clojure.core's own `isa?`, `parents`, `ancestors` and
`prefer-method` work on host types unchanged. The host owes only the
lookup -- today `host_super` in Eval.f90, which PLAN.md step 3 folds
into the one host table.

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

`ponytail`: dispatch is linear over the method table on every unmatched
value, where real Clojure memoizes the winner. A cache cleared by
addMethod/removeMethod is the upgrade if a hot multimethod shows up.


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

This also silently fixed a mystery: several of our own checks passed in
the REPL but failed inside the suite, because an earlier check
(deliberately) shadows `first` in `user`, and core.clj's own functions
were picking up the shadow.

## Running real Clojure's own test suite

`test/clj/clojure/test_clojure/` holds test files vendored from
clojure/clojure, run by `scripts/run-clojure-tests` (and its parallel
twin), one namespace per process so a hard failure cannot hide the
others. Language semantics are judged by Clojure's own assertions; the
hand-written checks in `test/f/*_test.f90` belong to the *host* -- the
collector, native arrays, the Fortran gotchas catalog -- which upstream
cannot test. PLAN.md step 2 is the plan to DERIVE a language suite from
this tree rather than run all 67 files against a JVM-shaped
denominator.

**A Fortran gotcha worth its own line**: `.and.` does not short-circuit.
Writing `head == "ns" .and. .not. resolves_to_macro("ns", macro_val, env)`
called `resolves_to_macro` for *every list form in the program*, and its
`intent(out)` argument clobbered the macro being expanded. Nested `if`s,
not compound conditions, whenever an operand has a side effect.

## Source positions: where a form came from

Built in the pre-GC evaluator and NOT carried into `clotran`, whose
reader has no positions at all. Kept because PLAN.md step 5 reproduces
this design on the analysed tree, and the three choices below were
made once already and should not be re-argued.

Every list form recorded the line, column and file it was read from,
and where it ENDED, so errors said `(/path/file.clj:6:3)`. Three design
choices worth recording:

**Positions live on the list node, not as metadata on every value.**
Real Clojure attaches `:line`/`:column` as form metadata, which means a
map allocation per form; over ~11k lines of bootstrap that is a lot of
maps, and only list forms are ever what an error or a stack frame
points at. Three integers on the node cost nothing to copy. On the
analysed tree they belong on the node. `(meta form)` synthesises
`{:line :column :end-line :end-column :file}` on demand, so core.clj's
own `(meta &form)` -- which `fn` uses -- still works.

**End positions, not just start.** Line-only positions give a
gdb-style debugger; start-and-end give sexp-level highlighting, which
is what makes CIDER's debugger pleasant. The reader already knows where
the closing paren is, so recording it now is free and retrofitting it
later would not be.

**Positions are carried through macro expansion.** The macro machinery
rebuilds lists constantly, and the first version dropped the position
every time -- so every form inside a
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

- `Eval.f90`: `has_error`, `last_error`, `ev_depth`/`ev_limit`,
  `gensym_id`, `qq_depth`, `reify_id`, `proxy_id`, the type table
  (`types_root`), the `binding` frame stack (`binding_stack_root`),
  the thrown value
- `GC.f90`: the value stack (`vstack`/`vs_top`) and the mark stack
- `LispReader.f90`: its error state
- `Namespace.f90`: the current namespace -- this is `*ns*`, which
  real Clojure makes thread-local

None of this was moved into a context type when the GC evaluator was
built, despite this section saying it was cheap then. PLAN.md step 5
does it as part of the frame stack.

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
not from the armchair.

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
and `maybeClass`. Both are answered nil by the host --
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

One consequence worth naming: a native buffer is a LEAF to the
collector -- it holds Fortran scalars, and there is nothing in it to
trace. A `:value` array therefore does NOT live in a native buffer:
its elements are clotran values and go in a GC run where they are
traced for free (see "Native arrays, ported to the GC heap" below).
Native buffers hold only Fortran scalar kinds, which makes the leaf
property an invariant.

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


## The GC: design and construction

Moved out of PLAN.md, which is for work not yet done. This is why the GC
and the data layer are the way they are. The refcounted evaluator's
crash investigations that used to follow are gone with it; the method
they taught survives in one line: two sampled runs are not evidence of
absence for a 1-in-6 bug.


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
- [x] **The value stack exists and is tested.** Built
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

      **`src/f/PersistentVector.f90`** -- the same 32-way trie as
      `PersistentVector.f90`, with every reference a GC handle instead
      of a refcounted pointer. `gcv_empty/count/nth/conj/assoc`, path
      copying unchanged, sharing untouched children exactly as before.
      Nothing uses it yet.

      The vector went first on purpose: it is the most intricate
      structure in the layer, and it is where the refcounted
      evaluator's use-after-free lived. Check 6a is
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

      **`src/f/PersistentList.f90`** -- the persistent list, same treatment.
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

      **`src/f/PersistentArrayMap.f90`** -- the array map, and `gc_equal` in the
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

      **`src/f/PersistentHashMap.f90`** -- the hash trie the map promotes into,
      plus `gc_hash` in the collector, mirroring `PersistentHashMap`'s
      `hash_of`: same mix32, same FNV-1a over the text, same tag mixed
      in so `"a"` and `\a` do not collide. It has to agree with
      `gc_equal` or a trie stores one key twice, so text hashes over
      CONTENT exactly as gc_equal compares content.

      Collision buckets **reuse PersistentArrayMap**: a set of keys sharing a
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

      **`src/f/Env.f90`** -- the lexical environment: a chain of
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
      covers and Env check 5 exercises.

      **`src/f/Assoc.f90`** -- the map clotran actually uses: array
      map to 8 entries, hash trie beyond, one-way, matching Clojure.
      It is a THIRD module rather than logic inside PersistentArrayMap, and that is
      forced rather than stylistic -- PersistentHashMap already uses PersistentArrayMap for
      collision buckets, so PersistentArrayMap using PersistentHashMap would be a module cycle
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

      **`src/f/Printer.f90`** -- values back to text, written before
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

      **`src/f/LispReader.f90`** -- text into the heap, and with the
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

      **`src/f/Eval.f90`** -- a core evaluator, and the module that
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

      Scope at that point was the core, deliberately:
      quote/if/do/def/let*/fn*/loop*/recur/defmacro*/quasiquote/try*/
      throw, twelve primitives, closures, varargs, multi-arity. It has
      since grown into the whole evaluator, form by form of core.clj.

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

      **Namespaces and Vars** (`src/f/Namespace.f90`), which closes
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

      1. PersistentList's empty-list singleton -- caught by check 4c, fixed by
         re-checking the slot.
      2. Namespace's registry -- `gc_global_set` on a stale index is
         silently a NO-OP (out of range), so the registry was never
         re-registered and every namespace lookup failed.
      3. Eval's thrown value -- worse: a stale index that lands back
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

      An internal error is catchable too, and arrives as an
      **exception object** -- class `RuntimeException`, the message
      as `.getMessage` -- not a bare string. A string would be
      indistinguishable from `(throw "x")`, so a handler that wants to
      re-raise anything it does not recognise would have no way to
      tell them apart. clotran's older evaluator uses a string here;
      this is a deliberate improvement on it rather than an accident
      of the port. Checks 14i/14j are that distinction. (It was the
      map `{:error "message"}` until `ex-message` and `(catch
      RuntimeException e ..)` needed to work on one; see "The
      language's leftovers" below.)

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

      `clotran` (`src/f/main.f90`) is a REPL over the new stack,
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

      `clotran some.clj` now loads files named on the command line,
      so the real core.clj can be tried against this evaluator and the
      first error it reports IS the next thing to build. Two bugs of
      mine had to go first:

      - **The file loader was O(n^2).** It appended line by line, and
        each `//` builds a whole new string. On an 8371-line file that
        is not slow, it is indistinguishable from a hang. Now one
        `inquire(size=)` and one stream read. The old reader carried
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
      representation, under a collector running at maximum paranoia.
      Closure and atom need no module of their own. The switch itself
      -- the evaluator onto the value stack, the old backing types gone
      -- followed, and the refcounted evaluator was deleted on
      2026-09-19.
---


Everything after this step is paid for by the edit-test loop, so make
the loop cheap before starting on the expensive steps.

- [x] **4a -- DONE.** `scripts/run-clojure-tests` drives `clotran`
      with core.clj loaded. It did drop hard at first, which was the
      signal being asked for; see "Where we are" for the current numbers.
      Its summary-line parser also had to learn that maps print with
      commas now, which the old evaluator did not do.

      The suite is Clojure's own assertions over the real core.clj
      functions, where our hand-written oracle was 107 cases someone
      typed in. It forced two things, both wanted:

      - **Retiring the refcounted evaluator.** Done 2026-09-19. Keeping
        two evaluators meant every fix had to be considered twice.
      - **Startup cost becomes the bottleneck.** The runner launches a
        process per namespace, so ~40 namespaces x 1.68s is around a
        minute of pure loading per run. Annoying, not blocking -- but it
        is what finally makes 4c worth doing.

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
Eval, `registry`, `current` and `ns_var` in Namespace, and
PersistentList's `empty`. The type table was the ninth, and `gc_global_new`
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

`fail` produced `{:error "..."}`, an ordinary map (now a
RuntimeException object), and `catch_matches`
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

## The reader collected the form it was building

`(case* 2 0 0 :other {2 [99 :wrong]} :compact :int #{2})` read back as
`()`. No error, no warning -- the reader returned an empty list for a
valid form and the evaluator dutifully evaluated it.

It surfaced while porting native arrays, which added about seven objects
to the bootstrap and pushed one `gc_init(64)` test over a heap-growth
threshold during a read. Nothing about arrays was wrong. The bug had
been there the whole time, waiting for the heap to fill at the wrong
moment.

**The defect.** Three of the reader's collection literals dropped the
caller's `roots` on their own allocations:

    items = read_seq(text, pos, "}", .true., roots)   ! forwarded
    m = gca_empty([vs_get(base + 1)])                  ! lost

Each of those functions keeps its OWN values on the value stack, which
the collector scans, so they look correctly rooted in isolation. The
caller's values are plain Fortran locals, reachable only through the
array it passed in. Drop it and a collection frees the form being built
around you.

Seven sites across three readers:

| form | reader | was |
| --- | --- | --- |
| `#{...}` | `read_set` | broken |
| `^meta` | `read_meta`, including its nested `read_form` | broken |
| `#(...)` | `read_anon_fn` and `rewrite_percent` | broken |
| `{...}` | `read_map` | already correct |
| `[...]`, `(...)` | `read_seq` | already correct |

`read_map` threads `roots` through every allocation and is the shape the
other three now copy.

**Why it survived.** `reader_test` already had a torture read test --
and it reads a flat list of sixty integers, which reaches none of the
collection literals. `eval_test`'s `ev` turns torture OFF during the
read on purpose ("reading and setup are not the subject"). So the one
place that would have caught this had a hole exactly its shape.

`check_nested_literals_under_torture` closes it: a set, a map, a vector,
a metadata form and an anonymous fn, each read under torture inside an
enclosing list. Against the unfixed reader it fails on exactly set,
metadata and anonymous fn and passes on map and vector -- which is the
independent confirmation that the diagnosis was right and that
`read_map` was never part of the problem.

**The lesson worth keeping.** Two rooting disciplines coexist here: the
value stack, which the collector scans, and explicit roots arrays, which
it only sees if you pass them. A function that uses the first and
forgets the second is correct about itself and wrong about everyone who
called it. That is invisible until the heap fills at the wrong moment,
which is what torture mode is FOR -- so a code path that torture never
reaches is a code path with no rooting test at all.

## Native arrays, ported to the GC heap and named for what they are

Native arrays existed only in the pre-GC evaluator, since deleted. The
shipping evaluator had no `aget`, no `aset`, no `make-array`, no
`alength` -- eight occurrences in the evaluator being retired, zero in
the one `./clotran` runs. The capability the whole project is for did
not survive the GC port, and nothing recorded that.

Worth noting how it stayed invisible: our tests are per-module and
NativeArray did not exist to have one, Clojure's suite never reaches
a Fortran array, and core.clj never calls one. A feature living only in
the evaluator scheduled for deletion is outside every scorecard here.

**The port is not a copy.** The buffer cannot live in a gc pool -- four
scalars and no pointer is the whole reason copying a `gc_value` is
cheap, a pool of them cannot hold `real(8)`, and a pooled buffer could
not be handed to `dgemm` anyway. So the buffer lives in a registry, the
object holds an integer handle, and the collector never touches it.
That is exactly what `Regex.f90` does with an ICU pattern, and it is
the reason PLAN insists the collector be non-moving.

**Two things that needed deciding.**

A `value` array does NOT go in the registry. Its elements are clotran
values holding heap references; outside the heap they would be untraced
and freed out from under the array. They go in a GC run in slot 1,
which `push_mark` already walks, so tracing costs nothing and the
registry owns only buffers the collector has no opinion about.

The sweep had no finalizer. It zeroed the kind and moved on, so
anything owning storage outside the heap leaked -- which DEVIATIONS 14
already recorded for Matcher without anyone connecting the two. There
is now a hook, registered by procedure pointer because `GC.f90` sits
below everything (the `gcp_set_forcer` inversion, and a MODULE
procedure because flang segfaults on host-associated callbacks). The
Matcher leak is fixable the same way now, and DEVIATIONS 14 says so.

**They are `fortran/make-array`, not `make-array`.** core.clj defines
its own, so a `clojure.core` binding is shadowed the moment it loads --
but that is the weaker reason. These take a Fortran KIND NAME rather
than a class, they are column-major, their lower bounds are per
dimension, and the buffer can go to `dgemm`. Borrowing Clojure's names
would have claimed they were the same thing. SEAMS asked for
`fortran.*` to mean a real Fortran object crossing a real boundary;
this is the first thing in it.

Clojure's own `aget`/`alength` over these are deliberately NOT done:
they route through `clojure.lang.RT/alength` and `Reflector/prepRet`,
which is compatibility rather than interop, and a different job.

**The check that matters** is `28e` in `eval_test`: allocate an
array, collect while it is rooted and confirm the buffer survives, drop
every reference, collect again and confirm the registry slot is freed.
A leak here is invisible from Clojure, so it is checked against the
registry's own count rather than through any value. `28d` is the half
people forget -- a finalizer that frees too eagerly looks identical to
a working one until something reads a freed buffer.

## The superlinear reduce: two causes, neither the one guessed

`(reduce + (range 16000))` took 161 seconds and 100,000 did not finish
in fifteen minutes, while `loop`/`recur` over the same counts was
linear. PLAN.md had guessed uncached protocol dispatch or lazy-seq
realisation. Both guesses were wrong, which is the reason the rule is
to instrument first.

**What the instruments were.** `CLOTRAN_STATS=1` prints evaluations,
allocations, collections and marks at exit; run at n = 1000, 2000,
4000, 8000 it showed evaluations and allocations perfectly linear
(1832 evaluations per element) and collections jumping from 883 to
2960 between 4000 and 8000, with marks 130M -> 622M. `sample` on the
running process gave the call tree. `CLOTRAN_TRACE_MACRO=1` names each
expansion on stderr; diffing a run against startup alone attributed
three `let`s and one `if-let` to every element.

**Cause 1, the collector's growth policy.** A pool grew only when a
collection freed nothing at all. `reduce` holds the head of the seq it
is reducing -- it is `reduce`'s own argument, and Clojure's compiler
clears that local after last use where a tree-walker keeps every
binding until the frame returns -- so the live set grows with n. When
the live set is nearly the whole pool, each collection frees a sliver,
the sliver is used up in a few hundred allocations, and it collects
again, marking the entire live set every time. Quadratic. The policy
is now the standard one: grow when a collection leaves the pool more
than half live, and grow the triggering pool until it can absorb the
whole live set (`last_marked`) before filling again, so collections
are proportional to allocation divided by live and marking is
proportional to allocation. A first version put the half-live test
inside the growth loop, which never terminates (doubling makes it
more true); it is outside it.

**Cause 2, and the larger one: analysis skipped map literals.**
`mx_walk` descended into lists and vectors and treated everything else
as a leaf. `extend` takes its method bodies as a MAP -- `(extend Object
InternalReduce {:internal-reduce (fn [s f val] (loop ... (if-let
...)))})` -- so every protocol method installed by `extend-type` or
`extend-protocol` kept its macros and re-expanded them on every call.
87% of a reduce was inside `expand_macro`. With maps and sets walked,
evaluations per element went 1832 -> 60, reduce over 100,000 runs in
17 seconds, and startup fell from 7.2 s to 4.1 s because core.clj's
own protocol installations were paying the same tax at load.

Neither cause is visible to any scorecard, and both had been there
since the GC evaluator was built.

## The analysis pass: nodes, frames and flat closures

Until 2026-09-19 clotran walked raw S-expressions at every evaluation:
each list form re-decided whether its head was a special form (a
24-way string cascade), a macro, host sugar or a call; each free symbol
was resolved against whatever `*ns*` was at that moment, patched by a
`__defining-ns__` binding in every closure's environment; locals were
name -> value maps chained per frame. `analyze.inc` and `exec.inc`
replace that with the two halves every real Clojure has.

**Analysis** (`analyze_top` -> `analyze`) runs once per top-level form
and produces OBJ_AST nodes: i1 the kind (`N_IF`, `N_CALL`, `N_FN`, ...),
i2 an integer operand, slot 1 children, slots 2-3 payloads. Macros are
expanded as they are met (a local shadows a macro, as
`Compiler.isMacro` has it), syntax-quote is expanded here too, and
every symbol is resolved once: a local to a frame slot, a Var to the
Var itself, `Class/field` to its value, a class literal to its keyword.
An unqualified symbol that resolves to nothing is an analysis error,
as in Clojure; a qualified one is deferred (DEVIATIONS 32). A
top-level `do` is not analysed as a unit -- `Compiler.eval` evaluates
its subforms one at a time, so an `(ns ...)` earlier in the same `do`
is in force for the rest -- and `N_TOPDO` does the same.

**Scopes** are GC objects (K_SCOPE blocks chained inside a K_FNINFO
per fn) because the analyser allocates constantly and everything it
holds must be rootable. A fn reserves consecutive slots for its
parameters; a `let`, `loop`, `letfn` or `catch` reserves slots in the
same fn's frame; shadowing is a new binding in a child block. A `loop`
reserves all its slots first and binds each name only after its init
is analysed, so the slots stay consecutive for `recur` while the scope
stays sequential.

**Closures are flat.** When an inner fn refers to an outer local,
`lookup_local` allocates a slot in the inner fn and records a capture
pair (outer slot -> inner slot) on the template; making the closure
COPIES those values. Locals are immutable in Clojure, so copying is
exact, and it is what makes a closure made in one loop iteration keep
that iteration's values after `recur` has rewritten the slots. The two
rebinding forms are handled explicitly: `recur` evaluates its
arguments and then writes the target's slots and returns a marker the
enclosing loop or fn body reads; `letfn` makes every closure, stores
them, and copies their captures a second time so each sees the others.

**A template** (slot 2 of `N_FN`, slot 1 of a closure) is
`[name arities captures nslots selfslot]`, each arity
`[nfixed variadic? first-slot body]`; one frame of `nslots` serves
every arity. `invoke_closure` picks the arity, fills parameters,
captures and the self name, and loops on the body while it recurs.

**Nothing bridges.** `eval_dot` and `eval_new` took forms for a
while after the walker went; the executor evaluated their parts and
handed them `(quote v)` forms, which `gce_eval` re-analysed back into
values. They now take the evaluated target, member name and argument
vector directly, and `quoted`, `quoted_list`, `apply_forms` and
`eval_forms_vec` went with the bridge. The old walker itself is gone:
every `eval_*` routine that took a form and an environment,
`make_closure`, `bind_params`, `select_clause`, `mx_walk`, and the
`__defining-ns__` lookups in `resolve_var`. A static call on a host
class, which is most of what core.clj does, is resolved to its native
at analysis and never reaches `eval_dot`. `range` and `iterate` cells
no longer close over an environment either: a pending tail carries
`[lo hi step]` or `[f x]` and `gce_force` builds the next cell itself.

**What it cost to find.** Three things the old walker never looked at
surfaced the moment fn bodies were analysed at definition: a `set!` on
a host static field inside `set-agent-send-executor!`, `monitor-enter`
from `locking`, and `%1` under a type hint that the fn-literal rewrite
had not renamed. Each had been latent for the life of the project.

## dgemm: the premise, tested

The project's claim is that hosting Clojure ON Fortran makes calling a
Fortran library an ordinary call, where bridging from the JVM makes it
a descriptor to fabricate and a copy to pay for. Until 2026-09-19 no
Fortran library had been called at all. `fortran/dgemm` is the first.

netlib's reference BLAS is vendored (`src/f/blas/`) rather than a
system BLAS linked, because a proof of the calling convention should
build identically everywhere; three F77 files compile under gfortran
and flang without a flag. `gcna_dgemm` in NativeArray.f90 selects the
`real(dp)` type of each registry buffer and calls `DGEMM('N','N', m, n,
k, 1, a, m, b, k, 0, c, m)`: the buffer is a contiguous rank-1
`allocatable`, the dummy is `A(LDA,*)`, and sequence association hands
the address across with no temporary -- which NOTES already established
for `a(*)` dummies when the registry was designed. The builtin above it
checks kinds, ranks, inner dimensions and refuses slices, so `xerbla`,
which STOPs, is never reached.

The test multiplies a 2x3 by a 3x2 and compares against the product
computed in Clojure over `aget` and against [58 64 139 154]. It is a
host check in language_test.clj, not an oracle case: real Clojure has
no `fortran` namespace to answer it.

What this did NOT settle, deliberately: kinds other than real8, the
transpose flags, in-place accumulation (beta), and anything a generated
binding would need to read from an `interface` block. One routine by
hand first; PLAN.md step 7 is the generator, and ChemSol is what it is
for.

## Source positions, second time: on the list cell, read by the analyser

The pre-GC evaluator recorded line, column and file on every list
cell; the port lost it ("Source positions: where a form came from",
above, is that design). It is back, smaller. `OBJ_CONS` had a free
integer, i2, and the reader puts the opening paren's character offset
there, packed with a file id (`file-id * 2^26 + offset`). Line and
column are not stored: `gcr_begin_file` indexes the newlines of a
file once and `gcr_position` recovers them by binary search when an
error needs them, which is rarely, rather than on every list read.
The analyser copies the position onto the node it builds for the
list; a macro's expansion keeps the position of the form that was
written, because the expansion's fresh cells have none of their own
and the node already has one. An error appends `  at file:line:col`
from the innermost node that has a position, once -- analysis errors
from the form, run-time errors from the node -- and every enclosing
node sees the mark already there and leaves it.

End positions are not recorded yet. The old design argued for them
(sexp-level highlighting in a debugger); when the debugger's frames
exist they are one more integer on the cell.

## The call stack

`push_frame`/`pop_frame` bracket every closure invocation
(`invoke_closure`); the executor sets `pending_site` from the call
node's position just before `apply`, so a frame is the closure entered
and where it was entered from. `fail` and `throw` call `capture_trace`
at once -- the stack must be read before the error unwinds it -- and
the REPL and loader print it after the message:

    Divide by zero  at src/clj/clojure/core.clj:1029:10
      at clojure.core// (p3.clj:1:17)
      at clojure.core/inner (p3.clj:3:3)
      at clojure.core/middle (p3.clj:5:3)
      at clojure.core/outer (p3.clj:6:1)

Each frame names the callee and the site in its caller, which is the
information a call site has; a frame does not know which line of its
own body is executing, because no position is recorded on entry to a
node, only consulted on error. `recur` pushes nothing, so a loop of a
million iterations is one frame, and a trace does not pretend
otherwise. The frames are not GC roots: a closure on the stack is in
its caller's value-stack slot for as long as the call lasts.

This is the CallInfo frame array PLAN.md's debugger section asked for.
What it is not yet: per-thread (it is a module array), a
`StackTraceElement` (DEVIATIONS 31), or a breakpoint.

## Locals clearing, and who was holding the head

`(reduce + (range 100000))` peaked at 645 MB and `(into [] (map inc
(range 100000)))` at 1.16 GB, with the collector doing its job: the
realised seq was LIVE. Two things held its head for the length of the
reduce, and neither was the loop that walks it.

The first was every frame on the way down. `reduce`'s own `coll`
parameter, `coll-reduce`'s `x` in the protocol dispatch, `seq-reduce`'s
`coll`: each frame keeps its slot until it returns, and it returns only
when the reduce is over. Clojure's compiler clears a local after its
last use for exactly this reason. The analyser now does the same: a
backwards liveness pass over each fn body (`liveness` in analyze.inc)
finds, on every path, the read after which a slot is never read again,
and marks that N_LOCAL; the executor nils the slot after that read. The
first version marked only the textually last read, which in
`(if p (f x) (g x))` is the one in the else branch -- the protocol
dispatch takes the then branch, and the head stayed put. Alternatives
are processed against the same after-set and merged, so both branches
clear. Reads inside a loop body are never last (the body runs again),
a body that recurs to its own fn is left alone (its captures are not
rewritten by the recur), and captured slots are counted as read when
the closure is made.

The second was the argument vector. The executor builds a call's
arguments into a vector, roots it on the value stack, and calls
`apply`; `invoke_closure` copies the values into the new frame. That
vector stayed rooted in the caller's slot for the whole call, holding
every argument -- so clearing the callee's slot changed nothing. The
caller now hands the vector over: it nils its slot just before `apply`,
which roots the vector at once, and `invoke_closure` drops its own root
as soon as the frame is filled. No allocation happens between the nil
and the next root, which is the one condition that makes this safe.

Both cases now stay at the 152 MB the loaded core.clj occupies. That
baseline is stage 3's business.
## ChemSol: main.f90 as a pipeline

The goal NOTES opened with -- `(-> mol readopt dg-ld solvout)` calling
real ChemSol code -- runs, and its output is the original program's
byte for byte on the three reference inputs (`scripts/chemsol-check`).
`examples/chemsol.cljf` is `main.f90` rewritten; the library is vendored
untouched.

**The binding.** `ChemSolBind.f90` holds one record, `cs_args`, with a
field per argument of `readopt`, `dg_ld` and `solvout`, named as the
routines name them. `Eval.f90` fills it from a map (`cs_from_map`),
calls the routine, and assoc's the written scalars back (`cs_to_map`).
Arrays never leave the registry: `gcna_real8_ptr` hands the binding a
contiguous pointer into the buffer and the routine's `x(*)` or
`x(3,*)` dummy takes it by sequence association, so what `readopt`
writes into `rpi` is what `dg_ld` reads a call later, and what the
driver can `aget` afterwards. Nothing is copied at any point.

**What the library dictated.** Three things a generator will have to be
told per routine, found by running rather than reading:

1. `readopt` reads from TWO units, and one of them is the .cs input
   itself -- the optional `rp` block at its end -- at whatever position
   main.f90's own reads had left it. The binding opens unit 45 on the
   input and skips the lines the driver consumed (`:input-skip`).
   Without that the first run died with an EOF on `fort.45`.
2. `dg_ld` has 400 MB of fixed-size locals. `size build/chemsol.o` went
   from 53 KB of data to 411 MB the moment `-frecursive` came off, and
   the SIGILL (exit 132) on the first call went with it. The original
   program never had the flag; the Makefile rule for `chemsol.f90`
   filters it out, and only there.
3. `ran2` keeps its seed in module variables. A second calculation in
   one process gets the continuation of the sequence, not a fresh one.
   The check runs one process per input.

**What the driver had to reproduce.** Formatted I/O is most of it:
`(a13)` for the name, `(17x,f10.4)` for the pcm charges, `(f9.2)` in
the header, and the blank lines Fortran's `/` edit descriptors emit.
`format` with `%9.2f` matches; the rest is `subs` and padding. The
charge-consistency and atom-type checks are two small functions.

**What did not need doing.** No clotran bug was hit. The one addition
to the host is `clotran-slurp`, since core.clj's `slurp` is written
over `java.io`.

## The JVM surface, as data

`static_member` was 550 lines of `if (cls == ...) ... case (mname)`,
`instance_member` 300 more, and `is_host_class` a third list of class
names that had to agree with the first by hand. It did not always:
`Ratio` was a host class with no members, `Boolean/TYPE` worked only
through the run-time keyword path because `Boolean` was not in the
list, and `Integer/TYPE` and `java.lang.Integer/TYPE` evaluated to
two different keywords depending on which spelling a file used.

Now `src/f/hosttable.inc` holds a `parameter` array of rows -- class,
member, builtin id (or a constant kind and its value), print name --
and the three functions are lookups over it. The class list IS the
set of classes with rows. A name is canonicalised once (`host_canon`:
`java.lang.` prefixed onto a bare name, the five short names the
libs import mapped), so both spellings land on one row.

The audit that decides what is a row is `scripts/audit-host`. The
finding was that nearly everything already there was reached: six
members were not, and they are gone. That is worth saying because
the expectation going in was a large unreached surface, and the
number says the table had been kept honest by the load failures that
added each row.

The constants are constant expressions (`huge`, `tiny`, `epsilon`,
`exp(1.0_gc_dp)` are all allowed in a `parameter`); the three IEEE
non-finite values are kinds, because `ieee_value` is not.

The lookup is a linear scan of ~300 rows. It runs at analysis time
for a static member and once per unresolved instance member; nothing
has shown it in a profile.

## Reader conditionals, and what a file extension means here

`#?` came in as a request to make `.cljc` libraries portable to
clotran, and the design question was only what the nothing-case is.
LispReader.java returns the reader itself as a sentinel when no
branch matches, and every collection loop skips it -- the same trick
`#_` uses. This reader already treats `#_` as "another kind of space"
in `skip_ignorables`, so a conditional could not go there (it may
produce a form), and returning a sentinel value would have needed a
value that nothing else can produce. Two module flags do it:
`read_cond` sets `rc_nothing` or `rc_splice` on the way out, and the
caller that just read a form -- `read_seq`, `read_map`, the three top
levels -- checks and clears them. Any other caller (`'`, `^`, `@`)
requires exactly one form and fails through `cond_leaked`.

Unselected branches are read under `suppress_read`, which is where
`*suppress-read*` lives on the JVM: a `#js {}` in a `:cljs` branch is
read past instead of failing on the tag. That was the difference
between "reads .cljc" and "reads the .cljc files people actually
write".

The feature is `:cljf`, matching the extension, the way `:cljs`
matches `.cljs` and `:cljr` matches `.cljr`. `:clj` is not claimed:
it means the JVM, and a `:clj` branch that reaches for
`java.util.concurrent` is exactly the one clotran must not take.
`classpath_find` looks for `.cljf`, `.cljc`, `.clj` in that order; the
reasoning is in DEVIATIONS 33.

## `class` is a keyword, and `import*` finally does something

The open question was whether `(class x)` should answer the type tag
(`:string`) or the thing a class literal evaluates to (`:String`).
core.clj decided it: `(condp = (class x) String ...)` in pprint,
`(defmethod print-method String ...)`, `(extend-type String ...)` all
compare `class` against the literal, and they only work if the two are
the same value. So `class_name_of` maps each tag to the JVM class the
literal names, the tag went behind `clotran-type` where host.clj reads
it, and `host_super` is keyed by those names. There is no class
SYSTEM in this: 25 lines of table, and Fortran has no classes to
model. What there is, is the vocabulary core.clj was written in, and
we run core.clj unmodified.

Two bugs came out from under it, both of the same shape: a name
written SHORT under an import. `(ExceptionInfo. ...)` in core.clj gave
an error whose class printed as `:ExceptionInfo`, unequal to the
literal `clojure.lang.ExceptionInfo`; and pprint's pretty writer,
`(proxy [Writer IDeref PrettyFlush] ...)` under `(import [clojure.lang
IDeref])`, was not an `IDeref`, so `deref` handed the proxy back
instead of its fields, and `(alter @*out* assoc ...)` then wrote a map
into the proxy's TYPE slot. That last one presented as a run-time
error naming a different member every run -- `opts.ppflush`,
`try.ppflush` -- because `class_text` was reading a recycled node.
The instrumented message (kind, tag, the slot's kind) found it in one
run; the theories before it did not.

The fix is the one DEVIATIONS 17 had been asking for: `import*`
records `Short -> full.name`, globally, and one function `class_key`
spells every class keyword. The hand-kept HOST_IMPORTS table went
with it. String.split, String.replaceAll and
`System/identityHashCode` were added along the way because pprint
reached them next; they are host members, so they are rows.

## pprint, and what a proxy inherits

Once `class` agreed with the literal, pprint failed four more times,
each on a host contract the pretty writer assumed:

1. `(.split s "\n" -1)` -- String.split takes a pattern SOURCE and
   compiles it; only Pattern.split took a Pattern.
2. `(.replaceFirst s0 "\\s+$" "")` -- the same, for replaceAll and
   replaceFirst.
3. `(newline)` is `(.append *out* ...)`, and the pretty writer is a
   `(proxy [Writer IDeref PrettyFlush] ...)` that defines `write` and
   not `append`. On the JVM `Writer.append` is a concrete method of
   the superclass that calls `write`, so the proxy inherits it. Here
   an unknown member on an instance fell through to the host native,
   `clotran-append`, which knows StringBuilders and Fortran units and
   did nothing for an instance. So the newline was dropped, silently
   -- `(pprint [1 2])` printed `[1 2]` with no line end, and nothing
   errored. `eval_dot` now maps `append` to the instance's own `write`.
4. `(.write w \space)` on that path: `Writer.append(char)` calls
   `write(int)` with the CODE POINT, and the proxy's `write` is a
   `condp` on `Integer`/`Long`; a Character matched no clause. And
   the column writer hands `(int \newline)` down to the base
   `StringWriter`, whose `write(int)` must write the character, not
   the digits -- `"a10"` was the symptom.

Each was a silent wrong answer before it was an error, which is the
order CLAUDE.md warns about. The oracle now holds six `with-out-str`
pprint cases against `clj`; the seventh, a 12-entry map, was dropped
because a JVM hash map iterates in its own order and the text cannot
be compared, only the values.

## The executor is a loop

Stage 2's first half. `exec` used to be a recursive Fortran function:
every Clojure call was `exec` -> `apply` -> `invoke_closure` -> `exec`
on the Fortran stack, which is why recursion died near 700 deep
(DEVIATIONS 7) and why nothing could suspend an evaluation halfway.
`run` is a loop over an explicit continuation stack instead. A
`kframe` is one pending node: its values -- node, frame, an aux slot,
the argument vector being built, the restart node -- live in a
five-slot region of the value stack, so the collector sees them
without a new root; `pc` and `i` are its progress. A child is
evaluated by pushing a frame; when it finishes it delivers `val`,
and the parent's `pc` says what to do with it.

Two rules make it cheap. A node in TAIL position -- the branch an
`if` took, the last form of a `do`, the body of a `let`, the callee's
body after a call -- replaces the frame that was waiting for it, so
the stack holds only what is still pending. And a `recur` is a value:
the marker flows up through tail-replaced frames to the one flagged
as a restart point, which runs its body again in the same locals.

The call stack the debugger sees is deliberately NOT the continuation
stack. A tail call reuses the kframe but pushes the callee onto the
call stack and leaves the caller there (`nfr` counts what the frame
owes on exit), so a trace names every call the way the JVM's does,
and a tail-recursive function without `recur` overflows at the frame
limit rather than looping in constant space. Being faithful to
Clojure won over free tail calls; `recur` is the loop.

What still nests: the node kinds the loop hands to helpers (a def's
value, a throw's argument, a vector literal's elements, deftype
methods, dot forms) and every native that calls back into Clojure --
forcing a lazy seq, a multimethod's dispatch function, `swap!`'s
function. Each of those is a nested `run` on the Fortran stack,
bounded by ev_limit as before, and is the equivalent of Loom's pinned
frame. The vector, map and set literals moved into the loop next
(50,000 deep through `[(h (dec n))]` works); the natives are the real seam, and the answer there is the
context type, not more cases in the loop.

Two things bit on the way. The first cut popped the caller's call
stack entry on a tail call, and `language_test`'s trace check caught
it in one run: a trace of `st-c` -> `st-b` -> `st-a` had lost `st-b`.
And a runaway recursion at a 1,000,000-frame limit printed a
26-megabyte trace, built by quadratic concatenation, which is what
was actually slow: the limit is 200,000 now and a rendered trace
stops at 128 frames.

## -O2, and the check that optimisation folded away

The build had no optimisation flag at all: `-g` and nothing else,
from the first Makefile on. Adding `-O2` gave 2.7x across the board
-- reduce over 100,000 from 6.6s to 2.4s, a loop/recur iteration from
25us to 9us, startup from 2.3s to 1.0s -- for nothing. The profile
had said so: the top entries were `gc_vec`, `gc_nil`, `gc_vec_len`,
`gc_slot`, trivial accessors that only an optimiser inlines.

It cost one bug, and the oracle caught it in the same run:
`(multiply-exact Long/MAX_VALUE 2)` stopped throwing. `mul_overflows`
multiplied and divided back; signed overflow is undefined in Fortran
as in C, and at -O2 the compiler folded `(a*b)/b /= a` to false. The
add and subtract checks tested the sign of the wrapped sum, the same
mistake. All three now decide by RANGE before the operation, which is
defined everywhere and what Math.addExact's own source does too.

`scripts/bench` runs the same forms through a warmed `clj` and
through clotran and prints the ratio, because James was right that
"two orders slower" was a guess: it is two to four, and the biggest
gap, `(reduce + (range n))` at 8,800x, is the JVM's specialised
range reduce against our seq walk, not the interpreter alone.

What the profile says is next, in order: every call builds its
argument vector as a PERSISTENT vector, and this vector has no tail
optimisation, so each `conj` allocates and copies a 32-slot node --
95 heap allocations per reduce step, most of them that. Arguments to
a closure can go straight into its frame; arguments to a native can
fill one node. The raw-vector pool mallocs each vector's storage
separately (`allocate(items(n))`), which is the malloc/free in the
profile; a slab would remove it. Both are constant factors, and
constant factors are all an interpreter has until the JIT.

## The call path: no vector per call

The profile after -O2 still said `gc_vec`, `node_assoc`, `gcv_conj`:
every call built its argument vector by `conj`, and this persistent
vector has no tail, so each conj copied a 32-slot node -- 95 heap
allocations per step of `(reduce + (range n))`. Two changes, both in
the executor's N_CALL frame:

- The callee is evaluated before its arguments, so it is known when
  they are. A node closure with a fixed arity of the right count gets
  its FRAME allocated then, and each argument is written into its
  slot as it arrives (`mode 2`); `bind_captures` finishes the frame
  and the same kframe becomes the body's. No argument vector exists.
- Everything else -- a native, a multimethod, a keyword, a variadic
  arity -- gets one vector built as one node (`gcv_build`) and filled
  in place (`gcv_put`). Literals and `exec_args` use the same.

And `gc_nil()` is a constant, `nilv`: it was 631 samples of function
calls clearing slots.

Per reduce step: 95 allocations -> 44, and `scripts/bench` moved
every ratio: fib 253x -> 142x, loop/recur 863x -> 475x, `into`
2296x -> 1127x, plain recursion 151x -> 118x. What is left per step
is structural: a malloc per raw vector (`allocate(items(n))` in
`gc_vec`, so every frame and every node is a malloc/free pair), the
frame itself, and 79 node evaluations, which is what interpreting
core.clj's seq-reduce loop costs with no inlining. A slab under
`gc_vec` and a native reduce over native ranges and vectors (which is
what LongRange.reduce and PersistentVector.reduce are on the JVM)
are the next two constant factors; past them the gap is the JIT's.

## The slab, and the 101 slots every frame carried

`gc_vec` allocated each raw vector's storage with its own
`allocate(items(n))`: a malloc and a free per frame, per vector node,
per argument vector. The profile after the call-path change was
malloc, free and memset. Now every run is a slice of one arena,
`vec_store`, handed out in power-of-two size classes with a free
list per class threaded through the first slot of each free run;
offsets survive the arena doubling, which pointers would not. All
twelve accesses were inside GC.f90, so nothing else changed.

The slab then made two things visible that malloc had hidden.

First, the collection trigger. The node pool collects when its node
COUNT fills, and grows when a sweep frees less than half of it. With
the arena, a run is 1 slot or 128, and the node count says nothing
about slot volume; the arena reached four times the live size. The
first fix -- collect when the arena would grow, and double it if the
sweep freed less than half -- looped: the node pool's own growth rule
ran after every arena-triggered collection and doubled the pool each
time, and `grow_vec` was the hot function in the sample. The second
-- double the arena when a sweep freed little -- took it to 67M slots
for 4.6M live, because "freed little" is what fragmentation across
size classes looks like. What holds is the classic rule, applied to
SLOTS: collect when as many slots have been handed out since the
last collection as twice what it found live, and otherwise let the
arena grow.

Second, and the one that mattered: 217,018 free runs of 128 slots at
exit. Frames. `CLOTRAN_TRACE_MACRO=1` now reports a template asking
for more than 64 slots, and every function did -- a one-argument
`(fn [n] ...)` had a 110-slot frame. `new_fn_scope` set the fn-info
object's `i1` to K_FNINFO, 101, as a kind tag, and `reserve_slots`
uses `i1` as the slot counter, so every frame in the system began at
slot 101. Nothing ever read the tag. The counter starts at zero now,
frames are the size of their locals, and the numbers moved more than
any change today: startup 1.0s -> 0.62s (2.3s this morning), reduce
over 100,000 1.85s -> 1.42s, a loop/recur iteration 5.8us -> 4.6us,
fib 20 0.12s -> 0.084s, memory after core.clj 280 MB -> 168 MB.

Instrument before theorising, again: the arena counters and the
per-class free-list report under CLOTRAN_STATS found both in one run
each, after two wrong policies written from the armchair.

## :inline is part of the language, and we were not honouring it

core.clj gives 129 definitions `:inline` metadata -- `+`, `-`, `<`,
`inc`, `zero?`, `aget`, `nth` and the rest -- a fn from argument
forms to a replacement form, with `:inline-arities` saying which
counts it covers. Compiler.analyzeSeq applies it right after
macroexpansion (`isInline`): `(+ a b)` never calls `+`, it becomes
`(. clojure.lang.Numbers (add a b))` at compile time. clotran ran
every one of those as a closure call: frame, call stack entry, a
second call from the body to the static native.

`inline_fn` in analyze.inc is `isInline`: resolve the head to a Var,
read `:inline` and `:inline-arities` from its metadata (the metadata
is evaluated at def time, so the fns are real), apply the predicate
to the argument count -- a set, `#{2}`, is callable, as on the JVM
-- and if it passes, apply the inline fn to the argument forms and
analyse what comes back. The static call it produces resolves to the
native at analysis (analyze_dot), so the arithmetic in a loop is one
node. `preserveTag` is skipped: a :tag is a hint nothing here reads.

`scripts/bench`: loop/recur 361x -> 194x (2.6us an iteration), fib
94x -> 58x, plain recursion 69x -> 44x, the map-building reduce
115x -> 100x. `(reduce + (range n))` stayed near 4,600x, because its
cost is `first`, `next` and the range cell per element, not the add:
that is where the JVM runs LongRange.reduce in Java, and where a
native reduce over native ranges and vectors is the faithful next
step.

## reduce is host code on the JVM too

`(reduce + (range n))` stayed at 4,600x after everything else because
none of it was arithmetic: per element, core.clj's seq-reduce called
`first`, `next` and `reduced?` as Clojure functions and the range
cell was realised into a lazy cons. On the JVM `(range n)` is a
LongRange, which implements IReduceInit, and `reduce` opens with
`(if (instance? clojure.lang.IReduceInit coll) (.reduce coll f val)
...)` -- a Java loop over longs, no seq at all. PersistentVector and
PersistentList reduce the same way. So a native `.reduce` is not a
shortcut around Clojure; it is where Clojure itself puts the loop.

`reduce_native` (B_REDUCEINIT, the `.reduce` row) walks a native range
by its arithmetic without allocating a cell, a vector by index, a
list by cells; a range that was partly realised continues from its
pending tail. A reduced value stops it and is unwrapped, as
Java's does. `instance?` answers IReduceInit for exactly those three,
a realised range cell now carries the mark that says it is one, and
`(class (range 3))` is LongRange. Nineteen oracle cases pin the
values against clj, reduced-early ones included.

The derived suite moved for the first time today: transducers 14/12
-> 20/6 pass/fail, 2170 pass overall, because `reduced` inside a
transducer now reaches the host loop that honours it.

## Two allocations a loop iteration did not need

After :inline, `(if (< i n) (recur (inc i) (+ acc i)) acc)` still
allocated per iteration: a one-node argument vector for each of `<`,
`inc` and `+` (two objects each), and a fresh OBJ_RECUR marker. Both
went.

A call to a builtin on a WHITELIST -- the numeric operations,
comparisons, inc/dec, the sign predicates, `=` and `identical?` --
with one or two arguments (`mode 3` in N_CALL) fills a reused
two-slot vector and calls `call_builtin` on it. The condition that
makes the reuse safe is that none of these keeps its argument vector
or calls back into Clojure, which is why `vector`, `list` and `conj`
can never be on that list; `scalar_builtin` says so beside the list.
Nesting is the trap: `(+ (f x) (g y))` evaluates `(g y)` after
`(f x)` has been computed, and anything inside `g` may use the
scratch, so the first argument is parked in a sixth kframe slot and
both are copied into the scratch only at the moment of the call.

The recur marker is one object for the whole process, held by a
global root; nothing reads anything out of it.

`scripts/bench`: loop/recur 186x -> 125x (1.7us an iteration), fib
57x -> 33x, plain recursion 46x -> 32x, the map-building reduce 37x
-> 26x. What is left in the loop is the interpretation itself --
k_push and k_finish per node, the frame reads -- and in `into` over
a lazy seq it is the seq: `map` makes a lazy cell, a thunk closure
and a cons per element where the JVM's chunked seqs do 32 at a time
through a chunk buffer. Chunked seqs are the next faithful step for
pipelines; `sort` at 616x is a comparator call per comparison.

## Chunked seqs, and the lazy seq that ate the chunk

`map`, `filter`, `keep`, `for` and `doseq` in core.clj all have a
chunked branch: ask `chunked-seq?`, take 32 elements through a chunk
buffer, and hand back `(chunk-cons (chunk b) (recur-on (chunk-rest
s)))`. Without the host types behind it that branch is dead and every
element costs a lazy cell, a thunk closure and a cons -- which is why
`into` over a mapped range was 1,000x the JVM when everything else had
come down to 30x.

The host side is four kinds and six members: OBJ_CHUNK (a window
[i1,i2) onto a backing run or vector -- a vector's seq chunks IN
PLACE, no copy), OBJ_CHUNKBUF (`ChunkBuffer.add`, `.chunk`),
OBJ_CHUNKSEQ (`ChunkedCons`), and `chunkedFirst`/`chunkedMore`/
`chunkedNext` on the seqs that have chunks: a vector's seq view and a
range. A range chunks by walking its arithmetic into a fresh run and
leaving a pending tail for the rest, so `(map inc (range 1e6))` never
materialises a cell.

Then it did nothing, and the reason took a probe to find. `map`
returns `(lazy-seq ... (chunk-cons ...))`, and `gce_force` SPLIT
whatever the thunk returned into the lazy cell's head and tail slots.
A ChunkedCons split that way is a plain cons: `chunked-seq?` on it is
false, so the next stage of the pipeline took the one-at-a-time
branch and chunking never propagated past the first collection. On
the JVM `LazySeq.seq()` returns the realised seq ITSELF -- it
delegates rather than wrapping -- so a lazy seq over a ChunkedCons IS
a ChunkedCons to everything downstream. LAZY_DELEG is that: slot 2
holds the realised seq and `to_seq` answers it.

Measured, against a warmed JVM: `(count (into [] (map inc (range
100000))))` 1,014x -> 514x, `(sort (map ...))` 616x -> 332x, plain
recursion 32x -> 23x. The derived suite did NOT move -- 2170 pass,
235 fail, 370 error, exactly as before -- because what chunking
changes is how many cells a pipeline allocates, not what it answers.
Nineteen oracle cases pin the answers instead, including the shapes
where a chunk boundary could hide a bug: 33 elements through a
32-wide chunk, a partly consumed chunk, a double range, a ratio
range, `map` over two collections, and an infinite range.

One thing it exposed rather than caused: hashing. A ChunkedCons is
equal to a vector of the same elements, and until now it hashed by
identity, like every lazy seq (DEVIATIONS 35). It hashes structurally
now WHEN the rest is already realised, and `seq_realised_p` checks
before folding -- a partly realised seq would otherwise hash its
first 32 elements and claim to be the whole sequence, which is the
silent wrong answer rather than the loud one.

## A break is data, and what it cost to get the caller's locals

The debugger PLAN.md asks for is a protocol, not a UI: pause, hand the
state to a handler, take a command back. This is the first half of it,
the part that is useful on its own -- the state, as data:

    {:reason :error
     :message "no such member: Long.nosuchmember"
     :frames [{:fn "clojure.core/boom" :file "x.clj" :line 1 :col 33
               :env {x 10, y 30}}
              {:fn "clojure.core/caller" ...}]}

`(clotran-break)` takes one anywhere and answers it -- a breakpoint
that needs no protocol at all, since the answer is a map you can look
at. An error takes one when `CLOTRAN_BREAK=1`, when
`CLOTRAN_BREAK_FILE=path` is set (appended, for a run that ends before
anyone can ask), or after `(clotran-break-on! true)` at a REPL, and
`(clotran-last-break)` reads the most recent one back, the way `*e`
holds the last exception. It is taken at the THROW, in capture_trace,
where every frame is still pending; after the unwind the locals are
gone. Capture is off by default: it builds a map of every frame at
every error, caught ones included.

Two things had to change to make the frames worth reading.

**Locals by name.** The analyser knew each local's name and slot and
threw the mapping away after analysis. `bind_name` now also records
slot -> name at the FN level, and it rides on the closure's template
as a sixth element. The debugger reads it; nothing else does.

**A tail call now keeps its own frame.** The executor reused the
caller's continuation frame for a call in tail position, which was
free -- the caller was finished with its locals -- until a break
wanted to show them. `(defn outer [coll] (let [n (count coll)]
(inner n 41)))` reported one frame, and the caller's `n` and `coll`
were unreachable, while the call stack named `outer` in the trace
either way. Now the callee's body is pushed rather than swapped in.
It costs about 5% on call-heavy benchmarks and some value-stack
memory per pending call, and it is also what Clojure does: there is
no tail-call elimination on the JVM, so the caller's frame is
genuinely still there.

`CLOTRAN_KEEP_LOCALS=1` turns the locals-clearing pass off, so a frame
shows every local it bound rather than nil for the ones already read.
Clojure has the same switch, `:disable-locals-clearing`, for the same
reason. Without it a break is still useful but half the values read
nil, which is honest -- the frame really has dropped them -- and
confusing the first time.

**A frame's locals are its arity's.** One frame serves every arity of
a fn -- the arities' slots are numbered consecutively, the second's
beginning where the first's end -- and the slot-to-name map was
fn-wide, so a frame of the first arity reported the last arity's
names over its own, and nil for all of them: `(defn two ([a] ..) ([a
b] ..))` paused in `(two 1)` showed `{a nil, b nil}`. Every fn with
more than one arity, which is most of core.clj, lied. The reader now
finds the frame's arity by its body node (the frame's restart node is
the body) and reports the slots in that arity's range, plus the fn's
own name and its captures, which every arity binds. Captures were the
second gap: their inner slots are allocated in `lookup_local`, not
`bind_name`, so they were never named at all and a closed-over value
never appeared in a frame.

**A frame is where its pending call is.** The position reported for
a frame was its body node's, and a body that came out of a macro --
every `let`, every `defn` with a docstring -- has no position, so a
break inside `(let [n ..] (clotran-break) ..)` reported `0:0`. What a
trace line shows is the innermost pending node WITHIN the function:
the call it is waiting on, or the break itself. The reader now takes
the first node with a position walking down from the top of the
continuation stack and resets at each fn frame, so `map`'s frame
reports core.clj line 2767, where its lazy seq calls `f`. A frame a
step has just entered has no pending node yet and its body is a `do`
the analyser made, positionless; that frame is where the body's
first form is.

What is NOT here: resuming. The handler Var, `:continue`, `:step` and
`{:eval form :frame 2}` all need the paused continuation stack to be
resumable from outside `run`, which is the same capability a green
thread needs (PLAN stage 2's context type). That is the next piece,
and the data above is meant to not change when it lands.

## A break resumes: the handler Var, a context of its own, and steps by calls

The second half of the protocol PLAN.md asked for. A break -- on
demand, at an error with break-on-error on, or at a step -- hands the
state map to `*clotran-break-handler*` and the handler's answer is a
command:

    :continue | {:continue v} | :step-in | :step-over | :step-out | :abort

`(clotran-break)` is worth `v`, or nil; `:abort` throws "aborted at
break" there; a handler that throws, throws there too, value and all.
With no handler bound the break is what it was, a snapshot answered
as a map, which is what a script and the language tests want.

**The handler runs in another context.** This is the first use of
stage 2's context type for its stated purpose. `take_break` parks the
paused context -- its continuation stack, value stack, call stack,
error and trace -- switches to a context kept for the handler, applies
the handler, and switches back before the native that took the break
returns. The comment on `gce_ctx_switch` says never to switch under a
run in progress; this is the one shape that is safe, a switch
bracketed inside one native call, because the paused run never
executes while the other context is live. The Fortran stack is shared
either way, so the handler context inherits `ev_depth` and the nesting
limit keeps counting.

What that buys over running the handler on the paused stacks: its
frames are its own (an error in the nested REPL prints its own trace,
not two hundred paused frames under it), the paused error state at an
error break is restored by the switch rather than by hand, and the
break map read by `(clotran-last-break)` describes the paused context
alone. What it costs: a `binding` in force at the break is a root value
in the handler, since the binding stack is per context -- which is why
the handler Var is read BEFORE the switch, where the user's `binding`
of it is in force.

**The REPL is the default handler.** The loop moved out of main.f90
into Eval (`repl.inc`), and `(clotran-repl state)` runs it nested: it
prints the state (eight frames, then a count) and a line naming the
commands, prompts `[1] user=>`, and `(clotran-resume cmd)` is how the
keyboard answers. Starting a REPL binds it as the handler if nothing
else is bound, so `./clotran` pauses into a nested REPL on
`(clotran-break)` and a script does not. One level: a break inside
the handler is a snapshot and an error there is not a break, so the
debugger does not debug itself and `(clotran-last-break)` is not
overwritten by a typo at the nested prompt.

**Steps count calls.** The executor has no line events; it has calls.
So from a stop at depth d (`fstack_top`): `:step-in` stops at the next
call anywhere, `:step-over` at the next call no deeper than d + 1 --
the calls this frame's fn makes, or its callers make after it returns,
walking this body without descending -- and `:step-out` at the next
call no deeper than d, once this frame is gone. One integer, checked
at the three places a callee's frame comes into being, after its
arguments are bound so the stop shows it on top. A step the form never
reached is cleared when the outermost run exits, or the next form's
first call would stop. At an error break a step is dropped: the throw
is in progress and the next call would be the `binding` macro's own
`pop-thread-bindings` in the finally.

**Eval-in-frame is the handler's job.** PLAN sketched `{:eval form
:frame n}` as a command. Locals are immutable and `:env` already holds
their values, so `(eval (list 'let (vec (mapcat (fn [[s v]] [s (list
'quote v)]) env)) form))` on the handler's side is the whole feature,
over the data, and the evaluator learned no command for it.

**Found on the way: an empty line quit the REPL.** The loop treated
`iostat < 0` with size 0 as end of file, and an empty line is end of
RECORD with size 0. It had been so since the loop was written; nobody
pressed Enter on nothing through a pipe. And under gfortran a read
after the end reports a POSITIVE code, which the nested REPL made
reachable (it reads the rest of the pipe, sees the end, resumes, and
the outer loop reads again) and which looped forever. Both loops now
test `is_iostat_end` and bail on any positive code; that fix landed
first, on its own.

## Threads over contexts: a future is a task, and a task is a context

PLAN.md's decision: a thread is an evaluator context, and the kinds
of thread are impls of one protocol. This is the primitive and the
first impl, `:green`: a TASK is a closure run in a context of its
own, on the one OS thread, and core.clj's `future`, `promise`,
`pmap`, `pcalls`, `pvalues` and `deref` run verbatim over the Java
objects they expect. `Agent/soloExecutor.submit` answers a task; a
task answers `.get`, `.isDone`, `.isCancelled`, `.cancel`; a
`CountDownLatch` was already an atom holding its count, and `.await`
now waits for zero; `Thread/sleep` is the clock. `(promise x)` needed
`compare-and-set!`, which had no host row, and a reify that
implements `IFn` to be callable through `apply`.

**When a task runs.** At submit, until it finishes or BLOCKS; then it
yields: its continuation stack, value stack and call stack stay parked
in its context, and whoever stepped it gets control back. The one
blocking primitive is `block_on`: inside a task at its outermost run
it parks the task with what it waits for and a deadline, sets
`yield_flag`, and the run loop exits without finishing the node that
blocked. Anywhere else -- the main context, or a task PINNED under a
native frame -- it runs the other tasks right there, nested, until the
wait is over: `pick_runnable` is a scan, `task_step` is the same
bracketed context switch the debugger's handler uses. Nothing runnable
and no deadline is a deadlock, reported rather than hung.

**The re-executable unit is the dispatch, not the node.** A parked
task resumes by running its loop again over the parked frames, and the
node that blocked runs again. The first version re-ran the whole `.`
node -- receiver, arguments, dispatch -- and a promise's `deref` came
back with a nil latch: the receiver `d` had been read once already,
that read was its last, and locals clearing had nulled the slot. One
`CLOTRAN_TASK_TRACE=1` line showed the target kind as nil; the theory
about nesting depth it replaced was wrong. So `.` is now a loop-driven
node like a call: the target, then the arguments, into the frame's
slots, then a dispatch that reads no local and can run twice. That
also took `.` calls out of the nested-run helper, which is where they
had been pinned all along -- a reify method reached through `.` used
to be applied through `invoke_closure`, a nested run, so a promise's
`deref` could never have yielded. It now comes back as a CALL REQUEST
the loop honours by entering the method in place of the node's frame
(`enter_call`), the same frame swap a tail call once got.

**Contexts come back.** Each task takes a context; a finished one is
emptied and its id kept for the next (`ctx_release`, the free list
`gce_ctx_new` pops), so a thousand futures use a handful of stacks.

**What moved.** Clojure's own `parallel` namespace: 0 of 2 tests to 2
of 2. `vars` reached its `(apply sample (range))`, which had never run
before, and hung -- `apply` realises its argument seq; now bounded and
an error, DEVIATIONS 37. The full scorecard is in the commit.

**Not here.** The protocol's other impls: `:process` through
`execute_command_line` for the pipeline vision, `:os` when the
collector can take it. Agents are still synchronous. `deref` with a
timeout inside a pinned wait counts the deadline but cannot park.

## clotran.thread: the contract, and green as its default

James's framing: start with green threads, but have the overall idea
of a contract of a thread first, then let green be the first
implementation and the default. So `src/clj/clotran/thread.cljf` is
two protocols and one current kind, the way core.matrix has one API
and pluggable implementations. `Kind` is what an implementation
supplies -- its name, what `-spawn` takes (`:fn` for a closure over
the shared heap, `:form` for a form and data when the heap is not
shared), `-spawn`, `-self`, `-receive` -- and `Handle` is what a
spawned thread answers: `-join`, `-status`, `-cancel`, `-send`. The
API is `spawn`, `join`, `status`, `cancel!`, `send!`, `receive` and
`self` over `*kind*`, with `set-kind!` to change the default and
`binding` to scope one.

`green` is a deftype whose handle wraps a task (tasks.inc): `-join`
is the task's `.get`, `-status` its state in the protocol's five
words, `-cancel` its `.cancel`, and the mailbox is a fifth slot on
the task, an atom holding a vector, which `block_on` already knows
how to wait on once `satisfied` learned that an atom holding a vector
is ready when it is not empty. `receive` is `.await` on it and a
take; a task switch happens only inside `.await`, so the take is not
interleaved. The main context has a mailbox of its own, so a worker
can reply to whoever sent, and `self` in the main context is a handle
that can be sent to but not joined. The host half is four builtins
interned into the namespace at bootstrap, as `fortran`'s are.

Two bugs stood in the way, each its own commit. `(def green "The
default kind." (Green.))` bound the docstring: `def` had never learned
its four-element form, and fixing it let core.clj's
`default-data-readers` init be analysed for the first time -- it
var-quotes a reader in the skipped `clojure.uuid`, so a qualified
var-quote that does not resolve now interns the Var unbound (the
var-quote's half of DEVIATIONS 32). And `(. x (-name))` was taken for
the field read `(.-name x)`: the dash shortcut ignored the analyser's
own is-call flag, so no protocol method spelt `-something` had ever
been callable on a deftype.

Not here: `:process`, which is the reason the contract has `-takes`.

## clotran.rt: host members written in Clojure, loaded on first use

"Let's just finish out the language." The language suite's errors
were counted by message: 200 of sequences' 222 were one missing
member on sorted sets, 61 were `clojure.lang.Volatile`, 28 were
`RT/chunkIteratorSeq`, 9 were `java.util.ArrayList`. This is the
three small ones.

`Volatile` is a new box kind, `OBJ_VOLATILE`: `deref` reads it,
`.reset` writes it, `instance?` knows it as `IDeref`, which is what
`@v` turns on -- without that, `@(volatile! 1)` answered the box, and
`partition-by`, whose transducer keeps its previous value in one,
started a partition per element.

The rest is a new kind of host-table row. ClojureScript writes
`iter`, `SeqIter`, `MultiIterator`, `TransformerIterator`,
`chunkIteratorSeq`, `ArrayList` and `Eduction` in Clojure
(core.cljs), so they are Clojure here too, in
`src/clj/clotran/rt.cljf`, ported nearly line for line: a mutable
field is an atom, since a deftype's fields cannot be set!
(DEVIATIONS 20), and the transformer's state is one map in one atom.
A row whose id is `B_RTFN` -- `RT/iter`, `RT/chunkIteratorSeq`,
`TransformerIterator/create` and `createMulti`,
`Collections/shuffle` -- names the var to call in its name column,
`apply` sends such a builtin to `rt_call`, and the constructors
`eval_new` cannot build natively, `ArrayList.` and `Eduction.`, go
the same way. `rt_call` loads the file through the same `RT/load`
path `require` uses, once, on the first row reached. `to_seq` learned
that a deftype with a `seq` method is whatever that answers, which is
how `(seq (eduction ..))` and `(vec (eduction ..))` work.

Why not Fortran: a lazy seq over an iterator needs a thunk that
closes over the iterator, and the host cannot make a closure; the
transducer's reducing function likewise closes over its buffer. In
Clojure both are one `fn`. The premise holds: core.clj is untouched,
and it reaches these by the JVM names it always used.

## Sorted collections: the array map, in order

Two hundred of the language suite's errors were one member on sorted
sets, `seqFrom`, because `sorted-map` and `sorted-set` had built hash
collections since the start (DEVIATIONS 9). The fix is not a tree. An
array map is two runs, keys and values, walked in order; a sorted map
is that with the keys kept in comparator order: `i2 = 1` marks it,
slot 3 holds the comparator, lookup is a binary search, and it is
never promoted to a hash trie however large it grows. `assoc` puts a
new key before the first key after it, `dissoc` closes the gap, each
by a positional copy of both runs -- O(n) per edit, so a map of n
entries is O(n^2) to build, which is the ponytail ceiling and stays
until a sorted map of many thousands matters. A sorted set is a set
over a sorted map, and comes for free.

Ordering may run a Clojure fn -- `sorted-map-by` -- and Assoc.f90
cannot call Eval, so it goes through a comparer procedure pointer Eval
installs, as the printer's forcer is installed: `compare_via` applies
the map's comparator, or Clojure's `compare` when it has none, and
throws ClassCastException for keys `compare` cannot order, as the JVM
does. A comparer that failed answers `huge(0)` and the search stops;
the value it would have produced is discarded with the error.

The rest is what core.clj asks a Sorted for: `seqFrom` (a seq of the
entries from the first key at or past one, forward or back),
`entryKey`, `comparator` (the fn, or `compare` itself), a `seq` with
a direction, and `rseq`, which had no row at all and now reverses a
vector too. `empty` keeps the order and comparator; `sorted?` and
`reversible?` know them; `(= (sorted-map 1 2) {1 2})` was already
true. Under GC torture the evaluator test builds one through assoc
and dissoc, since every edit allocates through the comparer.

**The reduced marker met the comparator.** `(reduced x)` is the map
`{:clotran/reduced x}`, and four places asked "is this value reduced?"
by probing any map for that key. On a sorted map the probe went
through the comparator, which compared `:clotran/reduced` against a
numeric key and threw ClassCastException -- so `(into (sorted-map)
{5 :e})` failed inside `reduce` while `(assoc (sorted-map) 5 :e)`
worked, and `println` of a sorted map overflowed the stack for a
different reason, the new class names having no supertype chain for
`print-method` to walk. One `is_reduced` helper, which never probes a
sorted map, replaced the four probes; `host_super` learned the two
tree classes. A representation trick that leans on "any map" has to be
revisited whenever a new kind of map arrives.

## Finishing the language: what the suite's own errors named

With sorted collections in, the language suite's remaining errors
were counted by message and worked in order, each its own commit:

- **`#(...)` named `%` `p1`**, where Clojure names it `p1__1#`. So
  `every-pred`'s `#(and (p1 %) (p2 %))` read its own argument as the
  predicate `p1`, and `((every-pred even? number?) 2 4 6 8)` said
  "not a function: 8". The reader now gives each `#()` a fresh suffix.
  The reader test had typed the old name in by hand -- the same trap
  the oracle exists to avoid -- and was corrected to Clojure's shape.
- **Metadata fell off.** `assoc`, `conj`, `disj`, `pop` and `empty`
  stripped the wrapper (DEVIATIONS 5) and answered bare; only `dissoc`
  kept it, by accident. `keep_meta` wraps the result again, and
  `into` already re-attached through `with-meta`. And a `def`'s Var
  had no metadata of its own: `:name`, `:ns`, `:file`, `:line` and
  `:column` are now set as DefExpr sets them, which is also why
  clojure.test's reports now name the test instead of `(nil)`.
- **Errors without classes.** `(quot 9 0)` failed with a bare message
  and `(thrown? ArithmeticException ...)` could not catch it; so with
  overflow and with `compare` on things that do not compare. They are
  ArithmeticException and ClassCastException now.
- **Small members**, Clojure in clotran.rt: `RT/req` behind `:keys!`
  destructuring, `(Object.)` as a sentinel (`get-in`'s not-found
  path uses one), the bit tests, `long-array` and `double-array` over
  Fortran arrays.

## The language's leftovers: what the reader never resolved, and what the runtime never raised

The next pass over the suite's failures turned up two things that were
not test-shaped bugs but language gaps that had never been noticed
because everything agreed with itself.

**`::keyword` was never resolved.** The reader took `::b` as a keyword
whose NAME began with a colon: it printed as `::b`, `(namespace ::b)`
was nil, and `(= ::b :user/b)` was false. core.clj uses `::` nine
times and every use compares a `::x` to another `::x`, so nothing
broke; the first thing that asked the keyword what it was named was
the multimethods suite's "Cyclic derivation: ::child has ::ancestor-1
as ancestor". LispReader.java resolves at READ time through
`Compiler.currentNS` and `namespaceFor` -- the current namespace for
`::x`, the alias -- an alias only, `lookupAlias`, so `::clojure.core/y`
is an invalid token even there -- for `::a/x`, and "Invalid token" for
an alias nobody made. LispReader.f90 cannot see namespaces, so the
evaluator installs a resolver the way it installs the sorted map's
comparer (`gcr_set_ns_resolver`, `kw_ns_of`). One
consequence worth knowing: a `::alias/x` is read when its FORM is
read, so the `require` that makes the alias has to be an earlier
top-level form, exactly as on the JVM -- a `(do (require ..) ::a/x)`
is an invalid token there too.

**A host failure was a map.** `fail` threw `{:error "message"}`, so
`(catch RuntimeException e (.getMessage e))` could not see it,
`ex-message` answered nil, and `thrown-with-msg?` never matched an
error the host raised. `error_value` now builds the same OBJ_ERR that
`fail_as` builds, of class RuntimeException. With it came the second
fact of class hierarchy after ArityException's: `RuntimeException`
catches every runtime class clotran throws (`is_runtime_class` lists
them), and nothing else -- `(catch RuntimeException e ..)` does not
take an `Exception.` someone threw, as on the JVM.

The rest were the suite's own findings, each checked against `clj`
before it became an oracle case:

- **`dissoc` on a metadata-carrying map answered it unchanged.**
  `gca_dissoc` saw the wrapper, not a map, and returned its argument;
  so a record's own field would not dissoc, because `without` is
  `(dissoc (with-meta (into {} this) __meta) k)`. It strips and keeps
  the metadata now, as `assoc` and `conj` did, and the oracle has a
  block of every operation over a wrapped map, vector, set and list.
- **A namespace's metadata.** `alter-meta!` set it and `meta` read
  nil, because `(meta x)` is `(if (instance? IMeta x) (.meta x))` and
  a Namespace did not claim IMeta.
- **`(seq (eduction ..))` was nil.** core.clj's own Eduction has
  `iterator` and `reduce` and no `seq`; RT.seqFrom seqs an Iterable
  through its iterator, so `inst_seq` does the same via
  `chunk-iterator-seq`. With that, `(= [2 3] (eduction (map inc) [1
  2]))` compares element by element, one instance to one sequence --
  two eductions stay unequal, as Object's equals leaves them.
- **`reduce-kv` on a vector.** The vector claims `IKVReduce` in its
  supers, so the protocol reaches `.kvreduce`, a row to
  clotran.rt's `kvreduce-of`: index and element, stopping at a
  reduced value.
- **Callable things.** A keyword called with no argument or with
  three is `ArityException` with the JVM's count and its `(> 20)`;
  a symbol is callable, the same lookup as a keyword's;
  `createAsIfByAssoc` merges a trailing map, which is what `(f :a 1
  {:b 2})` with `& {:keys ..}` means since 1.11.
- **`Long/valueOf`** read through Fortran's list-directed input,
  which took "1 2" and "1,2" as 1 and truncated Long/MAX_VALUE to 32
  bits. It is an optional sign and digits now, and 64-bit.
- **Small edges the tests named.** `(ex-data (ex-info "m" nil))` is
  `{}`; `(pr-str #'inc)` is `#'clojure.core/inc`; `(throw)` and
  `(throw a b)` are analysis errors; `& ` is not a `let*` or `loop*`
  binding ("Can't use & as a local binding", Compiler.LetExpr.Parser
  -- the clj on this machine is 1.12 and allows it, so that is a
  language-test check, not an oracle case); a method the table does
  not have fails in Reflector's words, "No matching method jump found
  taking 1 args for class String"; `Math.ulp` of infinity and zero,
  `IEEEremainder` by zero, and `floorDiv` of Long/MIN_VALUE by -1,
  which wraps rather than passing through a double.

## A map entry has a type, a Var has a root, and an error answers to its class

The suite's next failures were three things Clojure keeps and clotran
had flattened away.

**A map entry was a plain vector.** `(first {1 2})` IS a vector on the
JVM too -- `MapEntry` extends `APersistentVector` -- but it is also a
`Map$Entry`, and `clojure.walk` tells the two apart: `postwalk` rebuilds
a vector it is handed and leaves an entry alone, so a walker that turned
vectors into lists turned every map into `{nil nil}`. The mark lives in
a slot the vector never uses (slot 5; the trie root is slot 1 and `i2`
is the shift), set where entries are built -- the seq of a map, `find`,
a sorted map's seq, `MapEntry/create` -- and read by `map-entry?`
through `instance?` on `java.util.Map$Entry`. `conj` and `assoc` on an
entry build a fresh vector, so the mark falls off exactly where the
JVM's type does; `=` never looked at the slot, so `(= [1 2] (first {1
2}))` stays true. `class` still says PersistentVector: changing it would
change protocol dispatch on entries, and nothing asked for that.

**A Var's root and its binding were one slot.** `push-thread-bindings`
saved the value and overwrote it, so `with-redefs` inside a `binding` of
the same Var replaced the binding, and `def` under a binding did too;
the JVM's `bindRoot`, `alterRoot` and `DefExpr` all write the root
while a binding keeps showing its own value. The first binding of a Var
now parks the root in slot 5 and `i2` counts the bindings; `bindRoot`,
`alter-var-root`, `def` and `intern` write slot 5 while that count is
positive, `getRawRoot` reads it, and the last pop restores the root as
those may have left it. `set!` still writes the binding, as it should,
and so does `in-ns` -- `RT.CURRENT_NS.set` -- which the first cut of
this routed through `intern` and so through the root: under `(binding
[*ns* *ns*] (in-ns ..))` the namespace never changed, clotran.rt loaded
its definitions into the wrong namespace, and the suite's numbers and
ns-libs tests said so before the commit did.

**An error was an instance of nothing.** `(instance? ArithmeticException
e)` was false for the very error `catch ArithmeticException` takes, so
an agent's error handler could not tell what it was handed. The class
test `catch` uses is now `exc_class_matches`, and `instance?` asks it
for any throwable class name -- the same two edges of hierarchy, and
Throwable and Exception take anything.

And the small ones: `(:k coll not-found)` honours the default on a set
or a transient, not only a map; `Class/isAssignableFrom` answers from a
deftype's declared interfaces or a built-in's supertype chain instead
of `false` to everything, which is what lets `extend` refuse a type that
already implements the protocol inline, and `extends?` say so; and
`Long/valueOf` with the wrong count fails in the Reflector's words.

## What Clojure's verbatim suite named next: hashCode, causes, and a record's own methods

With the derived suite at 98.6%, the 67 verbatim namespaces were run
again (82% of executed, from 53%) and their language-shaped failures
read. What they named, each checked against `clj` before it became an
oracle case:

- **`Util.hash` is `Object.hashCode`, not `hasheq`.** The `case` macro
  keys its table with `Util/hash`, merges tests whose hashes collide
  into one bucket, and makes the merged test the int hash itself. Both
  rows pointed at clotran's `hash`, so `(case 1 1 :long
  -9223372034707292159 :big :else)` -- the suite's own collision --
  answered `:else`. `java_hashcode` is `Long.hashCode` for every
  integer (Clojure's are all longs there), `Double.hashCode`,
  `String.hashCode`, 1231 and 1237; `.hashCode` and `Util/hash` reach
  it, and `case_branch` hashes the value the same way. A merged
  bucket's key is the hash of its hash, which the JVM's boxed Integer
  makes the same number and a negative long does not, so `case_branch`
  probes that second key on a miss and lets skip-check say it was a
  merge.
- **An exception has a cause.** `(ex-info m data cause)` and
  `(Exception. m cause)` kept nothing in slot 5; `getCause` answered
  nil, so `ex-cause` and `Throwable->map`'s `:via` chain stopped at the
  first exception.
- **A macro's arity error counts what the caller wrote.** The
  ArityException said `(3)` for `(m0 1)`, `&form` and `&env` included;
  `macro_arity_fixup` takes the two off, only when the exception names
  the macro itself, as `Compiler.macroexpand1` does.
- **A private Var is not reachable by its qualified name** from another
  namespace: "var: other/secret is not public", as `resolveIn` says;
  `#'other/secret` still works, as there.
- **`find-ns` created namespaces.** So `(the-ns 'nope)` answered a
  namespace, `alias` to one nobody made succeeded, and `require`'s
  "namespace not found after loading" could never fire. It is
  `Namespace.find` now; `create-ns` has `findOrCreate` to itself,
  `remove-ns` exists, and a skipped JVM-only lib (DEVIATIONS 12) leaves
  an empty namespace behind so that `require` of it still succeeds --
  core.clj's own `(require '[clojure.java.io :as jio])` is form 645.
- **`find` answers the map's own key**, metadata and all, as
  `MapEntry(key, val)` does; it answered the lookup key.
- **A record's `conj`, `with-meta` and `meta` are its own methods.**
  `conj` on a record built a list of its entries; `with-meta` wrapped
  it and its `meta` method then saw no `__meta`. `cons`, `withMeta`
  and `meta` are what the defrecord expansion wrote, so they are called.
  And a deftype is an instance of what its interfaces EXTEND:
  `IPersistentMap` is an `IPersistentCollection`, `Counted`, `Seqable`
  and a `java.util.Map`, which is what `coll?`, `counted?`, `seqable?`
  and `clojure.walk` ask (`iface_extends`); `seqable?` itself is
  `RT.canSeq`, which had no row.
- **Math edges:** `pow` of 1 or -1 to an infinite power is NaN,
  `getExponent` of NaN and the infinities is 1024 and of zero and the
  subnormals -1023, `nextAfter` towards NaN is NaN; and `Boolean/TRUE`
  and `FALSE`.

## Multimethods: isa?, preferences, and where the method selection lives

DEVIATIONS 8 had stood since the first evaluator: a multimethod looked
its dispatch value up, walked the host's supertype chain for a class,
and fell to the default. No hierarchy, no `prefer-method`, no ambiguity
error -- and the verbatim suite's `preferences-multimethod-test` and
`indirect-preferences-mulitmethod-test` said so.

**The selection is Clojure.** `MultiFn.findAndCacheBestMethod`,
`prefers` and `preferMethod`'s conflict check are written in
`src/clj/clotran/multifn.cljf`, as ClojureScript writes them in
cljs.core (SEAMS.md: not host-bound). It is a file of its own, apart
from clotran.rt, because it is first needed while core.clj is still
loading -- core_print.clj's `prefer-method` calls come before
core_deftype.clj -- so it uses only what core.clj has defined by then:
no `deftype`, no `reduce`, `in-ns` rather than `ns`. Eval reaches it
through `mf_call`, the same lazy loader as `rt_call` with a file and a
flag of its own.

**The cache is Fortran.** A multimethod's slot 5 holds `[hierarchy-ref
prefers cache cached-hierarchy]`; `mf_lookup` answers from the cache
while the hierarchy is the object it was filled under, tries the exact
entry, and only then asks `find-method`, caching what it answers.
`addMethod`, `removeMethod`, `preferMethod` and `reset` drop the cache;
a `derive` replaces the hierarchy map, and the identity check drops it
too. A user multimethod dispatches in about 5 us, hit or cached miss.

**What `isa?` needed.** `(class? (class {}))` was false, so `isa?` never
took its `isAssignableFrom` branch for class keywords and print-method
could not see that a vector's class extends `IPersistentCollection`.
A keyword naming a deftype or spelt like a host class is a Class now;
`isAssignableFrom` reads the host chains and, for an interface, what it
extends (`iface_supers`, which `getInterfaces` also answers, so
`parents` and `bases` of an interface are not empty). Two things came
out of walking that: `Throwable`'s chain named itself, so `supers` of an
exception went round forever and printing one never returned; and where
two of print-dup's methods each dominate the other, the JVM's answer is
whichever its table yields last -- clotran takes the more specific by
`isa?`, which is the JVM's answer for a map and is recorded in
DEVIATIONS 8's closing note.

**Two things the suite found on the way.** The interface table has to
be DIRECT, as `clojure.lang` declares it: a transitive list that gave
`IPersistentVector` a `java.util.List` parent let print-method's
RandomAccess method -- preferred to List -- dominate the vector's own,
and `print-str` of a vector answered `#object[..]`; `supers` takes the
closure itself. And syntax-quote qualified `clojure.core` as
`this-ns/clojure.core`, which `Compiler.resolveSymbol` never does -- a
name with a dot in it is a class name and stays as written -- so
test_helper's `eval-in-temp-ns`, which `use`s `'clojure.core` inside a
syntax-quote, asked `require` for a namespace nobody had, and with
`find-ns` no longer inventing one, `require` finally said so.
