# Seams

Where Clojure-the-language stops and clotran-the-host begins.

This is not DEVIATIONS.md. A deviation is somewhere we are *wrong*. A seam is
somewhere we had to *choose*, and the choice was legitimate. Mixing the two
ledgers is how you end up defending an accident.

**References**, both pinned clones, both to be cited rather than recalled:

- `~/jborden/clojure` at `71b4623d` -- the same commit as our vendored
  core.clj (src/clj/clojure/PROVENANCE.md). This is what we must satisfy.
- `~/jborden/clojurescript` at `b45dff9f` -- a second implementation of the
  same language on a completely different host. This is what tells us which
  parts of the first one were ever really the language.

---

## The measurement

Two implementations of one language, counted:

|                          | core.clj | core.cljs |
|--------------------------|---------:|----------:|
| lines                    |    8,371 |    13,193 |
| host references          |      578 `clojure.lang.*` + 115 `java.*` | 208 `js/` |
| ...of which are throws   |        - | 131 `js/Error` |
| distinct host classes    |       81 |       ~20 |
| `deftype`                |        0 |        86 |
| `defprotocol`            |        0 |        59 |

core.cljs is 58% larger while touching its host roughly three times less.
The extra five thousand lines are `PersistentVector`, `PersistentHashMap`,
`BitmapIndexedNode`, `Subvec`, `ChunkedSeq`, `LazySeq`, `MultiFn`, `Atom`,
`Var`, `Namespace`, `Range` -- written *in Clojure*, as deftypes. On the JVM
those are Java files that core.clj merely calls.

So `clojure.lang.*` is not the host boundary. It is the runtime, and which
language the runtime is written in is an implementation decision, not a
semantic one. ClojureScript proves this by having made the decision
differently.

Subtract `js/Error` and ClojureScript's irreducible host surface is about a
dozen names: `RegExp`, `Array`, `Number`, `String`, `Object`, `Symbol`,
`Date`, `parseInt`, `parseFloat`, `isNaN`, `Math`. *That* is the seam.

---

## Why our line sits lower than ClojureScript's

ClojureScript's deftypes are **compiled**. `(deftype PersistentVector ...)`
becomes a real JS class with real property slots, monomorphic call sites, and
a JIT that specializes it after a few thousand calls.

The same deftype in clotran is **interpreted**: heap objects walked by
`gce_eval`, where every field access is a dispatch through the analyzer. That
is not a two-times tax on the coldest code in the system, it is roughly two
orders of magnitude on the hottest -- `conj`, `nth`, `assoc`, `first` sit
underneath everything else that runs.

ClojureScript can afford to put the line very high because its host compiles
what is above it. We interpret what is above it, so our line has to sit much
lower. This is the same tradeoff Rich made in the other direction: JVM
Clojure keeps `PersistentVector` in Java precisely because bytecode beats
anything he could have written in Clojure-on-Clojure.

We have no bytecode. In that specific sense we are closer to ClojureScript
than to Clojure -- but without the JIT that makes ClojureScript's choice pay.

---

## The rule

**Native (Fortran) if** it is needed to run the interpreter itself, or it
lives in an inner loop, or no expression for it exists in Clojure at all.

**Pure Clojure if** it is cold, or a thin composition over primitives.

Lowering is cheap and one-way: anything written in Clojure can be moved into
Fortran later when a profile asks for it. Raising is not. So when genuinely
undecided, write it in Clojure and wait to be told otherwise by measurement.

**Already in Fortran and buildable in Clojure? Leave it.** Rewriting working
native code upward costs speed and buys nothing.

---

## The four buckets

### A. Must be native -- no Clojure expression exists

The heap and `gc_value` itself, the evaluator, the reader, integer and float
arithmetic, character and string primitives, symbol and keyword identity, Var
roots, I/O, and regex (ICU). ClojureScript reaches for `js/` at exactly these
points too, which is the confirmation that they are real.

### B. Native by choice -- cljs writes these in Clojure, we write them in Fortran

`src/f/GCList.f90` (117), `GCVector.f90` (201), `GCMap.f90` (224),
`GCHamt.f90` (363), `GCAssoc.f90` (178) -- about 1,100 lines standing exactly
where core.cljs has deftypes. Also `OBJ_LAZY`, `OBJ_ATOM`, `OBJ_MULTIFN`,
`OBJ_NS`, `OBJ_VAR`.

These are performance decisions, they are reversible in principle, and they
are **not deviations**. They do not belong in DEVIATIONS.md. What they do owe
is the right *shape*: see the protocol list below.

### C. Free -- comes from vendored core.clj

Everything built on A and B: the seq library, destructuring, the macros,
`reduce` / `into` / `mapv` / `sort`, and `re-seq` / `re-find` / `re-matches`.
Each of these we do *not* write is a place we cannot be subtly wrong.

### D. JVM leakage -- API shape that exists only because Java

Reproduced faithfully because core.clj calls it, but not part of the
language. The detector is simple: if ClojureScript does not have it, it was
never Clojure.

Worked example -- `re-matcher` and `re-groups` occur **zero times** in all of
ClojureScript. Its entire regex API is four functions and 21 lines, and
`re-find` is single-arity. Clojure's `re-find` takes a second arity whose
argument is a stateful `java.util.regex.Matcher`. That statefulness is why we
carry `OBJ_MATCHER` at all, and it is the sole cause of the bounded
per-Matcher buffer leak in DEVIATIONS 14. We pay that cost for Java's API
shape, not for Clojure's semantics.

---

## What ClojureScript is for

Not a porting source. Three uses:

1. **The interface spec.** core.cljs declares 59 protocols -- `ISeq`,
   `IIndexed`, `ILookup`, `IReduce`, `IChunkedSeq`, `IDrop`, `IKVReduce`,
   `IEditableCollection` and the rest -- in Clojure, in one file. On the JVM
   the same information is scattered across Java interfaces you reverse
   engineer out of `RT.java`. This is the shape our bucket-B Fortran owes.

2. **A host-boundness test.** If cljs writes it in Clojure, it is bucket B,
   not bucket A, and our putting it in Fortran is a choice we should be able
   to state a reason for.

3. **A leakage detector.** Bucket D, above.

---

## Open

- The 59 protocols are a checklist we have never run against our Fortran.
  Which ones does clotran fail to present?
- Is anything currently in Fortran actually bucket C -- already free in
  core.clj, and we wrote it anyway?

---

## The big one: Clojure compiles, clotran interprets

Worth stating plainly because it is easy to get backwards: **Clojure is not
an interpreted language.** There is no interpreter in Clojure-on-JVM. Every
form, including one typed at a REPL prompt, goes

    read -> Compiler.analyze -> emit JVM bytecode -> load class -> invoke

`Compiler.eval` does exactly that and nothing else. ClojureScript is a
compiler too, to JavaScript, and `cljs.analyzer` is 5,185 lines of Clojure
doing the same job.

clotran is a tree-walking interpreter. It is the odd one out, and that is
the deepest seam in the project -- deeper than Fortran-versus-JVM, because
it changes *when* things are known, not just what they are written in.

### What that costs, concretely

Both real implementations resolve names **lexically, at analysis time**:

| | resolves a symbol | against |
|---|---|---|
| Clojure | `Compiler.analyze` | the namespace being compiled |
| ClojureScript | `cljs.analyzer/resolve-var` | `env`, carrying `:ns` and `:requires` |
| clotran | `gce_eval`, at call time | whatever `*ns*` happens to be |

So `` `(temp/do-template ...) `` inside `clojure.test` is, on the JVM,
already `clojure.template/do-template` by the time anything runs -- the
alias was consumed while reading, in the namespace that wrote it. clotran
still has the bare `temp/` at call time, in a namespace that never heard of
`temp`.

Every name-resolution bug found by running Clojure's own test suite was this
one bug wearing a different hat:

- `temp/do-template` -- an alias, unresolved
- `apply-template` -- an unqualified symbol, unresolved
- `__defining-ns__` being taken from `*ns*` at closure creation rather than
  inherited, so a nested `fn` created while a macro RAN got stamped with the
  caller's namespace

`__defining-ns__` is the giveaway. It is a runtime reconstruction of
something Clojure simply has: the namespace a form was written in. We carry
it in the environment, at a frame's cost, because we threw away the compile
step that would have known it for free.

### We are not stuck with this

clotran already has an analysis pass. `gce_analyze` runs once per top-level
form, deliberately mirroring `Compiler.analyze` -- and today its entire body
is `macroexpand_all`. Name resolution *could* happen there, lexically, with
the namespace known, and the interpreter could then walk a tree whose
symbols are already resolved. That is not compilation; it is the analysis
half that both real implementations do and we skipped.

Until then, treat it as the standing explanation: **when a bug is about
which namespace a name means, the cause is almost certainly that we are
asking at the wrong time.**
