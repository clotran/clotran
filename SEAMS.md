# Seams

Where Clojure-the-language stops and clotran-the-host begins.

This is not DEVIATIONS.md. A deviation is somewhere we are *wrong*. A seam is
somewhere we had to *choose*, and the choice was legitimate. Mixing the two
ledgers is how you end up defending an accident.

**References**, both pinned clones, both to be cited rather than recalled:

- `~/jborden/clojure` at `clojure-1.12.6` -- the same commit as our vendored
  core.clj (src/clj/clojure/PROVENANCE.md). This is what we must satisfy.
- `~/jborden/clojurescript` at `r1.12.145` -- a second implementation of the
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
| `deftype`                |        1 |        87 |
| `defprotocol`            |        1 |        60 |

core.cljs is 58% larger while touching its host roughly three times less.

(The `deftype` and `defprotocol` rows read 1, not 0: `(deftype Eduction
...)` at core.clj:8016 -- the form that was the wall -- and
`(defprotocol Inst)` at core.clj:7038 are both real. The point the rows
make is unchanged, two against 147, but see bucket A-bis below for why
the ratio does not mean what it looks like.)

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
roots, I/O, regex (ICU) and sockets. ClojureScript reaches for `js/` at
exactly these points too, which is the confirmation that they are real.

Sockets (2026-09-29) are the first of these built the way the vocabulary
section below argues for: a C shim for what differs between POSIX and
Winsock (`src/c/socket_shim.c`), `Socket.f90` over it, and clotran's own
namespaces on top -- `clotran.io` readers, `clotran.net`, `clotran.server`
-- naming no Java. cljs.core has no socket server either; its REPLs are
the host's. JVM names survive only where vendored Clojure writes them
(`java.io.StringReader.` in core.clj's `with-in-str`), as a mapping onto
clotran's type (DEVIATIONS 65).

### B. Native by choice -- cljs writes these in Clojure, we write them in Fortran

`src/f/PersistentList.f90` (117), `PersistentVector.f90` (201), `PersistentArrayMap.f90` (224),
`PersistentHashMap.f90` (363), `Assoc.f90` (178) -- about 1,100 lines standing exactly
where core.cljs has deftypes. Also `OBJ_LAZY`, `OBJ_ATOM`, `OBJ_MULTIFN`,
`OBJ_NS`, `OBJ_VAR`. The multimethod's OBJECT is native; its method
SELECTION -- `isa?`, preferences, the ambiguity error -- is Clojure, in
`src/clj/clotran/multifn.cljf`, exactly as cljs.core writes it, with only
the per-dispatch-value cache in Fortran.

These are performance decisions, they are reversible in principle, and they
are **not deviations**. They do not belong in DEVIATIONS.md. What they do owe
is the right *shape*: see the protocol list below.

### A-bis. `deftype*` and `reify*` -- native, and ClojureScript agrees

The table above says `deftype` appears **once in core.clj and 87 times in
core.cljs**, which reads like the clearest bucket-B case in the project:
ClojureScript writes in Clojure what we write in Fortran.

It is not. Those 87 are `deftype` the MACRO, and the macro expands to
`deftype*` the SPECIAL FORM, which neither implementation writes in
Clojure. Clojure interns it as a special form -- `Compiler.java:67`,
`Symbol.intern("deftype*")`, parsed at `Compiler.java:8516` under the
comment `(deftype* tagname classname [fields] :implements [interfaces]
:tag tagname methods*)`. ClojureScript lists it among its specials at
`analyzer.cljc:1509` and parses it at `analyzer.cljc:3678`,
`(defmethod parse 'deftype*)`. Both host compilers have a case
for it, which is the definition of bucket A.

So the count in the table measures something real but answers a different
question: it says core.cljs BUILDS ITS COLLECTIONS out of deftype where we
build ours out of Fortran modules (bucket B, and unchanged). It does not
say deftype itself is host-free.

What clotran makes native is the smallest thing that satisfies both:
a type is a name, its fields, a method table and a list of the class
names it claims. No class is generated, because `instance?` is the only
question anything asks and a list answers it. Everything above --
`deftype`, `reify`, `defrecord`, `extend-type`, `satisfies?` -- stays in
vendored `core_deftype.clj`, which is bucket C.

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

The iterator pieces are bucket B done the other way: `RT/iter`,
`RT/chunkIteratorSeq`, `TransformerIterator` and `ArrayList` are what
`sequence`, `iterator-seq`, `eduction` and the buffering transducers
name, ClojureScript writes every one of them in Clojure, and so
`src/clj/clotran/rt.cljf` does here: a host-table row whose id is
`B_RTFN` calls the var of that name in `clotran.rt`, loaded on first
use. The JVM member is the seam; the code behind it is the language's.
`Eduction` itself needs none of this: core.clj's own `(deftype Eduction
..)` at 8016 runs as written, its `iterator` reaching
`TransformerIterator/create` through the row above (a copy in
`clotran.rt` stood in for it until 2026-09-28, and `(class (eduction
..))` said so).

`future`, `promise`, `pmap` and `Thread/sleep` are the other worked
example, and the larger one: ClojureScript has none of them -- no
threads in a browser -- so by the detector they are Java showing
through. core.clj writes them against `Agent/soloExecutor.submit`, a
`Future`'s `get`/`isDone`/`cancel`, a `CountDownLatch` and
`TimeUnit`. We supply exactly those objects (tasks.inc) and the
definitions run verbatim, which is the premise; what is ours is the
thread underneath them, a context (PLAN.md), not a JVM thread. The
seam is the Java object surface; the primitive behind it is the
language's to define, and ClojureScript's silence says so.

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

---

## The vocabulary problem: we speak Java, and we are not the JVM

Counted in `src/f`: **59 distinct `clojure.lang.*` names and 29 distinct
`java.*` names**, as string literals in Fortran. `is_host_class` is a
list of them. `static_member` dispatches on them. `is_instance` is a
table keyed by them. `host_super` maps clotran's own type keywords TO
them.

ClojureScript is the control group, and it is unambiguous. core.cljs
names its host types **131 times as `js/Error`, 8 as `js/Number`, 7 as
`js/Date`, 6 as `js/RegExp`** -- its own host. It contains
`clojure.lang.` exactly three times: twice in a COMMENT ("a la
clojure.lang.APersistentMap") and once in `(.type js/Java
"java.lang.System")`, which is a GraalVM call explicitly reaching into
Java as a FOREIGN host.

So naming your host's types is not the problem -- every implementation
does it. Naming *somebody else's* host is. clotran is Fortran, and it
answers to `java.lang.Double`.

### The distinction that keeps this honest

Not all 88 are the same thing, and the fix is different for each:

**Names we must READ.** `core.clj` literally contains
`(Double/valueOf s)`, `(clojure.lang.Util/hash x)`,
`(clojure.lang.RT/seq coll)`. Running that file unmodified is the
premise of the project, so recognising those strings is FORCED. This is
not a wart; it is the interop surface, and it is the same surface
`(.type js/Java "java.lang.System")` is for ClojureScript. Keep it, and
keep it in ONE place rather than scattered across a dozen `select case`
blocks.

**Names we WRITE.** Everything else, and this is the part that is a
choice we got wrong:

- `test/f` asserts them **27 times** -- `(instance? java.util.regex.Pattern p)`,
  `(clojure.lang.Util/hash x)`. Those tests are asserting that a
  JVM-shaped shim exists, not that clotran hashes or matches correctly.
  They should assert clotran's own vocabulary and would then keep
  passing if every Java name were renamed tomorrow.
- `host_super` answers `clojure.lang.IPersistentVector` for a vector
  so a multimethod registered on the Java name dispatches, and `class`
  itself answers `clojure.lang.PersistentVector` (DEVIATIONS 34).
  Necessary at the boundary, but it means clotran's INTERNAL dispatch
  graph is spelled in Java.
- `instance?` accepts only Java names. `(instance? Regex p)` is not a
  thing anyone can write, even though `regex` is exactly what
  `clotran-type` answers.

### What is already right

`type_name` is clotran's own vocabulary and always has been: `vector`,
`map`, `set`, `symbol`, `keyword`, `int`, `double`, `string`, `regex`,
`matcher`, `delay`, `ns`, `var`. `(clotran-type x)` answers those, and
a deftype answers its own class name. So the outward-facing answer is
already ours -- it is the tables and the tests underneath that are not.

### The naming scheme: say which seam you are

A prefix per bucket, so the NAME says what kind of thing it is and no
one has to look it up:

| prefix | means | example |
| --- | --- | --- |
| `clotran.*` | our own type, our own vocabulary | `clotran.vector`, `clotran.regex`, `clotran.delay` |
| `fortran.*` | a REAL host thing -- an actual Fortran object crossing an actual boundary | `fortran.array`, a `dgemm` binding |
| `java.*`, `clojure.lang.*` | READ-ONLY compatibility, present only because `core.clj` writes it | `java.lang.Double`, `clojure.lang.Util` |

The point is not tidiness. Today a reader cannot tell, from
`clojure.lang.PersistentVector` appearing in `Eval.f90`, whether that
is a seam we are obliged to have or a habit we picked up. Under this
scheme they are distinguishable by sight, and `fortran.*` is the only
one that describes THIS host.

Seams are fine. Seams that call themselves by another host's names are
not, because the name is the documentation.

### `fortran.*` has native arrays in it, and one routine that takes them

When this section was written it had none, which was the finding that
prompted it: the one genuine Fortran interop surface -- native arrays,
contiguous, column-major, declared kind, the thing the whole project is
FOR -- lived only in the pre-GC evaluator, since deleted. `Eval.f90`
mentioned it zero times. It had not survived the GC port, and the only
copy was in code scheduled for deletion.

It is ported now, and it went into a `fortran` namespace rather than
`clojure.core` -- which is this section's argument made concrete rather
than an illustration of it:

    (fortran/make-array "real8" 3 4)
    (fortran/aget m 1 2)
    (fortran/array-kind a)   ;=> "real8"

Two reasons, and the weaker one is practical: core.clj defines its own
`make-array`, `aget`, `aset` and `alength`, so those names are shadowed
the moment it loads. The real reason is that these are not Clojure's
array functions with a different implementation underneath. They take a
Fortran KIND NAME rather than a class, they are column-major, their
lower bounds are per dimension, and the buffer they produce can be
handed to `dgemm`. Borrowing Clojure's names would have said they were
the same thing.

Clojure's own `aget`/`alength` remain unimplemented over these, which is
a separate decision: those route through `clojure.lang.RT/alength` and
`Reflector/prepRet`, and making them work is compatibility, not
interop. Worth 23 errors in Clojure's suite -- `RT/alength` (14) and
`RT/seqToTypedArray` (9) -- and not the same job as this.

### The rule this suggests

Java names are a vocabulary clotran must READ, never one it should
WRITE. A test, an error message, a dispatch table or a type answer
that says `java.lang.Double` is describing a host we are not -- and
`fortran.*` is the prefix that describes the one we ARE, which now has
native arrays in it and should collect everything else that genuinely
crosses into Fortran.

PLAN.md carries the work.
