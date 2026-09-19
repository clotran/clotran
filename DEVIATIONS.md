# Deviations from Clojure

Every place clotran does something real Clojure does not, why, and what it
would take to remove it. A deviation with no entry here is a bug.

Not everything native is a deviation. Where we merely *chose* Fortran over
pure Clojure for something Clojure could express, that is a seam, and it
belongs in SEAMS.md instead.

**Reference**: `~/jborden/clojure` -- a clone of `clojure/clojure` at
`71b4623d` -- the SAME commit as the vendored core.clj (see
src/clj/clojure/PROVENANCE.md). Paths below are relative to it. Cite the file and the method;
do not cite memory. That is the whole point of having the clone.

Categories:

- **temporary** -- a scaffold. Bootstrapping is incomplete; it goes away.
- **host** -- forced by Fortran. Cannot go away, but must be invisible.
- **open** -- we do not yet know which of the above it is.

| # | What | Kind | Where |
|---|------|------|-------|
| 1 | Load reads the whole file, then evaluates | temporary | `src/f/main.f90` |
| 2 | `host.clj` preloaded before `core.clj` | temporary | `src/clj/host.clj` |
| 3 | Symbols fall back to `clojure.core` instead of being referred | temporary | `src/f/Eval.f90` |
| 4 | `.` reaches a fixed table of host members, not arbitrary classes | host | `src/f/Eval.f90` |
| 5 | Metadata is a wrapper object, not carried on the value | host | `src/f/GC.f90` |
| 6 | Syntax-quote expands at eval time, not read time | open | `src/f/Eval.f90` |
| 7 | Recursion depth is ~600 frames, against Clojure's ~11,200 | host | `src/f/Eval.f90` |
| 8 | Multimethods dispatch on equality, plus a fixed host hierarchy | temporary | `src/f/Eval.f90` |
| 9 | Sorted collections are unsorted | temporary | `src/f/Eval.f90` |
| 10 | Refs are mutable boxes; dynamic bindings are global | temporary | `src/f/Eval.f90` |
| 11 | Transients are the persistent collections | host | `src/f/Eval.f90` |
| 12 | Five JVM-only libs are skipped by name, and not vendored | host | `src/f/Eval.f90` |
| 13 | Protocol dispatch is uncached | host | `src/f/GC.f90` |
| 14 | Regex is ICU under java.util.regex's names, ASCII-offset only | host | `src/f/Regex.f90` |
| 15 | `hash` values are gc_hash's, not the JVM's murmur3 | host | `src/f/GC.f90` |
| 16 | Names resolve at call time, not while analysing | host | `src/f/Eval.f90` |

---

## 1. Load reads the whole file before evaluating any of it

`Compiler.load` interleaves:

```java
for(Object r = LispReader.read(rdr, false, EOF, false, opts); r != EOF;
    r = LispReader.read(rdr, false, EOF, false, opts))
    { ... ret = eval(r,false); ... }
```

(`src/jvm/clojure/lang/Compiler.java`)

We call `gcr_read_all` first. This is observably wrong wherever reading
depends on state that evaluation sets -- `::kw` resolves against `*ns*`,
`#'` and `#=` read-time evaluation, and any change to `*read-eval*` or
`*data-readers*`.

**Removal**: make the reader streaming over a cursor so a form can be read,
evaluated, and the next read begun. `gcr_read_all` already walks a cursor
internally; it needs to be exposed one form at a time.

## 2. `host.clj` is loaded before `core.clj`

Clojure loads nothing before `clojure/core.clj`; its bootstrap is Java
(`RT.doInit`). Ours is partly Clojure, in `src/clj/host.clj`.

**Removal**: as natives replace it, `host.clj` shrinks. It is already down
to type predicates over `clotran-type` plus three scaffolding macros. When
`defn`/`fn`/`let` come from core.clj itself, the file goes.

## 3. Symbol resolution falls back to `clojure.core`

`resolve_var` tries the current namespace, then `clojure.core`. Clojure
has no such rule: a namespace sees `clojure.core` because `(ns ...)`
calls `refer-clojure`, which copies the mappings in. The difference
shows wherever referral is selective -- `(refer-clojure :exclude [map])`
cannot be honoured by a rule with no record of what was referred.

**Removal**: give `OBJ_NS` a refers map and implement `refer`.

## 4. `.` reaches a fixed table of host members

`clojure.lang.RT`, `Numbers`, `Util`, `Symbol`, `Keyword`, the three
`create` statics, and a list of instance members -- all in `static_member`
and `instance_member`. Clojure reaches any Java class by reflection.

This one is **host**, not temporary: there is no Fortran reflection to
reach, and the classes core.clj names do not exist here. What the table
holds is clotran's own primitives under the host's names -- `RT.more` is
what we already mean by `rest`, `Numbers/add` is `+` -- so the entries are
bindings, not adapters. It grows as core.clj asks for more.

An unlisted member fails **by name**, never as a generic `.` failure, so a
load report says which one to add next.

## 5. Metadata is a wrapper object

Clojure carries metadata ON the value: `Symbol`, `PersistentList` and the
rest implement `IObj`, so `^:static foo` is a Symbol that happens to have a
map attached. `gc_value` is a fixed four-field struct with no room for one,
so metadata is an `OBJ_META` object holding value and map.

This is **host**, and the cost is that everything which RECOGNISES a value
has to see past the wrapper: `strip_meta` at each of those points, and
`type_name` unwrapping so `(instance? clojure.lang.Symbol ^:static x)` is
still true. `with-meta` replaces rather than nests, matching `withMeta`.

Every place that forgot to unwrap was a real bug, and core.clj found them
all: a hinted parameter invisible in its own body, a hinted parameter
vector read as an arity mismatch, a hinted head symbol unresolvable, a Var
interned under a name nobody could spell.

**Removal**: none available. Widening `gc_value` would cost a word on every
value in the heap to serve the few that carry metadata.

## 6. Syntax-quote expands at eval time, not read time

`SyntaxQuoteReader` is a READER macro (`LispReader.java`): `` `x `` is
resolved, gensym-ed and expanded into `concat`/`seq` calls before the form
is ever evaluated. Ours is a `quasiquote` special form that `qq_expand`
handles during evaluation.

Auto-gensym is faithful -- one fresh name per syntax-quote, scoped by a map
the way `GENSYM_ENV` is -- but symbol resolution is not: Clojure qualifies
every symbol in a template to its namespace at read time, which is what
makes a macro immune to a caller having rebound a name. We leave symbols
bare.

**Open**, because it is not yet clear whether this can be moved into the
reader without also moving `*ns*` resolution there.

## 7. Recursion runs out of stack about twenty times sooner

Both runtimes stop somewhere; the JVM raises `StackOverflowError` and we
report `stack overflow near (f ...)`. What differs is how soon.

There is no depth to copy from Clojure, because the JVM's limit is a
**byte budget, not a frame count**: `-XX:ThreadStackSize`, 2048 KB by
default on this platform (`java -XX:+PrintFlagsFinal -version`), divided
by whatever each frame needs. Measured on real Clojure 1.12 here, a
non-tail-recursive function reaches:

| `-Xss` | frames |
|--------|--------|
| 512k   | 1,635  |
| 1m     | 5,528  |
| 2m (default) | 11,211 |
| 4m     | 24,731 |

Ours is measured the same way. On macOS's 8 MB default stack clotran
segfaults between 700 and 800 Clojure-level calls, and 2200 `gce_eval`
entries is the highest limit that still reports rather than crashing --
about 600 usable frames, from four times the stack. Roughly twenty times
shallower per megabyte.

The cause is structural, not a tuning mistake: one Clojure call costs a
whole chain of interpreter frames -- `gce_eval`, `eval_call`, `apply`,
`eval_body`, `gce_eval` again for each argument -- where the JVM has a
single JIT-compiled frame. `-frecursive`, which gfortran needs for
correctness here, puts every local on that stack.

`CLOTRAN_MAX_DEPTH` overrides the limit, which is what `-Xss` is for.

**Removal**: a bigger number is not the fix -- the limit exists because
the Fortran call stack *is* our control stack. The fix is to give the
evaluator an explicit continuation in the heap, which also happens to be
what a step debugger needs (PLAN.md step 4) and what makes tail calls
free beyond `recur`. CHICKEN Scheme reaches the same conclusion from the
other direction with Cheney on the M.T.A.: it treats the C stack as a
nursery and unwinds it periodically, which needs `longjmp` and a compiler
to C -- neither available here, and no `bind(c)` anywhere in `src/f` by
design. The transferable part is the principle, not the mechanism.

## 8. Multimethods dispatch on equality only

`MultiFn.getFn` picks the best method with `isA` over a hierarchy, and
raises when two methods match and neither is preferred. Ours looks up the
dispatch value, falls back to the default, and has no hierarchy, no
`prefer-method`, and no ambiguity check.

**Removal**: implement `isa?` over the hierarchy Var and widen
`findAndCacheBestMethod`. Not needed until `derive` is used.

## 9. Sorted collections are unsorted

`PersistentTreeSet/create` and `PersistentTreeMap/create` build ordinary
hash collections. core.clj reaches for a sorted set first to hold
`*loaded-libs*`, which only ever asks about membership.

**Removal**: a flag on the object plus a sort at `seq` time, or a real
balanced tree if the ordering has to be cheap.

## 10. Refs are mutable boxes, and dynamic bindings are global

`(ref x)` builds an atom: no transaction, no retry, no isolation.
`dosync` calls its thunk. `push`/`popThreadBindings` keep one global
stack where `Var.dvals` is a `ThreadLocal`.

Single-threaded all three are indistinguishable from the real thing.
With threads none of them is, which is why this is **temporary** and why
PLAN.md step 5 is concurrency.

## 11. Transients are the persistent collections

`asTransient` and `persistent` are identity; `conj!` and `assoc!` are
`conj` and `assoc`. A transient is an optimisation, not a semantic: used
correctly -- single-threaded and linearly -- the two give the same value.

What is lost is the speed, and the error Clojure raises when a transient
is used after being persisted.

## 12. Four JVM-only libs are skipped by name

`core_proxy`, `genclass`, `gvec` and `uuid`, plus `clojure.java.io`.
The first two import `clojure.asm`, `ClassWriter` and
`DynamicClassLoader` to emit bytecode; the rest want `java.util`.

Named individually rather than tolerating any missing file, so a real
typo in a load path is still an error. `instant` needs no entry: it is
guarded by `when-class`, and since `Class/forName` throws
`ClassNotFoundException` here, core.clj declines to load it on its own.

## 13. Protocol dispatch is uncached

`MethodImplCache` is a map with the right fields, and `fnFor` always
answers nil -- a permanently cold cache. Every protocol call therefore
goes through `-cache-protocol-fn` and `find-protocol-method`, which is
the CORRECT path and not the fast one.

The cache is stored on the function object itself, which is why
`OBJ_SLOTS` is 5 rather than 4: a closure's four slots are params, body,
env and arity clauses, and a protocol method has one clause per
signature, so none was free. The fifth slot costs one `gc_value` on
every object in the heap.

## 14. Regex is ICU, wearing java.util.regex's names

`#"..."` compiles at READ time via ICU's `uregex_*` C API (vendored
source, `src/c/icu`, built to static libraries -- see its own
PROVENANCE.md), reached through six operations: `Pattern/compile`,
`.matcher`, `.find`, `.matches`, `.groupCount`, `.group`. Those are
exactly what core.clj's own `re-pattern`/`re-matcher`/`re-find`/
`re-matches`/`re-groups`/`re-seq` compile down to, so nothing about
regex is a builtin above that -- the real functions ARE the ones
loaded from core.clj.

This is **host**, and it is the one place C exists in this codebase at
all (see `src/f/Regex.f90`'s own header comment on why that trade was
made). Three real gaps come with it:

- **ASCII/Latin-1 only.** Every byte is widened to a UTF-16 `UChar`
  with the high byte zero, never decoded as UTF-8, so `\d`, `\w`,
  case-insensitive matching and every offset are only correct for
  single-byte text -- which is what clotran's strings already are
  throughout `GC.f90`. A real multibyte string would need a real
  decoder in `regex_shim.c`, matching whatever this codebase decides
  UTF-8 support looks like everywhere else, not just here.
- **~~A Matcher's subject-text buffer leaks~~ -- FIXED, and it was worse
  than this entry said.** It described the text buffer only. In fact
  `cre_close` was declared in `Regex.f90`'s interface block and called
  from nowhere, so every compiled Pattern and every cloned Matcher
  leaked its whole ICU object for the life of the process. The registry
  was a fixed 4096 slots handed out by a wrapping counter, on the
  reasoning that handles are never freed -- so on wrap it would have
  handed out a slot still in use, which is a live Pattern silently
  pointing at someone else's compiled regex.

  The sweep now calls a finalizer for objects owning storage outside
  the heap -- added for native arrays, which own a Fortran buffer for
  the same reason -- and `OBJ_REGEX` and `OBJ_MATCHER` both take it.
  `regex_release` closes the ICU handle and empties the slot, and
  `alloc_slot` reuses emptied slots instead of wrapping.

  The subject text is freed alongside it, but NOT by asking ICU for the
  pointer back: `uregex_getText` on a handle that never had text set
  answers with something ICU owns, and freeing that aborts. The
  buffer's address is kept in the Fortran registry beside the handle,
  because the caller is the only thing that knows which pointers are
  its own.

- **No `region()`, `lookingAt()`, `replaceAll`/`replaceFirst`, or
  named groups.** Only the six operations core.clj's own regex
  functions need exist; `clojure.string`'s regex-based functions
  (`replace`, `split` and friends) will need whichever of these they
  actually call, added the same way, when something needs them.

**Removal of the ASCII limit**: real UTF-8 decoding in the shim.
The missing operations: add them to `regex_shim.h`/`.c` and the
`instance_member` table in `Eval.f90` as they come up, the same way
every other host member in this file did.

---

## Not deviations (checked, and matching)

- **A native bootstrap `ns` macro, replaced by core.clj's own.** `RT.doInit`
  interns `bootNamespace` -- find-or-create plus set-current, nothing else --
  as a macro Var, then `load("clojure/core")`; core.clj's `ns` (its line
  5976) redefines it. `in-ns` is interned the same way but is *not* a macro,
  so its argument evaluates.
- **The first error ends a load.** `Compiler.load` has no per-form `try`;
  its only `catch` is for `ReaderException`, to attach a line and rethrow.
  We did carry on past failures for a while, and core.clj showed why that is
  wrong: `(defmacro let ...)` expands to a `do` whose `defn` succeeded and
  whose next form failed, leaving a namespace holding a `let` that could not
  work. One missing definition, 206 cascading failures, and a form count
  that measured nothing.
- **Macro-ness is Var metadata.** `Var.setMacro` is
  `alterMeta(assoc, {:macro true})`; `isMacro` reads it back. So
  `(:macro (meta #'when))` is true, and `(def foo when)` does not produce a
  macro -- it refuses, with "Can't take value of a macro".
- **`Compiler.isMacro` asks the Var, on the unevaluated head**, and a local
  binding shadows it: "no local macros for now".
- **Every macro takes two hidden parameters.** `macroexpand1` builds
  `RT.cons(form, RT.cons(LOCAL_ENV.get(), form.next()))`; core.clj names
  them `&form` and `&env`. `RT.bootNamespace` spells the signature out:
  `invoke(Object __form, Object __env, Object arg1)`.
- **`(.member target args)` is `(. target member args)`**, rewritten in
  `macroexpand1`, as is `(Classname. args)` to `(new Classname args)`.
- **`fn*` takes an optional self-name**, bound inside the body so the
  function can call itself without going through its Var. core.clj writes it
  on nearly every primitive.
- **A seq is a call.** `Compiler.eval` dispatches on `ISeq`, not on one
  concrete list class. It has to: a macro assembles its expansion with
  `cons` and `seq`, so what comes back is a lazy cell or a view over a
  vector, never a `PersistentList`. Evaluating only cons cells made every
  such expansion self-evaluate in silence.
- **`recur` into a variadic arity binds the rest parameter directly**, to
  whatever value is passed -- it does not re-collect the remaining
  arguments. `(recur ret (first ks) (next ks))` must be able to hand `ks` a
  nil; re-collecting makes it `(nil)`, which is truthy, and core.clj's own
  `disj` then never terminates.
- **`conj` onto a map merges another map** (`APersistentMap.cons` walks the
  argument's seq and assocs each entry) and assocs a pair. `defn` builds a
  Var's metadata by conj-ing maps together.
- **The empty list is a singleton.** `PersistentList.EMPTY`.
- **`rest` returns a seq, never nil.** `next` is the one that returns nil --
  `RT.more` versus `RT.next`, which differ only there.
- **A Var is mutated on redefinition, not replaced** -- but ONLY by the
  namespace that owns it. That is what makes redefining a function at the
  REPL visible to existing closures, and what lets core.clj redefine a
  primitive that was interned natively. `Namespace.intern` gates it on
  `isInternedMapping`, and skipping that gate was a real bug: a namespace's
  mappings hold the Vars it REFERS as well as the ones it interned, so
  `(defn first [x] :s)` in any namespace found clojure.core's referred
  `first` and mutated THAT, redefining `clojure.core/first` for the whole
  program. Replacing a referred name now interns a new Var and prints
  `Namespace.checkReplacement`'s warning verbatim:

      WARNING: first already refers to: #'clojure.core/first in namespace: w1, being replaced by: #'w1/first

  A namespace that declares the shadowing up front --
  `(:refer-clojure :exclude (next))`, as `clojure.zip` does -- has nothing
  left to replace and so says nothing, which is also what Clojure does.
  `clj` prints this; babashka does not, being a reimplementation that
  omits it. That is why `clj` is the language oracle and bb is only the
  scripting language -- bb agreed with the old broken behaviour and with
  the new correct one, and so told us nothing either time.

---

## 15. `hash` answers different numbers than the JVM does

Clojure specifies `hash` as `Util.hasheq`, a murmur3 mix, and exposes the
algorithm through `hash-ordered-coll` and `hash-unordered-coll`. clotran
answers `gc_hash` instead: `(hash \a)` is 1915844612 here and 97 there.

This is a host difference rather than a defect -- ClojureScript's hashes
disagree with the JVM's too -- and the only property anything in core.clj
relies on holds: equal values hash equal. `case` is the load-bearing
caller. Its macroexpansion buckets the test constants by
`clojure.lang.Util/hash`, and `case*` re-derives the same case-int from
the runtime value, so both sides must be the SAME hash. Pointing either
at murmur3 without the other would silently send every `case` to its
default.

It would go away by implementing murmur3 in `gc_hash`, which is worth
doing only if a program ever needs a hash to match the JVM's across the
wire.

---

## 16. Names resolve at call time, not while analysing

Clojure resolves every symbol in `Compiler.analyze`, lexically, in the
namespace being compiled, before any bytecode exists. ClojureScript does
the same in `cljs.analyzer/resolve-var`, against an `env` carrying `:ns`
and `:requires`. clotran resolves in `gce_eval`, when the form runs,
against whatever `*ns*` is at that moment. SEAMS.md has the full
argument; this is the ledger entry.

Two patches stand in for the missing lexical information:

- **`__defining-ns__`**, an environment binding `make_closure` puts on
  every closure outside `clojure.core`, naming the namespace the closure
  was written in. `resolve_var` and syntax-quote both consult it before
  `*ns*`. It is INHERITED from the enclosing environment rather than read
  fresh from `*ns*`: a nested `fn` created while a macro is running
  belongs to the namespace that wrote it, not the one that called it.
- **Syntax-quote resolves aliases and Vars at expansion time** rather
  than read time (deviation 6), using that same binding, so
  `` `temp/do-template `` becomes `clojure.template/do-template`.

An unqualified symbol is only qualified when it actually resolves in the
writing namespace. Clojure qualifies unconditionally; doing that here
would break the bootstrap, where core.clj's own names must still fall
back to `clojure.core` (deviation 3).

It goes away by resolving names in `gce_analyze`, which already runs once
per top-level form and today only macroexpands.

## 17. A deftype's short name is global, not imported per namespace

`(deftype Point [x y])` expands to `(deftype* clojure.core/Point
clojure.core.Point ...)` followed by `(import clojure.core.Point)`, and
on the JVM that import is what makes the bare name `Point` mean that
class *in that namespace and nowhere else*. clotran's `import` is a
no-op (deviation 12's neighbour: a class is recognised by the SHAPE of
its name, so there is no class table to bind into), so there is nowhere
namespace-local to record it.

Instead `deftype*` registers the type under BOTH its full name and its
last segment, and `instance?` accepts an unqualified name that matches
the last segment of the declared one. `(Point. 3 4)`, `(new Point 3 4)`
and `(instance? Point p)` therefore work -- but they work *everywhere*,
not only where the import ran. Two namespaces each defining a `Point`
make the bare `Point` ambiguous, and the last one defined wins. The
fully-qualified name is never ambiguous. Measured:

    (ns aa) (deftype Point [x])
    (ns bb) (deftype Point [x y])
    (ns cc)
    (.-x (aa.Point. 1))     ;=> 1
    (.-y (bb.Point. 1 2))   ;=> 2
    (Point. 1)              ;=> arity error -- the bare name is bb.Point

It goes away when namespaces carry an import table, which is the same
place `clojure.core/import` would have to write.

## 18. A deftype instance prints without an identity

Clojure prints one as `#object[user.Point 0x4a2e1f "user.Point@4a2e1f"]`.
clotran prints `#object[user.Point]`. There is no address to report --
the heap is index-based and a slot index is not stable across a
collection -- and inventing a number would make two runs of the same
program print differently for no reason. Nothing reads the identity
back, so the only loss is that two distinct instances of one type print
identically.

## 19. `recur` in a deftype method must pass `this`

Clojure supplies the target object automatically, so a `recur` in a
method body passes one fewer argument than the method head declares:
"recur calls to the method head should *not* pass the target object, it
will be supplied automatically and can not be substituted." That is a
JVM artifact -- `this` is not a parameter there, it is the receiver.

Here a method is an ordinary closure whose first parameter is `this`, so
the recur point has the arity the head is written with and `recur` takes
all of them. A method body ported verbatim from Clojure that recurs will
get an arity error, which is at least loud.

It goes away by making the method's recur point exclude its first
parameter, which is a change to `select_clause`'s partner in
`eval_recur`, not to `deftype*`.

## 20. Mutable deftype fields are refused, not honoured

`^:volatile-mutable` and `^:unsynchronized-mutable` on a field are read
and discarded, and `(set! afield aval)` in a method body fails with
"set! needs a var". A method body sees its fields as let-bound locals
(that is how `bind_fields` gives them plain names), and a local is not
an assignable place, so the write has nowhere to go.

Measured, both ways:

    ;; clotran
    (set! v (inc v))   ;=> error: set! needs a var
    ;; clj, same deftype
    (set! v (inc v))   ;=> 2, and (str b) is then "2"

A LOUD failure rather than a silent discard, which is the one thing
that matters here: nothing quietly keeps the old value. Nothing in the
vendored tree uses a mutable field, so this blocks nothing today.

It goes away when a field is a writable slot rather than a let binding
-- the representation already allows it, since an instance holds its
fields in a run `gc_set_slot` can write.

## 21. `pr` of a namespace shows its name, not an `#object[...]` form

Clojure separates two things about a Namespace, and clotran can only
reproduce one of them:

| | Clojure | clotran |
|---|---|---|
| `(str *ns*)` | `"user"` | `"user"` |
| `(str [*ns*])` | `"[#object[clojure.lang.Namespace 0x.. \"user\"]]"` | `"[#<ns user>]"` |
| `(pr-str *ns*)` | `"#object[clojure.lang.Namespace 0x.. \"user\"]"` | `"user"` |

`Namespace.toString` is the NAME -- that is the row that matters, since
`namespace-munge` is `(.replace (str ns) \- \_)` and `deftype` builds
its class name out of it. clotran answers that correctly, and answers
the nested case correctly too, because a collection's `toString` prints
its elements rather than calling `toString` on each.

`pr` is the row it cannot reach. `core_print.clj` registers only
`print-dup` for `Namespace`, never `print-method`, so Clojure falls
through to `print-method Object` -> `print-object` ->
`print-tagged-object`, which writes `#object[` plus
`(format "0x%x " (System/identityHashCode o))`. clotran has neither
piece: `String/format` is not implemented, and there is no identity hash
to print for the reason in deviation 18 -- the heap is index-based, so a
slot index is not a stable identity. Dispatch therefore lands on
`print-method :default` -> `print-simple`, which is `(.write w (str o))`,
and `str` is the name.

Nothing in the vendored tree prints a namespace this way; the cost is
that `(pr-str *ns*)` does not round-trip through `read`, which the
`#object[...]` form does not either.

It goes away with `String/format` and an identity for host objects --
the same two pieces deviation 18 needs, and worth doing once for both
rather than twice.

The same holds for every other host object: a function prints as
`#<fn>`, a namespace as `#<ns user>`, where Clojure prints
`#object[user$eval1$fn__2 0x1a2b "user$eval1$fn__2@1a2b"]`. There is
no class name to report and no stable address (deviation 18), and
nothing reads the form back. `scripts/oracle` records these as
expected differences.

## 22. RESOLVED -- collections as keys hash and compare structurally

Kept as a record because the fix changed hashing semantics, and
because the way it was measured is worth remembering.

A collection used to hash and compare by its POOL SLOT, so an equal key
built anywhere else missed:

    (get {[1] 2} [1])                             ;=> nil,      clj 2
    (= #{[1]} #{[1]})                             ;=> false,    clj true
    (case {:a 1 :b 2} {:b 2 :a 1} :map :default)  ;=> :default, clj :map

All three now answer as Clojure does. `=` had been structural all
along, which is what made it confusing: the value compared equal and
the lookup still failed, because finding the key goes through
`gca_get`/`gca_contains` and those use `gc_equal`.

Hash and equality are installed TOGETHER, through `gc_set_coll_ops`,
and against the same notion of equality -- `deep_equal`, the one `=`
already used. A structural hash with an identity equality (or the
reverse) is worse than either alone: it puts one key in a trie twice
and finds whichever arm a lookup walks into.

Walking a collection needs logic that lives above `GC.f90` -- a
persistent vector is a 32-way trie -- so both are procedure-pointer
hooks, the same dependency inversion the finalizer uses.

Two details the invariant forced:

- Maps and sets hash UNORDERED, as a sum. Two equal maps may hand back
  their entries in different orders, and a fold that cared would hash
  them differently.
- A list and a vector of the same elements are equal in Clojure, so
  they share one hash scheme rather than mixing their kind in.

**What is left.** A LAZY SEQ as a key still hashes by identity.
Hashing one means realizing it, and `gc_hash` runs inside map inserts
and lookups, where an allocation can collect the half-built structure.
Equality only consults the hook when both sides are structural kinds,
so the two stay in step rather than disagreeing.

**How this was found**, which is the part worth keeping: two
assertions in Clojure's `control` suite were PASSING under the old
identity hashing, because a slot hash happened to land in the bucket
holding the right key and `=` then agreed. Widening integers to 64 bits
moved every bucket and the coincidence ended, so the scorecard fell by
two with nothing in the collection code having changed. Neither number
was measuring correct behaviour. Fixing it properly moved Clojure's
suite from 778 passing assertions to 797, all of it in two namespaces:
`control` 156 -> 164 and `clojure-set` 99 -> 110.

## 23. `(instance? clojure.lang.IObj f)` is false for a function

A function answers `IMeta` but not `IObj`. Clojure says both.

The reason is `print-method`'s `:default`:

    (if (instance? clojure.lang.IObj o)
      (print-method (vary-meta o #(dissoc % :type)) w)
      (print-simple o w))

Anything answering IObj there must have a `print-method` that DISPATCH
CAN REACH, or `:default` calls itself on the same object forever. A
closure had none: `host_super` has no entry for `fn`, `core_print`
registers nothing on `IFn`, and `print-method Object` is unreachable
because `print-object` needs `String/format`. So `(prn (fn [x] x))`
recursed until the stack ran out and the process died -- the same shape
as the vector segfault `host_super` was written to fix.

Answering false sends a closure to `print-simple`, which is
`(.write w (str o))` -- `#<fn>`, the shape every other host object here
prints in.

IMeta is answered SEPARATELY and a function does claim it. `meta` is
`(if (instance? clojure.lang.IMeta x) (.meta x))` at core.clj:210, so
the two being one case made `(meta (with-meta (fn [] 1) {:a 1}))` nil.
They are two cases now, and both behaviours are right:

    (meta (with-meta (fn [] 1) {:a 1}))   ;=> {:a 1}
    (pr-str (fn [x] x))                   ;=> "#<fn>"
    (instance? clojure.lang.IObj (fn []))  ;=> false, and clj says true

It goes away with `String/format`. That makes `print-object` run, which
makes `print-method Object` a reachable last resort for every type, at
which point `fn` can answer IObj truthfully. Deviations 18 and 21 want
the same thing, which is three reasons to do it once.

## 24. Arrays are never ragged

`(make-array Integer/TYPE 2 3)` in Clojure is `[[I` -- an array of two
references to separate `[I` arrays -- and nothing stops those rows
being different lengths, because each row is its own object.

clotran's is one rank-2 Fortran array: `a(2,3)`, a single contiguous
column-major block. Every row is the same length because there are no
rows, only a shape. A ragged array cannot be represented and will not
be.

This is a deliberate trade, not an omission. Contiguity is the entire
reason the representation is worth having -- the block can be handed to
a BLAS routine as a flat `buf(*)` argument, which `[[I` cannot be at any
price. Measured on the same memory:

    a(2,3) = 23.0                  ! a(i,j) access
    flat   = 11 21 31 12 22 32 ... ! the same bytes, column-major
    is_contiguous(a) = T
    flat(i + (j-1)*3) == a(i,j)    ! every cell

Note this one is NOT a JVM artifact, so SEAMS' usual test does not
apply: JavaScript arrays are nested too, and ClojureScript inherits the
same raggedness. It is a capability real Clojure has, given up on
purpose, in exchange for one real Clojure cannot offer.

It goes away only by representing arrays as arrays-of-arrays, which
would mean giving up the thing the project exists for.

## 25. `aset` on a primitive array accepts any number

Real Clojure:

    (aset (make-array Integer/TYPE 3) 0 10)
    ;; IllegalArgumentException: argument type mismatch
    ;;   java.lang.reflect.Array/set

`Array/set` takes an `Object`, so `10` arrives as a boxed `Long` and
the JVM refuses to store it in an `int[]`. Getting it in requires the
type to be exact -- `(aset-int a 0 10)` or `(aset a 0 (int 10))` --
and `aset-int` exists precisely because the plain one cannot do it.

clotran stores it. There is no boxing here, so there is no boxed type
to mismatch: an int array is `integer(4)` and the value is a clotran
integer, which goes in. The typed family -- `aset-int`, `aset-double`,
`aset-boolean` -- all reach the same builtin, because on the JVM they
differ only in the boxing they avoid.

So clotran is strictly more PERMISSIVE: every program real Clojure
accepts, clotran accepts and agrees with. What differs is that a
program relying on the exception -- catching it to detect a wrong
element type -- sees no exception. The tests in `language_test.clj`
use `aset-int`/`aset-double` anyway, so they mean the same thing under
both.

Closing it would mean tracking a declared element type per call site
and rejecting a value whose Clojure type is not exactly it, which is
re-creating boxing in order to reproduce its error message.

## 26. Integer overflow wraps where Clojure throws

The reader agrees with Clojure on every number SHAPE (hex, octal,
explicit radix, exponents), ratios are exact, and integers are 64-bit
like Clojure's `long`. What is left is the top of that range. Measured,
clotran first, `clj` second:

    (* 9999999999 9999999999)  7766279611452241921   throws "long overflow"

Clojure checks and raises `ArithmeticException: long overflow`; Fortran
wraps, and clotran does not check. So this is a wrong answer that looks
plausible -- the failure mode CLAUDE.md singles out -- but it is now
confined to values above 2^63 rather than above 2^31.

What it replaced is worth recording, because it stood for a long time
and showed on no scorecard: `ival` was Fortran's default `integer`, 32
bits, so `9999999999` read back as `1410065407` and `2147483648` as
`-2147483648`. The `real` beside it in `gc_value` had been widened to
`real(8)` early on with precisely this argument, and the integer was
left behind.

Closing the remainder means checking each operation for overflow and
raising, and then arbitrary precision behind `+'`, `*'` and friends,
which promote instead of throwing.

`42N` and `1.5M` read as SYMBOLS, so they resolve to nothing and fail
where they are used rather than where they are read. They are not read
as 42 and 1.5: answering with a near-miss of a different type would be
the same silent-wrong-answer mistake as the truncation above.

`3/4` used to be in that list and is not any more -- there is a real
Ratio now, exact and normalized, and `(/ 1 3)` is `1/3` rather than
`0.3333333333`. What remains is one difference of TYPE, not of value:
when ratio arithmetic collapses to a whole number Clojure answers a
BigInt and clotran answers an integer.

    (+ 1/2 1/2)   clotran 1    clj 1N
    (/ 1/2 1/4)   clotran 2    clj 2N

That is Clojure's Ratio arithmetic running through BigInteger, so the
result carries BigInt's type out with it. Both agree the value is one
and two, and `(= 1 1N)` is true, so it shows only in `type` and in
printing. It goes away with BigInt and not before.

Raising at READ time was tried and reverted, and the reason is worth
keeping. These are valid Clojure, so a reader error is not merely
pedantic -- and clotran aborts a whole file on one (deviation 1), so a
single `2/3` takes every form after it down. Twelve of Clojure's 67
test namespaces contain a ratio literal; erroring on them took the
suite from 766 passing assertions to 223, `control.clj` alone losing
153. A symbol is wrong in one form; an error was wrong in every form
after it.

The two real fixes are a Ratio type, or per-form reader recovery so
that one unreadable form does not abort a load. Both are larger than
the reader.

A ratio narrows on the same edge, and sooner. Its numerator is 64-bit
like any other integer, but the DENOMINATOR lives in the field a heap
reference would use, which is 32-bit -- so a denominator past 2^31
wraps. The intermediate of a sum is the product of the denominators,
and reducing at every step rather than once at the end keeps that as
small as it can be without removing the ceiling.

## 27. The two smallest subnormal doubles print with one digit too few

`Double.toString` is specified as the shortest decimal that reads back
as the same double, and clotran's printer finds exactly that -- by
writing the value with one significant digit, then two, then three,
reading each back and stopping at the first that returns the same bits.
It agrees with Clojure on every value tried except two, at the very
bottom of the subnormal range:

| | clotran | clj |
|---|---|---|
| `(pr-str Double/MIN_VALUE)` | `5.0E-324` | `4.9E-324` |
| `(pr-str 9.9E-324)` | `1.0E-323` | `9.9E-324` |

Both of clotran's answers read back as the same double -- `5E-324` and
`1E-323` are unambiguous, because at that magnitude the neighbouring
representable values are a factor of two apart. They are genuinely
shorter than the JDK's, so this is not a rounding error; the JDK emits
a second digit here that its own specification does not require.

`(= (read-string (pr-str x)) x)` holds for both, which is the property
that matters. What differs is the text, and only for the two smallest
positive doubles there are.

Removing it means reproducing `Double.toString`'s exact digit choice
rather than the shortest round trip -- worth doing only if something
starts comparing printed doubles as strings.

## 28. `proxy` is a special form, and accepts methods no superclass declares

Clojure's `proxy` is a macro in `core_proxy.clj`, which is not vendored:
it is written against the class loader, generating a class at runtime
and installing a method map on it. There is no class loader here, so
the macro cannot run.

clotran makes `proxy` a special form instead, built on the machinery
`reify` already uses -- a type object whose methods are closures, and
one instance of it. The two shapes `proxy` has that `reify` does not
are handled by rewriting the forms before that machinery sees them:
`this` is prepended to every parameter vector, and nested arities
(`(f ([] 0) ([a] a))`) are flattened into the one-arity-per-form list
`reify` writes by hand.

Three differences remain, all of them consequences of clotran having no
class hierarchy (deviation 4):

**Any method name is accepted.** Real Clojure checks each method
against the superclass and interfaces given, and refuses one they do
not declare:

    (.f (proxy [Object] [] (f [] 1)))
    ;; clj     No matching field found: f
    ;; clotran 1

There is nothing to check against: `[Object]` is a keyword, not a class
with a method table. So a typo'd method name is silently a new method
rather than an error.

**The constructor arguments are read and discarded.** `(proxy [C] [a b]
...)` has no superclass to construct.

**`proxy-super` does not exist**, for the same reason -- there is no
superclass method to call through to.

**Removal**: vendoring `core_proxy.clj` does not help; it needs
`Class/forName`, `.getDeclaredMethods` and a class loader. Removing
this means giving clotran real classes, which is the same work
deviation 4 names.

## 29. An agent's action runs on the calling thread, before `send` returns

Clojure's `send` queues an action onto a thread pool and returns
immediately; the agent's value changes some time later, and `await`
blocks until the queue drains. clotran has one thread, so `.dispatch`
runs the action on the spot and `send` returns an agent whose value has
already changed.

Everything built on that is real: the error mode (`:fail` or
`:continue`), the error handler, `agent-error`, `restart-agent` and
validators all behave as Clojure describes them. What differs is *when*:

    (send a slow-fn)
    @a          ;; clj      the OLD value, for a while
                ;; clotran  the new one, always

    (await a)   ;; clj      blocks
                ;; clotran  returns at once, there is nothing in flight

`await` is written around a `CountDownLatch`, which is here a plain
counter for the same reason: the count is already zero by the time
anything waits on it.

The difference is visible in exactly one place a single-threaded program
can see it -- an action that throws surfaces its exception at the `send`
call rather than on the agent's own thread. `send` still returns the
agent rather than rethrowing, so the failure is observed through
`agent-error` as Clojure intends.

**Removal**: threads. This is the same seam as deviation 10 (refs are
mutable boxes) and 11 (transients are the persistent collections) --
every one of them is single-threadedness showing through, and none of
them can go until Fortran here has somewhere to put a second thread.

## 30. `1N` is an integer and `1M` is a double

Clojure reads `1N` as a `clojure.lang.BigInt` and `1M` as a
`java.math.BigDecimal`. clotran has neither type, and used to read both
as SYMBOLS -- so `(cond 0M :a true :b)` answered "unable to resolve
symbol: 0M" rather than `:a`, and `(= 45M (deref a))` could not run at
all.

Each suffix now drops to the nearest thing clotran does have, and the
choice was made by what `=` then says rather than by which looks
closest:

| | Clojure | clotran | why |
|---|---|---|---|
| `1N` | BigInt | integer | `(= 1N 1)` is TRUE in Clojure, and stays true |
| `1M` | BigDecimal | double | `(= 1M 1)` is FALSE in Clojure, and `(= 1.0 1)` is false here |

Reading `45M` as the integer `45` would have been the obvious choice and
the wrong one: it makes `(= 45M 45)` true where Clojure says false,
because a BigDecimal is its own equality category. A double lands in a
different category from an integer for exactly the same reason, so the
comparison comes out right without the type existing.

What is lost is arbitrary precision and the type itself:

    (type 1N)     clojure.lang.BigInt      -> :int
    (type 1M)     java.math.BigDecimal     -> :double
    (pr-str 1N)   "1N"                     -> "1"
    (pr-str 1M)   "1M"                     -> "1.0"
    (* 1M 0.1M)                            -> not exact decimal

and, with it, everything `with-precision` is for. A literal past
2^63 is the same 64-bit ceiling deviation 26 names.

**Removal**: a numeric tower with BigInt and BigDecimal in it. That is
the same work deviation 26 ends on, and the suffixes are its most
visible symptom rather than a separate problem.

## 31. Stack traces are empty

`(.getStackTrace e)` answers an empty array; Clojure answers one
`StackTraceElement` per frame, and `clojure.stacktrace` and
`clojure.test`'s failure reports print them. The evaluator keeps no
frames -- there is nothing to report. It is honest rather than wrong:
`(alength (.getStackTrace e))` is 0, never a fabricated trace.

**Removal**: PLAN.md step 5. Once evaluation runs over explicit frames
with source positions on nodes, a trace is a walk up that stack, and
this entry closes together with the debugger it unblocks.
