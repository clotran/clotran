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
| 1 | Load reads the whole file, then evaluates | temporary | `src/f/gc_main.f90` |
| 2 | `host.clj` preloaded before `core.clj` | temporary | `src/clj/host.clj` |
| 3 | Symbols fall back to `clojure.core` instead of being referred | temporary | `src/f/GCEval.f90` |
| 4 | `.` reaches a fixed table of host members, not arbitrary classes | host | `src/f/GCEval.f90` |
| 5 | Metadata is a wrapper object, not carried on the value | host | `src/f/GC.f90` |
| 6 | Syntax-quote expands at eval time, not read time | open | `src/f/GCEval.f90` |
| 7 | Recursion depth is ~600 frames, against Clojure's ~11,200 | host | `src/f/GCEval.f90` |
| 8 | Multimethods dispatch on equality, plus a fixed host hierarchy | temporary | `src/f/GCEval.f90` |
| 9 | Sorted collections are unsorted | temporary | `src/f/GCEval.f90` |
| 10 | Refs are mutable boxes; dynamic bindings are global | temporary | `src/f/GCEval.f90` |
| 11 | Transients are the persistent collections | host | `src/f/GCEval.f90` |
| 12 | Five JVM-only libs are skipped by name, and not vendored | host | `src/f/GCEval.f90` |
| 13 | Protocol dispatch is uncached | host | `src/f/GC.f90` |
| 14 | Regex is ICU under java.util.regex's names, ASCII-offset only | host | `src/f/Regex.f90` |
| 15 | `hash` values are gc_hash's, not the JVM's murmur3 | host | `src/f/GC.f90` |
| 16 | Names resolve at call time, not while analysing | host | `src/f/GCEval.f90` |

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
`instance_member` table in `GCEval.f90` as they come up, the same way
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

## 22. A collection used as a map key or set element matches by identity

Values compare deeply. KEYS do not:

    (= {:a [1]} {:a [1]})   ;=> true,  and clj agrees -- a value
    (= {[1] 2} {[1] 2})     ;=> FALSE, clj says true -- a key
    (get {[1] 2} [1])       ;=> nil,   clj says 2
    (= #{[1]} #{[1]})       ;=> FALSE, clj says true

`deep_equal` compares a map's values with itself, so a collection VALUE
is structural. Finding the key to compare is `gca_get`/`gca_contains`,
which use `gc_equal` -- same tag, same scalar or text, and for anything
in the object pool the same POOL SLOT. Two structurally equal vectors
are two slots, so neither is found under the other.

`gc_equal` says so in its own comment and calls it a separate decision;
this is that decision written down rather than left implicit. It is the
same root cause for maps and for sets, because a set is a map from each
element to itself.

Scalars -- keywords, symbols, strings, numbers -- are exact, and that is
what a map key almost always is. Nothing in the vendored tree keys a map
by a collection.

Removing it is bigger than it looks: `gca_get` would need deep equality,
and the HAMT path would need `gc_hash` to hash a collection
STRUCTURALLY, so that two equal vectors land in the same bucket before
equality is ever consulted. That is a change to hashing semantics --
see deviation 15, which is the other half of the same subject -- and
wants its own commit.
