# Deviations from Clojure

Every place clotran does something real Clojure does not, why, and what it
would take to remove it. A deviation with no entry here is a bug.

Not everything native is a deviation. Where we merely *chose* Fortran over
pure Clojure for something Clojure could express, that is a seam, and it
belongs in SEAMS.md instead.

**Reference**: `~/jborden/clojure` -- a clone of `clojure/clojure` at
`clojure-1.12.6` (`31a3138a`) -- the SAME release as the vendored core.clj (see
src/clj/clojure/PROVENANCE.md). Paths below are relative to it. Cite the file and the method;
do not cite memory. That is the whole point of having the clone.

Categories:

- **temporary** -- a scaffold. Bootstrapping is incomplete; it goes away.
- **host** -- forced by Fortran. Cannot go away, but must be invisible.
- **open** -- we do not yet know which of the above it is.

| # | What | Kind | Where |
|---|------|------|-------|
| 1 | RESOLVED -- load reads one form, evaluates it, reads the next | -- | `src/f/main.f90` |
| 2 | `host.clj` preloaded before `core.clj` | temporary | `src/clj/host.clj` |
| 3 | Symbols fall back to `clojure.core` instead of being referred | temporary | `src/f/Eval.f90` |
| 4 | `.` reaches a fixed table of host members, not arbitrary classes | host | `src/f/Eval.f90` |
| 5 | Metadata is a wrapper object, not carried on the value | host | `src/f/GC.f90` |
| 6 | Syntax-quote expands at analysis time, not read time | open | `src/f/analyze.inc` |
| 7 | Recursion depth is ~600 frames, against Clojure's ~11,200 | host | `src/f/Eval.f90` |
| 8 | RESOLVED -- multimethods dispatch with `isa?` and preferences | -- | `src/clj/clotran/multifn.cljf` |
| 9 | RESOLVED -- sorted collections | -- | `src/f/Assoc.f90` |
| 10 | RESOLVED for refs -- transactions, serialized; `set!` of an unbound Var sets its root | temporary | `src/f/Eval.f90` |
| 11 | RESOLVED -- transient maps and sets are boxes mutated in place; vectors are real transients | -- | `src/f/Eval.f90` |
| 12 | Three host-bound libs are skipped by name, and not vendored | host | `src/f/Eval.f90` |
| 13 | Protocol dispatch is uncached | host | `src/f/GC.f90` |
| 14 | Regex is ICU under clj's regex's names; `\w` and `(?i)` are Unicode | host | `src/f/Regex.f90` |
| 15 | `hash` values are gc_hash's, not clj's murmur3 | host | `src/f/GC.f90` |
| 16 | RESOLVED -- names resolve while analysing | -- | `src/f/analyze.inc` |

---

## 1. Load reads the whole file before evaluating any of it

`Compiler.load` interleaves: it reads one form, evaluates it, and only
then reads the next (upstream's `Compiler`, in the clone at
`~/jborden/clojure`).

We call `gcr_read_all` first. This is observably wrong wherever reading
depends on state that evaluation sets -- `::kw` resolves against `*ns*`,
`#'` and `#=` read-time evaluation, and any change to `*read-eval*` or
`*data-readers*`.

**Removal**: make the reader streaming over a cursor so a form can be read,
evaluated, and the next read begun. `gcr_read_all` already walks a cursor
internally; it needs to be exposed one form at a time.

**RESOLVED 2026-09-19.** `gcr_read_next` reads one form from a
position and advances it; `load_file` in main.f90 and the `load-file`
builtin read, analyse, evaluate and read again, as `Compiler.load`
does. The same change gave list forms a source position (the opening
paren's offset, on the cons cell), which the analyser copies to its
node and an error reports as `file:line:col`.

## 2. `host.clj` is loaded before `core.clj`

Clojure loads nothing before `clojure/core.clj`; its bootstrap is clj
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

`RT`, `Numbers`, `Util`, `Symbol`, `Keyword`, the three
`create` statics, and a list of instance members -- all in `static_member`
and `instance_member`. Clojure reaches any clj class by reflection.

A CLASS SYMBOL in code (2026-09-28): a qualified one -- `user.Person`,
`no.such.Klass` -- must name a class that exists, as `Class.forName`
must in clj, or it is Compiler's "Unable to resolve classname".
What exists here: a class with a row in the tables, a deftype or
defrecord (from the moment its `deftype*` is analysed, as clj has
the class from compiling it), an interface a type implements, a
protocol's interface (its namespace, munged or not, holds the Var), and
anything under `clotran.` -- the host's classes and the types clotran's
namespaces define, whose namespace loads when one is first named. A
bare name is a class only through an import or as a type clotran
knows; any other is "Unable to resolve symbol", as in clj, and so is a
`catch` of a class there is not (DEVIATIONS 67).

This one is **host**, not temporary: there is no Fortran reflection to
reach, and the classes core.clj names do not exist here. What the table
holds is clotran's own primitives under the host's names -- `RT.more` is
what we already mean by `rest`, `Numbers/add` is `+` -- so the entries are
bindings, not adapters. It grows as core.clj asks for more.

An unlisted member fails **by name**, never as a generic `.` failure, so a
load report says which one to add next -- in Reflector's words for an
instance member, "No matching method jump found taking 1 args for class
String", so `thrown-with-msg?` can match it.

The exception classes have no hierarchy either, with two edges and a
ceiling: `Throwable` and `Exception` catch everything; `RuntimeException`
catches every runtime class clotran throws (`is_runtime_class` lists them,
and a host failure is one); `ArityException` is an
`IllegalArgumentException`. Since 2026-09-27 a few more parents that
code catches by are known (Eval.f90, exc_parent): `NumberFormatException`
is an `IllegalArgumentException`, `FileNotFoundException` and
`EOFException` are `IOException`s, and the array and string index
exceptions are `IndexOutOfBoundsException`s. A class caught under any
other parent is not caught.

## 5. Metadata is a wrapper object

Clojure carries metadata ON the value: `Symbol`, `PersistentList` and the
rest implement `IObj`, so `^:static foo` is a Symbol that happens to have a
map attached. `gc_value` is a fixed four-field struct with no room for one,
so metadata is an `OBJ_META` object holding value and map.

This is **host**, and the cost is that everything which RECOGNISES a value
has to see past the wrapper: `strip_meta` at each of those points, and
`type_name` unwrapping so `(instance? Symbol ^:static x)` is
still true. `with-meta` replaces rather than nests, matching `withMeta`.

Every place that forgot to unwrap was a real bug, and core.clj found them
all: a hinted parameter invisible in its own body, a hinted parameter
vector read as an arity mismatch, a hinted head symbol unresolvable, a Var
interned under a name nobody could spell.

**Removal**: none available. Widening `gc_value` would cost a word on every
value in the heap to serve the few that carry metadata.

## 6. Syntax-quote expands at analysis time, not read time

`SyntaxQuoteReader` is a READER macro (`LispReader`): `` `x `` is
resolved, gensym-ed and expanded into `concat`/`seq` calls before the form
is ever evaluated. Ours is a `quasiquote` special form that `qq_expand`
handles during ANALYSIS (`analyze_quasiquote`), once per form, in the
namespace the form is analysed in -- which for a macro body is the
namespace the macro was written in. It used to run at every evaluation.

Auto-gensym is faithful -- one fresh name per syntax-quote, scoped by a map
the way `GENSYM_ENV` is -- and so, since 2026-09-19, is symbol
resolution: `qq_alias` is `Compiler.resolveSymbol` as `syntaxQuote`
calls it. An unqualified symbol becomes `ns/name` -- the Var's own
namespace if it resolves to one, the writing namespace otherwise --
unless it is a special form, a class name, an auto-gensym, `&`, or host
sugar. That is what makes a macro immune to a caller having rebound a
name, and what makes clojure.test's `run-test` find `test-var`, which
is defined later in its file than the macro that names it.

Two consequences had to be handled where Clojure's compiler handles
them: a member name in a `.` form and a method name in a `deftype*`
arrive qualified and are read by their name part (`HostExpr.Parser`,
`NewInstanceMethod.parse`), and `(def ns/x ...)` defines `x` when `ns`
is the current namespace (`DefExpr`).

What remains open is only WHEN: analysis time rather than read time.
The difference is observable through `read-string` -- `(read-string
"`x")` answers the unexpanded `(quasiquote x)` here and the expansion
in Clojure -- and closes by moving `qq_expand` into the reader.

## 7. RESOLVED -- recursion runs out of stack about twenty times sooner

**RESOLVED 2026-09-19.** The executor is a loop over an explicit
continuation stack (exec.inc, `run`), so a Clojure call no longer
costs Fortran stack. Measured: a non-tail-recursive function reaches
100,000 deep and returns; clj's default stops near 11,000. The
limit is now a FRAME COUNT, 200,000 by default, `CLOTRAN_MAX_FRAMES`
to change it, and it bounds the call stack too. There is NO tail-call
optimisation, because Clojure has none: a tail-recursive function
without `recur` overflows at the limit, exactly as in clj, only
later. What a call in tail position reuses is the continuation frame
(memory), while the caller stays on the call stack, so a trace names
every call and the count is what overflows. `recur` is the loop. What still
nests on the Fortran stack is a native calling back into Clojure --
forcing a lazy seq, a multimethod's dispatch, a def's value -- and
`CLOTRAN_MAX_DEPTH` (2200) still bounds that. A rendered trace stops
at 128 frames with `... N more`; `.getStackTrace` has them all.

COMPILED code nests too: a compiled fn calling a compiled fn is a
Fortran call, counted against `CLOTRAN_MAX_DEPTH`, so compiled
recursion stops at about 2,200 deep where the interpreter's reaches
100,000 and clj's about 11,000 (measured 2026-09-29: a non-tail
recursion of 5,000 overflows compiled, runs interpreted). Raising it
means a Fortran stack sized for it; not done.

Since 2026-09-27 the VALUE stack is fixed, not grown: compiled code
holds a view of it across calls, so it may never move. 4,194,304 slots
per thread (64 MB of address space, calloc'd, so real only where
touched), `CLOTRAN_STACK_SLOTS` to change it. The frame limit trips
first -- its deepest case, a one-line fn at 200,000 frames, used
1,400,000 slots -- but a deep recursion through frames with many
temporaries could fill the stack before it, and that stops the process
("the value stack is full") where clj throws a catchable
StackOverflowError. The original entry follows.

Both runtimes stop somewhere; clj raises `StackOverflowError` and we
report `stack overflow near (f ...)`. What differs is how soon.

There is no depth to copy from Clojure, because clj's limit is a
**byte budget, not a frame count**: `-XX:ThreadStackSize`, 2048 KB by
default on this platform (`clj -XX:+PrintFlagsFinal -version`), divided
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
`eval_body`, `gce_eval` again for each argument -- where clj has a
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

## 8. RESOLVED -- multimethods dispatch with `isa?` over the hierarchy, and preferences

**RESOLVED 2026-09-21.** `MultiFn.getFn`'s selection -- every method
whose dispatch value the actual one `isa?`, the dominant one by
preference or by `isa?` when several match, the default when none, and
`IllegalArgumentException` when two match and neither dominates -- is
written in Clojure in `src/clj/clotran/multifn.cljf`, as ClojureScript
writes it in cljs.core. `prefer-method` records preferences and refuses
a conflict; `prefers`, `methods`, `get-method` and `remove-all-methods`
read and reset the tables; the hierarchy given to `defmulti` is honoured
and a change to it drops the per-multimethod cache (Eval.f90
`mf_lookup`). `isa?` on class keywords goes through `isAssignableFrom`,
which reads a deftype's interfaces and the host's supertype chains,
including what an interface extends.

One choice remains where clj's own answer is arbitrary: when two
matching methods each dominate the other -- one preferred through a
parent, the other by `isa?` -- clj takes whichever its method table
yields last; clotran takes the more specific by `isa?`. That is the
clj's answer for print-dup of a map, and nothing clj decides
deterministically differs.

## 9. RESOLVED -- sorted collections

`sorted-map`, `sorted-map-by`, `sorted-set`, `sorted-set-by`,
`subseq`, `rsubseq` and `rseq` work, from core.clj's own
definitions. A sorted map is the array map with its keys kept in
comparator order -- a flag and a comparator slot on the object, a
binary search, and no promotion to a hash trie however large it
grows (Assoc.f90) -- and a sorted set is a set over one. Every
assoc copies the two runs, so building one of n entries is O(n^2):
a balanced tree when a sorted map of many thousands matters. The
comparator is called through a hook Eval supplies, since ordering
may run a Clojure fn; with none it is Clojure's `compare`, and keys
it cannot order throw ClassCastException as in clj.

## 10. RESOLVED -- refs are transactional; `set!` of an unbound Var still sets its root

**RESOLVED for refs 2026-09-28** (feat/threads). `dosync` is a
transaction: `alter`, `commute` and `ref-set` write a per-transaction
log (Eval.f90, `tx_log`), a `deref` inside the transaction reads it
(`tx_value`), and the commit (`tx_commit`) validates every written ref
first -- one refusal and nothing is written -- then sets each and runs
its watches with the old and new values. An exception discards the
log. `alter` or `ref-set` outside a transaction is Clojure's
IllegalStateException "No transaction running"; `io!` inside one throws,
since `LockingTransaction/isRunning` answers. A `dosync` inside a
`dosync` is the same transaction.

What is NOT clj's: transactions are SERIALIZED under one lock
(`tx_lk`) rather than run optimistically with retries. Every schedule
this produces is a serial one, which is exactly what STM guarantees,
so no program can tell the difference by its values; what differs is
throughput under contention (none, here) and the history that retries
produce: `ref-history-count` is always 0, `ref-min-history` 0,
`ref-max-history` 10. `commute` is `alter` under serialization, which
is one of the orders commute permits.

Dynamic bindings are no longer part of this entry: since PLAN.md step
14f each thread has its own, as `Var.dvals` is a `ThreadLocal` -- a
stack of frames, each a map of Var to box, with the frame below merged
in (Namespace.f90, `gcn_var_value`; GC.f90, `gc_stack%bindings`).
`binding-conveyor-fn` carries a frame to a future through
`cloneThreadBindingFrame`/`resetThreadBindingFrame`, and
`get-thread-bindings`, `thread-bound?`, `bound-fn` and `var-set` give
what `clj` gives. What differs: `set!` or `var-set` of a Var with no
binding on this thread sets its ROOT, where Clojure throws "Can't
change/establish root binding of: *x* with set". clotran's `load` does
not bind `*warn-on-reflection*` and the rest the way `Compiler.load`
does, so a file's `(set! *warn-on-reflection* true)` would otherwise be
an error. Removal: bind those in `load` as `Compiler.load` does, then
throw.

## 11. RESOLVED -- transient maps and sets are boxes, mutated in place

**RESOLVED 2026-09-28.** `(transient m)` on a hash map or a hash set is
a box over the persistent value (`OBJ_TMAP`); `conj!`, `assoc!`,
`dissoc!` and `disj!` are the persistent operation on what is inside,
stored back into the box, which they answer; `count`, `get`,
`contains?` and `find` read through; `persistent!` seals the box and
answers the value, and any use after that is Clojure's
IllegalAccessError "Transient used after persistent! call". So
`(let [t (transient {:x 1 :y 2})] (dissoc! t :x) (persistent! t))` is
`{:y 2}` here as there, where it used to be `{:x 1 :y 2}`, and
`(persistent! (dissoc! t :x))` still is. Hash maps and hash sets are
`IEditableCollection`, so `into` takes the transient path as on the
clj; sorted collections have no transient there or here. The class is
`PersistentHashMap$TransientHashMap`, `PersistentArrayMap$TransientArrayMap`
or `PersistentHashSet$TransientHashSet` by what is inside. A vector's
transient was real since 2026-09-26 (PersistentVector.f90).

What is NOT clj's: the box does no in-place editing of the
structure itself, so `assoc!` costs what `assoc` costs -- the speed a
transient buys in clj is not bought here, only the semantics.

## 12. Three host-bound libs are skipped by name

`core_proxy`, `genclass` and `gvec`, plus Clojure's io library, which
clotran replaces with its own, `clotran.files` (DEVIATIONS 40). The first two import
`clojure.asm`, `ClassWriter` and `DynamicClassLoader` to emit bytecode;
`gvec` wants clj's collection library. `uuid` was skipped until
2026-09-28; it now runs verbatim on a `UUID` that clotran.rt
defines as a record under that name.

Named individually rather than tolerating any missing file, so a real
typo in a load path is still an error. `instant` needs no entry: it is
guarded by `when-class`, and since `Class/forName` throws
`ClassNotFoundException` here, core.clj declines to load it on its own.

## 13. RESOLVED -- protocol dispatch is cached

`MethodImplCache` is a map with the right fields, and `fnFor` read
nothing: it always answered nil, a permanently cold cache, so every
protocol call went through `-cache-protocol-fn` and
`find-protocol-method` -- the correct path, at 13 us a call. Since
2026-09-29 `fnFor` is MethodImplCache.findFnFor's map branch
(Eval.f90 `B_FNFOR`): the entry the cache's map holds for the class,
and its fn. core.clj's own `-cache-protocol-fn` fills the map on the
first call for a class, as it does in clj, and re-extending a
protocol resets the caches the same way, so nothing else changed: a
protocol call is two map lookups, 0.95 us. The `mre` (most recent
entry) shortcut and the hashed-table form are not modelled; the map
form answers the same.

The cache is stored on the function object itself, which is why
`OBJ_SLOTS` is 5 rather than 4: a closure's four slots are params, body,
env and arity clauses, and a protocol method has one clause per
signature, so none was free. The fifth slot costs one `gc_value` on
every object in the heap.

## 14. Regex is ICU, wearing clj's regex's names

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

- **~~ASCII/Latin-1 only~~ -- FIXED 2026-09-21; what is left is
  the class definitions.** The shim decodes the pattern and the
  subject as UTF-8 (`u_strFromUTF8`; bytes that are not UTF-8 are
  widened one to one as before), so a match is over characters and
  every offset ICU reports is a character index, which the Fortran
  side turns into bytes with `u8_slice` (deviation 41). What still
  differs is what a class MEANS: clj's regex's `\w`, `\d`, `\s`
  and `\b` are ASCII unless `(?U)` is given, and `(?i)` folds ASCII only
  unless `(?u)` is; ICU's are Unicode always. So `(re-find #"\w+"
  "héllo")` is `"héllo"` here and `"h"` in clj, and `#"(?i)É"`
  finds `é` here and nothing there. The oracle marks both.
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

**Removal of the class difference**: ICU has no ASCII-only mode for
its classes; the pattern would be rewritten on the way in (`\w` to
`[a-zA-Z0-9_]` and so on, unless `(?U)` is present). Not sought: the
Unicode meaning is the one a reader of `\w` expects.
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

## 15. RESOLVED -- `hash` answers different numbers than clj does

**RESOLVED 2026-09-27.** `gc_hash` is `Util.hasheq`, bit for bit:
`Murmur3.hashLong` for integers, `hashInt` of clj string hash for
strings, `Symbol.hasheq` and `Keyword.hasheq`, `Double.hashCode` with
-0.0 as 0.0, a Ratio's and a BigInt's `BigInteger.hashCode`, BigDecimal's
after `stripTrailingZeros`, and `hashOrdered`/`hashUnordered` for
collections (GC.f90, "Clojure's hashes"; Eval.f90, gce_coll_hash). The
trie iterates in hash order the way PersistentHashMap does, and sets and
`hash-map` are hashed at every size, as PersistentHashSet and
PersistentHashMap are, so a set or a map past eight entries seqs in the
order clj's does. `case` is unaffected: its macroexpansion and `case*`
still share one hash. Left different: a lazy seq, which hashes by identity
until realised (deviation 35), a class object, and a record. The
original entry follows.

Clojure specifies `hash` as `Util.hasheq`, a murmur3 mix, and exposes the
algorithm through `hash-ordered-coll` and `hash-unordered-coll`. clotran
answers `gc_hash` instead: `(hash \a)` is 1915844612 here and 97 there.

This is a host difference rather than a defect -- ClojureScript's hashes
disagree with clj's too -- and the only property anything in core.clj
relies on holds: equal values hash equal. `case` is the load-bearing
caller. Its macroexpansion buckets the test constants by
`Util/hash`, and `case*` re-derives the same case-int from
the runtime value, so both sides must be the SAME hash. Pointing either
at murmur3 without the other would silently send every `case` to its
default.

It would go away by implementing murmur3 in `gc_hash`, which is worth
doing only if a program ever needs a hash to match clj's across the
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

**RESOLVED 2026-09-19.** `analyze.inc` resolves every symbol once, with
the writing namespace and the lexical scope known: a local becomes a
frame slot, a Var reference holds the Var, a class literal is a
constant. `__defining-ns__` is gone. What remains of this entry is
deviation 3 (the `clojure.core` fallback inside `resolve_var`) and the
new deviation 32.

## 17. A deftype's short name is global, not imported per namespace

`(deftype Point [x y])` expands to `(deftype* clojure.core/Point
clojure.core.Point ...)` followed by `(import clojure.core.Point)`, and
in clj that import is what makes the bare name `Point` mean that
class *in that namespace and nowhere else*. clotran's `import*` records
the short name in ONE list for the whole process (`record_import`),
not per namespace, so a class name written short after an import
means the imported class everywhere.

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
clj artifact -- `this` is not a parameter there, it is the receiver.

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

## 21. RESOLVED -- `pr` of a namespace shows its name, not an `#object[...]` form

**RESOLVED 2026-09-19.** Both missing pieces exist: `String/format` and
`System/identityHashCode` (a heap object's pool index, stable because
the collector does not move). `(pr-str *ns*)` is now
`#object[Namespace 0x3 "user"]`, an atom prints as
`#object[Atom 0x.. {:status :ready, :val 1}]`, and the
number after `0x` is the one thing that still differs from clj.
A function still prints as `#<fn>`: deviation 23. The original entry
follows.

Clojure separates two things about a Namespace, and clotran can only
reproduce one of them:

| | Clojure | clotran |
|---|---|---|
| `(str *ns*)` | `"user"` | `"user"` |
| `(str [*ns*])` | `"[#object[Namespace 0x.. \"user\"]]"` | `"[#<ns user>]"` |
| `(pr-str *ns*)` | `"#object[Namespace 0x.. \"user\"]"` | `"user"` |

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

## 23. `(instance? IObj f)` is false for a function

A function answers `IMeta` but not `IObj`. Clojure says both.

The reason is `print-method`'s `:default`:

    (if (instance? IObj o)
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
`(if (instance? IMeta x) (.meta x))` at core.clj:210, so
the two being one case made `(meta (with-meta (fn [] 1) {:a 1}))` nil.
They are two cases now, and both behaviours are right:

    (meta (with-meta (fn [] 1) {:a 1}))   ;=> {:a 1}
    (pr-str (fn [x] x))                   ;=> "#<fn>"
    (instance? IObj (fn []))  ;=> false, and clj says true

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

The same goes for a row's IDENTITY: `(aget m 0)` is a fresh view of
row 0 each time, so `(identical? (aget m 0) (aget m 0))` is false here
and true in clj, and `to-array` -- which answers an `Object[]` as
itself -- copies a row.

This is a deliberate trade, not an omission. Contiguity is the entire
reason the representation is worth having -- the block can be handed to
a BLAS routine as a flat `buf(*)` argument, which `[[I` cannot be at any
price. Measured on the same memory:

    a(2,3) = 23.0                  ! a(i,j) access
    flat   = 11 21 31 12 22 32 ... ! the same bytes, column-major
    is_contiguous(a) = T
    flat(i + (j-1)*3) == a(i,j)    ! every cell

Note this one is NOT a clj artifact, so SEAMS' usual test does not
apply: JavaScript arrays are nested too, and ClojureScript inherits the
same raggedness. It is a capability real Clojure has, given up on
purpose, in exchange for one real Clojure cannot offer.

It goes away only by representing arrays as arrays-of-arrays, which
would mean giving up the thing the project exists for.

## 25. `aset` on a primitive array accepts any number

Real Clojure:

    (aset (make-array Integer/TYPE 3) 0 10)
    ;; IllegalArgumentException: argument type mismatch
    ;;   Array/set

`Array/set` takes an `Object`, so `10` arrives as a boxed `Long` and
clj refuses to store it in an `int[]`. Getting it in requires the
type to be exact -- `(aset-int a 0 10)` or `(aset a 0 (int 10))` --
and `aset-int` exists precisely because the plain one cannot do it.

clotran stores it. There is no boxing here, so there is no boxed type
to mismatch: an int array is `integer(4)` and the value is a clotran
integer, which goes in. The typed family -- `aset-int`, `aset-double`,
`aset-boolean` -- all reach the same builtin, because in clj they
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

## 26. RESOLVED -- BigInt, and what a Ratio still cannot hold

**RESOLVED 2026-09-21.** There is a `BigInt`:
`src/f/BigInt.f90` is arbitrary-precision integer arithmetic over
decimal text (add, subtract, multiply, truncating divmod, compare),
and a big integer is that text in the string pool under its own tag
(`GCT_BIG`), so the collector marks it as it marks a string and
nothing else in the heap changed. `42N` reads as one, so does a plain
literal past 2^63, `(pr-str 1N)` is `"1N"`, `(= 1N 1)` is true and the
two hash alike, and `+'` `-'` `*'` `inc'` `dec'` promote instead of
throwing. `(* 99999999999999999999N 99999999999999999999N)` is exact.

What is NOT closed, and is the rest of this entry:

- **A Ratio's numerator and denominator are still 64-bit.** So a
  division that leaves a remainder outside that range --
  `(/ 99999999999999999999N 7)` -- raises "a Ratio of BigInts is not
  supported" rather than answering an exact ratio. Clojure's Ratio
  holds two BigIntegers. Removing it is the same change again, one
  level up: a Ratio whose parts are big integers.
- **`1.5M` is still a double** (deviation 30), so there is no
  BigDecimal and `(bigint 2.5)` fails where Clojure routes it through
  `BigDecimal/valueOf`.
- **One big integer type, not two.** `biginteger` answers the same
  BigInt, which prints `1N` where Clojure's `BigInteger`
  prints `1`.
  So `(instance? BigInt x)` and `(instance?
  BigInteger x)` are both true of `1N` and of `(biginteger
  1)`, where clj answers one of each.
- **`long` of a BigInt truncates** rather than throwing when the value
  is out of range: the row is shared with `uncheckedLongCast`, and
  `even?` needs the truncating one.
- **`range` narrows its bounds.** `(range 1N 4N)` is `(1 2 3)` here and
  `(1N 2N 3N)` in clj. The values are equal and compare equal; the
  ELEMENT TYPE is a long. A BigInt used as an index, a count or a
  range bound is narrowed the same way (`as_int`), which is what makes
  `(nth v 1N)` answer element 1 rather than element 0.

What the entry recorded before, kept because the reasoning still
stands:

**The overflow half was resolved on 2026-09-19 (fedccc9).** `+`, `-`, `*`,
`inc` and `dec` raise `ArithmeticException: long overflow` as
`Numbers.throwIntOverflow` does, and the `unchecked-` variants wrap.
What this entry now records is what those checks cannot give: the
promoting operators `+'`, `*'`, `inc'` and `dec'` have no BigInt to
promote INTO, so they throw where Clojure answers `10000000000000000000N`.

The reader agrees with Clojure on every number SHAPE (hex, octal,
explicit radix, exponents), ratios are exact, and integers are 64-bit
like Clojure's `long`. What is left is the top of that range.

What it replaced is worth recording, because it stood for a long time
and showed on no scorecard: `ival` was Fortran's default `integer`, 32
bits, so `9999999999` read back as `1410065407` and `2147483648` as
`-2147483648`. The `real` beside it in `gc_value` had been widened to
`real(8)` early on with precisely this argument, and the integer was
left behind.

`42N` and `1.5M` once read as SYMBOLS, so they resolved to nothing and
failed where they were used rather than where they were read.

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

**`proxy-super` throws.** There is no superclass method to call
through to, so `(proxy-super m ...)` expands to a throw of
UnsupportedOperationException naming `m` (`src/clj/clotran/core_proxy.cljf`,
loaded in place of `core_proxy.clj`). Until 2026-09-29 the macro did not
exist at all, and `clojure.repl` -- whose `source-fn` builds a proxy that
calls it -- could not load.

**Removal**: vendoring `core_proxy.clj` does not help; it needs
`Class/forName`, `.getDeclaredMethods` and a class loader. Removing
this means giving clotran real classes, which is the same work
deviation 4 names.

## 29. RESOLVED -- an agent's actions run on a thread of the agent's own

**RESOLVED 2026-09-28** (feat/threads). `send` and `send-off` queue the
action on the agent (`"queue"` and `"running"` in its fns map, replaced
by compare-and-swap) and, if no thread is draining it, start one
(`clotran.rt/agent-run`, a future); the thread runs the queued actions
in order, one at a time, each with the sender's binding frame and the
validator, watches, error handler and `:fail`/`:continue` modes as
before (`clotran-agent-run1`), and stops when the queue is empty -- in
the same swap that marks the agent not running, so a later `send`
starts a new drain. `send` returns at once, as Agent.dispatch does;
`await` and `await-for` wait through core.clj's own latch action.

`*agent*` is bound during an action (core.clj's binding-conveyor-fn
carries the sender's frame, `*agent*` in it). A `send` made inside an
action is HELD until the action ends, as Agent.dispatchAction holds it
in `nested`: released if the action succeeds, dropped if it throws, an
error handler's own sends going out at once; one made inside `dosync`
waits for the commit and an abort drops it (LockingTransaction's
`enqueue`). A failed agent keeps the actions queued behind the
failure, and `restart-agent` resumes them unless `:clear-actions`,
refuses an agent that has not failed ("Agent does not need a restart")
and runs the validator on the new state first, as Agent.restart does.

Not clj's: there is no thread pool -- a drain is a thread while an
agent has work and none when it has not -- and `send` and `send-off`
are the same, so there is no pool to exhaust; `set-agent-send-executor!`
and `set-agent-send-off-executor!` are accepted and set nothing.

## 30. RESOLVED -- BigDecimal, except for rounding

**RESOLVED 2026-09-21.** `1M` reads as a `BigDecimal`:
`src/f/BigDec.f90` is an unscaled BigInt and a scale, and the scale is
part of the value, so `1M`, `1.0M` and `1.00M` are three decimals that
print apart and compare EQUAL, as clj's `compareTo` and Clojure's `=`
say they do. Every scale rule is BigDecimal's: add and subtract take
the larger scale, multiply adds them, and division is exact or it
throws. `(* 1M 0.1M)` is `0.1M`, `(+ 0.1M 0.2M)` is `0.3M`, and
`(= 1.0M 1.0)` is false because a decimal is its own equality
category -- which is what `(transduce (dedupe) conj [1 1.0 1.0M 1N])`
in Clojure's own transducer tests asks about.

`with-precision` works too, with all eight of clj's rounding modes:
`MathContext` is a map of `:precision` and `:rounding`, and
`RoundingMode`'s constants are the keywords of their own
names. What DEFAULT it has is deviation 43, and it is a deliberate one.

What is NOT closed:

- **`.setScale`, `.precision` and the rest of BigDecimal's methods**
  are not host members. The arithmetic is here, the object protocol is
  not.

and, with it, everything `with-precision` is for. A literal past
2^63 is the same 64-bit ceiling deviation 26 names.

**Removal**: a numeric tower with BigInt and BigDecimal in it. That is
the same work deviation 26 ends on, and the suffixes are its most
visible symptom rather than a separate problem.

## 31. RESOLVED -- stack traces

`(.getStackTrace e)` answers an empty array; Clojure answers one
`StackTraceElement` per frame, and `clojure.stacktrace` and
`clojure.test`'s failure reports print them. The evaluator keeps no
frames -- there is nothing to report. It is honest rather than wrong:
`(alength (.getStackTrace e))` is 0, never a fabricated trace.

**Removal**: PLAN.md step 5. Once evaluation runs over explicit frames
with source positions on nodes, a trace is a walk up that stack, and
this entry closes together with the debugger it unblocks.

**RESOLVED 2026-09-19.** The evaluator keeps a call stack (one entry
per closure invocation: the closure and where it was called from). A
Throwable is given the stack at construction, as clj's is, or at the
throw if it has none; `.getStackTrace` answers it as an array of
elements, and each element answers `getClassName` (the function's
qualified name), `getMethodName` (always `invoke`), `getFileName` and
`getLineNumber` (the call site's). The elements are maps rather than a
class, which shows only under `class`. The top frame of an `ex-info`
trace is `clojure.core/ex-info`, as it is in clj.

What differs from clj: no `invokeStatic`/`doInvoke` pairs, no
frames for builtins, and a `recur` loop is one frame.

## 32. A qualified symbol that does not resolve is a run-time error

Clojure fails to COMPILE a form naming a Var that does not exist:
`Unable to resolve symbol: jio/reader`. clotran's analyser does the
same for an unqualified symbol, but a QUALIFIED one that fails to
resolve is deferred (`N_LATEVAR`): the function containing it is
defined, and only a call of it fails, with the same message.

The reason was a library core.clj names before it can load (deviation
12): failing at analysis would stop core.clj at that form. Deferring
keeps the file loading and moves the failure to the call, and it is
also where a clotran namespace loads on first use: `clotran.io/text-reader`,
named in core.clj before clotran.io can load, loads it when first called.

The var-quote is NARROWER (2026-09-28). `#'clojure.instant/read-instant-date`
in core.clj's `default-data-readers` names a Var in a library that is
never loaded here, and Clojure would refuse the form; so a qualified
name whose NAMESPACE DOES NOT EXIST is interned unbound in a namespace
made for it and marked `:clotran/placeholder`, and the map loads. A
namespace that exists -- `user` from another namespace, say -- refuses
as `Compiler.lookupVar` does: "Unable to resolve var: user/x in this
context". (`resolve_var` no longer creates a namespace to look in.)

**Removal**: either load those libraries (they are clj-bound) or
accept the form as-is; the honest end state is that `slurp` is defined
in terms of a host reader clotran supplies.

## 33. Reader conditionals are read in every file, and `.cljf` is a source extension

Clojure reads `#?(...)` and `#?@(...)` only from a `.cljc` file, or
when `read` is handed `{:read-cond :allow}`; in a `.clj` file the form
is an error, "Conditional read not allowed". clotran reads them in
every file.

The feature it claims is `:cljf`, after the extension, alongside
`:default`. `:clj` is clj and is not claimed, so a `.cljc` library
ported here gets a `:cljf` branch wherever it had a `:clj` one, and
that is the whole port. A branch nobody selects is read under the
equivalent of `*suppress-read*` and dropped, so a `:cljs` branch may
hold `#js {}`; a selected branch has no data readers and an unknown
tag there fails by name, as before. `:read-cond :preserve` does not
exist here.

`require` and `load` look for `name.cljf`, then `name.cljc`, then
`name.clj`, on each classpath root in turn. `RT.load` prefers `.clj`
to `.cljc`; here the portable file is the one with a chance of
loading, so it wins.

**Removal**: tie the allowance to the extension as Clojure does, so
`#?` in a `.clj` errors. Nothing depends on the leniency; it exists so
a `.clj` being ported can be edited in place before it is renamed.

## 34. RESOLVED -- a class is a value of its own kind

**RESOLVED 2026-09-21.** A class is `GCT_CLASS`: its canonical name in
the string pool, printed as that name, equal and hashed by it. So
`(class 1)` is `clotran.host.int8` (DEVIATIONS 67), `(pr-str (class 1))` is
`"clotran.host.int8"` and not a keyword, `(str (class 1))` is
`"class clotran.host.int8"` as `Class.toString` would give it, `(class (class
1))` is `clotran.host.class`, `(class? (class 1))` is true and
`(keyword? (class 1))` is false. `(= (class x) clotran.host.string)` holds,
because the literal and the answer are the same name: `class_key` is
the one spelling rule, now `canon_class` in full.

`(resolve 'NonExistentClass.Name)` is nil, as in clj. There is no
class loader to ask, so `known_class_name` decides: a row in the host
table, a deftype, or a name under `clotran.`. A made-up package answers
nil; a made-up class under `clotran.host` would not.

What still differs from a `Class`:

- clotran has one map, one set, one seq view and one function class
  where clj has many, so the most common clj class stands for
  each: every map is a `clotran.host.persistent_array_map`, every `seq` a
  `clotran.host.persistent_vector_chunked_seq`, every function a
  `clotran.host.a_function`. An array's class is its element kind and
  rank, `int/1`.
- `supers` answers the short chain `host_super` lists -- the
  interfaces `core_print` and `core_deftype` dispatch on -- not the
  two dozen a clj class implements. It must include every interface a
  protocol in the loaded code is extended to, or `find-protocol-impl`
  picks a different implementation: until 2026-09-25 the chunked seqs
  lacked `IChunkedSeq`, so InternalReduce fell to Object and a reduce
  over `(map f (range n))` walked element by element (the oracle now
  checks the pick). With no superclass chain (below), CollReduce picks
  Object where Clojure picks ASeq for a ChunkedCons -- the same body,
  `(seq-reduce coll f val)`, so the same answer.
- there is no `Class` object graph: no `getSuperclass`, no
  `getDeclaredMethods`, nothing reflective. A class here is a NAME
  with the runtime's own answers behind it.

The internal type TAG -- `:string`, `:vector`, `:int` -- is what
`clotran-type` answers and what `host.clj`'s predicates are written
on; it is not `class`, and never was meant to leak.

## 35. An unrealised seq hashes by identity, so it is not found as a map key

`(= (map inc [1 2 3]) [2 3 4])` is true here, as it is in Clojure. But
`(hash (map inc [1 2 3]))` is an identity hash, not the sequence hash,
so `(get {(list 2 3 4) :v} (map inc [1 2 3]))` answers nil where
Clojure answers `:v`. Equality and hash disagree, which is a guarantee
Clojure gives and clotran does not.

The reason is structural. `gc_hash` runs INSIDE a map insert or lookup,
and it takes no root set: anything it allocates cannot root the
half-built trie the caller is holding. Hashing a lazy seq means
REALISING it, which runs arbitrary Clojure and allocates freely, so
hashing-by-forcing from there would be a collector bug rather than a
slow path. `is_structural_kind` in GC.f90 therefore leaves `OBJ_LAZY`
out, and anything not in that list falls back to an identity hash.

What IS hashed structurally: lists, vectors, maps, sets, seq views,
and -- since chunked seqs arrived -- a ChunkedCons whose whole rest is
already realised (`seq_realised_p` checks before folding; a partly
realised one would otherwise hash its first 32 elements and claim to
be the whole sequence, which is the silent wrong answer, not the loud
one). That guard bites more often than it sounds: `map` builds its result
with `(chunk-cons (chunk b) (map f (chunk-rest s)))`, and the rest
handed to `chunk-cons` has not been realised yet, so a ChunkedCons
straight out of `map` hashes by identity. `(hash (doall (seq (map inc
[1 2 3]))))` is the sequence hash; `(hash (seq (map inc [1 2 3])))` is
not.

**Removal**: give `gc_hash` a root set, which means threading roots
through `gca_assoc`, `gca_get` and the trie, and then hashing may
force. That is the same plumbing PLAN stage 2 removes in the other
direction (roots leaving signatures once the operand stack holds
them), so it is worth doing after that, not before.

## 36. `binding` accepts a Var that was not declared `^:dynamic`

`(def g nil) (binding [g 1] g)` answers `1` here. Clojure refuses it
at compile time -- `Can't dynamically bind non-dynamic var: user/g`
(`clj`; Compiler's `BindingInit` checks `Var.isDynamic`) -- and
ClojureScript warns and refuses too, so the rule is the language's,
not clj's. `push-thread-bindings` here binds whatever Var it is
handed, and no Var carries a dynamic flag: `(def ^:dynamic *h* nil)`
and `(def h nil)` are the same object to it.

Noticed while giving the debugger its handler Var,
`*clotran-break-handler*`, which the language tests bind with
`binding` and which works either way.

**Removal**: record `:dynamic` from a `def`'s metadata on the Var (and
mark the earmuffed core Vars `RT.doInit` makes dynamic), and have
`push-thread-bindings` refuse a Var without it. Small; it waits only
for someone to want the refusal.

## 37. RESOLVED -- `apply` hands a variadic fn its rest unrealised

**RESOLVED 2026-09-21.** `RestFn.applyTo` takes the fixed parameters
off the seq and hands the rest to the function as the seq it is, so
`(apply f (range))` returns when `f` is `[& args]`. `apply` now does
the same for a variadic closure (or a Var holding one): it takes the
required arguments off the front, conses any extra leading arguments
onto what is left, and `bind_closure` binds the rest parameter to that
seq itself (`invoke_closure`'s `restseq`). Clojure's own
`test-vars-apply-lazily` passes. What remains: a native, a keyword or
a fn with no variadic arity spreads its arguments as before, bounded
at 1,000,000 -- `(apply + (range))` is an error, not a hang, where the
clj would run out of memory.

## 38. RESOLVED -- a future runs on a thread of its own

Until PLAN.md step 14f a future was a TASK run on the one OS thread
there was, until it blocked, then parked. Now it starts on a thread of
its own when it is made and runs beside whoever made it (tasks.inc):
side effects happen in either order, a wait is a real wait (a condition
variable, not a spin), and four `(future (clotran.thread/sleep 300))`
take 306 ms together. Pinning is gone with the baton.

What remains, and stays by choice:

- **Deadlock is an error.** `@(promise)` with nothing left that could
  deliver it throws "deadlock: nothing left to run can make the promise
  or mailbox ready" where Clojure blocks forever. It is found by
  counting: every live thread waiting, none with a deadline.
- **`ExecutionException` carries the text, not the cause.**
  `.getCause` is nil, and the message is the failure's class and
  message without ex-info's data map (`clj` says
  `"ExceptionInfo: boom {}"`).

## 39. A map entry's class is clotran.host.persistent_vector

`(first {1 2})` answers `map-entry?` and `(instance? Map$Entry
..)` as Clojure's does -- the entry is a two-element vector carrying a
mark in a slot vectors never use, set where entries are built and read by
`instance?` (NOTES.md, "A map entry has a type"). What differs is
`class`: Clojure says `MapEntry`, clotran says
`clotran.host.persistent_vector`.

This is a **choice**. `class` is what protocol dispatch and `print-method`
look up, and a MapEntry class with its own supertype chain would have to
reproduce `APersistentVector`'s for every protocol extended to vectors to
keep reaching entries. Nothing in the vendored suite asks an entry its
class; `map-entry?` is what it asks, and that is answered.

**Removal**: `class_name_of` answering MapEntry for a marked vector, and
`host_super` giving that name the vector chain plus `IMapEntry` and
`Map$Entry`.

## 40. `core_print.clj`, `data.clj` and `clotran.files` are clotran's own

`clotran.files` joined them on 2026-09-27: skipped as host-bound, it left
core.clj's `slurp` and `spit` -- written against `jio/reader` and
`jio/writer` -- unable to run at all. `src/clj/clotran/files.cljf`
defines the namespace over clotran's whole-file primitives: `reader`
(with `.readLine`, so `line-seq` works), `writer` (`:append`), `copy`,
`file`, `make-parents`, `delete-file`; TEXT only, and `resource` is nil.

Two of the vendored files are Clojure written against clj's collection library:
`core_print.clj` dispatches `print-method` and `print-dup` on
`Map`, `Collection`, `List`, `RandomAccess` and `Set` and
prefers among them, and `data.clj` extends its two protocols to three of
them. Running them verbatim meant modelling clj's interface inheritance
in Fortran -- a `Class` that is a keyword, `isAssignableFrom`,
`getInterfaces`, a table of what `List` extends -- for two
files. ClojureScript's answer to both is a version of its own (its
printing is on a protocol in core.cljs, and it ships `data.cljs`), and so
is clotran's: `src/clj/clotran/core_print.cljf` and `data.cljf` are the
same files with host keys taken out, loaded in their place by
`B_RTLOAD`. The vendored files stay in the tree, unmodified and unread,
as `core_proxy.clj` does (deviation 12).

What differs from clj: a value that is only a clj's collection library collection
has no print method here, and nothing in clotran makes one. Everything
that prints a Clojure value is Rich's, line for line.

`diff` used to partition an array as an atom, because `Class.isArray`
was hard-wired false and `data.cljf` had been edited to say `:atom`
unconditionally. `isArray` answers now and the upstream line is back,
so `(diff [1 2] (into-array [1 2]))` is `[nil nil [1 2]]` as it is on
clj.

**Removal**: none sought. This is the premise applied, not bent: the
language is reproduced, clj is an implementation detail.

## 41. A string is indexed by code point, not by UTF-16 unit

A string is UTF-8 bytes in the pool and every operation that counts or
indexes it -- `count`, `nth`, `get`, `subs`, `.charAt`, `.indexOf`,
`.substring`, `seq`, `reverse`, `.length`, regex group spans -- counts
CHARACTERS (`u8_count`, `u8_off`, `u8_slice` in `GC.f90`). A character
is its code point, so `\é` reads, `(str \u2002)` prints the three
bytes of U+2002, `Character/isWhitespace` and `toUpperCase` are ICU's
(`cu_*` in `regex_shim.c`; `u_isWhitespace` is defined as clj's), and
`(clojure.string/trim "\u2000bar\t \u2002")` is `"bar"` as it is
in clj. Clojure's own string tests pass in full.

What differs: clj's unit is the UTF-16 code unit, and a code point
off the Basic Multilingual Plane is two of them. `(count "😀")` is 2
there and 1 here; `(first "😀")` is a lone surrogate there and the
character here; `(char 128512)` throws there and is that character
here. Every string in the test suites is on the plane, so no test
sees it. The case maps are ICU's simple ones, a code point to a code
point, where `String.toUpperCase` would turn `ß` into `SS`.

**Removal**: none sought. The code point is what a string of text
is made of; the surrogate pair is what clj is made of.

---

## 42. `s/check-asserts` cannot be turned on

clojure.spec.alpha's `assert` is
`(if RT/checkSpecAsserts (assert* ...) x)`, and
`check-asserts` flips that field with `(set! (. RT
checkSpecAsserts) flag)`. The field is here as a host static that reads
FALSE -- clj's default, `-Dclojure.spec.check-asserts` unset -- so
`(s/assert spec x)` is `x`, as it is on a stock clj. `set!` of a host
static has nowhere to write (DEVIATIONS 4), so `(s/check-asserts true)`
throws instead of enabling the checks.

**Removal**: a writable box behind the row, as `Compiler/LINE` has, and
`set!` on a static that names one.

---

## 43. `*math-context*` has a working precision, so a decimal division answers

Clojure binds `*math-context*` to nil, and a BigDecimal division with
no context is EXACT OR NOTHING: `(/ 1M 3)` throws
`ArithmeticException: Non-terminating decimal expansion; no exact
representable decimal result.` You get a number only by wrapping the
form in `with-precision`.

clotran binds it to `MathContext.DECIMAL128` instead -- 34 significant
digits, rounding half to even, which is IEEE 754-2008's decimal128 and
clj's own name for it. `(/ 1M 3)` answers
`0.3333333333333333333333333333333333M`.

**Why**, and this is the one deviation taken for a reason outside
Clojure: clotran is for people doing arithmetic, and no other language
they use raises on a third.

| | one third |
|---|---|
| MATLAB, Octave | `1/3` is a double, `0.3333`; there is no exact-decimal type and no exception |
| Julia | `1/3` is a `Float64`; `big(1)/big(3)` is a `BigFloat` at the global working precision -- 256 bits, about 77 decimal digits, changed with `setprecision` |
| Clojure | `(/ 1M 3)` throws unless `with-precision` says otherwise |
| clotran | `(/ 1M 3)` is 34 digits, and `with-precision` is `setprecision` |

Nothing else moves. A precision only rounds a result that has MORE
significant digits than it, so every exact case answers exactly as
Clojure does: `(* 1M 0.1M)` is `0.1M`, `(+ 0.1M 0.2M)` is `0.3M`,
`(/ 1M 8)` is `0.125M`, `(/ 100M 4)` is `25M`. A literal keeps every
digit it was written with, because reading is not an operation. Exact
integers and ratios are untouched -- `(/ 1 3)` is still `1/3`, which is
more accurate than any decimal and is what Julia's `1//3` does too.

**Clojure's arithmetic is one binding away.** `(binding [*math-context*
nil] (/ 1M 3))` throws exactly as clj does, because nil is still
"exact or nothing" here. That is also the switch to reach for if a
program needs to KNOW that a result was inexact rather than be handed a
rounded one.

The visible cost: `*math-context*` prints as `{:precision 34, :rounding
:HALF_EVEN}` where Clojure prints nil, and a division that Clojure
refuses gives an answer here. Both are in the oracle as expected
differences, so the day either changes, the ledger says so.

**Removal**: bind the Var to nil at bootstrap (`gce_base_env`). One
line, and everything else about the decimal stays as it is.

## 44. RESOLVED -- `tap>` delivers on the calling thread, before it returns

**RESOLVED** (found 2026-09-29; it went with DEVIATIONS 38, when every
task got an OS thread of its own). The tap thread is a real thread now,
so `(do (tap> 1) @seen)` is `[]` here as in clj, and the tap has run a
moment later. The prepl check in language_test sees a `:tap` message
both before and after its `:ret`, as clj can. What follows is the entry
as it was.

Clojure's tap set is fed by an `ArrayBlockingQueue` with a daemon
thread draining it, so `(tap> x)` puts the value on the queue and
returns `true` at once; the tap functions run later, on that thread.
A tap that appends to an atom is therefore still empty on the line
after `tap>`.

clotran has one OS thread (DEVIATIONS 38): the tap thread is a task,
the queue is a task mailbox, and `.offer` steps the ready tasks before
it returns. So the taps have already run when `tap>` answers, and
`(do (tap> 1) @seen)` is `[1]` here and `[]` there.

Nothing else differs: `add-tap`, `remove-tap` and the return value of
`tap>` are the same, and a program that reads the tap's effect later
rather than immediately cannot tell the two apart. Only a program that
reads it IMMEDIATELY sees an answer Clojure would not have yet.

**Removal**: the same thing that removes 38 -- real threads. Delivery
becomes whatever the scheduler does, which is what Clojure's is.

## 45. RESOLVED -- a short, byte or char array had its storage kind's class

**RESOLVED 2026-09-27.** `byte-array`, `short-array` and `char-array`
are one and two bytes an element -- Fortran's `integer(1)` and
`integer(2)`, the char array read unsigned -- and are `[B`, `[S` and
`[C`. A store wraps as clj's narrowing does: `(vec (byte-array [1
200 -129]))` is `[1 -56 127]` on both. What is read back is boxed as
clj boxes it -- `(class (aget (byte-array 1) 0))` is `Byte`
-- and so are `(byte 1)`, `(short 1)`, `(int 1)` and `(float 1)`: an
integer or double carries its width, arithmetic answers a Long or
Double as Clojure's does, and `=` and `hash` ignore the width as
Clojure's do. `aset` takes what `RT.aset`'s overloads take -- a byte
array a Byte, a char array a Character -- and anything else is the
Reflector's IllegalArgumentException; `aset-byte` and friends cast
first. `.getComponentType` answers the element type, so `bytes?` is
true for a byte array. Checked value by value against clj in
test/clj/oracle.clj.

## 46. RESOLVED -- data readers work in `clojure.edn` and nowhere else

**RESOLVED 2026-09-28.** `#tag form` is readable everywhere. The reader
still cannot apply a data reader -- it would have to call the
evaluator -- so it leaves the literal as a marker,
`{:clotran/tagged-literal true :clotran/unread true :tag t :form f}`,
and `clotran.reader/resolve-tags` resolves the markers in a form before
it is analysed (`gce_analyze`) or answered by `read-string`, exactly as
`LispReader.CtorReader` does at read time: `*data-readers*`, then
`default-data-readers`, then `*default-data-reader-fn*`, and otherwise
Clojure's own "No reader function for tag x". Innermost first, quoted
data included, metadata kept. A `tagged-literal` a program built has no
`:clotran/unread` and is left alone. `clojure.edn` resolves its own
markers against its opts, as before. `#uuid` reads because
`clojure.uuid` now runs verbatim (DEVIATIONS 12); `#inst` still wants a
date type.

## 47. `all-ns` answers a namespace per host class name as well

`(count (all-ns))` is 64 here against real Clojure's dozen, and the
extra entries are host class names: `Math`, `String`, `UUID`,
`RT` and every other class a loaded file mentions.

The cause is that a qualified host symbol goes through the same
registry a namespace does. `(RT/count x)` resolves
`RT` by `gcn_find_or_create`, which makes a real
`Namespace` object for it, and the registry is what `all-ns` walks. The
entries are genuine namespace objects, empty of bindings, so nothing
distinguishes them by kind.

This was invisible until 2026-09-23, because `Namespace/all` had no
host member and `all-ns` simply threw. It answers now, and answers too
much, which is the honest trade: a function that works with a caveat
against one that does not work at all.

What it costs: anything that walks every namespace sees 50 more than it
should. `(ns-publics x)` on one of them is empty, so a search like the
compiler's is slow rather than wrong. A program that PRINTS all-ns
shows names no Clojure program would.

**Removal**: mark a namespace made for a host class -- a flag in the
object, or a separate registry for imports -- and filter it out of
`gcn_all`. The resolution path that creates them is `analyze_symbol`'s,
and it is the only caller that should be setting the flag.

## 48. Type hints: the runtime half is Clojure's, the compile-time half is not

A hint changes what a Clojure program DOES, and clotran now does it: a
`^long` or `^double` parameter or return converts by `RT.longCast` /
`RT.doubleCast` after a checkcast to Number (`Compiler.emitUnboxArg`),
so `((fn [^long n] n) 1.5)` is 1 and `((fn [^long n] n) \a)` throws; an
array hint is a checkcast where the value is USED as an array (`aget`,
`aset`, `alength`), so a `^doubles` parameter handed a vector is fine
until indexed. More than four primitive parameters, a variadic one, and
`^int`/`^float` parameters fail as they do in clj. The oracle's
"Type hints" cases compare all of this by exception class.

What differs is everything clj decides by its static types:

- `recur` to a `^long` parameter with a double is a compile error there
  ("recur arg for primitive local ... is not matching primitive"); here
  the value is converted again on the next iteration.
- `(let [^long x 1.5] x)` is an UnsupportedOperationException there
  ("Can't type hint a local with a primitive initializer"); here the
  hint on a let local is ignored.
- `*unchecked-math*` does not switch a parameter's conversion to
  `uncheckedLongCast`; the checked cast is always used.
- `aget`/`alength` (not `aset`, which answers as the Reflector does) on an UNHINTED non-array is a reflection
  IllegalArgumentException there (and on a literal `nil`, a compile
  error); here it is a RuntimeException "not an array". A hinted nil is
  a NullPointerException on both, with a different message.

**Removal**: each item is a static check in the analyser. The recur
check needs the primitive kind of each loop local, which
`prim_hint_body` already knows; the let check needs the init's
primitive type, which needs the compiler's type inference in the
analyser rather than only in `compiler.cljf`.

## 49. (Resolved 2026-09-25) A task blocked below compiled code was pinned

A future that blocked below a COMPILED function could not park: there
was Fortran on the one shared machine stack between the block and the
task's context, so the task was pinned, and a wait only its starter
could satisfy was a deadlock error. Every task now runs on its own OS
thread (Threads.f90, tasks.inc: the baton), so it waits where it
blocks and is resumed there; only one thread runs clotran code at a
time, so every answer is what it was. language_test's parking checks
pass with `make compiled-core` in place, and the compiler no longer
keeps blocking functions interpreted.

Kept, resolved, so the numbers after it stay where they are.

## 50. Pure Fortran writes a double as Fortran does

Tier-A code compiled to pure Fortran (`clotran.purefort`, PLAN.md step
13) follows Fortran's conventions for text, not clj's: a double inside
an error message is written with the `ES` edit descriptor,
`1.0000000000000000E+030`, where clj and clotran's interpreter write
`1.0E30`. The value is the same; `scripts/pure-check` compares such a
number by value. `ES` rather than list-directed or `G0` output because
the standard fixes its layout, so gfortran and flang write the same text.

The same holds wherever pure code turns a value into text -- `str`,
`print`, `println`: a long is `I0`, a double `ES24.16E3`, a boolean
Fortran's `T` or `F` where Clojure writes `true` or `false`. So a
string that holds a number differs too: `(str 2.5)` is `"2.5"`
interpreted and `"2.5000000000000000E+000"` as pure Fortran, and
`(count (str 2.5))` differs with it.

A decision, not an accident: pure Fortran is meant to read as Fortran
to the Fortran programs that use it. **Removal** is not planned.

## 51. Division by zero says "Divide by zero" where clj's primitive path says "/ by zero"

In clj the message depends on static types: `Numbers.quotient` of
two boxed values throws "Divide by zero", but `(quot 7 0)` with literal
longs compiles to clj's primitive `x / y`, whose message is clj's own
"/ by zero". clotran says "Divide by zero" on every path -- the boxed
path's answer, which is also what a function of unhinted parameters
gets in clj. Pure Fortran does the same.

**Removal**: track, per value, whether clj would have it primitive
(the compiler's type inference already follows Clojure's rules), and
choose the message by that.

## 52. A parallel loop reports whichever failing iteration stops first

`amap`, and a loop of the same shape, compile to `do concurrent` in pure
Fortran (PLAN.md step 11), and a threaded build runs the iterations at
once. When more than one iteration would fail -- an index out of bounds,
a long overflow -- Clojure reports the LOWEST index, because it runs them
in order; a threaded build reports whichever fails first in time. The
program stops either way, and a single failing iteration reports the
same message on every build (`scripts/pure-check` runs each case
threaded, under flang and gfortran, and compares).

**Removal**: record the failing index per iteration and report the
lowest after the loop -- which means not stopping at the first failure,
and a pure procedure cannot defer an `error stop`.

## 53. `identical?` on equal numbers is true

Numbers are immediate values here -- a tag and a 64-bit payload in the
value itself -- so two equal numbers are the same value, and
`(identical? 1.5 1.5)`, `(identical? 1000 1000)` and
`(let [x 1.5] (identical? x x))` are all true. In clj each is a boxed
object: `clj` answers false for all three (the last because each use of
`x` boxes the primitive again), and true for `(identical? 100 100)` only
because Long caches -128..127. So clj's answer depends on boxing
decisions no Clojure program can rely on; clotran's is value identity.
Reals compare by value, as `==` does: `0.0` and `-0.0` are identical, and
a NaN is identical to itself.

Removal would mean boxing numbers, which is the cost this representation
exists to avoid (PLAN.md, the calling convention's step 3). Not planned.

## 54. A name built with a slash in its namespace splits at the first slash

A symbol or keyword is kept as one text, and its namespace is the part
before the FIRST slash -- which is what the reader does: `:a/b/c` is
namespace `"a"`, name `"b/c"`, on both hosts. Clojure's two-argument
`keyword` and `symbol` keep the two halves as given, so
`(keyword "a/b" "c")` prints `:a/b/c` on both but answers namespace
`"a/b"` and name `"c"` in `clj`, and `"a"` and `"b/c"` here. clojuredocs
itself calls such names non-conformant; `(keyword "a" "b/c")`, the
reader's split, is identical on both.

**Removal**: store where the namespace ends beside the text, and have
`namespace`, `name`, `=` and hashing read it.

## 55. RESOLVED -- clojure.core is direct-linked, as Clojure compiles it

**RESOLVED 2026-09-28.** Clojure compiles its own namespaces with direct
linking: one core function calls another without going through the
Var, so `with-redefs`, `alter-var-root` or a `def` of a core name
changes what USER code sees and leaves core's own calls alone. Here the
analyser, for a call head in a `clojure.*` namespace read from the
vendored tree (`src/clj/clojure/`) that names a `clojure.*` Var, binds
the site to the closure the Var holds AT ANALYSIS (analyze.inc,
`direct_link_flag`), as clj binds at compile time, and the site
never reads the Var again (exec.inc, N_CALL). A Var bound to a host
builtin at that moment stays late-bound: the host binds builtins into
clojure.core before core.clj defines the real thing, and clj has no
such placeholder. Installing a compiled namespace re-roots its Vars and
bumps an epoch; a site then reads its Var once more and takes only a
compiled fn from it. `(with-redefs [first last] (first [1 2]))` is 2 on
both, `((with-redefs [first last] #(first [1 2])))` 1, and a user's own
`(ns clojure.zz)` is not linked, as it is not there.

What stays late-bound, as in clj: a Var marked `^:dynamic`,
`^:redef` or `^:protocol` (a protocol fn is re-rooted by every
`extend`; in clj its closure has no static entry point to link
to), a macro, a multimethod (re-rooted when its `defmulti` is
evaluated again), an earmuffed name, and every call from a namespace
outside `clojure.*`.

The one difference from clj is WHEN the binding is taken: at the
first call here, at compile time there. core.clj redefines `reduce`
part way through (after its protocols load); a clj caller compiled
before that links the early `reduce` for good, a caller here that
first runs after it takes the later one. The two answers are the same;
the later one is faster.

## 56. An index is 64-bit; clj truncates a vector's to 32

`(get ["a" "b" "c"] 4294967296)` is `"a"` in clj, `(contains? [1 2
3] 4294967296)` true and `(find [1 2 3] 4294967296)` `[4294967296 1]`:
`RT.get`, `RT.contains` and `RT.find` take a vector's key through
`Number.intValue()`, which keeps the low 32 bits, so 2^32 is index 0.
Here an index is a 64-bit integer and 2^32 is out of range: nil, false,
nil. ClojureScript answers as clotran does. Checked with clj 2026-09-28
(clojuredocs `contains?#example2`, `find#example1`, `get#example6`).

**Removal**: truncate the way `intValue` does, in `get`, `contains?`
and `find` on vectors -- three lines, and a wrong answer copied on
purpose. Not done.

## 57. `vec`, `sort` and `to-array` copy an array; clj aliases it

In clj `(vec an-object-array)` shares the array
(`LazilyPersistentVector.createOwning`), so an `aset` afterwards shows
in the vector; `(sort an-array)` and `(sort-by f an-array)` sort the
array in place; `(to-array an-object-array)` is the array itself,
`identical?` to it. Here each makes a copy, as ClojureScript does.
Checked with clj 2026-09-28 (clojuredocs `vec#example1`,
`sort-by#example5`, `to-array#example1`).

**Removal**: a vector over a native array's buffer, and sorting the
buffer in place. Aliasing a mutable array under a persistent vector is
clj's shortcut, not the language's; not done.

## 58. RESOLVED -- core's one-line wrappers are on the call stack

`first`, `rest`, `next`, `seq`, `cons` and the other clojure.core fns
whose body is one host call on their own parameters -- `(fn [coll]
(. RT (first coll)))` -- are called as that host call
when the arity matches (analyze.inc `wrapper_builtin`). For one commit
that dropped them from the call stack: a break inside `(first 5)`
showed the caller and not `clojure.core/first`, where clj's trace
has `clojure.core$first`. The elided call now pushes the wrapper's
entry while its builtin runs (exec.inc N_CALL, `apply`,
`gce_apply_slots`), at no measured cost; language_test checks the
entry is there by each road and that none is left behind. Not done
for user fns, and not while a step is pending, so stepping still stops
in them.

## 59. A lazy seq's thunk keeps its closed-over locals after it runs

`lazy-seq` makes its thunk `(fn* ^{:once true} [] body)`, and clj
compiler clears a once-only fn's closed-over locals at their last read
(Compiler, `ObjExpr.emitLocal`: `onceOnly && clear &&
lb.canBeCleared` stores null into the field). So a thunk that throws,
run again by the next access -- LazySeq keeps the fn when it throws --
finds those locals null:

    (let [n (atom 0) s (lazy-seq (swap! n inc) (throw (ex-info "t" {})))]
      [(try (first s) (catch Exception e (ex-message e)))
       (try (next s) (catch Exception e (ex-message e)))])
    ;; clj:     ["t" "Cannot invoke \"...IAtom.swap...\" because \"atom\" is null"]
    ;; clotran: ["t" "t"]

clotran runs the thunk again with its captures intact and it throws
what it threw the first time. Found 2026-09-29 while checking in-loop
forcing (flat.inc), which it predates: the tree walker answers the same.
test/clj/oracle.clj carries the case under expect-diff.

**Removal**: honour `:once` on fn* -- clear a capture at its last read
in a once-only fn, as locals clearing already does for locals. Clj
behaviour is an optimisation leaking through (the retry's error is an
NPE about the compiler's own field), so matching it buys nothing a
program could want; not done.

## 60. A deftype's own equals and hasheq are not consulted

A deftype that defines `equals` (Object) or `hasheq` (IHashEq) is still
compared and hashed by identity: `=` does not call its `equals`, and a
map or set does not call its `hasheq`.

    (deftype VP [x] Object (equals [_ o] (and (instance? VP o) (= x (.-x o))))
                    IHashEq (hasheq [_] (hash x)))
    [(= (VP. 1) (VP. 1)) (count (set [(VP. 1) (VP. 1)]))]
    ;; clj: [true 1]    clotran: [false 2]

Records are NOT affected (2026-09-29): a record is equal by type and
values and hashes as emit-defrecord's hasheq does -- the class symbol's
hash xor the unordered hash of its map view -- computed in Fortran from
the field names (Eval.f90 `gce_coll_hash`, `gce_coll_equal`). Before
that, records were identity-hashed and identity-compared inside maps
and sets: a set of twenty equal records had twenty members, and a map
keyed by a record could not find it again.

**Removal**: call the instance's own methods from gce_coll_equal and
gce_coll_hash. They run inside a map insert, where an allocation was
unsafe while a callee could drop its caller's roots; with
scripts/root-check in the gate that is now checkable, but every caller
of gc_hash and gc_equal would have to be audited first. Not done.

## 61. A vector key past 32 bits is out of range, not wrapped

Clj's vector takes a key's `.intValue()` (APersistentVector
`valAt`, `containsKey`, `entryAt`, `assoc`, `invoke`), so a Long key
wraps to its low 32 bits. clotran compares the whole 64-bit value:

    (let [v [1 2 3] b 4294967296]
      [(get v b) (contains? v b) (find v b) (assoc v b 9)])
    ;; clj     [1 true [4294967296 1] [9 2 3]]
    ;; clotran [nil false nil <IndexOutOfBoundsException>]

(and `([1 2 3] 4294967296)` throws IndexOutOfBoundsException where clj
answers 1).

Deliberate. This is clj's `int` showing through, not the language:
ClojureScript's PersistentVector `-lookup` checks `(number? k)` and
then the bounds, with no truncation (cljs/core.cljs, `ILookup`), and
answers as clotran does. clojuredocs has three examples that exist to
warn about clj behaviour (`get`, `find`, `contains?`); they count
as failures in its scorecard.

**Removal**: one helper taking a key to its signed low 32 bits, called
from each of the vector key paths above. Not planned.

## 62. An array of references does not know its element class

Every array of references is an `Object[]` here: a `value`-kind native
array, whose class is `[LObject;` whatever it was made for.

    [(class (make-array String 1)) (class (into-array ["a"]))
     (instance? (Class/forName "[LString;") (make-array String 1))]
    ;; clj     [String/1 String/1 true]
    ;; clotran [Object/1 Object/1 false]

Primitive arrays are not affected (`int/1`, `double/2` are right), and
the array class SYMBOLS resolve: `String/1`, `int/2` and `[I` name
the classes they name in clj.

**Removal**: an element class beside `elem_kind` in NativeArray's
registry, set by `make-array` and `into-array` (from its type argument,
or the first element's class as `into-array` infers it), copied by
`aclone`, and read by `array_class_name`. Not planned yet.

## 63. `vec` of an array copies it

`vec` of an array aliases it in both Clojure (`LazilyPersistentVector
.createOwning`, up to 32 elements) and ClojureScript (`.fromArray
PersistentVector coll true`), and both docstrings say the array "will be
aliased and should not be modified". clotran copies it, so modifying the
array afterwards does not show through the vector:

    (let [a (to-array [0 0 0]) v (vec a)] (aset a 1 9) v)
    ;; clj [0 9 0]    clotran [0 0 0]

Only a program doing what the docstring says not to can tell.

**Removal**: a vector leaf would have to share storage with a native
array, which the persistent vector's nodes do not model. Not planned.

## 64. A transient used in place keeps what was added to it

`conj!` and `assoc!` "must be used for their return value"; a transient
bashed in place instead is unspecified. In clj the ninth entry of a
transient array map makes a NEW transient hash map and returns it, so a
program that ignores the return value loses that entry. clotran's
transient map is one object throughout, so nothing is lost:

    (let [t (transient {:a 1 :b 2 :c 3 :d 4 :e 5 :f 6 :g 7 :h 8})]
      (conj! t [:i 9]) (persistent! t))
    ;; clj     8 entries, no :i
    ;; clotran 9 entries

ClojureScript switches the same way at the same size (TransientArrayMap
`-assoc!`, `HASHMAP-THRESHOLD` 8, in cljs/core.cljs). Only a program
the docstring calls wrong can tell.

**Removal**: an array-map transient that hands back a different object
past eight entries and leaves the old one frozen. Not planned.

## 65. Character streams are clotran's own types

core.clj writes `(StringReader. s)` in `with-in-str`, wraps it in
`LineNumberingPushbackReader.`, and reads with
`LispReader/read`. Those names are mapped onto clotran.io's
own readers (`src/clj/clotran/io.cljf`: a text reader, a pushback reader,
a line-numbering reader), which have the methods vendored Clojure calls --
`.read`, `.unread`, `.readLine`, `.getLineNumber`, `.captureString` --
and nothing else of clj's io:

    (class (StringReader. "x"))
    ;; clj     StringReader
    ;; clotran clotran.io.TextReader

A `BufferedReader` over a clotran reader is that reader, since
every clotran reader already reads a line at a time. clotran is its own
host, and a clj name appears only where vendored Clojure writes it.

`read` over a stream takes one form's characters off it by LispReader's
rules -- a token ends at whitespace or a terminating macro character,
pushed back; a string, regex or collection at its closer -- and hands the
text to clotran's reader, so the two cannot disagree about what a form
means. A list read from a line-numbering reader does not carry the
`{:line :column}` metadata clj gives it, and a read that fails there
throws the error itself, where clj wraps it in a
`LispReader$ReaderException` whose data holds the line and column.

**Removal**: not planned; it is the design.

## 66. `(String. array)` is refused

clj builds a string from a char array, `(String. (char-array "ab"))` is
`"ab"`, and from bytes with a charset, `(String. bytes "UTF-8")`. Both
are clj's String constructors, and vendored Clojure writes neither.
clotran refuses an array there with an IllegalArgumentException naming
what to use instead -- `clotran.io/utf8-string` decodes bytes,
`(apply str cs)` joins chars -- and `clotran.io/utf8-bytes` is the other
direction.

Before 2026-09-29 an array there became the text of the OBJECT,
`"#<object>"`: a silent wrong answer, which this replaces with a loud one.

**Removal**: not planned; clotran does not model clj's constructors
(no-clj-emulation, SEAMS.md). If ported code needs it, map `(String. cs)`
for a char array onto `(apply str cs)` -- a mapping, not a String class.

## 67. Classes have clotran's names

clj names a class for clj: `Long`, `PersistentVector`,
`StringReader`. clotran has no clj, so its classes are named for
what they are written in:

- **Written in Fortran** (the host): `clotran.host.` and a snake_case
  name, Fortran's convention. A scalar takes its Fortran kind --
  `clotran.host.int8`, `real8`, `int4`, `char`, `logical`, `string`;
  `Object` is `clotran.host.value` -- and everything else is the class's
  simple name in snake_case: `clotran.host.persistent_vector`,
  `clotran.host.map_entry`, `clotran.host.arithmetic_exception`.
- **Written in Clojure**: the deftype's own name in its namespace, in
  Clojure's CamelCase -- `clotran.io.TextReader`, `clotran.io.File`,
  `clotran.rt.ArrayList`, `clotran.uuid.UUID`.

    (class 1)                      ;; clj Long       clotran clotran.host.int8
    (class (StringReader. "x"))
                                   ;; clj StringReader clotran clotran.io.TextReader
    (pr-str (class (object-array 1)))
                                   ;; clj Object/1   clotran clotran.host.value/1
    Double/TYPE                    ;; clj double               clotran :real8

clotran reads only its own names. A clj name -- `String`, `Writer`,
`RT` -- is an unknown class, as a made-up one is:

    (instance? String "x")        ;; clj true   clotran: Unable to resolve symbol: String

Clojure's own source writes clj names, so it is not loaded as it comes:
`upstream/` holds it unmodified and `upstream/derive` writes
`src/clj/clojure` and `test/clj/clojure` from it with every class in
clotran's name, resolving each file's bare names through its imports and
Clojure's default ones (`upstream/class-names.edn`, `upstream/names.clj`).
Where a clotran type is built from its fields but upstream passes the
host constructor's arguments, the renamed code calls clotran's factory
instead: `(StringReader. s)` becomes `(clotran.io/text-reader s)`.
Several clj classes share a clotran class where clotran has one
implementation -- `BigInt` and `BigInteger` are
both `clotran.host.bigint`.

Code ported from clj needs the same renaming; `upstream/names.clj`
does it for any file. The oracle uses it in both directions: each case
goes to clj in upstream's names, and clj's answer comes back in
clotran's, accepted as it stands where a name was only a symbol
(`` `Map ``). `upstream/check-names` keeps clj names out of
everything else.

**Removal**: not planned; it is the design.
