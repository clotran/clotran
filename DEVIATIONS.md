# Deviations from Clojure

Every place clotran does something real Clojure does not, why, and what it
would take to remove it. A deviation with no entry here is a bug.

Not everything native is a deviation. Where we merely *chose* Fortran over
pure Clojure for something Clojure could express, that is a seam, and it
belongs in SEAMS.md instead.

**Reference**: `~/jborden/clojure` -- a clone of `clojure/clojure` at
`clojure-1.12.6` (`31a3138a`) -- the SAME release as the vendored core.clj (see
upstream/clojure/src/clj/clojure/PROVENANCE.md). Paths below are relative to it. Cite the file and the method;
do not cite memory. That is the whole point of having the clone.

Categories:

- **temporary** -- a scaffold. Bootstrapping is incomplete; it goes away.
- **host** -- forced by Fortran. Cannot go away, but must be invisible.
- **design** -- a choice, made on purpose and kept: Fortran's
  conventions where the host decides (James, 2026-10-01), clotran's own
  types and names where clj's are its host showing through
  (no-clj-emulation), or a capability traded for a better one.
- **1.x** -- known, and staying through 1.0 by decision (PLAN step 35),
  each entry saying what removing it takes.
- **open** -- we do not yet know which of the above it is.
- **--** -- resolved; the entry stays as the record.

| # | What | Kind | Where |
|---|------|------|-------|
| 1 | RESOLVED -- load reads one form, evaluates it, reads the next | -- | `src/f/main.f90` |
| 2 | RESOLVED -- nothing preloaded before `core.clj` | -- | `src/f/main.f90` |
| 3 | RESOLVED -- a namespace sees clojure.core by referral | -- | `src/f/Eval.f90` |
| 4 | `.` reaches a fixed table of host members, not arbitrary classes | host | `src/f/Eval.f90` |
| 5 | Metadata is a wrapper object, not carried on the value | host | `src/f/GC.f90` |
| 6 | RESOLVED -- syntax-quote is the reader's | -- | `src/f/Eval.f90` |
| 7 | RESOLVED -- recursion runs 200,000 frames deep interpreted (compiled ~2,200) | -- | `src/f/Eval.f90` |
| 8 | RESOLVED -- multimethods dispatch with `isa?` and preferences | -- | `src/clj/clotran/multifn.cljf` |
| 9 | RESOLVED -- sorted collections | -- | `src/f/Assoc.f90` |
| 10 | RESOLVED -- refs are transactional; `set!` of an unbound Var is refused | -- | `src/f/Namespace.f90` |
| 11 | RESOLVED -- transient maps and sets are boxes mutated in place; vectors are real transients | -- | `src/f/Eval.f90` |
| 12 | Host-bound libs are skipped or replaced by name | host | `src/f/Eval.f90` |
| 13 | RESOLVED -- protocol dispatch is cached | -- | `src/f/Eval.f90` |
| 14 | Regex is ICU under clj's regex's names; `\w` and `(?i)` are Unicode | host | `src/f/Regex.f90` |
| 15 | RESOLVED -- `gc_hash` is Util.hasheq, bit for bit | -- | `src/f/GC.f90` |
| 16 | RESOLVED -- names resolve while analysing | -- | `src/f/analyze.inc` |
| 17 | RESOLVED -- a deftype's short name is imported per namespace | -- | -- |
| 18 | A host object -- a deftype instance, a fn, a namespace -- prints with clotran's identity and text | design | -- |
| 19 | RESOLVED -- `recur` in a deftype method leaves out `this` | -- | -- |
| 20 | RESOLVED -- mutable deftype fields are honoured | -- | -- |
| 21 | RESOLVED -- `pr` of a namespace shows its name, not an `#object[...]` form | -- | -- |
| 22 | RESOLVED -- collections as keys hash and compare structurally | -- | -- |
| 23 | RESOLVED -- a function is an IObj | -- | -- |
| 24 | Arrays are never ragged | design | -- |
| 25 | RESOLVED -- `aset` on a primitive array accepted any number | -- | -- |
| 26 | RESOLVED -- BigInt, and what a Ratio still cannot hold | -- | -- |
| 27 | RESOLVED -- the two smallest subnormal doubles printed with one digit too few | -- | -- |
| 28 | `proxy` is a special form, and accepts methods no superclass declares | host | -- |
| 29 | RESOLVED -- an agent's actions run on a thread of the agent's own | -- | -- |
| 30 | RESOLVED -- BigDecimal, except for rounding | -- | -- |
| 31 | RESOLVED -- stack traces | -- | -- |
| 32 | RESOLVED for a user's code -- a qualified symbol that does not resolve is refused when analysed | -- | -- |
| 33 | Reader conditionals are read in every file, and `.cljf` is a source extension | open (James) | -- |
| 34 | RESOLVED -- a class is a value of its own kind | -- | -- |
| 35 | RESOLVED -- an unrealised seq hashed by identity, so it was not found as a map key | -- | -- |
| 36 | RESOLVED -- `binding` refuses a Var not declared `^:dynamic` | -- | -- |
| 37 | RESOLVED -- `apply` hands a variadic fn its rest unrealised | -- | -- |
| 38 | RESOLVED -- a future runs on a thread of its own | -- | -- |
| 39 | A map entry's class is clotran.host.persistent_vector | design | -- |
| 40 | `core_print.clj`, `data.clj` and `clotran.files` are clotran's own | design | -- |
| 41 | A string is indexed by code point, not by UTF-16 unit | design | -- |
| 42 | RESOLVED -- `s/check-asserts` turns the checks on | -- | -- |
| 43 | `*math-context*` has a working precision, so a decimal division answers | design | -- |
| 44 | RESOLVED -- `tap>` delivers on the calling thread, before it returns | -- | -- |
| 45 | RESOLVED -- a short, byte or char array had its storage kind's class | -- | -- |
| 46 | RESOLVED -- data readers work in `clojure.edn` and nowhere else | -- | -- |
| 47 | RESOLVED -- `all-ns` answers clotran's own libraries beside clj's, not host class names | -- | -- |
| 48 | Type hints: clj's static types, inferred here for what they refuse, narrower | 1.x | -- |
| 49 | RESOLVED -- A task blocked below compiled code was pinned | -- | -- |
| 50 | Pure Fortran writes a double as Fortran does | design | -- |
| 51 | Division by zero says "Divide by zero" where clj's primitive path says "/ by zero" | 1.x | -- |
| 52 | A parallel loop reports whichever failing iteration stops first | host | -- |
| 53 | `identical?` on equal numbers is true | design | -- |
| 54 | A name built with a slash in its namespace splits at the first slash | 1.x | -- |
| 55 | RESOLVED -- clojure.core is direct-linked, as Clojure compiles it | -- | -- |
| 56 | An index is 64-bit; clj truncates a vector's to 32 | design | -- |
| 57 | `vec`, `sort` and `to-array` copy an array; clj aliases it | design | -- |
| 58 | RESOLVED -- core's one-line wrappers are on the call stack | -- | -- |
| 59 | A lazy seq's thunk keeps its closed-over locals after it runs | design | -- |
| 60 | RESOLVED -- a deftype's hash is asked at each hash | -- | -- |
| 61 | A vector key past 32 bits is out of range, not wrapped | design | -- |
| 62 | RESOLVED -- an array of references knows its element class | -- | -- |
| 63 | `vec` of an array copies it | design | -- |
| 64 | A transient used in place keeps what was added to it | design | -- |
| 65 | Character streams are clotran's own types | design | -- |
| 66 | `(String. array)` is refused | design | -- |
| 67 | Classes have clotran's names | design | -- |
| 68 | RESOLVED -- an uncaught error in a program is reported as clojure.main reports one | -- | -- |
| 69 | A shift by 64 or more follows clotran's host, Fortran | design | -- |
| 70 | A Ratio becomes a double by Fortran's quotient | design | -- |
| 71 | `count`, `compare` and `hash` answer clotran's one integer | design | -- |
| 72 | A ratio less the smallest long is exact | design | -- |
| 73 | A loop or try in an expression adds no frame | design | -- |
| 74 | A hash map's nil key is walked where its hash puts it | 1.x | -- |
| 75 | A UUID's text is the canonical one | design | -- |
| 76 | min and max order 0.0 and -0.0 by position, always | design | -- |
| 77 | The host's abs of a long is the long's, reflection or not | design | -- |
| 78 | A future after shutdown-agents still runs | design | -- |
| 79 | The names clj imports into every namespace are not names here | design | -- |
| 80 | An input stream's `skip` stops at the end, a file's as an array's | design | -- |
| 81 | `.hashCode` of a core value is not a member | design | -- |

---

## 1. RESOLVED -- load reads one form, evaluates it, reads the next

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

## 2. RESOLVED -- nothing of clotran's loads before core.clj

**RESOLVED 2026-10-12.** Clojure loads nothing before `clojure/core.clj`;
its bootstrap is the host's (`RT.doInit`). clotran's once loaded
`src/clj/host.clj` first -- scaffolding `defn`, `fn` and `let` macros
and type predicates over `clotran-type`, from when core.clj could not
load. core.clj defines every one of them itself, and it now loads with
nothing ahead of it; the file is gone. What stands in for `RT.doInit`
is Fortran: the special forms, the builtins core.clj's host calls
reach, and the `ns` and `in-ns` core answers in every namespace
(DEVIATIONS 3).

## 3. RESOLVED -- a namespace sees clojure.core by referral, not by a fall-back

**RESOLVED 2026-10-10 (PLAN step 35).** `resolve_var` and `ns-resolve`
no longer fall back to clojure.core: a namespace's mappings are what
`refer` put there, so `(ns foo (:refer-clojure :exclude [map]))` leaves
`map` unresolved in foo and `(in-ns 'bare)` sees nothing of core, as in
clj -- nothing but `ns` and `in-ns`, which Compiler.resolveIn answers in
every namespace, and which a library's first form needs when it is
required from a namespace that has not referred core yet (scripts/fuzz-macro
found that case). `user` is given clojure.core as RT.doInit gives it (Eval.f90,
gce_refer_core: every public Var core owns, a snapshot of the same Var
objects), by the REPL, a script and a program; the host's own tests get
the builtins the same way before core.clj. Measured against clj in
test/clj/oracle.clj. The original entry follows.

---

Symbol resolution falls back to `clojure.core`

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

## 6. RESOLVED -- syntax-quote is the reader's

**RESOLVED 2026-10-12.** `SyntaxQuoteReader` is a READER macro and so is
clotran's: `` `form `` is expanded as it is read (Eval.f90
`syntax_quote`, a port of `LispReader.syntaxQuote`, installed as the
reader's expander), into clj's own shape -- `(clojure.core/seq
(clojure.core/concat (clojure.core/list ...) ...))`, `(clojure.core/apply
clojure.core/vector ...)` for a vector, `hash-map` and `hash-set` likewise,
`(clojure.core/with-meta ...)` for metadata but the reader's `:line` and
`:column`, `(quote x)` for nil, true and a special form. `(read-string
"`x")` is `(quote user/x)`, as in clj, and the expansion is a seq, not a
list: `(list? `(a))` is false on both. Names resolve in the namespace
current when the form is read (`Compiler.resolveSymbol`): a Var to its
own namespace, anything else to the reader's, a name the namespace maps
to a class to the class's full name, `catch`, `finally`, `&`, `.m` and
specials as written; each syntax-quote has its own `x#` names, made in
reading order (`GENSYM_ENV`). `(quasiquote x)` is no special form, as
in clj. A tagged literal's marker (DEVIATIONS 46) is quoted whole.

What it took beyond the port: a form now reaches the analyser holding
seqs where it held lists, as clj's compiler accepts (`forms_as_lists`
lists them at the top level and after a macro or an `:inline`
expansion); and while the expansion runs the reader's roots -- the
form it is part way through -- are on the value stack. A `#(...)` names its
parameters as FnReader does, each numbered at its first use.
`scripts/fuzz-read` generates syntax-quote against clj.

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
temporaries could fill the stack before it. Until 2026-10-12 that
stopped the process ("the value stack is full"); a call made with
less than the stack's last 65,536 slots free now raises
`stack_overflow_error`, catchable as clj's StackOverflowError is
(Eval's stack_low, in every executor; scripts/fuzz-spec found it, a
nested `s/*` conforming). The fuzzers compare no case clj itself overflows on:
the depth is each host's. The original entry follows.

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

## 10. RESOLVED -- refs are transactional; `set!` of an unbound Var is refused

**RESOLVED for `set!` 2026-10-10 (PLAN step 35).** `set!` and `var-set`
of a Var with no binding on this thread are clj's refusal, "Can't
change/establish root binding of: x with set", and never write the root.
What made the root write look necessary is now bound the way clj binds
it: a file load pushes `Compiler.load`'s frame (`*ns*`,
`*warn-on-reflection*`, `*unchecked-math*`, `*data-readers*`, each at its
current value, popped however the load ends), and once core.clj has
loaded the process runs under clojure.main's `with-bindings` frame
(`*ns*`, `*warn-on-reflection*`, the print Vars, `*1` to `*e` and the
rest), as its REPL and its scripts do. So `(set! *warn-on-reflection*
true)` at a file's top ends with the file, and at the prompt holds for the
session. Measured against clj in test/clj/oracle.clj. The transactional
part is unchanged below.

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

## 12. Host-bound libs are skipped or replaced by name

`gvec` is skipped: it wants clj's collection library. `core_proxy` and
`genclass` import `clojure.asm`, `ClassWriter` and `DynamicClassLoader`
to emit bytecode, and each is replaced by clotran's own file, loaded in
its place: `clotran/core_proxy.cljf` (DEVIATIONS 28) and
`clotran/genclass.cljf`, whose `gen-class` is nothing -- as clj's is
whenever `*compile-files*` is false, which for clotran is always -- so
`(ns app.core (:gen-class))` is an ordinary namespace. Clojure's io
library is replaced by `clotran.files` (DEVIATIONS 40). `uuid` was skipped until
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
still share one hash. Left different: a class object, and a record (a
lazy seq hashed by identity until entry 35 resolved it). The original
entry follows.

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

## 16. RESOLVED -- names resolve while analysing

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
constant. `__defining-ns__` is gone. What remained of this entry was
deviation 3 (the `clojure.core` fallback inside `resolve_var`) and
deviation 32, both since resolved.

## 17. RESOLVED -- a deftype's short name is imported per namespace

**RESOLVED 2026-10-10 (PLAN step 35).** `import*` records a short name
in the namespace being analysed (Eval.f90, record_import, `import_ns`),
and a bare class name resolves through that namespace's imports and
nothing else (canon_class), a host class (`clotran.host.*`) being every
namespace's, as clj's own base classes are everywhere there; a type is registered under its full
name only. So `(Point. 1)` in a namespace that did not define or import it
is clj's "Unable to resolve classname: Point" when analysed,
`(instance? Point x)` there is "Unable to resolve symbol: Point in this
context", two
namespaces' `Point`s are two classes, and `aa.Point` works everywhere.
`new` and a static call's target are made canonical when analysed, by
the namespace the form is written in, never the one running; the import
itself is recorded when `import*` RUNS, as ImportExpr.eval records it,
so one inside a fn body takes effect when the fn runs. Measured
against clj in test/clj/oracle.clj; scripts/fuzz-deftype makes types in
random namespaces. The original entry follows.

---

A deftype's short name is global, not imported per namespace

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

## 18. A host object -- a deftype instance, a fn, a namespace -- prints with clotran's identity and text

Clojure prints one as `#object[user.Point 0x4a2e1f "user.Point@4a2e1f"]`.
clotran prints `#object[user.Point 0x3b214 "#object[user.Point]"]`
(measured 2026-10-10): the identity is there since entry 21 gave host
objects one (`System/identityHashCode`), and what differs is the text
inside, which in clj is `Object.toString`'s `class@hash` and here is
the printer's own form. By design: the text of a host object is the
host's, and nothing reads it back. Two distinct instances print
distinctly, which is what this entry once lacked.

The same for every host object: a function prints as
`#object[user$fn 0xf6a8 "#<fn>"]` where clj prints
`#object[user$eval1$fn__135 0x49d98dc5 "user$eval1$fn__135@49d98dc5"]`,
and a namespace as `#object[clotran.host.namespace 0x8 "clojure.core"]`
(measured 2026-10-14). `scripts/oracle` records these as expected
differences under this entry.

## 19. RESOLVED -- `recur` in a deftype method leaves out `this`

**RESOLVED 2026-10-10 (PLAN step 35).** A `recur` in a deftype, defrecord
or reify method takes one argument fewer than the head declares and
passes `this` through unchanged, as clj does; passing it is clj's
refusal, "Mismatched argument count to recur, expected: 1 args, got:
2", which is now the wording of every recur arity error. The method is
still an ordinary closure whose first parameter is `this`: the analyser
knows it for a method (every method body is wrapped in `clotran-fields*`,
fields or not) and supplies that parameter's local as the first recur
argument, so the three executors see a full-arity recur and need no
change. A `loop` inside a method, and a `fn` made in one, recur as they
always did. Measured against clj in test/clj/oracle.clj; the refusal's
wording in test/clj/language_test.clj, raised when the form is analysed,
as clj raises it. The original entry follows.

---

`recur` in a deftype method must pass `this`

Clojure supplies the target object automatically, so a `recur` in a
method body passes one fewer argument than the method head declares:
"recur calls to the method head should *not* pass the target object, it
will be supplied automatically and can not be substituted." That is a
clj artifact -- `this` is not a parameter there, it is the receiver.

Here a method is an ordinary closure whose first parameter is `this`, so
the recur point has the arity the head is written with and `recur` takes
all of them. A method body ported verbatim from Clojure that recurs will
get "recur has the wrong number of arguments" when the type is
defined (measured 2026-10-10), which is at least loud.

It goes away by making the method's recur point exclude its first
parameter, which is a change to `select_clause`'s partner in
`eval_recur`, not to `deftype*`.

## 20. RESOLVED -- mutable deftype fields are honoured

**RESOLVED 2026-10-10 (PLAN step 35).** A field marked
`^:volatile-mutable` or `^:unsynchronized-mutable` is read and written
through `this` wherever its name is not shadowed: the analyser keeps a
table of the method's fields (`clotran-fields*`, filed by
`bind_fields`), and `(set! f v)` in the type's own method is
`(set! (.-f this) v)`, a write into the instance's field vector,
answering v; a read after it sees the new value, in the method, in a
loop, and in a fn made there, which reads through its captured `this`.
A set! of a field not declared mutable, or of a mutable one from a fn
made in the method, is clj's refusal, "Cannot assign to non-mutable:
f" -- in clj when the type is defined, here when the method first
runs, since a method body is analysed when first run; the one
residual. A mutable field is private, as in clj: read through a
method, never `.-f` from outside. A local that shadows the name is
the local, as in clj. Measured against clj in
test/clj/oracle.clj (Tally, Shadow). Records' `__hash` and `__hasheq`
are mutable fields, so their caching now happens. The original entry
follows.

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
A function prints as `#object[user$fn 0x.. "#<fn>"]`; what differs
is the text inside, entry 18. The original entry follows.

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

`String/format` and an identity for host objects both exist since
(2026-10-10: `(pr-str (P. 1))` is `#object[user.P 0x3b214 ...]`);
what stays is the text inside the form, the host's, as entry 18 says.

The same held for every other host object; since 2026-10-10 each
prints as an `#object[...]` with an identity, and only the text inside
differs (entry 18).

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

**What was left**, a lazy seq as a key hashing by identity, is entry
35, resolved: `(= (hash (map inc [1 2])) (hash '(2 3)))` is true
(measured 2026-10-10).

**How this was found**, which is the part worth keeping: two
assertions in Clojure's `control` suite were PASSING under the old
identity hashing, because a slot hash happened to land in the bucket
holding the right key and `=` then agreed. Widening integers to 64 bits
moved every bucket and the coincidence ended, so the scorecard fell by
two with nothing in the collection code having changed. Neither number
was measuring correct behaviour. Fixing it properly moved Clojure's
suite from 778 passing assertions to 797, all of it in two namespaces:
`control` 156 -> 164 and `clojure-set` 99 -> 110.

## 23. RESOLVED -- a function is an IObj

**RESOLVED 2026-10-10 (PLAN step 35).** `(instance? clotran.host.i_obj
(fn []))` is true, as clj's AFunction is one. What had kept it false was
printing: print-method's :default re-dispatches on an IObj, and a fn had
no print-method it could reach; since entry 21 gave host objects
`String/format` and an identity, print-method Object is that last resort
and a fn with metadata prints as `#object[...]`, with or without a
`:type` in its metadata. Measured against clj in test/clj/oracle.clj.
The original entry follows.

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

`String/format` exists since, and a fn carries metadata already
(`with-meta` and `meta` work on one, above); what is left is
`instance?` answering IObj for a fn, measured false on 2026-10-10 where
clj says true. Small, and open (PLAN step 35).

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

## 25. RESOLVED -- `aset` on a primitive array accepted any number

**RESOLVED with entry 45 (2026-09-27):** `aset` takes what `RT.aset`'s
overloads take, and anything else is the Reflector's refusal. Measured
2026-10-10: `(aset (long-array 2) 0 1.5)` is "No matching method aset
found taking 3 args" here and in clj. The original entry follows.

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

- ~~A Ratio's numerator and denominator are still 64-bit.~~ **Closed
  2026-10-01.** A Ratio's parts are any size (Eval.f90 rational.inc):
  one that fits is immediate, any other is its `n/d` text, and every
  operation is exact. Before, the denominator lived in 32 bits and the
  numerator overflowed unchecked -- `(/ 1 3000000000)` was
  `1/-1294967296` and `(+ 9223372036854775807 1/2)` was `-1/2`, wrong
  answers rather than the error this entry promised (scripts/fuzz
  --fns found them). `rationalize`, missing until then, is
  Numbers.rationalize's.
- **`1.5M` is a decimal** since entry 30 resolved (measured
  2026-10-10: `(class 1.5M)` is clotran.host.decimal).
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

## 27. RESOLVED -- the two smallest subnormal doubles printed with one digit too few

**RESOLVED 2026-10-05.** `(pr-str Double/MIN_VALUE)` is `4.9E-324` and
`(pr-str 9.9E-324)` is `9.9E-324`, as in clj. The entry said the JDK's
second digit was more than its specification requires; it is not.
`Double.toString` writes at least one digit after the point, so never
fewer than two, and when one digit would read back it writes the two
nearest the value. The printer does the same now (Printer.f90,
`real_str`).

The same change fixed a real shortest-round-trip bug the entry did not
know of. The nearest p-digit decimal need not read back when another
p-digit decimal does: 2^122 is `5.316911983139664E36`, whose nearest 16
digits end `...663`, the next double down, so clotran printed 17 digits.
98 of the 4196 signed powers of two printed a digit longer than clj
(scripts/fuzz-fn found one); the printer now also asks the two
neighbours one unit in the last digit away. The oracle prints every
power of two against clj.

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

## 32. RESOLVED for a user's code -- a qualified symbol that does not resolve is refused when analysed

**RESOLVED 2026-10-10 (PLAN step 35), everywhere but the vendored tree.**
In a user's file or at the prompt an unresolved qualified symbol is
Compiler.resolveIn's refusal when the form is analysed: "No such var:
s/nope" (the symbol as written) where the namespace or alias exists,
"var: #'a/p is not public" where it is private, "No such namespace: x"
where there is none -- a mistyped class name included -- and the
var-quote's "Unable to resolve var: x/y in this context"; a static call
on a class nothing knows, `(Strng/format "x")`, is "No such namespace:
Strng" when analysed too, a `deftype*` having declared its class name
when it was analysed, as clj defines the class then. The deferral
below (N_LATEVAR, and the var-quote's placeholder namespace) remains for
the vendored tree, clotran's own files and Clojure's own tests, by their
file names (analyze.inc, defers_late_vars), since core.clj names
libraries before they load and names ones that are skipped (DEVIATIONS
12). Measured against clj in test/clj/oracle.clj. The original entry
follows.

---

A qualified symbol that does not resolve is a run-time error

Clojure fails to COMPILE a form naming a Var that does not exist:
`Unable to resolve symbol: jio/reader` (for a namespace that does not
exist at all, clj's message is its host's ClassNotFoundException,
measured 2026-10-10). clotran's analyser does the
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

**Open, for James (2026-10-12):** keep the leniency by design, or
remove it for 1.0. Removing it touches three readers -- the Fortran
reader's every entry (`read-string` and `read` honouring `:read-cond`,
a file's by its extension, the REPL allowing), and `clotran.io`'s
stream reader, which reads `#?` in Clojure -- and `:read-cond
:preserve` (ReaderConditional values) would be its own piece. It only
ever accepts text clj refuses; no program clj runs reads differently.

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

- clotran has one map, one set and one seq view where clj has many, so
  the most common clj class stands for each: every map is a
  `clotran.host.persistent_array_map`. A vector's `seq` is a
  `clotran.host.persistent_vector_chunked_seq`, as in clj; a map's, a
  set's and a string's are each a `clotran.host.a_seq`, the superclass
  of clj's `PersistentArrayMap$Seq`, `APersistentMap$KeySeq` and
  `StringSeq`. So IDrop, which clj 1.12's `drop`, `nthrest` and
  `nthnext` ask first, is the vector's, its seq's and a long range's
  here, and not a string's or an array map's seq's or `repeat`'s: those
  drop by walking, to the same values, as a lazy seq. An array's class is its
  element kind and rank, `int/1`.
- a function's class is named as clj's compiler names it,
  `clojure.core$int_QMARK_`, `user$foo_bar$hop` (and as cljs names its
  fns), since spec reads a function's name back out of it (`fn-sym`;
  found by `scripts/fuzz-spec`). Without clj's `__N` counters: two
  anonymous fns written in the same place share a class name, where
  in clj each `fn*` form has its own. An arity error names the fn the
  same way, demunged: `passed to: user/bar/fn` where clj says
  `user/bar/fn--134` (scripts/fuzz drops the counters before
  comparing). Its supers are `AFunction`'s,
  less the host's `Runnable`, `Callable`, `Comparator` and
  `Serializable`.
- `supers` answers the short chain `host_super` lists -- the
  interfaces `core_print` and `core_deftype` dispatch on -- not the
  two dozen a clj class implements. It must include every interface a
  protocol in the loaded code is extended to, or `find-protocol-impl`
  picks a different implementation: until 2026-09-25 the chunked seqs
  lacked `IChunkedSeq`, so InternalReduce fell to Object and a reduce
  over `(map f (range n))` walked element by element (the oracle now
  checks the pick). With no superclass chain (below), CollReduce picks
  Object where Clojure picks ASeq for a ChunkedCons -- the same body,
  `(seq-reduce coll f val)`, so the same answer. Until 2026-10-05 a
  vector's seq could not claim `IChunkedSeq` either, because every seq
  view shared its class, and `(reduce + (seq v))` walked element by
  element, 985 ms a 10^6 where the chunks take 81.
- there is no `Class` object graph: no `getSuperclass`, no
  `getDeclaredMethods`, nothing reflective. A class here is a NAME
  with the runtime's own answers behind it.

The internal type TAG -- `:string`, `:vector`, `:int` -- is what
`clotran-type` answers; it is not `class`, and never was meant to
leak.

## 35. RESOLVED -- an unrealised seq hashed by identity, so it was not found as a map key

**RESOLVED 2026-10-02.** A lazy seq, and a ChunkedCons whose rest is
not yet realised, is realised to hash it (`walk_seq_hash`) and compared
by its elements inside a map or set (`gc_equal`, `is_seq_kind`), as
`ASeq.hasheq` and `Util.equiv` do: `(contains? #{(map inc [1 2])} [2
3])` is true and `(hash (range 3))` is `(hash [0 1 2])`. What made it
safe is the GC hold (`gc_hold_begin`): nothing is collected while
`gc_hash` runs, so what realising allocates cannot take the half-built
trie with it, and no root set had to be threaded through. Found when
clotran's compiler looked a pooled constant up by value -- a lazy seq
stored, a list asked for, equal but hashed apart -- and wrote `sv(b + )`
(scripts/fuzz-spec, compiled). The original text follows.

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

## 36. RESOLVED -- `binding` refuses a Var not declared `^:dynamic`

**RESOLVED 2026-10-10 (PLAN step 35).** `push-thread-bindings` refuses a
Var whose metadata has no `:dynamic`, with clj's wording and class:
`Can't dynamically bind non-dynamic var: user/g`, an
IllegalStateException, at run time as `Var.pushThreadBindings` does.
A `def` puts `:dynamic` in the Var's metadata; the host's own earmuffed
Vars (`*ns*`, `*out*`, `*print-length*` ...) get it when they are made
(bind_var), as clj declares each of them. Measured against clj in
test/clj/oracle.clj. The original entry follows.

`(def g nil) (binding [g 1] g)` answers `1` here. Clojure refuses it
at run time -- `Can't dynamically bind non-dynamic var: user/g`, an
IllegalStateException from `Var.pushThreadBindings` in clj's own
source (not the compiler, as this entry once said; measured
2026-10-10) -- and
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

## 42. RESOLVED -- `s/check-asserts` turns the checks on

**RESOLVED 2026-10-10 (PLAN step 35).** `RT/checkSpecAsserts` is a
writable box behind its host-table row (HK_BOXVAR): reading the static
answers the box WHEN RUN -- every other static is folded at analysis,
since its value cannot change -- and `(set! clotran.host.rt/checkSpecAsserts flag)`,
which is what `s/check-asserts` does, writes it. `(s/check-asserts
true)` then `(s/assert int? "x")` is the ExceptionInfo clj throws,
`(s/check-asserts?)` answers what was set, and off again `s/assert` is
its value. Measured against clj in test/clj/oracle.clj. The original
entry follows.

clojure.spec.alpha's `assert` is
`(if RT/checkSpecAsserts (assert* ...) x)`, and
`check-asserts` flips that field with `(set! (. RT
checkSpecAsserts) flag)`. The field is here as a host static that reads
FALSE -- clj's default, `-Dclojure.spec.check-asserts` unset -- so
`(s/assert spec x)` is `x`, as it is on a stock clj. `set!` of a host
static has nowhere to write (DEVIATIONS 4), so `(s/check-asserts true)`
answers true and enables nothing (measured 2026-10-10:
`(s/check-asserts?)` stays false and `(s/assert int? "x")` answers
"x"): a silent no-op where it once threw, which is worse, and open.

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

## 47. RESOLVED -- `all-ns` answers clotran's own libraries beside clj's, not host class names

**RESOLVED (measured 2026-10-10).** `(count (all-ns))` is 17 here
against clj's 13, and the extra four are real libraries with publics
-- clotran.rt, clotran.files, clotran.thread, clotran.uuid,
clotran.multifn and fortran -- loaded with core; no namespace is made
for a host class any more: `(find-ns 'Math)` and `(find-ns
'clotran.host.rt)` are nil after qualified host calls. The cause this
entry describes is gone. The original entry follows.

`(count (all-ns))` was 64 here against real Clojure's dozen, and the
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

## 48. Type hints: clj's static types, inferred here for what they refuse, narrower

A hint changes what a Clojure program DOES, and clotran does it: a
`^long` or `^double` parameter or return converts by `RT.longCast` /
`RT.doubleCast` after a checkcast to Number (`Compiler.emitUnboxArg`),
or by `uncheckedLongCast` when `*unchecked-math*` is on as the fn is
analysed, so `((fn [^long n] n) 1.5)` is 1 and `((fn [^long n] n) \a)`
throws; an array hint is a checkcast where the value is USED as an
array (`aget`, `aset`, `alength`); more than four primitive parameters,
a variadic one, and `^int`/`^float` parameters fail as they do in clj;
and `aget`, `aset` and `alength` on a non-array are the Reflector's
IllegalArgumentException ("No matching method aget found taking 2
args", "More than one matching method found" for nil, "Argument is not
an array" through aget's fn body).

clj also types each expression when it compiles it, and refuses by
that type (since 2026-10-12 here too, analyze.inc `static_prim`):

- a recur to a `^long` or `^double` fn parameter whose argument is not
  that primitive ("recur arg for primitive local ... is not matching
  primitive", RecurExpr), found when the fn is emitted: after its body,
  and after
- a primitive return hint given a body of another primitive
  ("Mismatched primitive return", ObjMethod.emitBody), and
- a hinted let or loop local whose init is a primitive ("Can't type
  hint a local with a primitive initializer", LocalBinding; a tag is a
  symbol or a string, as Compiler.tagOf reads one, so `case`'s
  evaluated `{:tag Object}` is none).

The inference types literals, the casts, Numbers' ops by their
overloads (`+` of a double and an Object is a double, of a long and an
Object a Number; `max` of a long and a double an Object), comparisons,
`count`, a hinted array's `aget` and `alength`, the host's math as
`Math`'s signatures, `if` (a recurring branch the other's type), `do`,
`let`, locals (a loop local its init's, as clj's first pass; a
closed-over one where it was bound), and calls through a Var (an
`:arglists` vector with a primitive is invokePrim, else an Object).
`scripts/fuzz-hints` generates all of these against clj.

What differs: what it does not type, it lets through, so clotran
accepts some programs clj refuses and never the reverse -- a host
instance method or field, a deftype's primitive field, a static of a
host class other than math, an array whose type clj knows from its
constructor's return rather than a hint, and an `:inline` core fn
outside its table (bit-test, say). A loop
clj re-analyses with a boxed local (a recur that did not match) is not
re-analysed here; only an error that second pass alone would find
differs. The class a recur message names is clotran's, or Object where
clj names one of its host's (a Number, a vector's abstract class); `(recur nil)` to a primitive
parameter is that IllegalArgumentException here, a NullPointerException
inside clj's compiler there. A hinted nil array is a
NullPointerException on both, with a different message.

**Removal**: each untyped form above is a case of `static_prim`;
`scripts/fuzz-hints` grows a shape with each.

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

This is the STANDALONE road's. Inside a compiled library (PLAN step
13) a pure version's message is the interpreter's: the double is
carried back to the dispatcher in the error record and the runtime
writes it, so `(long 1.0E300)` says `1.0E300` either way (fuzz-fn
found the Fortran text there, seed 3339268384). Versions that print
are not dispatched to in a library, so no other text reaches a user
from pure code there.

A decision, not an accident: pure Fortran is meant to read as Fortran
to the Fortran programs that use it. **Removal** is not planned.

## 51. Division by zero says "Divide by zero" where clj's primitive path says "/ by zero"

**Stays through 1.0 (decided 2026-10-10, PLAN step 35):** choosing the
string needs clj's static type inference in the analyser; the exception
class is the same on both.

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

**Stays through 1.0 (decided 2026-10-10, PLAN step 35):** the removal is a
namespace boundary stored beside every interned symbol and keyword text,
for names clojuredocs itself calls non-conformant.

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
`identical?` to it. Here each makes a copy -- as ClojureScript does for `sort` and
`to-array`; its `vec` aliases an array, as clj's does (entry 63).
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

## 60. RESOLVED -- a deftype's hash is asked at each hash

**RESOLVED 2026-10-11.** A deftype's own `equals` (and `equiv`) is its
`=`, and its `hasheq`, else `hashCode`, is its `hash`, as a map key and
in a set too -- as clj's `Util.equiv` and `Util.hasheq` ask them. Its
`compareTo` is its `compare`. The hash method is now called at EACH
hash, as in clj: a `hashCode` with a side effect has it every time, and
a type whose hash reads a `^:volatile-mutable` field answers the field's
current value. It used to be asked once, at construction, because
hashing runs inside a map insert, where running Clojure could collect
what the insert holds; `gc_hash` now calls `gce_coll_hash` under the
GC hold (GC.f90 `gc_hold_begin`), which defers every collection until
the hold ends, so the method runs there as a lazy seq's realisation
already did.

Records are equal by type and values and hash as emit-defrecord's
hasheq does, computed in Fortran from the field names (Eval.f90
`gce_coll_hash`, `gce_coll_equal`). A type that declares no hash
method hashes by identity, as in clj. `scripts/fuzz-deftype` moves a
hash field between hashes and counts the calls, against clj.

## 61. A vector key past 32 bits is out of range, not wrapped

(The same fact as entry 56, seen from the key's side; both stand.)

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

## 62. RESOLVED -- an array of references knows its element class

**RESOLVED 2026-10-10 (PLAN step 35).** A `value` array carries the
class it was made for beside its kind (NativeArray, `elem_class`): what
`make-array` was given, what `into-array` was given or inferred from the
first element (Object for nil or nothing), copied by `aclone`, kept in
the image. `(class (make-array String 1))` is `String/1`, `instance?`
of `String/1` is true of it and of `Object/1` too, as a String[] is an
Object[]; `into-array` refuses an element that is not an instance of
the class, "array element type mismatch", as the typed store does.
Measured against clj in test/clj/oracle.clj. The original entry follows.

---

An array of references does not know its element class

Every array of references is an `Object[]` here: a `value`-kind native
array, whose class is `[LObject;` whatever it was made for.

    [(class (make-array String 1)) (class (into-array ["a"]))
     (instance? (Class/forName "[LString;") (make-array String 1))]
    ;; clj     [String/1 String/1 true]
    ;; clotran [clotran.host.value/1 clotran.host.value/1 false]  -- Object, under entry 67's names

Primitive arrays are not affected (`int/1`, `double/2` are right), and
the array class SYMBOLS resolve: `String/1`, `int/2` and `[I` name
the classes they name in clj.

**Removal**: an element class beside `elem_kind` in NativeArray's
registry, set by `make-array` and `into-array` (from its type argument,
or the first element's class as `into-array` infers it), copied by
`aclone`, and read by `array_class_name`. Not planned yet.

## 63. `vec` of an array copies it

(Entry 57 covers this, with `sort` and `to-array`; kept for its heading.)

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

A message that would name a host artifact names clotran's instead: a
library that cannot be found is "Could not locate app/core.cljf,
app/core.clj or app/core.cljc on the load path", where clj's lists a
compiled class file first and says classpath.

Code ported from clj needs the same renaming; `upstream/names.clj`
does it for any file. The oracle uses it in both directions: each case
goes to clj in upstream's names, and clj's answer comes back in
clotran's, accepted as it stands where a name was only a symbol
(`` `Map ``). `upstream/check-names` keeps clj names out of
everything else.

**Removal**: not planned; it is the design.

## 68. RESOLVED -- an uncaught error in a program is reported as clojure.main reports one

**RESOLVED 2026-10-10 (PLAN step 35).** A program (`clotran -m app.core`,
`clotran app.cljf`, a built executable) ends an uncaught exception with
clojure.main's two lines, on stderr, status 1:

    Execution error (arithmetic_exception) at app.core/-main (core.cljf:2).
    Divide by zero

The class is clotran's own simple name, left out for `exception` and
`runtime_exception` as clj leaves out Exception and RuntimeException;
the frame is the innermost at the throw (a host-raised exception
records it too, raise_class's capture_innermost), and the line is the
call, construction or throw in progress there -- every path that can
raise notes its site first, and a call through an inlined core fn keeps
the position of what was written rather than its expansion's. A throw
outside any fn names the file and the line of its form. What differs:
no "Full report at" file is written.
A load's failure (`load-file`, `require`, the REPL) keeps clotran's own
report, with the form and the trace. check-program asserts the text.
The original entry follows.

---

An uncaught error in a program is reported as a load failure

`clj -M -m app.core` ends an uncaught exception with its own report:

    Execution error (ArithmeticException) at app.core/-main (core.clj:2).
    Divide by zero

clotran's (`clotran -m app.core`, `clotran app.cljf`) is the one a load
prints when a form fails -- the message, where, and the form -- on stderr:

      Divide by zero  at -m app.core:2:1
        in: (clojure.core/apply app.core/-main clojure.core/*command-line-args*)
    load -m app.core: stopped at form 2

The status is 1 in both. The value and the message are the same; the
layout is not, and clj's names the frame that threw where clotran's names
the form that was running.

**Removal**: print clojure.main's `ex-str` layout in program mode, which
needs the throwing frame's var and file (the trace has them, DEVIATIONS
on traces).

## 69. A shift by 64 or more follows clotran's host, Fortran

`(bit-shift-left 1 64)` is 0 here and 1 in clj; `(bit-shift-right -8
65)` is -1 here and -4 there. clj's `Numbers.shiftLeft` is its host's
`x << n`, which takes only the low six bits of a long's shift count,
so a shift by 64 is a shift by 0. That is the host, not the
language: ClojureScript's `bit-shift-left` is the host's own `<<`
(cljs/core.cljc, `(js* "(~{} << ~{})")`), which takes five bits of a
32-bit count -- the two hosts already disagree. clotran's host is
Fortran, and its shifts are Fortran's `shiftl`, `shifta` and `shiftr`:
every bit shifted out, so a count of 64 or more leaves 0 (or -1 for an
arithmetic right shift of a negative number). James, 2026-10-01: keep
Fortran's conventions, do not replace them with clj's host's.

Counts from 0 to 63 agree. A negative count is outside Fortran's range
for these intrinsics, and is not relied on. `bit-set`, `bit-clear`,
`bit-flip` and `bit-test` follow, being a shifted mask in clj too
(`Numbers.setBit` is `x | (1L << n)`): an index of 64 or more touches
no bit here, where clj's takes it modulo 64.

**Removal**: none intended. Masking the count (`iand(n, 63)`) would
match clj's host at one line per shift, and was written and reverted.

## 70. A Ratio becomes a double by Fortran's quotient

`(double 2/3)` is 0.6666666666666666 here and 0.6666666666666667 in
clj, and so is a ratio's part in mixed arithmetic: `(+ 2/3 -2.25)` is
-1.5833333333333335 here, -1.5833333333333333 there. clj's
`Ratio.doubleValue` rounds the ratio to 16 significant decimal digits
(`MathContext.DECIMAL64`) and converts that decimal; clotran divides
the two parts as IEEE doubles, which is the correctly rounded quotient
for parts up to 2^53 -- what a Fortran program computing n/d gets.
James, 2026-10-01: keep Fortran's conventions. The two differ by at
most a unit in the last place; scripts/fuzz allows exactly that when a
ratio is in the form.

**Removal**: none. James, 2026-10-01: "Definitely keep the Fortran
version, it is more accurate" -- the IEEE quotient is the correctly
rounded double, the 16-digit detour is not.

## 71. `count`, `compare` and `hash` answer clotran's one integer

In clj, `(class (count [1]))`, `(class (compare 1 2))` and `(class
(hash 1))` are `Integer`, the host's boxed 32-bit int; everything else
integral is a `Long`. clotran answers its 64-bit integer
(`clotran.host.int8`) for these. `(int x)` itself is an int
(`clotran.host.int4`), as an int array's element is, interpreted and
compiled. It is seen where the class
is: a protocol extended to longs dispatches on `(count xs)` here and
finds no method in clj, and `(satisfies? P (count xs))` is true here
and false there. ClojureScript answers a JavaScript number for both --
the type is the host's, not the language's. James, 2026-10-01: keep
Fortran's conventions.

**Removal**: none intended; a 32-bit integer kind would have to exist
first, and arithmetic on it widen as Numbers does.

## 72. A ratio less the smallest long is exact

In clj, `(- -7/2 Long/MIN_VALUE)` throws "long overflow", as does
`(- 1/2 Long/MIN_VALUE)`, though the answer -- `18446744073709551609/2`
-- is a ratio, nowhere near a long. The throw is how the host computes
it: `Numbers.minus` is `x + (-y)`, and negating the smallest long
overflows before the ratio arithmetic starts (`-'`, which negates
with promotion, answers the ratio). `-`'s docstring promises a throw
when longs overflow; this result is not a long, so the throw is clj's
host, not the language, and ClojureScript has no ratios to say
otherwise. clotran subtracts exactly. Two longs still throw, as the
docstring says: `(- 0 Long/MIN_VALUE)` overflows in both. Found by
`scripts/fuzz --fns`.

The same negation reaches two BOXED longs: in clj, `(- x y)` with y
the smallest long overflows whenever the longs arrive boxed, though
`(- -5 Long/MIN_VALUE)` is 9223372036854775803 -- which is what clj
answers when its compiler sees primitive longs. clotran answers the
difference either way, overflowing only when it does not fit, as clj's
primitive path does. A BigInt less the smallest long shows the same
negation without the throw: clj's `(unchecked-subtract 123456789012345678901234567890N
Long/MIN_VALUE)` wraps the negation, so it adds the smallest long and
answers the BigInt less 2^63 -- 2^64 short of the exact difference, the
BigInt plus 2^63, which clotran answers (`scripts/fuzz-num`). A ratio or
BigDecimal less the smallest long does the same: clj's `(unchecked-subtract
1.5M -9223372036854775808)` is -9223372036854775806.5M, clotran's
9223372036854775809.5M. A double does not differ, its sum rounding both
ways to 9.223372036854776E18. scripts/fuzz-num does not generate the three.

**Removal**: none intended -- it would mean overflowing on purpose
where the exact answer is at hand.

## 73. A loop or try in an expression adds no frame

In clj, `(let [r (loop ...)] ...)` and `(let [r (try ...)] ...)` show
an extra `ns/outer/fn` frame in a stack trace. The compiler wraps a
loop, let or try that sits in expression position (not a return or a
statement) as `((fn* [] form))` and calls it, so the trace shows the
call (clj's compiler: the try, let and loop parsers each analyse
`((fn* [] form))` in the form's place when the context is an
expression). That is how clj's bytecode compiler gets an empty operand
stack, not something the language says. clotran evaluates the form in
place, so a trace shows only the frames the program wrote.
`scripts/fuzz-frames` removes these frames from clj's chain before it
compares.

**Removal**: none intended -- the frame is not the program's.

## 74. A hash map's nil key is walked where its hash puts it

**Stays through 1.0 (decided 2026-10-10, PLAN step 35):** the removal
changes the trie and model/hashseq.lisp's theorem for the order of one
key; equality, hashing and lookup already agree.

clj keeps a hash map's nil key out of the trie (`PersistentHashMap`'s
`hasNull`), and its seq puts that entry first:
`(seq (assoc (zipmap (range 10) (range 10)) nil :n))` starts `[nil :n]`.
clotran stores nil in the trie with the rest, so the entry comes where
its hash places it, beside 0, whose hash is the same. Hash order is not
part of the language, and every other key is walked in clj's order
because the hashes are the same; only nil is placed differently. Sets
too. Equality, hashing and lookup are not affected (found by
`scripts/fuzz-coll`, which leaves nil out of the hashed kinds' keys so
the order of everything else stays checked).

**Removal**: keep nil out of the trie as clj does, with the seq putting
its entry first. The cursor's walk and model/hashseq.lisp's theorem
change with it.

## 75. A UUID's text is the canonical one

clj's `#uuid` and `parse-uuid` hand the string to its host's
`UUID.fromString`, which takes any five dash-separated groups of up to
sixteen hex digits and pads them: `#uuid "1-2-3-4-5"` reads as
`#uuid "00000001-0002-0003-0004-000000000005"`, and a group one digit
short reads padded. clotran's `UUID/fromString` (`clotran.uuid`) takes
only the canonical 8-4-4-4-12 form and refuses the rest with "Invalid
UUID string", where clj refuses only a string with the wrong number of
groups or one over 36 characters ("UUID string too large").
ClojureScript's compile-time `#uuid` is the same host call
(`cljs.tagged_literals/read-uuid`), and its runtime `uuid` checks
nothing at all: the leniency is the host's, not the language's.
`scripts/fuzz-read` does not compare a text whose `#uuid` either side
refuses.

**Removal**: write the host's padding rules into `clotran.uuid`, if a
program is found that relies on them.

## 76. min and max order 0.0 and -0.0 by position, always

clj's `min` and `max` are `Numbers.min/max`, overloaded by the
arguments' static types. The boxed overload (any value that came
through a fn, a collection or an un-hinted local) is `NaN` first, then
`x < y ? x : y` (`max`: `x > y ? x : y`), so a tie answers `y`:
`(min -0.0 0.0)` is `0.0`. When both arguments are statically
doubles (two double literals, or `^double` locals), the compiler picks
the primitive overload, which is the host's `Math.min`. That orders
`-0.0` below `0.0`, so the same call written with literals answers
`-0.0`. clotran's `min` and `max` are one builtin with no static types,
and always answer as the boxed overload does. ClojureScript writes
exactly that in Clojure (`cljs.core/min`: `NaN?`, then `<`), so the
boxed path is the language and the primitive ordering is the host.
They differ only on a tie between `0.0` and `-0.0`, both statically
doubles.

**Removal**: give the compiled mode's `^double` arithmetic its own
`min`/`max` that orders signed zeros, if a program is found that
relies on the difference.

## 77. The host's abs of a long is the long's, reflection or not

In clj, `(Math/abs x)` with x a boxed long the compiler cannot type is
resolved by reflection at run time, and the reflector accepts a Long for
an `int` parameter as readily as for a `long` one: it calls `abs(int)`,
narrowing first. `(let [x (identity -4611686018427387904)] (Math/abs x))`
answers 0 -- the low 32 bits -- where `(Math/abs (long x))`, typed when it
compiles, answers 4611686018427387904. clotran's `clotran.host.math/abs`
has one integer overload and answers the latter either way, as Clojure's
own `abs` does on both. Found by `scripts/fuzz`; its host `abs` is now
given a `(long ...)`, so clj compiles the long overload and the check
tests what abs means rather than which overload reflection picks.
ClojureScript has no overloads to pick between.

**Removal**: none intended -- it would mean narrowing a long on purpose.

## 78. A future after shutdown-agents still runs

In clj, `future` submits to the agents' solo executor, so after
`(shutdown-agents)` a `future` is rejected with an exception from the
executor; a `send` after it is accepted and its action never runs. In
clotran a future is a thread of its own (tasks.inc, PLAN step 14f) and
shutdown-agents (PLAN step 24) ends the agent pool's workers and stops
sends from starting work, as clj does, but leaves futures alone: a
`future` after it runs. Removing it would mean refusing futures after
shutdown, which nothing we have wants; ClojureScript has neither
agents nor shutdown-agents, so this is the host's to decide.

## 79. The names clj imports into every namespace are not names here

clj gives every namespace its host's own base classes unimported:
`(Math/abs -3)` is 3 in a fresh namespace, `(StringBuilder. "ab")` builds
one, `String` is a class. Those are the host showing through, and
clotran's host is Fortran: its classes are `clotran.host.math`,
`clotran.host.string_builder`, `clotran.host.string`, and a program
writes them so (or imports them). `(Math/abs -3)` here is "No such
namespace: Math" when analysed, `(StringBuilder. "ab")` "Unable to
resolve classname: StringBuilder", and `` `String `` reads as `user/String` (a name no namespace maps to a class). `Object` too: a deftype or reify implementing it writes `clotran.host.value`, as the derived macros do, and `(reify Object ...)` is ClassNotFoundException: Object (since 2026-10-11, when unknown interfaces began to be refused). upstream/class-names.edn's
`:implicit` lists clj's set, for the derive to rename in the vendored
sources; the runtime never sees it. Measured 2026-10-11, when seeding
those names into every namespace was tried and taken out: it was the
host emulation clotran does not do, and `upstream/check-names` said so.

**Removal**: none intended. A package may import what it likes under
its own names; the root language names its own host.

## 80. An input stream's `skip` stops at the end, a file's as an array's

clj's `(io/input-stream f)` over a file is a `BufferedInputStream` around
a `FileInputStream`, and its `skip` answers what that layering does:
before the first read, or once the buffer is empty, the file's own
`skip`, which may go past the end and answers the whole count -- `(.skip
i 5)` on a 4-byte file is 5, and `(.skip i 1)` at the end is 1; after a
read has filled the buffer, at most what is buffered. Over a byte array
it is at most what is left. clotran's input stream is one thing whatever
it reads: `skip` answers at most what is left, 0 at the end, as clj's
does over an array. Reading and `available` agree throughout; only the
count `skip` answers past the end differs.

**Removal**: none intended: it is clj's host's buffering, not the
language (no-clj-emulation). `scripts/fuzz-bytes` exercises `skip` over
an array's stream, where the two agree.

## 81. `.hashCode` of a core value is not a member

clj's host gives every object a `hashCode`, its own 32-bit hash beside
the language's `hash` (hasheq): `(.hashCode {:a 1})` is 1013910568,
`(.hashCode "ab")` 3105. clotran has the one hash, `hash`, which is
clj's hasheq bit for bit (DEVIATIONS 15); `.hashCode` on a map, vector,
string, keyword or number is "No matching method hashCode", and on a
record, whose generated method calls `APersistentMap/mapHash`, "no such
member". A deftype or reify that defines `hashCode` itself has it, and
it is that type's `hash` when it defines no `hasheq` (DEVIATIONS 60).
ClojureScript has no `hashCode` either; it is the host's, not the
language's (no-clj-emulation).

**Removal**: none intended. Writing clj's host's string, number and
collection hashCode formulas into this host would emulate that host for
a number no Clojure function asks for.
