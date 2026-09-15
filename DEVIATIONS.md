# Deviations from Clojure

Every place clotran does something real Clojure does not, why, and what it
would take to remove it. A deviation with no entry here is a bug.

**Reference**: `~/jborden/clojure` -- a clone of `clojure/clojure` at
`07adae6`. Paths below are relative to it. Cite the file and the method;
do not cite memory. That is the whole point of having the clone.

Categories:

- **temporary** -- a scaffold. Bootstrapping is incomplete; it goes away.
- **host** -- forced by Fortran. Cannot go away, but must be invisible.
- **open** -- we do not yet know which of the above it is.

| # | What | Kind | Where |
|---|------|------|-------|
| 1 | Load reads the whole file, then evaluates | temporary | `src/f/gc_main.f90` |
| 2 | Load continues past a failing form | temporary | `src/f/gc_main.f90` |
| 3 | `host.clj` preloaded before `core.clj` | temporary | `src/clj/host.clj` |
| 4 | Symbols fall back to `clojure.core` instead of being referred | temporary | `src/f/GCEval.f90` |
| 5 | `.` reaches a fixed table of host members, not arbitrary classes | host | `src/f/GCEval.f90` |

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
`*data-readers*`. core.clj does not currently hit those cases in the 544
forms that load, which is the only reason it has not bitten yet.

**Removal**: make the reader streaming over a cursor so a form can be read,
evaluated, and the next read begun. `gcr_read_all` already walks a cursor
internally; it needs to be exposed one form at a time.

## 2. Load reports a failing form and continues

Same loop. Clojure has no per-form `try`: the only `catch` in `load` is for
`LispReader.ReaderException`, and it exists to attach line/column and
rethrow. An exception ends the load.

We continue and print `N of M forms loaded`. That number is the current
measure of bootstrap progress, and stopping at form one would hide it.

**Removal**: when core.clj loads clean, delete the per-form branch and let
the first error abort, as Clojure does.

## 3. `host.clj` is loaded before `core.clj`

Clojure loads nothing before `clojure/core.clj`; its bootstrap is Java
(`RT.doInit`). Ours is partly Clojure, in `src/clj/host.clj`.

**Removal**: as natives replace it, `host.clj` shrinks. It is already down
to type predicates over `clotran-type` plus three scaffolding macros. When
`defn`/`fn`/`let` come from core.clj itself, the file goes.

## 4. Symbol resolution falls back to `clojure.core`

`resolve_var` tries the current namespace, then `clojure.core`. Clojure
has no such rule: a namespace sees `clojure.core` because `(ns ...)`
calls `refer-clojure`, which copies the mappings in. The difference
shows wherever referral is selective -- `(refer-clojure :exclude [map])`
cannot be honoured by a rule with no record of what was referred.

**Removal**: give `OBJ_NS` a refers map and implement `refer`.

## 5. `.` reaches a fixed table of host members

`clojure.lang.RT`, `clojure.lang.PersistentList` and a handful of
instance members, listed in `static_member` and `instance_member`.
Clojure reaches any Java class by reflection.

This one is **host**, not temporary: there is no Fortran reflection to
reach, and the classes core.clj names do not exist here. What the table
holds is clotran's own primitives under the host's names -- `RT.more` is
what we already mean by `rest` -- so the entries are bindings, not
adapters. It grows as core.clj asks for more.

---

## Not deviations (checked, and matching)

- **A native bootstrap `ns` macro, replaced by core.clj's own.** `RT.doInit`
  interns `bootNamespace` -- find-or-create plus set-current, nothing else --
  as a macro Var, then `load("clojure/core")`; core.clj's `ns` (its line
  5976) redefines it. `in-ns` is interned the same way but is *not* a macro,
  so its argument evaluates. We do exactly this, in `GCEval.f90`.
- **The empty list is a singleton.** `PersistentList.EMPTY`.
- **`rest` returns a seq, never nil.** `next` is the one that returns nil.
- **A Var is mutated on redefinition, not replaced.** That is what makes
  redefining a function at the REPL visible to existing closures.
