# Vendored Clojure source

Every `.clj` file here is Rich Hickey's, unmodified, from
`github.com/clojure/clojure` at commit `d4bb93f0` -- the `clojure-1.12.0`
release tag, the version the `clj` on this machine runs.

Until 2026-09-29 these came from master at `71b4623d` (1.13 interim),
whose core.clj carries experimental map-destructuring directives
(`:select`, `:excess`, `:all`, `:keys!`, marked WIP upstream) that no
release has. Running an unreleased core against a 1.12 oracle meant the
two disagreed on `*clojure-version*` and on anything the interim
branch changed, so everything moved back to the release: this tree, the
test tree, the spec jars, and the clone.

Do not edit them. If clotran cannot load one, that is clotran's bug --
the whole point of the project is that these files run as written.

The reference clone at `~/jborden/clojure` is checked out at the SAME
commit, and DEVIATIONS.md cites its Java. Keep the two in step. Reading
the Java of one version while running the core.clj of another is the same
mistake as citing memory, and it nearly bit us: the clone was first taken
at master `07adae6`, three hunks newer than what we run (`tap->`, a
rewritten `select-keys`, one `BigDecimal/valueOf` cast). Re-vendoring to
match the clone was the wrong direction -- our tests are written against
these files -- so the clone moved instead.

To confirm they still match:

    diff -r ~/jborden/clojure/src/clj/clojure src/clj/clojure

## What is deliberately NOT vendored

core.clj ends by loading five sibling libs. None of them is portable, and
the reason is not effort, it is that they are the JVM:

| file | needs |
|------|-------|
| `core_proxy.clj` | `clojure.asm`, `ClassWriter`, `DynamicClassLoader` -- emits JVM bytecode at runtime |
| `genclass.clj`   | the same, for named AOT classes |
| `gvec.clj`       | `java.util.Collection`, `java.util.concurrent` |
| `instant.clj`    | `java.sql.Timestamp`, `java.text.SimpleDateFormat` |

`proxy` and `gen-class` generate classes; there is nothing for them to
generate here.

Those four, plus `java/`, are the only files from upstream's `src/clj`
that are NOT here. Everything else is, whether or not it currently
loads -- `set`, `data`, `edn`, `datafy`, `walk`, `uuid` and `template`
already do. `uuid.clj` is here and runs VERBATIM (2026-09-28): its
`java.util.UUID` is a record clotran.rt defines under that name, behind
`UUID/fromString` and `UUID/randomUUID`.

Skip them BY NAME, never by absence. core.clj says `(load
"core_proxy")` and clotran skips that by name. An earlier evaluator
relied on the file simply not being there, and vendoring it turned a
silent skip into a real load that broke `defprotocol`,
`extend-protocol`, `satisfies?` and `into` -- a red crosscheck from
adding a file. Adding a file can be a breaking change.

That boundary is also the useful one: everything a Clojure program
normally reaches for -- the seq library, destructuring, the macros -- is
in core.clj itself, above that line.

## The one file that is not upstream's

`version.properties` is ours. Upstream keeps it at
`src/resources/clojure/version.properties` and it reads:

    version=${version}

-- a Maven template, filled in at build time from `pom.xml`, which at
`clojure-1.12.0` says `1.12.0`. There is no Maven here, so the
filled-in value is committed instead:

    version=1.12.0

core.clj's form 656 reads it off the classloader and parses it with
`re-matches` into `*clojure-version*`. Bump it whenever the vendored
core.clj is re-vendored from a different tag, or `(clojure-version)`
starts lying about what is actually running.

Note this makes `diff -r ~/jborden/clojure/src/clj/clojure src/clj/clojure`
report it as an extra file. The spec trees below are the other expected
extras.

## clojure.spec.alpha and clojure.core.specs.alpha

`spec/alpha.clj`, `spec/gen/alpha.clj`, `spec/test/alpha.clj` and
`core/specs/alpha.clj` are not in the clojure/clojure repository; they
are separate libraries the JVM loads from Maven. They are here verbatim
from the jars the pinned clone's own `pom.xml` names:

| library | version | jar sha1 |
|---|---|---|
| org.clojure/spec.alpha | 0.5.238 | `4eb5dea521c4e6e1f68c2c47517f14a922003e60` |
| org.clojure/core.specs.alpha | 0.4.74 | `d56a8d4c666ff8140e6d0a62d41263134be39254` |

The Compiler loads the first two (`spec/alpha`, `core/specs/alpha`) at
the first macro expansion after core.clj (`Compiler.ensureMacroCheck`),
and from then on `clojure.spec.alpha/macroexpand-check` runs before
every macro call; clotran does the same (`check_specs` in Eval.f90,
switched on by main.f90 after the first file loads, off under
`CLOTRAN_SPEC_SKIP_MACROS` as under `clojure.spec.skip-macros`).
`spec/gen/alpha.clj` loads because spec requires it; its generators
reach for test.check on first use, which is not here. `spec/test/alpha.clj`
is vendored for completeness and loads on `require`.

## Vendored, unmodified, and not loaded

`core_print.clj` and `data.clj` are here verbatim for the diff, but
clotran loads `src/clj/clotran/core_print.cljf` and `data.cljf` in their
place -- the same files with the `java.util` dispatch keys taken out
(DEVIATIONS.md 40). ClojureScript ships its own versions of both for the
same reason.
