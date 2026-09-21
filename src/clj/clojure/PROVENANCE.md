# Vendored Clojure source

Every `.clj` file here is Rich Hickey's, unmodified, from
`github.com/clojure/clojure` at commit `71b4623d` (master, 2026-09-07).

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
| `uuid.clj`       | `java.util.UUID` |

`proxy` and `gen-class` generate classes; there is nothing for them to
generate here.

Those five, plus `java/`, are the only files from upstream's `src/clj`
that are NOT here. Everything else is, whether or not it currently
loads -- `set`, `data`, `edn`, `datafy`, `walk`, `uuid` and `template`
already do.

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
`71b4623d` says `1.13.0-master-SNAPSHOT`. There is no Maven here, so the
filled-in value is committed instead:

    version=1.13.0-master-SNAPSHOT

core.clj's form 656 reads it off the classloader and parses it with
`re-matches` into `*clojure-version*`. Bump it whenever the vendored
core.clj is re-vendored from a different tag, or `(clojure-version)`
starts lying about what is actually running.

Note this makes `diff -r ~/jborden/clojure/src/clj/clojure src/clj/clojure`
report it as an extra file. That is the only expected difference.

## Vendored, unmodified, and not loaded

`core_print.clj` and `data.clj` are here verbatim for the diff, but
clotran loads `src/clj/clotran/core_print.cljf` and `data.cljf` in their
place -- the same files with the `java.util` dispatch keys taken out
(DEVIATIONS.md 40). ClojureScript ships its own versions of both for the
same reason.
