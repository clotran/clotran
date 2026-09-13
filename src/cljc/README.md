# src/cljc

Clotran-language source that's portable in the `.cljc` sense: written
against standard Clojure semantics, using reader conditionals
(`#?(...)`) only where a piece of code genuinely needs to branch per
host. Real Clojure uses `:clj`/`:cljs`/`:cljr`/... feature keys for
this; clotran will need its own (`:cljf`? undecided) once the reader
supports reader conditionals at all (see NOTES.md).

This is where the growing `clojure.core`-equivalent library belongs:
currently `not`/`cond` are still hardcoded as a literal string in
`Eval.f90`'s `eval_core_bootstrap` -- extracting that into a real
file here, loaded at startup, is the first thing that should land in
this directory.
