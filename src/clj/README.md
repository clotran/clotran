# src/clj

Real Clojure source, mirroring the upstream
[clojure/clojure](https://github.com/clojure/clojure) repo's own
`src/clj/clojure/...` layout (namespace segments as directories, same
as the JVM classpath convention) -- this is the actual file `Eval.f90`
loads at startup. Edited in place with additive `#?(:cljf ...)`
reader-conditional branches wherever real Clojure's own Java interop
can't run here; the real `:clj` branch of anything already ported
never gets deleted or rewritten, so the file stays a genuine port of
the original, not a rewrite inspired by it.

A file moves to `src/cljc` once it actually has a `#?(...)` branch in
it -- that's the real Clojure convention for when a file earns the
`.cljc` extension, not before. See NOTES.md ("Importing real
clojure/core.clj") for the running log of what's ported, what's
stubbed, and why.
