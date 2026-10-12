# src/clj

Clojure source loaded at startup.

- `clojure/` -- Rich Hickey's, vendored unmodified from
  `clojure/clojure` at `clojure-1.12.6`. See `clojure/PROVENANCE.md`. Never
  edited; if clotran cannot load one of these files, that is clotran's
  bug.
- `clotran/` -- clotran's own namespaces (`.cljf`), loaded when first
  named. Nothing of ours loads before core.clj (DEVIATIONS.md 2).

Layout mirrors upstream's `src/clj/clojure/...` (namespace segments as
directories) because that is the classpath convention `load` and
`require` resolve against.
