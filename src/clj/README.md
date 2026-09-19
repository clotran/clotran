# src/clj

Clojure source loaded at startup.

- `clojure/` -- Rich Hickey's, vendored unmodified from
  `clojure/clojure` at `71b4623d`. See `clojure/PROVENANCE.md`. Never
  edited; if clotran cannot load one of these files, that is clotran's
  bug.
- `host.clj` -- the one file of ours. Loaded BEFORE core.clj, it holds
  only what core.clj cannot supply because it depends on how this host
  represents values: the type predicates over `clotran-type`, and the
  three scaffolding macros needed to write them. DEVIATIONS.md 2 says
  when it goes.

Layout mirrors upstream's `src/clj/clojure/...` (namespace segments as
directories) because that is the classpath convention `load` and
`require` resolve against.
