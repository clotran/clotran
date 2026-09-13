# src/clj

Clotran-only Clojure-language source: code that has no reason to be
portable (nothing here needs a reader conditional because nothing
else reads it) or that specifically depends on something only this
host provides. Most language-level code should live in `src/cljc`
instead by default -- only put something here when it's genuinely
clotran-specific.
