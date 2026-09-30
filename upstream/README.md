# upstream

Clojure's own source and test suite, vendored unmodified
(`clojure/src/clj/clojure/PROVENANCE.md` and
`clojure/test/clojure/PROVENANCE.md` say from where and at what
release). clotran does not load these copies.

`derive` writes them into `src/clj/clojure` and `test/clj/clojure`,
each class in clotran's name:

- `class-names.edn` -- what clotran calls each class, namespace and
  constructor the upstream sources write.
- `names.clj` -- the renaming: a file is lexed, so a class in code is
  resolved by that file's imports and a name in a string or comment is
  renamed as text. `scripts/oracle` uses it in both directions, to send
  its cases to clj and to read clj's answers.

This directory is the one place in clotran that names the JVM's
classes. To take a new upstream release: replace the copies, run
`derive`, and add to `class-names.edn` whatever it names that is new.
