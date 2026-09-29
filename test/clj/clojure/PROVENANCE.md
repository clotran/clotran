# Vendored Clojure test suite

`test_clojure/` and `test_helper.clj` are Clojure's own tests, unmodified,
from `github.com/clojure/clojure` at commit `d4bb93f0` (`clojure-1.12.0`) --
the SAME release as the vendored core.clj (see `src/clj/clojure/PROVENANCE.md`).

Do not edit them. They are the conformance measure: `test/f/*_test.f90`
covers the Fortran host, which upstream cannot test, and everything about
the LANGUAGE is checked here by Clojure's own assertions rather than by
ours. A test that fails is clotran's bug, not the test's.

To confirm they still match:

    diff -r ~/jborden/clojure/test/clojure test/clj/clojure

`scripts/run-clojure-tests` drives them, one namespace per run so a hard
failure in one file cannot hide the others.

Many will not pass, and several cannot: the suite covers `proxy`,
`genclass`, annotations, `java.*` interop and AOT compilation, none of
which exist here. They are vendored anyway. Knowing which of the 67 fail
and why is the point; choosing in advance which to grade ourselves on is
how a number becomes flattering instead of true.
