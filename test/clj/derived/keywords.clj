;; DERIVED from test/clj/clojure/test_clojure/keywords.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.keywords (:use clojure.test))



;; keywords.clj:27 [language]
(deftest arity-exceptions
  (is (thrown-with-msg? IllegalArgumentException #"Wrong number of args \(0\) passed to: :kw" (:kw)))
  (is (thrown-with-msg? IllegalArgumentException #"Wrong number of args \(20\) passed to: :foo/bar" (apply :foo/bar (range 20))))
  (is (thrown-with-msg? IllegalArgumentException #"Wrong number of args \(> 20\) passed to: :foo/bar" (apply :foo/bar (range 21))))
  (is (thrown-with-msg? IllegalArgumentException #"Wrong number of args \(> 20\) passed to: :foo/bar" (apply :foo/bar (range 22)))))
