;; DERIVED from upstream/clojure/test/clojure/test_clojure/test_fixtures.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.test-fixtures (:use clojure.test))

(declare ^:dynamic *a* ^:dynamic *b* ^:dynamic *c* ^:dynamic *d*)

(def ^:dynamic *n* 0)

(defn fixture-a [f]
  (binding [*a* 3] (f)))

(defn fixture-b [f]
  (binding [*b* 5] (f)))

(defn fixture-c [f]
  (binding [*c* 7] (f)))

(defn fixture-d [f]
  (binding [*d* 11] (f)))

(defn inc-n-fixture [f]
  (binding [*n* (inc *n*)] (f)))

(def side-effects (atom 0))

(defn side-effecting-fixture [f]
  (swap! side-effects inc)
  (f))

(use-fixtures :once fixture-a fixture-b)

(use-fixtures :each fixture-c fixture-d inc-n-fixture side-effecting-fixture)

(use-fixtures :each fixture-c fixture-d inc-n-fixture side-effecting-fixture)

(defn should-not-trigger-fixtures [])

;; test_fixtures.clj:46 [language]
(deftest can-use-once-fixtures
  (is (= 3 *a*))
  (is (= 5 *b*)))

;; test_fixtures.clj:50 [language]
(deftest can-use-each-fixtures
  (is (= 7 *c*))
  (is (= 11 *d*)))

;; test_fixtures.clj:54 [language]
(deftest use-fixtures-replaces
  (is (= *n* 1)))

;; test_fixtures.clj:57 [language]
(deftest can-run-a-single-test-with-fixtures
  ;; We have to use a side-effecting fixture to test that the fixtures are
  ;; running, in order to distinguish fixtures run because of our call to
  ;; test-vars below from the same fixtures running prior to this test
  (let [side-effects-so-far @side-effects
        reported (atom [])]
    (binding [report (fn [m] (swap! reported conj (:type m)))]
      (test-vars [#'can-use-each-fixtures]))
    (is (= [:begin-test-var :pass :pass :end-test-var] @reported))
    (is (= (inc side-effects-so-far) @side-effects))))

;; test_fixtures.clj:70 [language]
(deftest a-var-lacking-test-meta-should-not-trigger-fixtures
  (let [side-effects-so-far @side-effects]
    (test-vars [#'should-not-trigger-fixtures])
    (is (= side-effects-so-far @side-effects))))
