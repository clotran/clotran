;; DERIVED from test/clj/clojure/test_clojure/atoms.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.atoms (:use clojure.test))



;; atoms.clj:21 [language]
(deftest swap-vals-returns-old-value
  (let [a (atom 0)]
    (is (= [0 1] (swap-vals! a inc)))
    (is (= [1 2] (swap-vals! a inc)))
    (is (= 2 @a))))

;; atoms.clj:27 [language]
(deftest deref-swap-arities
  (binding [*warn-on-reflection* true]
    (let [a (atom 0)]
      (is (= [0 1] (swap-vals! a + 1)))
      (is (= [1 3] (swap-vals! a + 1 1)))
      (is (= [3 6] (swap-vals! a + 1 1 1)))
      (is (= [6 10] (swap-vals! a + 1 1 1 1)))
      (is (= 10 @a)))))

;; atoms.clj:36 [language]
(deftest deref-reset-returns-old-value
  (let [a (atom 0)]
    (is (= [0 :b] (reset-vals! a :b)))
    (is (= [:b 45M] (reset-vals! a 45M)))
    (is (= 45M @a))))

;; atoms.clj:42 [language]
(deftest reset-on-deref-reset-equality
  (let [a (atom :usual-value)]
    (is (= :usual-value (reset! a (first (reset-vals! a :almost-never-seen-value)))))))
