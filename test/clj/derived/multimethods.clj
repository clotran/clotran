;; DERIVED from upstream/clojure/test/clojure/test_clojure/multimethods.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.multimethods (:use clojure.test [clojure.test-helper :only (with-var-roots)]) (:require [clojure.set :as set]))

(defmacro for-all
  [& args]
  `(dorun (for ~@args)))

(defn transitive-closure
  "Return all objects reachable by calling f starting with o,
   not including o itself. f should return a collection."
  [o f]
  (loop [results #{}
         more #{o}]
    (let [new-objects (set/difference more results)]
      (if (seq new-objects)
        (recur (set/union results more) (reduce into #{} (map f new-objects)))
        (disj results o)))))

(def family
  (reduce #(apply derive (cons %1 %2)) (make-hierarchy)
          [[::parent-1 ::ancestor-1]
           [::parent-1 ::ancestor-2]
           [::parent-2 ::ancestor-2]
           [::child ::parent-2]
           [::child ::parent-1]]))

;; multimethods.clj:98 [language]
(deftest cycles-are-forbidden
  (testing "a tag cannot be its own parent"
    (is (thrown-with-msg? clotran.host.throwable #"\(not= tag parent\)"
          (derive family ::child ::child))))
  (testing "a tag cannot be its own ancestor"
    (is (thrown-with-msg? clotran.host.throwable #"Cyclic derivation: :clojure.test-clojure.multimethods/child has :clojure.test-clojure.multimethods/ancestor-1 as ancestor"
          (derive family ::ancestor-1 ::child)))))
