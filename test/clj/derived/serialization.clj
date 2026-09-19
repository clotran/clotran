;; DERIVED from test/clj/clojure/test_clojure/serialization.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.serialization (:use clojure.test))

(defrecord SerializationRecord [a b c])

(defn- build-via-transient
  [coll]
  (persistent!
    (reduce conj! (transient coll) (map vec (partition 2 (range 1000))))))

;; serialization.clj:126 [language]
(deftest misc-serialization
  (are [v] (= v (-> v serialize deserialize))
    25/3
    :keyword
    ::namespaced-keyword
    'symbol))

;; serialization.clj:163 [language]
(deftest function-serialization
  (let [capture 5]
    (are [f] (= capture ((-> f serialize deserialize)))
      (constantly 5)
      (fn [] 5)
      #(do 5)
      (constantly capture)
      (fn [] capture)
      #(do capture))))
