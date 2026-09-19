;; DERIVED from test/clj/clojure/test_clojure/delays.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.delays (:use clojure.test))



;; delays.clj:5 [language]
(deftest calls-once
  (let [a (atom 0)
        d (delay (swap! a inc))]
    (is (= 0 @a))
    (is (= 1 @d))
    (is (= 1 @d))
    (is (= 1 @a))))

;; delays.clj:34 [language]
(deftest saves-exceptions
  (let [f #(do (throw (Exception. "broken"))
               1)
        d (delay (f))
        try-call #(try
                    @d
                    (catch Exception e e))
        first-result (try-call)]
    (is (instance? Exception first-result))
    (is (identical? first-result (try-call)))))
