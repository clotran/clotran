;; DERIVED from test/clj/clojure/test_clojure/errors.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.errors (:use clojure.test))

(defn f0 [] 0)

(defn f1 [a] a)

(defn f2:+><->!#%&*|b [x] x)

(defmacro m0 [] `(identity 0))

(defmacro m1 [a] `(inc ~a))

(defmacro m2 [] (assoc))

;; errors.clj:69 [language]
(deftest extract-ex-data
  (try
   (throw (ex-info "example error" {:foo 1}))
   (catch Throwable t
     (is (= {:foo 1} (ex-data t)))))
  (is (nil? (ex-data (RuntimeException. "example non ex-data")))))

;; errors.clj:110 [language]
(deftest ex-info-allows-nil-data
  (is (= {} (ex-data (ex-info "message" nil))))
  (is (= {} (ex-data (ex-info "message" nil (Throwable. "cause"))))))
