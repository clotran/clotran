;; DERIVED from upstream/clojure/test/clojure/test_clojure/errors.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.errors (:use clojure.test))

(defn f0 [] 0)

(defn f1 [a] a)

(defn f2:+><->!#%&*|b [x] x)

(defmacro m0 [] `(identity 0))

(defmacro m1 [a] `(inc ~a))

(defmacro m2 [] (assoc))

;; errors.clj:52 [language]
(deftest compile-error-examples
  (are [form errtype re] (thrown-with-cause-msg? errtype re (eval form))
       '(clotran.host.int8/parseLong) clotran.host.exception #"No matching method.*taking 0 args"
       '(clotran.host.int8/parseLong :a :b :c) clotran.host.exception #"No matching method.*taking 3 args")
  (are [form errtype re] (thrown-with-msg? errtype re (eval form))
       '(.jump "foo" 1) clotran.host.exception #"No matching method.*taking 1 arg"))

;; errors.clj:69 [language]
(deftest extract-ex-data
  (try
   (throw (ex-info "example error" {:foo 1}))
   (catch clotran.host.throwable t
     (is (= {:foo 1} (ex-data t)))))
  (is (nil? (ex-data (clotran.host.runtime_exception. "example non ex-data")))))

;; errors.clj:110 [language]
(deftest ex-info-allows-nil-data
  (is (= {} (ex-data (ex-info "message" nil))))
  (is (= {} (ex-data (ex-info "message" nil (clotran.host.throwable. "cause"))))))
