;; DERIVED from test/clj/clojure/test_clojure/reflect.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.reflect (:use clojure.data clojure.test clojure.pprint))

(defn nodiff
  [x y]
  (let [[x-only y-only common] (diff x y)]
    (when (or x-only y-only)
      (is false (with-out-str (pprint {:x-only x-only
                                       :y-only y-only
                                       :common common}))))))

;; reflect.clj:27 [language]
(deftest field-descriptor->class-symbol-test
  (are [s d] (= s (@#'reflect/field-descriptor->class-symbol d))
       'clojure.asm.Type<><> "[[Lclojure/asm/Type;"
       'int "I"
       'java.lang.Object "Ljava.lang.Object;"))

;; reflect.clj:33 [language]
(deftest internal-name->class-symbol-test
  (are [s n] (= s (@#'reflect/internal-name->class-symbol n))
       'java.lang.Exception "java/lang/Exception"))
