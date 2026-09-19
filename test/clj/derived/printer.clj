;; DERIVED from test/clj/clojure/test_clojure/printer.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.printer (:use clojure.test [clojure.test-helper :only [platform-newlines]]) (:require [clojure.pprint :refer [pprint]]))

(def ^{:foo :anything} var-with-meta 42)

(def ^{:type :anything} var-with-type 666)

;; printer.clj:21 [language]
(deftest print-length-empty-seq
  (let [coll () val "()"]
    (is (= val (binding [*print-length* 0] (print-str coll))))
    (is (= val (binding [*print-length* 1] (print-str coll))))))

;; printer.clj:26 [language]
(deftest print-length-seq
  (let [coll (range 5)
        length-val '((0 "(...)")
                     (1 "(0 ...)")
                     (2 "(0 1 ...)")
                     (3 "(0 1 2 ...)")
                     (4 "(0 1 2 3 ...)")
                     (5 "(0 1 2 3 4)"))]
    (doseq [[length val] length-val]
      (binding [*print-length* length]
        (is (= val (print-str coll)))))))

;; printer.clj:38 [language]
(deftest print-length-empty-vec
  (let [coll [] val "[]"]
    (is (= val (binding [*print-length* 0] (print-str coll))))
    (is (= val (binding [*print-length* 1] (print-str coll))))))

;; printer.clj:43 [language]
(deftest print-length-vec
  (let [coll [0 1 2 3 4]
        length-val '((0 "[...]")
                     (1 "[0 ...]")
                     (2 "[0 1 ...]")
                     (3 "[0 1 2 ...]")
                     (4 "[0 1 2 3 ...]")
                     (5 "[0 1 2 3 4]"))]
    (doseq [[length val] length-val]
      (binding [*print-length* length]
        (is (= val (print-str coll)))))))

;; printer.clj:55 [language]
(deftest print-level-seq
  (let [coll '(0 (1 (2 (3 (4)))))
        level-val '((0 "#")
                    (1 "(0 #)")
                    (2 "(0 (1 #))")
                    (3 "(0 (1 (2 #)))")
                    (4 "(0 (1 (2 (3 #))))")
                    (5 "(0 (1 (2 (3 (4)))))"))]
    (doseq [[level val] level-val]
      (binding [*print-level* level]
        (is (= val (print-str coll)))))))

;; printer.clj:67 [language]
(deftest print-level-length-coll
  (let [coll '(if (member x y) (+ (first x) 3) (foo (a b c d "Baz")))
        level-length-val
        '((0 1 "#")
          (1 1 "(if ...)")
          (1 2 "(if # ...)")
          (1 3 "(if # # ...)")
          (1 4 "(if # # #)")
          (2 1 "(if ...)")
          (2 2 "(if (member x ...) ...)")
          (2 3 "(if (member x y) (+ # 3) ...)")
          (3 2 "(if (member x ...) ...)")
          (3 3 "(if (member x y) (+ (first x) 3) ...)")
          (3 4 "(if (member x y) (+ (first x) 3) (foo (a b c d ...)))")
          (3 5 "(if (member x y) (+ (first x) 3) (foo (a b c d Baz)))"))]
    (doseq [[level length val] level-length-val]
      (binding [*print-level* level
                *print-length* length]
        (is (= val (print-str coll)))))))

;; printer.clj:108 [language]
(deftest print-var
  (are [x s] (= s (pr-str x))
       #'pr-str  "#'clojure.core/pr-str"
       #'var-with-meta "#'clojure.test-clojure.printer/var-with-meta"
       #'var-with-type "#'clojure.test-clojure.printer/var-with-type"))
