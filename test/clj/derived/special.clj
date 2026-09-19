;; DERIVED from test/clj/clojure/test_clojure/special.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.special (:use clojure.test) (:require [clojure.test-helper :refer [should-not-reflect]]))

(require '[clojure.string :as s])

;; special.clj:26 [language]
(deftest multiple-keys-in-destructuring
  (let [foo (fn [& {:keys [x]}] x)
        bar (fn [& options] (apply foo :x :b options))]
    (is (= (bar) :b))
    (is (= (bar :x :a) :a))))

;; special.clj:32 [language]
(deftest empty-list-with-:as-destructuring
  (let [{:as x} '()]
    (is (= {} x))))

;; special.clj:36 [language]
(deftest keywords-in-destructuring
  (let [m {:a 1 :b 2}]
    (let [{:keys [:a :b]} m]
      (is (= [1 2] [a b])))
    (let [{:keys [:a :b :c] :or {c 3}} m]
      (is (= [1 2 3] [a b c])))))

;; special.clj:43 [language]
(deftest namespaced-keywords-in-destructuring
  (let [m {:a/b 1 :c/d 2}]
    (let [{:keys [:a/b :c/d]} m]
      (is (= [1 2] [b d])))
    (let [{:keys [:a/b :c/d :e/f] :or {f 3}} m]
      (is (= [1 2 3] [b d f])))))

;; special.clj:50 [language]
(deftest namespaced-keys-in-destructuring
  (let [m {:a/b 1 :c/d 2}]
    (let [{:keys [a/b c/d]} m]
      (is (= [1 2] [b d])))
    (let [{:keys [a/b c/d e/f] :or {f 3}} m]
      (is (= [1 2 3] [b d f])))))

;; special.clj:57 [language]
(deftest namespaced-syms-in-destructuring
  (let [{:syms [a/b c/d e/f] :or {f 3}} {'a/b 1 'c/d 2}]
    (is (= [1 2 3] [b d f]))))

;; special.clj:61 [language]
(deftest namespaced-keys-syntax
  (let [{:a/keys [b c d] :or {d 3}} {:a/b 1 :a/c 2}]
    (is (= [1 2 3] [b c d]))))

;; special.clj:65 [language]
(deftest namespaced-syms-syntax
  (let [{:a/syms [b c d] :or {d 3}} {'a/b 1 'a/c 2}]
    (is (= [1 2 3] [b c d]))))

;; special.clj:70 [language]
(deftest binding-types-not-allowed
  (doseq [directive [:a1/keys :a1/syms :a1/keys! :a1/syms!]
          binding ['b/c :c :b1/c]]
    (let [val {(if (= (name directive) "keys")
                 (keyword (namespace directive) "c")
                 (symbol (namespace directive) "c")) 1}]
      (is (thrown-with-cause-msg? Exception #"did not conform to spec"
            (eval `(let [{~directive ~(vector binding)} ~val] ~'c)))))))

;; special.clj:79 [language]
(deftest keywords-not-allowed-in-let-bindings
  (is (thrown-with-cause-msg? Exception #"did not conform to spec"
                        (eval '(let [:a 1] a))))
  (is (thrown-with-cause-msg? Exception #"did not conform to spec"
                        (eval '(let [:a/b 1] b))))
  (is (thrown-with-cause-msg? Exception #"did not conform to spec"
                        (eval '(let [[:a] [1]] a))))
  (is (thrown-with-cause-msg? Exception #"did not conform to spec"
                        (eval '(let [[:a/b] [1]] b)))))

;; special.clj:89 [language]
(deftest namespaced-syms-only-allowed-in-map-destructuring
  (is (thrown-with-cause-msg? Exception #"did not conform to spec"
                        (eval '(let [a/x 1, [y] [1]] x))))
  (is (thrown-with-cause-msg? Exception #"did not conform to spec"
                        (eval '(let [[a/x] [1]] x)))))

;; special.clj:95 [language]
(deftest or-doesnt-create-bindings
  (is (thrown-with-cause-msg? Exception #"Unable to resolve symbol: b"
                        (eval '(let [{:keys [a] :or {b 2}} {:a 1}] [a b])))))

;; special.clj:99 [language]
(deftest amp-not-allowed-as-let-or-loop*-binding-name
  (is (thrown? Exception (eval '(let [& 42] &))))
  (is (thrown? Exception (eval '(let* [& 42] &))))
  (is (thrown? Exception (eval '(loop* [& 42] &)))))

;; special.clj:105 [language]
(deftest resolve-keyword-ns-alias-in-destructuring
  (let [{:keys [::s/x ::s/y ::s/z] :or {z 3}} {:clojure.string/x 1 :clojure.string/y 2}]
    (is (= [1 2 3] [x y z]))))
