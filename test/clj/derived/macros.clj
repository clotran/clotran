;; DERIVED from upstream/clojure/test/clojure/test_clojure/macros.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.macros (:use clojure.test))

(defmacro c
  [arg]
  (if (= 'b (first arg))
    :foo
    :bar))

(def constantly-nil (constantly nil))

;; macros.clj:28 [language]
(deftest ->test
  (let [a 2, b identity]
    (is (= (-> a b c)
           (c (b a))))))

;; macros.clj:33 [language]
(deftest ->>test
  (let [a 2, b identity]
    (is (= (->> a b c)
           (c (b a))))))

;; macros.clj:38 [language]
(deftest ->metadata-test
  (testing "a trivial form"
    (is (= {:hardy :har :har :-D}
           (meta (macroexpand-1 (list `-> (with-meta
                                            'quoted-symbol
                                            {:hardy :har :har :-D})))))))
  (testing "a nontrivial form"
    (let [a (with-meta 'a {:foo :bar})
          b (with-meta '(b c d) {:bar :baz})
          e (with-meta 'e {:baz :quux})
          expanded (macroexpand-1 (list `-> a b e))]
      (is (= expanded '(e (b a c d))))
      (is (= {:baz :quux} (meta (first expanded))))
      (is (= {:bar :baz} (meta (second expanded))))
      (is (= {:foo :bar} (meta (second (second expanded))))))))

;; macros.clj:55 [language]
(deftest ->>metadata-test
  (testing "a trivial form"
    (is (= {:hardy :har :har :-D}
           (meta (macroexpand-1 (list `->> (with-meta
                                             'quoted-symbol
                                             {:hardy :har :har :-D})))))))
  (testing "a non-trivial form"
    (let [a (with-meta 'a {:foo :bar})
          b (with-meta '(b c d) {:bar :baz})
          e (with-meta 'e {:baz :quux})
          expanded (macroexpand-1 (list `->> a b e))]
      (is (= expanded '(e (b c d a))))
      (is (= {:baz :quux} (meta (first expanded))))
      (is (= {:bar :baz} (meta (second expanded))))
      (is (= {:foo :bar} (meta (last (second expanded))))))))

;; macros.clj:73 [language]
(deftest some->test
  (is (nil? (some-> nil)))
  (is (= 0 (some-> 0)))
  (is (= -1 (some-> 1 (- 2))))
  (is (nil? (some-> 1 constantly-nil (- 2)))))

;; macros.clj:79 [language]
(deftest some->>test
  (is (nil? (some->> nil)))
  (is (= 0 (some->> 0)))
  (is (= 1 (some->> 1 (- 2))))
  (is (nil? (some->> 1 constantly-nil (- 2)))))

;; macros.clj:85 [language]
(deftest cond->test
  (is (= 0 (cond-> 0)))
  (is (= -1 (cond-> 0 true inc true (- 2))))
  (is (= 0 (cond-> 0 false inc)))
  (is (= -1 (cond-> 1 true (- 2) false inc))))

;; macros.clj:91 [language]
(deftest cond->>test
  (is (= 0 (cond->> 0)))
  (is (= 1 (cond->> 0 true inc true (- 2))))
  (is (= 0 (cond->> 0 false inc)))
  (is (= 1 (cond->> 1 true (- 2) false inc))))

;; macros.clj:97 [language]
(deftest as->test
  (is (= 0 (as-> 0 x)))
  (is (= 1 (as-> 0 x (inc x))))
  (is (= 2 (as-> [0 1] x
             (map inc x)
             (reverse x)
             (first x)))))

;; macros.clj:105 [language]
(deftest threading-loop-recur
  (is (nil? (loop []
              (as-> 0 x
                (when-not (zero? x)
                  (recur))))))
  (is (nil? (loop [x nil] (some-> x recur))))
  (is (nil? (loop [x nil] (some->> x recur))))
  (is (= 0 (loop [x 0] (cond-> x false recur))))
  (is (= 0 (loop [x 0] (cond->> x false recur)))))
