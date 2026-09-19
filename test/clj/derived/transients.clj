;; DERIVED from test/clj/clojure/test_clojure/transients.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.transients (:use clojure.test))

(defn- hash-obj [hash]
  (reify Object (hashCode [this] hash)))

;; transients.clj:4 [language]
(deftest popping-off
  (testing "across a node boundary"
    (are [n] 
      (let [v (-> (range n) vec)]
        (= (subvec v 0 (- n 2)) (-> v transient pop! pop! persistent!)))
      33 (+ 32 (inc (* 32 32))) (+ 32 (inc (* 32 32 32)))))
  (testing "off the end"
    (is (thrown-with-msg? IllegalStateException #"Can't pop empty vector"
          (-> [] transient pop!))))
  (testing "copying array from a non-editable when put in tail position")
    (is (= 31 (let [pv (vec (range 34))]
                (-> pv transient pop! pop! pop! (conj! 42))
                (nth pv 31)))))

;; transients.clj:21 [language]
(deftest dissocing
  (testing "dissocing colliding keys"
    (is (= [0 {}] (let [ks (concat (range 7) [(hash-obj 42) (hash-obj 42)])
                        m (zipmap ks ks)
                        dm (persistent! (reduce dissoc! (transient m) (keys m)))]
                    [(count dm) dm])))))

;; transients.clj:28 [language]
(deftest test-disj!
  (testing "disjoin multiple items in one call"
    (is (= #{5 20} (-> #{5 10 15 20} transient (disj! 10 15) persistent!)))))

;; transients.clj:35 [language]
(deftest persistent-assoc-on-collision
  (testing "Persistent assoc on a collision node which underwent a transient dissoc"
    (let [a (reify Object (hashCode [_] 42))
          b (reify Object (hashCode [_] 42))]
      (is (= (-> #{a b} transient (disj! a) persistent! (conj a))
            (-> #{a b} transient (disj! a) persistent! (conj a)))))))

;; transients.clj:50 [concurrency]
(deftest transient-mod-ok-across-threads
  (let [v [1 2 3]
        t (transient v)
        t2 @(future (conj! t 4))
        p (persistent! t2)]
    (is (= [1 2 3 4] p))))

;; transients.clj:57 [language]
(deftest transient-lookups
  (let [tv (transient [1 2 3])]
    (is (= 1 (get tv 0)))
    (is (= :foo (get tv 4 :foo)))
    (is (= true (contains? tv 0)))
    (is (= [0 1] (find tv 0)))
    (is (= nil (find tv -1))))
  (let [ts (transient #{1 2})]
    (is (= true (contains? ts 1)))
    (is (= false (contains? ts 99)))
    (is (= 1 (get ts 1)))
    (is (= nil (get ts 99))))
  (let [tam (transient (array-map :a 1 :b 2))]
    (is (= true (contains? tam :a)))
    (is (= false (contains? tam :x)))
    (is (= 1 (get tam :a)))
    (is (= nil (get tam :x)))
    (is (= [:a 1] (find tam :a)))
    (is (= nil (find tam :x))))
  (let [thm (transient (hash-map :a 1 :b 2))]
    (is (= true (contains? thm :a)))
    (is (= false (contains? thm :x)))
    (is (= 1 (get thm :a)))
    (is (= nil (get thm :x)))
    (is (= [:a 1] (find thm :a)))
    (is (= nil (find thm :x)))))
