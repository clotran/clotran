;; DERIVED from test/clj/clojure/test_clojure/data_structures.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.data-structures (:use clojure.test) (:require [clojure.string :as string]))

(defn diff [s1 s2]
  (seq (reduce disj (set s1) (set s2))))

(defn tempty? [t]
  (= (count t) 0))

(defn case-indendent-string-cmp [s1 s2]
  (compare (string/lower-case s1) (string/lower-case s2)))

(defn hash-ordered [collection]
  (-> (reduce (fn [acc e] (unchecked-add-int (unchecked-multiply-int 31 acc) (hash e)))
              1
              collection)
      (mix-collection-hash (count collection))))

(defn hash-unordered [collection]
  (-> (reduce unchecked-add-int 0 (map hash collection))
      (mix-collection-hash (count collection))))

(defrecord Rec [a b])

;; data_structures.clj:269 [language]
(deftest test-conj
  ; doesn't work on strings or arrays
  (is (thrown? ClassCastException (conj "" \a)))
  (is (thrown? ClassCastException (conj (into-array []) 1)))

  (are [x y] (= x y)
      (conj nil 1) '(1)
      (conj nil 3 2 1) '(1 2 3)

      (conj nil nil) '(nil)
      (conj nil nil nil) '(nil nil)
      (conj nil nil nil 1) '(1 nil nil)

      ; list -> conj puts the item at the front of the list
      (conj () 1) '(1)
      (conj () 1 2) '(2 1)

      (conj '(2 3) 1) '(1 2 3)
      (conj '(2 3) 1 4 3) '(3 4 1 2 3)

      (conj () nil) '(nil)
      (conj () ()) '(())

      ; vector -> conj puts the item at the end of the vector
      (conj [] 1) [1]
      (conj [] 1 2) [1 2]

      (conj [2 3] 1) [2 3 1]
      (conj [2 3] 1 4 3) [2 3 1 4 3]

      (conj [] nil) [nil]
      (conj [] []) [[]]

      ; map -> conj expects another (possibly single entry) map as the item,
      ;   and returns a new map which is the old map plus the entries
      ;   from the new, which may overwrite entries of the old.
      ;   conj also accepts a MapEntry or a vector of two items (key and value).
      (conj {} {}) {}
      (conj {} {:a 1}) {:a 1}
      (conj {} {:a 1 :b 2}) {:a 1 :b 2}
      (conj {} {:a 1 :b 2} {:c 3}) {:a 1 :b 2 :c 3}
      (conj {} {:a 1 :b 2} {:a 3 :c 4}) {:a 3 :b 2 :c 4}

      (conj {:a 1} {:a 7}) {:a 7}
      (conj {:a 1} {:b 2}) {:a 1 :b 2}
      (conj {:a 1} {:a 7 :b 2}) {:a 7 :b 2}
      (conj {:a 1} {:a 7 :b 2} {:c 3}) {:a 7 :b 2 :c 3}
      (conj {:a 1} {:a 7 :b 2} {:b 4 :c 5}) {:a 7 :b 4 :c 5}

      (conj {} (first {:a 1})) {:a 1}           ; MapEntry
      (conj {:a 1} (first {:b 2})) {:a 1 :b 2}
      (conj {:a 1} (first {:a 7})) {:a 7}
      (conj {:a 1} (first {:b 2}) (first {:a 5})) {:a 5 :b 2}

      (conj {} [:a 1]) {:a 1}                   ; vector
      (conj {:a 1} [:b 2]) {:a 1 :b 2}
      (conj {:a 1} [:a 7]) {:a 7}
      (conj {:a 1} [:b 2] [:a 5]) {:a 5 :b 2}

      (conj {} {nil {}}) {nil {}}
      (conj {} {{} nil}) {{} nil}
      (conj {} {{} {}}) {{} {}}

      ; set
      (conj #{} 1) #{1}
      (conj #{} 1 2 3) #{1 2 3}

      (conj #{2 3} 1) #{3 1 2}
      (conj #{3 2} 1) #{1 2 3}

      (conj #{2 3} 2) #{2 3}
      (conj #{2 3} 2 3) #{2 3}
      (conj #{2 3} 4 1 2 3) #{1 2 3 4}

      (conj #{} nil) #{nil}
      (conj #{} #{}) #{#{}} ))

;; data_structures.clj:349 [language]
(deftest test-peek
  ; doesn't work for sets and maps
  (is (thrown? ClassCastException (peek #{1})))
  (is (thrown? ClassCastException (peek {:a 1})))

  (are [x y] (= x y)
      (peek nil) nil

      ; list = first
      (peek ()) nil
      (peek '(1)) 1
      (peek '(1 2 3)) 1

      (peek '(nil)) nil     ; special cases
      (peek '(1 nil)) 1
      (peek '(nil 2)) nil
      (peek '(())) ()
      (peek '(() nil)) ()
      (peek '(() 2 nil)) ()

      ; vector = last
      (peek []) nil
      (peek [1]) 1
      (peek [1 2 3]) 3

      (peek [nil]) nil      ; special cases
      (peek [1 nil]) nil
      (peek [nil 2]) 2
      (peek [[]]) []
      (peek [[] nil]) nil
      (peek [[] 2 nil]) nil ))

;; data_structures.clj:382 [language]
(deftest test-pop
  ; doesn't work for sets and maps
  (is (thrown? ClassCastException (pop #{1})))
  (is (thrown? ClassCastException (pop #{:a 1})))

  ; collection cannot be empty
  (is (thrown? IllegalStateException (pop ())))
  (is (thrown? IllegalStateException (pop [])))

  (are [x y] (= x y)
      (pop nil) nil

      ; list - pop first
      (pop '(1)) ()
      (pop '(1 2 3)) '(2 3)

      (pop '(nil)) ()
      (pop '(1 nil)) '(nil)
      (pop '(nil 2)) '(2)
      (pop '(())) ()
      (pop '(() nil)) '(nil)
      (pop '(() 2 nil)) '(2 nil)

      ; vector - pop last
      (pop [1]) []
      (pop [1 2 3]) [1 2]

      (pop [nil]) []
      (pop [1 nil]) [1]
      (pop [nil 2]) [nil]
      (pop [[]]) []
      (pop [[] nil]) [[]]
      (pop [[] 2 nil]) [[] 2] ))

;; data_structures.clj:419 [language]
(deftest test-list
  (are [x]  (list? x)
      ()
      '()
      (list)
      (list 1 2 3) )

  ; order is important
  (are [x y] (not (= x y))
      (list 1 2) (list 2 1)
      (list 3 1 2) (list 1 2 3) )

  (are [x y] (= x y)
      '() ()
      (list) '()
      (list 1) '(1)
      (list 1 2) '(1 2)

      ; nesting
      (list 1 (list 2 3) (list 3 (list 4 5 (list 6 (list 7)))))
        '(1 (2 3) (3 (4 5 (6 (7)))))

      ; different data structures
      (list true false nil)
        '(true false nil)
      (list 1 2.5 2/3 "ab" \x 'cd :kw)
        '(1 2.5 2/3 "ab" \x cd :kw)
      (list (list 1 2) [3 4] {:a 1 :b 2} #{:c :d})
        '((1 2) [3 4] {:a 1 :b 2} #{:c :d})

      ; evaluation
      (list (+ 1 2) [(+ 2 3) 'a] (list (* 2 3) 8))
        '(3 [5 a] (6 8))

      ; special cases
      (list nil) '(nil)
      (list 1 nil) '(1 nil)
      (list nil 2) '(nil 2)
      (list ()) '(())
      (list 1 ()) '(1 ())
      (list () 2) '(() 2) ))

;; data_structures.clj:464 [language]
(deftest test-find
  (are [x y] (= x y)
      (find {} :a) nil

      (find {:a 1} :a) [:a 1]
      (find {:a 1} :b) nil
      (find {nil 1} nil) [nil 1]

      (find {:a 1 :b 2} :a) [:a 1]
      (find {:a 1 :b 2} :b) [:b 2]
      (find {:a 1 :b 2} :c) nil

      (find {} nil) nil
      (find {:a 1} nil) nil
      (find {:a 1 :b 2} nil) nil ))

;; data_structures.clj:573 [language]
(deftest test-keys
  (are [x y] (= x y)      ; other than map data structures
      (keys ()) nil
      (keys []) nil
      (keys #{}) nil
      (keys "") nil )

  (are [x y] (= x y)
      ; (class {:a 1}) => clojure.lang.PersistentArrayMap
      (keys {}) nil
      (keys {:a 1}) '(:a)
      (keys {nil 1}) '(nil)
      (diff (keys {:a 1 :b 2}) '(:a :b)) nil              ; (keys {:a 1 :b 2}) '(:a :b)

      ; (class (sorted-map :a 1)) => clojure.lang.PersistentTreeMap
      (keys (sorted-map)) nil
      (keys (sorted-map :a 1)) '(:a)
      (diff (keys (sorted-map :a 1 :b 2)) '(:a :b)) nil   ; (keys (sorted-map :a 1 :b 2)) '(:a :b)

      ; (class (hash-map :a 1)) => clojure.lang.PersistentHashMap
      (keys (hash-map)) nil
      (keys (hash-map :a 1)) '(:a)
      (diff (keys (hash-map :a 1 :b 2)) '(:a :b)) nil )   ; (keys (hash-map :a 1 :b 2)) '(:a :b)

  (let [m {:a 1 :b 2}
        k (keys m)]
    (is (= {:hi :there} (meta (with-meta k {:hi :there}))))))

;; data_structures.clj:602 [language]
(deftest test-vals
  (are [x y] (= x y)      ; other than map data structures
      (vals ()) nil
      (vals []) nil
      (vals #{}) nil
      (vals "") nil )

  (are [x y] (= x y)
      ; (class {:a 1}) => clojure.lang.PersistentArrayMap
      (vals {}) nil
      (vals {:a 1}) '(1)
      (vals {nil 1}) '(1)
      (diff (vals {:a 1 :b 2}) '(1 2)) nil              ; (vals {:a 1 :b 2}) '(1 2)

      ; (class (sorted-map :a 1)) => clojure.lang.PersistentTreeMap
      (vals (sorted-map)) nil
      (vals (sorted-map :a 1)) '(1)
      (diff (vals (sorted-map :a 1 :b 2)) '(1 2)) nil   ; (vals (sorted-map :a 1 :b 2)) '(1 2)

      ; (class (hash-map :a 1)) => clojure.lang.PersistentHashMap
      (vals (hash-map)) nil
      (vals (hash-map :a 1)) '(1)
      (diff (vals (hash-map :a 1 :b 2)) '(1 2)) nil )   ; (vals (hash-map :a 1 :b 2)) '(1 2)

  (let [m {:a 1 :b 2}
        v (vals m)]
    (is (= {:hi :there} (meta (with-meta v {:hi :there}))))))

;; data_structures.clj:631 [language]
(deftest test-sorted-map-keys
  (is (thrown? ClassCastException (sorted-map () 1)))
  (is (thrown? ClassCastException (sorted-map #{} 1)))
  (is (thrown? ClassCastException (sorted-map {} 1)))

  (is (thrown? ClassCastException (assoc (sorted-map) () 1)))
  (is (thrown? ClassCastException (assoc (sorted-map) #{} 1)))
  (is (thrown? ClassCastException (assoc (sorted-map) {} 1)))

  ;; doesn't throw
  (let [cmp #(compare (count %1) (count %2))]
    (assoc (sorted-map-by cmp) () 1)
    (assoc (sorted-map-by cmp) #{} 1)
    (assoc (sorted-map-by cmp) {} 1)))

;; data_structures.clj:647 [language]
(deftest test-key
  (are [x]  (= (key (first (hash-map x :value))) x)
      nil
      false true
      0 42
      0.0 3.14
      2/3
      0M 1M
      \c
      "" "abc"
      'sym
      :kw
      () '(1 2)
      [] [1 2]
      {} {:a 1 :b 2}
      #{} #{1 2} ))

;; data_structures.clj:665 [language]
(deftest test-val
  (are [x]  (= (val (first (hash-map :key x))) x)
      nil
      false true
      0 42
      0.0 3.14
      2/3
      0M 1M
      \c
      "" "abc"
      'sym
      :kw
      () '(1 2)
      [] [1 2]
      {} {:a 1 :b 2}
      #{} #{1 2} ))

;; data_structures.clj:682 [language]
(deftest test-get
  (let [m {:a 1, :b 2, :c {:d 3, :e 4}, :f nil, :g false, nil {:h 5}}]
    (is (thrown? IllegalArgumentException (get-in {:a 1} 5)))
    (are [x y] (= x y)
         (get m :a) 1
         (get m :e) nil
         (get m :e 0) 0
         (get m nil) {:h 5}
         (get m :b 0) 2
         (get m :f 0) nil

         (get-in m [:c :e]) 4
         (get-in m '(:c :e)) 4
         (get-in m [:c :x]) nil
         (get-in m [:f]) nil
         (get-in m [:g]) false
         (get-in m [:h]) nil
         (get-in m []) m
         (get-in m nil) m

         (get-in m [:c :e] 0) 4
         (get-in m '(:c :e) 0) 4
         (get-in m [:c :x] 0) 0
         (get-in m [:b] 0) 2
         (get-in m [:f] 0) nil
         (get-in m [:g] 0) false
         (get-in m [:h] 0) 0
         (get-in m [:x :y] {:y 1}) {:y 1}
         (get-in m [] 0) m
         (get-in m nil 0) m)))

;; data_structures.clj:713 [language]
(deftest test-req!
  (let [m {:a 1, :b 2, :f nil, :g false, nil "nil"}]
    (is (thrown? Exception (req! m :e)))
    (are [x y] (= x y)
         (req! m :a)  1
         (req! m nil) "nil"
         (req! m :b)  2
         (req! m :f)  nil)))

;; data_structures.clj:722 [language]
(deftest test-nested-map-destructuring
  (let [sample-map {:a 1 :b {:a 2}}
        {ao1 :a {ai1 :a} :b} sample-map
        {ao2 :a {ai2 :a :as m1} :b :as m2} sample-map
        {ao3 :a {ai3 :a :as m} :b :as m} sample-map
        {{ai4 :a :as m} :b ao4 :a :as m} sample-map]
    (are [i o] (and (= i 2)
                    (= o 1))
         ai1 ao1
         ai2 ao2
         ai3 ao3
         ai4 ao4)))

;; data_structures.clj:798 [language]
(deftest test-sorted-set
  ; only compatible types can be used
  (is (thrown? ClassCastException (sorted-set 1 "a")))
  (is (thrown? ClassCastException (sorted-set '(1 2) [3 4])))

  ; creates set?
  (are [x] (set? x)
       (sorted-set)
       (sorted-set 1 2) )

  ; equal and unique
  (are [x] (and (= (sorted-set x) #{x})
                (= (sorted-set x x) (sorted-set x)))
      nil
      false true
      0 42
      0.0 3.14
      2/3
      0M 1M
      \c
      "" "abc"
      'sym
      :kw
      [] [1 2]
  )
  ; cannot be cast to java.lang.Comparable
  (is (thrown? ClassCastException (sorted-set ())))
  (is (thrown? ClassCastException (sorted-set {})))
  (is (thrown? ClassCastException (sorted-set #{})))
  (is (thrown? ClassCastException (sorted-set '(1 2) '(1 2))))
  (is (thrown? ClassCastException (sorted-set {:a 1 :b 2} {:a 1 :b 2})))
  (is (thrown? ClassCastException (sorted-set #{1 2} #{1 2})))

  (are [x y] (= x y)
      ; generating
      (sorted-set) #{}
      (sorted-set 1) #{1}
      (sorted-set 1 2) #{1 2}

      ; sorting
      (seq (sorted-set 5 4 3 2 1)) '(1 2 3 4 5)

      ; special cases
      (sorted-set nil) #{nil}
      (sorted-set 1 nil) #{nil 1}
      (sorted-set nil 2) #{nil 2}
      (sorted-set []) #{[]} ))

;; data_structures.clj:847 [language]
(deftest test-sorted-set-by
  ; only compatible types can be used
  ; NB: not a ClassCastException, but a RuntimeException is thrown,
  ; requires discussion on whether this should be symmetric with test-sorted-set
  (is (thrown? Exception (sorted-set-by < 1 "a")))
  (is (thrown? Exception (sorted-set-by < '(1 2) [3 4])))

  ; creates set?
  (are [x] (set? x)
       (sorted-set-by <)
       (sorted-set-by < 1 2) )

  ; equal and unique
  (are [x] (and (= (sorted-set-by compare x) #{x})
                (= (sorted-set-by compare x x) (sorted-set-by compare x)))
      nil
      false true
      0 42
      0.0 3.14
      2/3
      0M 1M
      \c
      "" "abc"
      'sym
      :kw
      ()  ; '(1 2)
      [] [1 2]
      {}  ; {:a 1 :b 2}
      #{} ; #{1 2}
  )
  ; cannot be cast to java.lang.Comparable
  ; NB: not a ClassCastException, but a RuntimeException is thrown,
  ; requires discussion on whether this should be symmetric with test-sorted-set
  (is (thrown? Exception (sorted-set-by compare '(1 2) '(1 2))))
  (is (thrown? Exception (sorted-set-by compare {:a 1 :b 2} {:a 1 :b 2})))
  (is (thrown? Exception (sorted-set-by compare #{1 2} #{1 2})))

  (are [x y] (= x y)
      ; generating
      (sorted-set-by >) #{}
      (sorted-set-by > 1) #{1}
      (sorted-set-by > 1 2) #{1 2}

      ; sorting
      (seq (sorted-set-by < 5 4 3 2 1)) '(1 2 3 4 5)

      ; special cases
      (sorted-set-by compare nil) #{nil}
      (sorted-set-by compare 1 nil) #{nil 1}
      (sorted-set-by compare nil 2) #{nil 2}
      (sorted-set-by compare #{}) #{#{}} ))

;; data_structures.clj:900 [language]
(deftest test-set
  ; set?
  (are [x] (set? (set x))
      () '(1 2)
      [] [1 2]
      #{} #{1 2}
      {} {:a 1 :b 2}
      (into-array []) (into-array [1 2])
      "" "abc" )

  ; unique
  (are [x] (= (set [x x]) #{x})
      nil
      false true
      0 42
      0.0 3.14
      2/3
      0M 1M
      \c
      "" "abc"
      'sym
      :kw
      () '(1 2)
      [] [1 2]
      {} {:a 1 :b 2}
      #{} #{1 2} )

  ; conversion
  (are [x y] (= (set x) y)
      () #{}
      '(1 2) #{1 2}

      [] #{}
      [1 2] #{1 2}

      #{} #{}         ; identity
      #{1 2} #{1 2}   ; identity

      {} #{}
      {:a 1 :b 2} #{[:a 1] [:b 2]}

      (into-array []) #{}
      (into-array [1 2]) #{1 2}

      "" #{}
      "abc" #{\a \b \c} )

  ; get, get not-found, invoke on sets and transient sets
  (are [e enf s k] (and
                     (= e (get s k))
                     (= enf (get (transient s) k 1))
                     (= e (s k))
                     (= enf ((transient s) k 1))
                     (= e (k s))
                     (= enf (k s 1)))
    :a :a #{:a} :a
    nil 1 #{:a} :b
    nil 1 #{} :a
    nil 1 #{nil} :a))

;; data_structures.clj:1116 [language]
(deftest test-array-map-arity
  (is (thrown? IllegalArgumentException
               (array-map 1 2 3))))

;; data_structures.clj:1120 [language]
(deftest test-assoc
  (are [x y] (= x y)
       [4] (assoc [] 0 4)
       [5 -7] (assoc [] 0 5 1 -7)
       {:a 1} (assoc {} :a 1)
       {nil 1} (assoc {} nil 1)
       {:a 2 :b -2} (assoc {} :b -2 :a 2))
  (is (thrown? IllegalArgumentException (assoc [] 0 5 1)))
  (is (thrown? IllegalArgumentException (assoc {} :b -2 :a))))

;; data_structures.clj:1356 [language]
(deftest singleton-map-in-destructure-context
  (let [sample-map {:a 1 :b 2}
        {:keys [a] :as m1} (list sample-map)]
    (is (= m1 sample-map))
    (is (= a 1))))

;; data_structures.clj:1362 [language]
(deftest trailing-map-destructuring
  (let [sample-map {:a 1 :b 2}
        add  (fn [& {:keys [a b]}] (+ a b))
        addn (fn [n & {:keys [a b]}] (+ n a b))]
    (testing "that kwargs are applied properly given a map in place of the key/val pairs"
      (is (= 3 (add  :a 1 :b 2)))
      (is (= 3 (add  {:a 1 :b 2})))
      (is (= 13 (addn 10 :a 1 :b 2)))
      (is (= 13 (addn 10 {:a 1 :b 2})))
      (is (= 103 ((partial addn 100) :a 1 {:b 2})))
      (is (= 103 ((partial addn 100 :a 1) {:b 2})))
      (is (= 107 ((partial addn 100 :a 1) {:a 5 :b 2}))))
    (testing "built maps"
      (let [{:as m1} (list :a 1 :b 2)
            {:as m2} (list :a 1 :b 2 {:c 3})
            {:as m3} (list :a 1 :b 2 {:a 0})
            {:keys [a4] :as m4} (list nil)]
        (= m1 {:a 1 :b 2})
        (= m2 {:a 1 :b 2 :c 3})
        (= m3 {:a 0 :b 2})
        (= m1 (seq-to-map-for-destructuring (list :a 1 :b 2)))
        (= m2 (seq-to-map-for-destructuring (list :a 1 :b 2 {:c 3})))
        (= m3 (seq-to-map-for-destructuring (list :a 1 :b 2 {:a 0})))
        (= a4 nil)))))

;; data_structures.clj:1387 [language]
(deftest keys-bang
  (let [sample-map {:a 1 :b 2}]
    (testing ":keys! happy path, binds and throws when key missing"
      (is (= 1 (let [{:keys! [a b]} sample-map] a)))
      (is (thrown? Exception (let [{:keys! [a b]} {:a 1}] a))))
    (testing ":keys! with & bind and don't bind"
      (is (= 1 (let [{:keys! [a & :b]} sample-map] a)))
      (is (thrown? Exception (let [{:keys! [a & :b]} {:a 1}] a))))
    (testing "nested maps with :keys! &"
      (let [sample-map {:a 1 :b {:a 2 :b 3 :c 4 :d 42}}
            {a :a {aa :a :as m :keys! [b c & :d]} :b} sample-map]
        (is (= m (:b sample-map)))
        (is (= a 1))
        (is (= aa 2))
        (is (= b 3))
        (is (= c 4))
        (is (thrown? Exception (let [{a :a {aa :a :as m :keys! [b c & :d :e]} :b} sample-map] a)))
        (is (thrown? Exception (let [{a :a {aa :a :as m :keys! [b c & :d]} :b} (update sample-map :b dissoc :c)] a)))))
    (testing "a broad range of qualified names/declarators with :keys! &"
      (let [sample-map {:foo/a 1 :b 2 :foo/c 3}
            {:keys! [foo/a & :b]} sample-map
            {:keys! [b & :foo/c]} sample-map
            sample-map2 {:foo/aa 1 :bb 2 :foo/cc 3}
            {:foo/keys! [aa & :foo/cc]} sample-map2]
        (is (= a 1))
        (is (= b 2))
        (is (thrown? Exception (let [{:keys! [b & :foo/c]} (dissoc sample-map :b)] b)))
        (is (thrown? Exception (let [{:keys! [b & :foo/c]} (dissoc sample-map :foo/c)] b)))
        (is (= 1 (let [{:foo/keys! [aa & :bb]} sample-map2] aa)))
        (is (= aa 1))
        (is (= 1 (let [{:keys! [::a & ::b]} {::a 1 , ::b 2}] a)))))
    (testing "that right of & is unbound (compile-time errors)"
      (is (thrown? Exception (eval '(let [{:keys! [a & :b]} sample-map] b))))
      (is (thrown? Exception (eval '(let [{a :a {aa :a :as m :keys [b c & :e]} :b} sample-map] e))))
      (is (thrown? Exception (eval '(let [{:keys! [foo/a & :foo/c]} sample-map] c))))
      (let [sample-map2 {:foo/aa 1 :bb 2 :foo/cc 3}]
        (is (thrown? Exception (eval '(let [{:foo/keys! [foo/aa & :foo/cc]} sample-map2] cc))))))))

;; data_structures.clj:1425 [language]
(deftest syms-bang
  (let [sample-map '{a 1 b 2}]
    (testing ":syms! happy path, binds and throws when key missing"
      (is (= 1 (let [{:syms! [a b]} sample-map] a)))
      (is (thrown? Exception (let [{:syms! [a b]} {:a 1}] a))))
    (testing ":syms! with & bind and don't bind"
      (is (= 1 (let [{:syms! [a & 'b]} sample-map] a)))
      (is (thrown? Exception (let [{:syms! [a & 'b]} {:a 1}] a))))
    (testing "nested maps with :syms! &"
      (let [sample-map '{a 1 b {a 2 b 3 c 4 d 42}}
            {a 'a {aa 'a :as m :syms! [b c & 'd]} 'b} sample-map]
        (is (= m ('b sample-map)))
        (is (= a 1))
        (is (= aa 2))
        (is (= b 3))
        (is (= c 4))
        (is (thrown? Exception (let [{a 'a {aa :a :as m :syms! [b c & 'd 'e]} 'b} sample-map] a)))
        (is (thrown? Exception (let [{a 'a {aa :a :as m :syms! [b c & 'd]} 'b} (update sample-map 'b dissoc 'c)] a)))))
    (testing "a broad range of qualified names/declarators with :syms! &"
      (let [sample-map '{foo/a 1 b 2 foo/c 3}
            {:syms! [foo/a & 'b]} sample-map
            {:syms! [b & 'foo/c]} sample-map
            sample-map2 '{foo/aa 1 bb 2 foo/cc 3}
            {:foo/syms! [aa & 'foo/cc]} sample-map2]
        (is (= a 1))
        (is (= b 2))
        (is (thrown? Exception (let [{:syms! [b & 'foo/c]} (dissoc sample-map 'b)] b)))
        (is (thrown? Exception (let [{:syms! [b & 'foo/c]} (dissoc sample-map 'foo/c)] b)))
        (is (= aa 1))
        (is (= 1 (let [{:foo/syms! [aa & 'bb]} sample-map2] aa)))))
    (testing "that right of & is unbound (compile-time errors)"
      (is (thrown? Exception (eval '(let [{:syms! [a & 'b]} sample-map] b))))
      (is (thrown? Exception (eval '(let [{a a {aa a :as m :syms [b c & 'e]} :b} sample-map] e))))
      (is (thrown? Exception (eval '(let [{:syms! [foo/a & 'foo/c]} sample-map] c))))
      (let [sample-map2 '{foo/aa 1 bb 2 foo/cc 3}]
        (is (thrown? Exception (eval '(let [{:foo/syms! [foo/aa & 'foo/cc]} sample-map2] cc))))))))

;; data_structures.clj:1462 [language]
(deftest strs-bang
  (let [sample-map {"a" 1 "b" 2}]
    (testing ":strs! happy path, binds and throws when key missing"
      (is (= 1 (let [{:strs! [a b]} sample-map] a)))
      (is (thrown? Exception (let [{:strs! [a b]} {:a 1}] a))))
    (testing ":strs! with & bind and don't bind"
      (is (= 1 (let [{:strs! [a & "b"]} sample-map] a)))
      (is (thrown? Exception (let [{:strs! [a & "b"]} {:a 1}] a))))
    (testing "nested maps with :strs! &"
      (let [sample-map {"a" 1 "b" {"a" 2 "b" 3 "c" 4 "d" 42}}
            {a "a" {aa "a" :as m :strs! [b c & "d"]} "b"} sample-map]
        (is (= m (get sample-map "b")))
        (is (= a 1))
        (is (= aa 2))
        (is (= b 3))
        (is (= c 4))
        (is (thrown? Exception (let [{a "a" {aa "a" :as m :strs! [b c & "d" "e"]} "b"} sample-map] a)))
        (is (thrown? Exception (let [{a "a" {aa "a" :as m :strs! [b c & "d"]} "b"} (update sample-map "b" dissoc "c")] a)))))
    (testing "that right of & is unbound (compile-time errors)"
      (is (thrown? Exception (eval '(let [{:strs! [a & "b"]} sample-map] b))))
      (is (thrown? Exception (eval '(let [{a "a" {aa "a" :as m :keys [b c & "e"]} "b"} sample-map] e)))))))

;; data_structures.clj:1484 [language]
(deftest select-directive
  (let [m {:a 1 :b 2 :c 3 :d 4
           'sa 10 'sb 20 'sc 30 'sd 40
           "stra" 100 "strb" 200 "strc" 300 "strd" 400
           :foo/x 1000 :foo/y 2000 :foo/z 3000
           ::x 10000 ::y 20000 ::z 30000
           :nested {:aa 1 'saa 10 "straa" 100}}

        {:keys [a b & :c :z]
         :keys! [d]
         :select keys-sel} m

        {:syms [sa sb & 'sc 'sz]
         :syms! [sd]
         :select syms-sel} m

        {:strs [stra strb & "strc" "strz"]
         :strs! [strd]
         :select strs-sel} m

        {:foo/keys [x & :y :zz]
         :foo/keys! [z]
         :select qkeys-sel} m

        {::keys [x & :y :zz]
         ::keys! [z]
         :select aqkeys-sel} m

        {{aa :aa saa 'saa
          :select nest-sel} :nested
         aqx ::x
         :select tl-sel} m

        {:keys! [a b & :c]
         :keys [d & :z]
         :or {}
         :select or-sel} m

        {:keys [a b c d]
         :syms [sa sb sc sd]
         :strs [stra strb strc strd]
         :foo/keys! [x y z]
         ::keys [x y z]
         nest :nested
         :as mm
         :select sel-mm} m]
    (are [expected result] (= expected result)
      keys-sel {:a 1 :b 2 :c 3 :d 4}
      syms-sel '{sa 10 sb 20 sc 30 sd 40}
      strs-sel {"stra" 100 "strb" 200 "strc" 300 "strd" 400}
      qkeys-sel {:foo/x 1000 :foo/z 3000}
      aqkeys-sel {::x 10000 ::z 30000}
      nest-sel '{:aa 1, saa 10}
      tl-sel '{:nested {:aa 1, saa 10} ::x 10000}
      or-sel {:a 1 :b 2 :c 3 :d 4}
      sel-mm mm))
  (testing "base cases"
    (is (nil? (let [{{a :a} :n :select s} nil] s))
        "if you haven't supplied a map, select won't make one for no reason")

    (testing "you get what you supplied if nothing else"
      (is (= {} (let [{{a :a} :n :select s} {}] s)))
      (is (= {:n nil} (let [{{a :a} :n :select s} {:n nil}] s)))
      (is (= {:n {}} (let [{{a :a} :n :select s} {:n {}}] s))))

    (testing "defaults can turn nothing into something"
      (is (= {:n {:a 42}} (let [{{a :a :or {a 42}} :n :select s} nil] s)))
      (is (= {:n {:a 42}} (let [{{a :a :or {a 42}} :n :select s} {:n nil}] s))))))

;; data_structures.clj:1553 [language]
(deftest select-or-defaults
  (let [sample-map {:a 1, :b 2, :c  {:aa 10 :bb 20},
                    'd 4  'e 5  'f  {'dd 40 'ee 50},
                    "g" 6 "h" 7 "i" {"gg" 60 "hh" 70},}]
    (testing "happy path"
      (testing ":defaults"
        (is (empty? (let [{:defaults d :or {}} {}] d)))
        (is (thrown? Exception (eval '(let [{:defaults d :or {:a 1}} {}] d))))
        (is (= {:a 1} (let [{:keys [a] :defaults d :or {:a 1}} {}] d)))
        (is (= {:a 1} (let [{:keys [a] :defaults d :or {a 1}} {}] d)))
        (is (= {:a 1, 'b 2, "c" 3} (let [{b 'b, c "c", :keys [a] :defaults d :or {:a 1, 'b 2, "c" 3}} {}] d))))
      
      (testing ":keys + :select + :or + defaults"
        (let [{:keys [a b z & :c :d] {:keys! [aa & :bb]} :c
               :or {:d 42, z :or-z}
               :select m
               :defaults dfs} sample-map]
          (is (= 1 a))
          (is (= 2 b))
          (is (= 10 aa))
          (is (= {:z :or-z, :c {:aa 10, :bb 20}, :b 2, :d 42, :a 1} m))
          (is (= {:d 42, :z :or-z} dfs))))

      (testing ":syms + :select + :or + defaults"
        (let [{:syms [d e z & 'd 'f] {:syms! [dd & 'ee]} 'f
               :or {'d 42, z :or-z}
               :select m
               :defaults dfs} sample-map]
          (is (= 4 d))
          (is (= 5 e))
          (is (= 40 dd))
          (is (= '{f {dd 40, ee 50}, e 5, d 4, z :or-z} m))
          (is (= '{d 42, z :or-z} dfs))))

      (testing ":strs + :select + :or + defaults"
        (let [{:strs [g h z & "d" "i"] {:strs! [gg & "hh"]} "i"
               :or {"d" 42, z :or-z}
               :select m
               :defaults dfs} sample-map]
          (is (= 6 g))
          (is (= 7 h))
          (is (= 60 gg))
          (is (= {"d" 42, "z" :or-z, "i" {"gg" 60, "hh" 70}, "g" 6, "h" 7} m))
          (is (= {"d" 42, "z" :or-z} dfs))))

      (testing "mixed things after &"
        (is (= 1 (let [{:keys [a & 'b]} {:a 1}] a)))
        (is (= 1 (let [{:keys! [a & 'b "c"]} {:a 1, 'b 2, "c" 3}] a))))

      (testing "known compile-time errors"
        (is (thrown? Exception (eval '(let [{:keys [a] :defaults d :or {:a 1, a 1}} {}] d))))
        (is (thrown? Exception (eval '(let [{:defaults d} {}] d))))))))

;; data_structures.clj:1606 [language]
(deftest all-directive
  (testing "base cases"
    (testing "you get what you supplied if nothing else"
      (is (= {:a 1 :b 2 :c 3}
             (let [{:keys [a] :all m} {:a 1 :b 2 :c 3}] m)))
      (is (nil? (let [{:keys [a] :all m} nil] m)))
      (is (= {} (let [{:keys [a] :all m} {}] m)))
      (is (nil? (let [{{a :a} :n :all m} nil] m)))
      (is (= {} (let [{{a :a} :n :all m} {}] m)))
      (is (= {:n nil} (let [{{a :a} :n :all m} {:n nil}] m)))
      (is (= {:n {}} (let [{{a :a} :n :all m} {:n {}}] m)))
      (testing "with binding names"
        (is (= {:a 42} (let [{a :a :or {a 42} :all m} {}] m)))
        (is (= {:a 1 :b 2} (let [{a :a :or {a 42} :all m} {:a 1 :b 2}] m)))))
    (testing "empty :or"
      (is (nil? (let [{:keys [a] :or {} :all m} nil] m)))
      (is (= {} (let [{:keys [a] :or {} :all m} {}] m)))
      (is (= {:n {}} (let [{{a :a :or {}} :n :or {} :all m} {:n {}}] m))))
    (testing "all turns nothing into something"
      (is (= {:a 42} (let [{:keys [a] :or {a 42} :all m} nil] m)))
      (is (= {:a 42} (let [{:keys [a] :or {a 42} :all m} {}] m)))
      (is (= {:n {:a 42}} (let [{{a :a :or {a 42}} :n :all m} {:n nil}] m))))
    (testing ":or defaults must correspond to binding with :all"
      (is (thrown? Exception (eval '(let [{:keys [a] :or {a 1 z 2} :all m} {}] m))))))
  (testing "defaults applied in :all"
    (is (= {:a 1}       (let [{:keys [a] :or {a 42} :all m} {:a 1}] m)))
    (is (= {:n {:a 42}} (let [{{a :a :or {a 42}} :n :all m} nil] m)))
    (is (= {:n {:nn {:a 1 :b 2}}}
           (let [{{{a :a :or {a 1}} :nn :or {}} :n :or {} :all m} {:n {:nn {:b 2}}}] m)))
    (is (= [{:n1 {:a 1}, :n2 {:b 20, :c 30}} {:a 1} {:b 20 :c 30}]
           (let [{{a :a :or {a 1} :all all-n1} :n1
                  {b :b :or {b 2} :all all-n2} :n2
                  :all outer-all}
                 {:n1 {} :n2 {:b 20 :c 30}}]
             [outer-all all-n1 all-n2]))))
  (testing "paired with &"
    (is (= {:z 42 :a 1 :b 2}
           (let [{:keys [a b & :c :z] :or {:z 42} :all m} {:a 1 :b 2}] m)))
    (is (= {:z 100 :a 1 :b 2}
           (let [{:keys [a b & :c :z] :or {:z 42} :all m} {:a 1 :b 2 :z 100}] m)))
    (testing ":or defaults must correspond to binding with :all plus &"
      (is (thrown? Exception (eval '(let [{:keys [a b & :c] :or {c 42} :all m} {:a 1 :b 2}] m))))))
  (testing ":all with :defaults"
      (is (= [{:a 1} {:a 1}]
             (let [{:keys [a] :or {a 1} :all all-m :defaults dfs} {}]
               [all-m dfs])))
      (is (= [{:a 5 :b 2} {:a 1}]
             (let [{:keys [a] :or {a 1} :all all-m :defaults dfs} {:a 5 :b 2}]
               [all-m dfs]))))
  (testing "combinations"
    (let [sample-map {:a 1, :b 2, :c {:aa 10},
                      'd 4, 'e 5, 'f {'dd 40},
                      "g" 6, "h" 7, "i" {"gg" 60},
                      :foo/x 1000, :foo/y 2000,
                      ::z 3000,
                      :extra 42}
          {:keys [a & :missing]
           :keys! [b]
           {:keys [aa & :bb] :or {:bb 200} :all all-c} :c
           :syms [d]
           :syms! [e]
           {:syms [dd & 'ee] :or {'ee 500} :all all-f} 'f
           :strs [g]
           :strs! [h]
           {:strs [gg & "hh"] :or {"hh" 700} :all all-i} "i"
           :foo/keys [x]
           ::keys [z]
           :or {:missing :default-missing}
           :all all-m
           :select sel-m
           :defaults dfs
           :as as-m} sample-map]

      (is (= 1 a)) (is (= 2 b))
      (is (= 4 d)) (is (= 5 e))
      (is (= 6 g)) (is (= 7 h))
      (is (= 1000 x)) (is (= 3000 z))
      (is (= {:aa 10 :bb 200} all-c))
      (is (= '{dd 40 ee 500} all-f))
      (is (= {"gg" 60 "hh" 700} all-i))
      (is (= as-m sample-map))
      (is (= {:missing :default-missing} dfs))

      (testing ":all merges manually"
        (is (= all-m (merge sample-map
                            {:missing :default-missing
                             :c all-c
                             'f all-f
                             "i" all-i})))
        (is (contains? all-m :extra))
        (is (contains? all-m :foo/y))
        (is (= sel-m (dissoc all-m :extra :foo/y)))))))
