;; DERIVED from upstream/clojure/test/clojure/test_clojure/data_structures.clj by upstream/derive-tests -- do not edit.
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
  (is (thrown? clotran.host.class_cast_exception (conj "" \a)))
  (is (thrown? clotran.host.class_cast_exception (conj (into-array []) 1)))

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
  (is (thrown? clotran.host.class_cast_exception (peek #{1})))
  (is (thrown? clotran.host.class_cast_exception (peek {:a 1})))

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
  (is (thrown? clotran.host.class_cast_exception (pop #{1})))
  (is (thrown? clotran.host.class_cast_exception (pop #{:a 1})))

  ; collection cannot be empty
  (is (thrown? clotran.host.illegal_state_exception (pop ())))
  (is (thrown? clotran.host.illegal_state_exception (pop [])))

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
      ; (class {:a 1}) => clotran.host.persistent_array_map
      (keys {}) nil
      (keys {:a 1}) '(:a)
      (keys {nil 1}) '(nil)
      (diff (keys {:a 1 :b 2}) '(:a :b)) nil              ; (keys {:a 1 :b 2}) '(:a :b)

      ; (class (sorted-map :a 1)) => clotran.host.persistent_tree_map
      (keys (sorted-map)) nil
      (keys (sorted-map :a 1)) '(:a)
      (diff (keys (sorted-map :a 1 :b 2)) '(:a :b)) nil   ; (keys (sorted-map :a 1 :b 2)) '(:a :b)

      ; (class (hash-map :a 1)) => clotran.host.persistent_hash_map
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
      ; (class {:a 1}) => clotran.host.persistent_array_map
      (vals {}) nil
      (vals {:a 1}) '(1)
      (vals {nil 1}) '(1)
      (diff (vals {:a 1 :b 2}) '(1 2)) nil              ; (vals {:a 1 :b 2}) '(1 2)

      ; (class (sorted-map :a 1)) => clotran.host.persistent_tree_map
      (vals (sorted-map)) nil
      (vals (sorted-map :a 1)) '(1)
      (diff (vals (sorted-map :a 1 :b 2)) '(1 2)) nil   ; (vals (sorted-map :a 1 :b 2)) '(1 2)

      ; (class (hash-map :a 1)) => clotran.host.persistent_hash_map
      (vals (hash-map)) nil
      (vals (hash-map :a 1)) '(1)
      (diff (vals (hash-map :a 1 :b 2)) '(1 2)) nil )   ; (vals (hash-map :a 1 :b 2)) '(1 2)

  (let [m {:a 1 :b 2}
        v (vals m)]
    (is (= {:hi :there} (meta (with-meta v {:hi :there}))))))

;; data_structures.clj:631 [language]
(deftest test-sorted-map-keys
  (is (thrown? clotran.host.class_cast_exception (sorted-map () 1)))
  (is (thrown? clotran.host.class_cast_exception (sorted-map #{} 1)))
  (is (thrown? clotran.host.class_cast_exception (sorted-map {} 1)))

  (is (thrown? clotran.host.class_cast_exception (assoc (sorted-map) () 1)))
  (is (thrown? clotran.host.class_cast_exception (assoc (sorted-map) #{} 1)))
  (is (thrown? clotran.host.class_cast_exception (assoc (sorted-map) {} 1)))

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
    (is (thrown? clotran.host.illegal_argument_exception (get-in {:a 1} 5)))
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

;; data_structures.clj:789 [language]
(deftest test-sorted-set
  ; only compatible types can be used
  (is (thrown? clotran.host.class_cast_exception (sorted-set 1 "a")))
  (is (thrown? clotran.host.class_cast_exception (sorted-set '(1 2) [3 4])))

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
  ; cannot be cast to clotran.host.comparable
  (is (thrown? clotran.host.class_cast_exception (sorted-set ())))
  (is (thrown? clotran.host.class_cast_exception (sorted-set {})))
  (is (thrown? clotran.host.class_cast_exception (sorted-set #{})))
  (is (thrown? clotran.host.class_cast_exception (sorted-set '(1 2) '(1 2))))
  (is (thrown? clotran.host.class_cast_exception (sorted-set {:a 1 :b 2} {:a 1 :b 2})))
  (is (thrown? clotran.host.class_cast_exception (sorted-set #{1 2} #{1 2})))

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

;; data_structures.clj:838 [language]
(deftest test-sorted-set-by
  ; only compatible types can be used
  ; NB: not a ClassCastException, but a RuntimeException is thrown,
  ; requires discussion on whether this should be symmetric with test-sorted-set
  (is (thrown? clotran.host.exception (sorted-set-by < 1 "a")))
  (is (thrown? clotran.host.exception (sorted-set-by < '(1 2) [3 4])))

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
  ; cannot be cast to clotran.host.comparable
  ; NB: not a ClassCastException, but a RuntimeException is thrown,
  ; requires discussion on whether this should be symmetric with test-sorted-set
  (is (thrown? clotran.host.exception (sorted-set-by compare '(1 2) '(1 2))))
  (is (thrown? clotran.host.exception (sorted-set-by compare {:a 1 :b 2} {:a 1 :b 2})))
  (is (thrown? clotran.host.exception (sorted-set-by compare #{1 2} #{1 2})))

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

;; data_structures.clj:891 [language]
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
      "abc" #{\a \b \c} ))

;; data_structures.clj:1094 [language]
(deftest test-array-map-arity
  (is (thrown? clotran.host.illegal_argument_exception
               (array-map 1 2 3))))

;; data_structures.clj:1098 [language]
(deftest test-assoc
  (are [x y] (= x y)
       [4] (assoc [] 0 4)
       [5 -7] (assoc [] 0 5 1 -7)
       {:a 1} (assoc {} :a 1)
       {nil 1} (assoc {} nil 1)
       {:a 2 :b -2} (assoc {} :b -2 :a 2))
  (is (thrown? clotran.host.illegal_argument_exception (assoc [] 0 5 1)))
  (is (thrown? clotran.host.illegal_argument_exception (assoc {} :b -2 :a))))

;; data_structures.clj:1334 [language]
(deftest singleton-map-in-destructure-context
  (let [sample-map {:a 1 :b 2}
        {:keys [a] :as m1} (list sample-map)]
    (is (= m1 sample-map))
    (is (= a 1))))

;; data_structures.clj:1340 [language]
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
