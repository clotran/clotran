;; DERIVED from test/clj/clojure/test_clojure/transducers.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.transducers (:require [clojure.string :as s] [clojure.test :refer :all]))

(defn- inc$ [n]
  (if (number? n) (inc n) 1))

(defn- dec$ [n]
  (if (number? n) (dec n) 1))

(defn- odd?$ [n]
  (if (number? n) (odd? n) false))

(defn- pos?$ [n]
  (if (number? n) (pos? n) false))

(defn- empty?$ [s]
  (if (instance? clojure.lang.Seqable s) (empty? s) false))

(def gen-mapfn
  (pickfn inc$ dec$))

(def gen-mapcatfn
  (pickfn vector
          #(if (instance? clojure.lang.Seqable %) (partition-all 3 %) (vector %))))

(def gen-predfn
  (pickfn odd?$ pos?$ empty?$ sequential?))

(def gen-indexedfn
  (pickfn (fn [index item] index)
          (fn [index item] item)
          (fn [index item] (if (number? item) (+ index item) index))))

(def gen-drop-while (fbind gen-predfn drop-while))

(def gen-map (fbind gen-mapfn map))

(def gen-mapcat (fbind gen-mapcatfn mapcat))

(def gen-filter (fbind gen-predfn filter))

(def gen-remove (fbind gen-predfn remove))

(def gen-keep (fbind gen-predfn keep))

(def gen-partition-by (fbind gen-predfn partition-by))

(def gen-take-while (fbind gen-predfn take-while))

(def gen-keep-indexed (fbind gen-indexedfn keep-indexed))

(def gen-map-indexed (fbind gen-indexedfn map-indexed))

(defn apply-as-seq [coll actions]
  (doall
    (loop [s coll
           [action & actions'] actions]
          (if action
            (recur ((:seq action) s) actions')
            s))))

(defn apply-as-xf-seq
  [coll actions]
  (doall (sequence (apply comp (map :xf actions)) coll)))

(defn apply-as-xf-into
  [coll actions]
  (into [] (apply comp (map :xf actions)) coll))

(defn apply-as-xf-eduction
  [coll actions]
  (into [] (eduction (apply comp (map :xf actions)) coll)))

(defn apply-as-xf-transduce
  [coll actions]
  (transduce (apply comp (map :xf actions)) conj coll))

(defmacro return-exc [& forms]
  `(try ~@forms (catch Throwable e# e#)))

(defn build-results
  [coll actions]
  (let [s (return-exc (apply-as-seq coll actions))
        xs (return-exc (apply-as-xf-seq coll actions))
        xi (return-exc (apply-as-xf-into coll actions))
        xe (return-exc (apply-as-xf-eduction coll actions))
        xt (return-exc (apply-as-xf-transduce coll actions))]
    {:coll    coll
     :actions (concat '(->> coll) (map :desc actions))
     :s       s
     :xs      xs
     :xi      xi
     :xe      xe
     :xt      xt}))

(defn result-good?
  [{:keys [s xs xi xe xt]}]
  (= s xs xi xe xt))

;; transducers.clj:226 [language]
(deftest test-dedupe
  (are [x y] (= (transduce (dedupe) conj x) y)
             [] []
             [1] [1]
             [1 2 3] [1 2 3]
             [1 2 3 1 2 2 1 1] [1 2 3 1 2 1]
             [1 1 1 2] [1 2]
             [1 1 1 1] [1]

             "" []
             "a" [\a]
             "aaaa" [\a]
             "aabaa" [\a \b \a]
             "abba" [\a \b \a]

             [nil nil nil] [nil]
             [1 1.0 1.0M 1N] [1 1.0 1.0M 1N]
             [0.5 0.5] [0.5]))

;; transducers.clj:245 [language]
(deftest test-cat
  (are [x y] (= (transduce cat conj x) y)
             [] []
             [[1 2]] [1 2]
             [[1 2] [3 4]] [1 2 3 4]
             [[] [3 4]] [3 4]
             [[1 2] []] [1 2]
             [[] []] []
             [[1 2] [3 4] [5 6]] [1 2 3 4 5 6]))

;; transducers.clj:255 [language]
(deftest test-partition-all
  (are [n coll y] (= (transduce (partition-all n) conj coll) y)
                  2 [1 2 3] '((1 2) (3))
                  2 [1 2 3 4] '((1 2) (3 4))
                  2 [] ()
                  1 [] ()
                  1 [1 2 3] '((1) (2) (3))
                  5 [1 2 3] '((1 2 3))))

;; transducers.clj:264 [language]
(deftest test-take
  (are [n y] (= (transduce (take n) conj [1 2 3 4 5]) y)
             1 '(1)
             3 '(1 2 3)
             5 '(1 2 3 4 5)
             9 '(1 2 3 4 5)
             0 ()
             -1 ()
             -2 ()))

;; transducers.clj:274 [language]
(deftest test-drop
  (are [n y] (= (transduce (drop n) conj [1 2 3 4 5]) y)
             1 '(2 3 4 5)
             3 '(4 5)
             5 ()
             9 ()
             0 '(1 2 3 4 5)
             -1 '(1 2 3 4 5)
             -2 '(1 2 3 4 5)))

;; transducers.clj:284 [language]
(deftest test-take-nth
  (are [n y] (= (transduce (take-nth n) conj [1 2 3 4 5]) y)
             1 '(1 2 3 4 5)
             2 '(1 3 5)
             3 '(1 4)
             4 '(1 5)
             5 '(1)
             9 '(1)))

;; transducers.clj:293 [language]
(deftest test-take-while
  (are [coll y] (= (transduce (take-while pos?) conj coll) y)
                [] ()
                [1 2 3 4] '(1 2 3 4)
                [1 2 3 -1] '(1 2 3)
                [1 -1 2 3] '(1)
                [-1 1 2 3] ()
                [-1 -2 -3] ()))

;; transducers.clj:302 [language]
(deftest test-drop-while
  (are [coll y] (= (transduce (drop-while pos?) conj coll) y)
                [] ()
                [1 2 3 4] ()
                [1 2 3 -1] '(-1)
                [1 -1 2 3] '(-1 2 3)
                [-1 1 2 3] '(-1 1 2 3)
                [-1 -2 -3] '(-1 -2 -3)))

;; transducers.clj:311 [language]
(deftest test-re-reduced
  (is (= [:a] (transduce (take 1) conj [:a])))
  (is (= [:a] (transduce (comp (take 1) (take 1)) conj [:a])))
  (is (= [:a] (transduce (comp (take 1) (take 1) (take 1)) conj [:a])))
  (is (= [:a] (transduce (comp (take 1) (take 1) (take 1) (take 1)) conj [:a])))
  (is (= [[:a]] (transduce (comp (partition-by keyword?) (take 1)) conj [] [:a])))
  (is (= [[:a]] (sequence (comp (partition-by keyword?) (take 1)) [:a])))
  (is (= [[[:a]]] (sequence (comp (partition-by keyword?) (take 1)  (partition-by keyword?) (take 1)) [:a])))
  (is (= [[0]] (transduce (comp (take 1) (partition-all 3) (take 1)) conj [] (range 15))))
  (is (= [1] (transduce (take 1) conj (seq (long-array [1 2 3 4]))))))

;; transducers.clj:322 [language]
(deftest test-sequence-multi-xform
  (is (= [11 12 13 14] (sequence (map +) [1 2 3 4] (repeat 10))))
  (is (= [11 12 13 14] (sequence (map +) (repeat 10) [1 2 3 4])))
  (is (= [31 32 33 34] (sequence (map +) (repeat 10) (repeat 20) [1 2 3 4]))))

;; transducers.clj:327 [language]
(deftest test-eduction
  (testing "one xform"
    (is (= [1 2 3 4 5]
           (eduction (map inc) (range 5)))))
  (testing "multiple xforms"
    (is (= ["2" "4"]
           (eduction (map inc) (filter even?) (map str) (range 5)))))
  (testing "materialize at the end"
    (is (= [1 1 1 1 2 2 2 3 3 4]
          (->> (range 5)
            (eduction (mapcat range) (map inc))
            sort)))
    (is (= [1 1 2 1 2 3 1 2 3 4]
          (vec (->> (range 5)
                 (eduction (mapcat range) (map inc))
                 to-array))))
    (is (= {1 4, 2 3, 3 2, 4 1}
          (->> (range 5)
            (eduction (mapcat range) (map inc))
            frequencies)))
    (is (= ["drib" "god" "hsif" "kravdraa" "tac"]
          (->> ["cat" "dog" "fish" "bird" "aardvark"]
            (eduction (map clojure.string/reverse))
            (sort-by first)))))
  (testing "expanding transducer with nils"
           (is (= '(1 2 3 nil 4 5 6 nil)
                  (eduction cat [[1 2 3 nil] [4 5 6 nil]])))))

;; transducers.clj:355 [language]
(deftest test-eduction-completion
  (testing "eduction completes inner xformed reducing fn"
    (is (= [[0 1 2] [3 4 5] [6 7]]
           (into []
                 (comp cat (partition-all 3))
                 (eduction (partition-all 5) (range 8))))))
  (testing "outer reducing fn completed only once"
    (let [counter (atom 0)
          ;; outer rfn
          rf      (completing conj #(do (swap! counter inc)
                                        (vec %)))
          coll    (eduction  (map inc) (range 5))
          res     (transduce (map str) rf [] coll)]
      (is (= 1 @counter))
      (is (= ["1" "2" "3" "4" "5"] res)))))

;; transducers.clj:371 [language]
(deftest test-run!
  (is (nil? (run! identity [1])))
  (is (nil? (run! reduced (range)))))

;; transducers.clj:375 [language]
(deftest test-distinct
  (are [out in] (= out (sequence (distinct in)) (sequence (distinct) in))
       [] []
       (range 10) (range 10)
       [0] (repeat 10 0)
       [0 1 2] [0 0 1 1 2 2 1 1 0 0]
       [1] [1 1N]))

;; transducers.clj:383 [language]
(deftest test-interpose
  (are [out in] (= out (sequence (interpose :s) in))
       [] (range 0)
       [0] (range 1)
       [0 :s 1] (range 2)
       [0 :s 1 :s 2] (range 3))
  (testing "Can end reduction on separator or input"
    (let [expected (interpose :s (range))]
      (dotimes [i 10]
        (is (= (take i expected)
          (sequence (comp (interpose :s) (take i))
                    (range))))))))

;; transducers.clj:396 [language]
(deftest test-map-indexed
  (is (= []
         (sequence (map-indexed vector) [])))
  (is (= [[0 1] [1 2] [2 3] [3 4]]
         (sequence (map-indexed vector) (range 1 5)))))

;; transducers.clj:402 [language]
(deftest test-into+halt-when
  (is (= :anomaly (into [] (comp (filter some?) (halt-when #{:anomaly}))
                        [1 2 3 :anomaly 4])))
  (is (= {:anomaly :oh-no!,
          :partial-results [1 2]}
         (into []
               (halt-when :anomaly #(assoc %2 :partial-results %1))
               [1 2 {:anomaly :oh-no!} 3 4]))))
