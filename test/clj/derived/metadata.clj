;; DERIVED from upstream/clojure/test/clojure/test_clojure/metadata.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.metadata (:use clojure.test [clojure.test-helper :only (eval-in-temp-ns)]) (:require [clojure.set :as set]))



;; metadata.clj:100 [language]
 (deftest fns-preserve-metadata-on-maps
   (let [xm {:a 1 :b -7}
         x (with-meta {:foo 1 :bar 2} xm)
         ym {:c "foo"}
         y (with-meta {:baz 4 :guh x} ym)]
 
     (is (= xm (meta (:guh y))))
     (is (= xm (meta (reduce #(assoc %1 %2 (inc %2)) x (range 1000)))))
     (is (= xm (meta (-> x (dissoc :foo) (dissoc :bar)))))
     (let [z (assoc-in y [:guh :la] 18)]
       (is (= ym (meta z)))
       (is (= xm (meta (:guh z)))))
     (let [z (update-in y [:guh :bar] inc)]
       (is (= ym (meta z)))
       (is (= xm (meta (:guh z)))))
     (is (= xm (meta (get-in y [:guh]))))
     (is (= xm (meta (into x y))))
     (is (= ym (meta (into y x))))
     
     (is (= xm (meta (merge x y))))
     (is (= ym (meta (merge y x))))
     (is (= xm (meta (merge-with + x y))))
     (is (= ym (meta (merge-with + y x))))
 
     (is (= xm (meta (select-keys x [:bar]))))
     (is (= xm (meta (set/rename-keys x {:foo :new-foo}))))
 
     ;; replace returns a seq when given a set.  Can seqs have
     ;; metadata?
     
     ;; TBD: rseq, subseq, and rsubseq returns seqs.  If it is even
     ;; possible to put metadata on a seq, does it make sense that the
     ;; seqs returned by these functions should have the same metadata
     ;; as the sorted collection on which they are called?
     ))

;; metadata.clj:136 [language]
 (deftest fns-preserve-metadata-on-vectors
   (let [xm {:a 1 :b -7}
         x (with-meta [1 2 3] xm)
         ym {:c "foo"}
         y (with-meta [4 x 6] ym)]
 
     (is (= xm (meta (y 1))))
     (is (= xm (meta (assoc x 1 "one"))))
     (is (= xm (meta (reduce #(conj %1 %2) x (range 1000)))))
     (is (= xm (meta (pop (pop (pop x))))))
     (let [z (assoc-in y [1 2] 18)]
       (is (= ym (meta z)))
       (is (= xm (meta (z 1)))))
     (let [z (update-in y [1 2] inc)]
       (is (= ym (meta z)))
       (is (= xm (meta (z 1)))))
     (is (= xm (meta (get-in y [1]))))
     (is (= xm (meta (into x y))))
     (is (= ym (meta (into y x))))
 
     (is (= xm (meta (replace {2 "two"} x))))
     (is (= [1 "two" 3] (replace {2 "two"} x)))
 
     ;; TBD: Currently subvec drops metadata.  Should it preserve it?
     ;;(is (= xm (meta (subvec x 2 3))))
 
     ;; TBD: rseq returns a seq.  If it is even possible to put
     ;; metadata on a seq, does it make sense that the seqs returned by
     ;; these functions should have the same metadata as the sorted
     ;; collection on which they are called?
     ))

;; metadata.clj:168 [language]
 (deftest fns-preserve-metadata-on-sets
   ;; TBD: Do tests independently for set, hash-set, and sorted-set,
   ;; perhaps with a loop here.
   (let [xm {:a 1 :b -7}
         x (with-meta #{1 2 3} xm)
         ym {:c "foo"}
         y (with-meta #{4 x 6} ym)]
 
     (is (= xm (meta (y #{3 2 1}))))
     (is (= xm (meta (reduce #(conj %1 %2) x (range 1000)))))
     (is (= xm (meta (-> x (disj 1) (disj 2) (disj 3)))))
     (is (= xm (meta (into x y))))
     (is (= ym (meta (into y x))))
 
     (is (= xm (meta (set/select even? x))))
     (let [cow1m {:what "betsy cow"}
           cow1 (with-meta {:name "betsy" :id 33} cow1m)
           cow2m {:what "panda cow"}
           cow2 (with-meta {:name "panda" :id 34} cow2m)
           cowsm {:what "all the cows"}
           cows (with-meta #{cow1 cow2} cowsm)
           cow-names (set/project cows [:name])
           renamed (set/rename cows {:id :number})]
       (is (= cowsm (meta cow-names)))
       (is (= cow1m (meta (first (filter #(= "betsy" (:name %)) cow-names)))))
       (is (= cow2m (meta (first (filter #(= "panda" (:name %)) cow-names)))))
       (is (= cowsm (meta renamed)))
       (is (= cow1m (meta (first (filter #(= "betsy" (:name %)) renamed)))))
       (is (= cow2m (meta (first (filter #(= "panda" (:name %)) renamed))))))
 
     ;; replace returns a seq when given a set.  Can seqs have
     ;; metadata?
 
     ;; union: Currently returns the metadata of the largest input set.
     ;; This is an artifact of union's current implementation.  I doubt
     ;; any explicit design decision was made to do so.  Like join,
     ;; there doesn't seem to be much reason to prefer the metadata of
     ;; one input set over another, if at least two input sets are
     ;; given, but perhaps defining it to always return a set with the
     ;; metadata of the first input set would be reasonable?
 
     ;; intersection: Returns metadata of the smallest input set.
     ;; Otherwise similar to union.
 
     ;; difference: Seems to always return a set with metadata of first
     ;; input set.  Seems reasonable.  Not sure we want to add a test
     ;; for it, if it is an accident of the current implementation.
 
     ;; join, index, map-invert: Currently always returns a value with
     ;; no metadata.  This seems reasonable.
     ))
