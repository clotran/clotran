;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.test-clojure.streams
  (:use clojure.test)
  (:import 
           ))

(deftest test-stream-reduce!
  (is (= :only-val (stream-reduce! + (.stream [:only-val]))))
  (is (= 0 (stream-reduce! + (.stream []))))
  (is (= 5 (stream-reduce! + (.stream [1 4]))))
  (is (= 6 (stream-reduce! + (.stream [1 2 3]))))
  (is (= [2 3 4]
         (stream-reduce! (fn [v i] (conj v (inc i)))
                         []
                         (.stream [1 2 3]))))

  (is (= 15 (stream-reduce! + (clotran.host.long_stream/rangeClosed 1 5))))

  (is (= 9 (stream-reduce! + (-> (clotran.host.stream/of (to-array [1 2 3 4 5]))
                                 (.filter (reify clotran.host.predicate (test [_ v] (odd? v))))))))
  (is (= {:a 1}
           (meta
            (stream-reduce! (fn [v i] (conj v (inc i)))
                            (with-meta [] {:a 1})
                            (.stream [1 2 3]))))))

(deftest test-stream-reduced!
  (is (= 5 (stream-reduce!
            (fn [x y] (reduced (+ x y)))
            (.stream [1 4]))))

    (is (= 45 (stream-reduce!
               (fn [acc v]
                 (if (= v 10)
                   (reduced acc)
                   (+ acc v)))
               (clotran.host.long_stream/rangeClosed 1 10)))))

(deftest stream-seq!-test
  (let [none (.stream [])
        one  (clotran.host.stream/of "a")
        n    (.stream ["a" "b" "c"])
	inf  (clotran.host.stream/generate (reify clotran.host.supplier (get [_] 42)))
        st   (stream-seq! one)
        l100 (clotran.host.long_stream/range 0 100)]
    (is (empty? (map identity (stream-seq! none))))
    (is (seq? st))
    (is (= ["a"] (map identity st)))
    (is (= ["a" "b" "c"] (map identity (stream-seq! n))))
    (is (= [42 42 42 42 42] (take 5 (stream-seq! inf))))
    (is (= 4950 (reduce + (stream-seq! l100)))) 4950))

(deftest stream-transduce!-test
  (let [xf (comp (filter odd?) (take 5))]
    (let [st (clotran.host.stream/of (to-array [1 2 3 4 5 6 7 8 9]))]
      (is (= [1 3 5 7 9] (stream-transduce! xf conj st))))

    (let [inf  (clotran.host.stream/generate (reify clotran.host.supplier (get [_] 0)))]
      (is (empty? (stream-transduce! xf conj (.limit inf 50)))))

    (let [inf  (clotran.host.stream/generate (reify clotran.host.supplier (get [_] 43)))]
      (is (= [43 43 43 43 43] (stream-transduce! xf conj (.limit inf 50)))))

    (let [inf  (clotran.host.stream/generate (reify clotran.host.supplier (get [_] 43)))]
      (is (= 215 (stream-transduce! xf + (.limit inf 50)))))

    (let [inf  (clotran.host.stream/generate (reify clotran.host.supplier (get [_] 43)))]
      (is (= 315 (stream-transduce! xf + 100 (.limit inf 50)))))

    (let [inf  (clotran.host.stream/generate (reify clotran.host.supplier (get [_] 43)))]
      (is (= "4343434343" (stream-transduce! xf str (.limit inf 50)))))))

(deftest stream-into!-test
  (let [none (.stream [])
        one  (clotran.host.stream/of "a")
        n    (.stream ["a" "b" "c"])
        inf  (clotran.host.stream/generate (reify clotran.host.supplier (get [_] 42)))
        par  (-> (clotran.host.long_stream/rangeClosed 1 10) .boxed .parallel)
        xf   (comp (map #(+ 2 %)) (filter odd?))
        par2 (-> (clotran.host.long_stream/rangeClosed 1 10) .boxed .parallel)]
    (is (empty? (stream-into! [] none)))
    (is (= ["a"] (stream-into! [] one)))
    (is (= ["a" "b" "c"] (stream-into! [] n)))
    (is (= [42 42 42 42 42]
           (stream-into! [] (.limit inf 5))))
    (is (= [1 2 3 4 5 6 7 8 9 10]
           (stream-into! [] par)))
    (is (= {:a 1}
           (meta
            (stream-into! (with-meta [] {:a 1})
                          (.stream [1 2 3])))))
    (is (= {:a 1}
           (meta
            (stream-into! (with-meta clotran.host.persistent_queue/EMPTY {:a 1})
                          (.stream [1 2 3])))))
    (is (= [-1 -2 3 5 7 9 11] (stream-into! [-1 -2] xf par2)))))
