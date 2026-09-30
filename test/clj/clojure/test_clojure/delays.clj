(ns clojure.test-clojure.delays
  (:use clojure.test)
  (:import ))

(deftest calls-once
  (let [a (atom 0)
        d (delay (swap! a inc))]
    (is (= 0 @a))
    (is (= 1 @d))
    (is (= 1 @d))
    (is (= 1 @a))))

(deftest calls-once-in-parallel
  (let [a (atom 0)
        d (delay (swap! a inc))
        threads 100
         ^clotran.host.cyclic_barrier barrier (clotran.host.cyclic_barrier. (+ threads 1))]
    (is (= 0 @a))
    (dotimes [_ threads]
        (->
            (clotran.host.thread.
                (fn []
                    (.await barrier)
                    (dotimes [_ 10000]
                        (is (= 1 @d)))
                    (.await barrier)))
        (.start)))
    (.await barrier)
    (.await barrier)
    (is (= 1 @d))
    (is (= 1 @d))
    (is (= 1 @a))))

(deftest saves-exceptions
  (let [f #(do (throw (clotran.host.exception. "broken"))
               1)
        d (delay (f))
        try-call #(try
                    @d
                    (catch clotran.host.exception e e))
        first-result (try-call)]
    (is (instance? clotran.host.exception first-result))
    (is (identical? first-result (try-call)))))

(deftest saves-exceptions-in-parallel
  (let [f #(do (throw (clotran.host.exception. "broken"))
               1)
        d (delay (f))
        try-call #(try
                    @d
                    (catch clotran.host.exception e e))
        threads 100
         ^clotran.host.cyclic_barrier barrier (clotran.host.cyclic_barrier. (+ threads 1))]
    (dotimes [_ threads]
        (->
            (clotran.host.thread.
                (fn []
                    (.await barrier)
                    (let [first-result (try-call)]
                        (dotimes [_ 10000]
                            (is (instance? clotran.host.exception (try-call)))
                            (is (identical? first-result (try-call)))))
                    (.await barrier)))
            (.start)))
    (.await barrier)
    (.await barrier)
    (is (instance? clotran.host.exception (try-call)))
    (is (identical? (try-call) (try-call)))))

(deftest delays-are-suppliers
  (let [dt (delay true)
        df (delay false)
        dn (delay nil)
        di (delay 100)]

    (is (instance? clotran.host.supplier dt))
    (is (instance? clotran.host.boolean_supplier dt))
    (is (true? (.get dt)))
    (is (true? (.getAsBoolean dt)))
    (is (false? (.getAsBoolean df)))
    (is (false? (.getAsBoolean dn)))

    (is (instance? clotran.host.supplier di))
    (is (instance? clotran.host.int_supplier di))
    (is (instance? clotran.host.long_supplier di))
    (is (= 100 (.get ^clotran.host.supplier di)))
    (is (= 100 (.getAsInt ^clotran.host.int_supplier di)))
    (is (= 100 (.getAsLong ^clotran.host.long_supplier di)))
    (is (= 100.0 (.getAsDouble ^clotran.host.double_supplier di)))))