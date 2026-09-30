;; DERIVED from upstream/clojure/test/clojure/test_clojure/protocols.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.protocols (:use clojure.test clojure.test-clojure.protocols.examples) (:require [clojure.test-clojure.protocols.more-examples :as other] [clojure.set :as set] clojure.test-helper))

(defrecord EmptyRecord [])

(defrecord TestRecord [a b])

(deftype ExtendTestWidget [name])

(deftype ExtendersTestWidget [])

(deftype ReExtendingTestWidget [])

(defrecord DefrecordObjectMethodsWidgetA [a])

(defrecord DefrecordObjectMethodsWidgetB [a])

(defrecord RecordWithSpecificFieldNames [this that k m o])

(defrecord RecordToTestStatics1 [a])

(defrecord RecordToTestStatics2 [a b])

(defrecord RecordToTestStatics3 [a b c])

(defrecord RecordToTestBasis [a b c])

(defrecord TypeToTestBasis [a b c])

(defrecord RecordToTestFactories [a b c])

(defrecord RecordToTestA [a])

(defrecord RecordToTestB [b])

(defrecord RecordToTestDegenerateFactories [])

(deftype TypeToTestFactory [a])

(defrecord RecordToTestLiterals [a])

(deftype TypeToTestLiterals [a])

(def lang-str "en")

(defrecord RecordToTestPrinting [a b])

(defrecord RecordToTest__ [__a ___b])

(defrecord TypeToTest__   [__a ___b])

(defrecord RecordToTestLongHint [^long a])

(defrecord RecordToTestByteHint [^byte a])

(defrecord RecordToTestBoolHint [^boolean a])

(deftype TypeToTestLongHint [^long a])

(deftype TypeToTestByteHint [^byte a])

;; protocols.clj:262 [language]
(deftest defrecord-with-specific-field-names
  (let [rec (new RecordWithSpecificFieldNames 1 2 3 4 5)]
    (is (= rec rec))
    (is (= 1 (:this (with-meta rec {:foo :bar}))))
    (is (= 3 (get rec :k)))
    (is (= (seq rec) '([:this 1] [:that 2] [:k 3] [:m 4] [:o 5])))
    (is (= (dissoc rec :k) {:this 1, :that 2, :m 4, :o 5}))))

;; protocols.clj:680 [language]
(deftest test-base-reduce-kv
  (is (= {1 :a 2 :b}
         (reduce-kv #(assoc %1 %3 %2)
                    {}
                    (seq {:a 1 :b 2})))))
