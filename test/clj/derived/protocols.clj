;; DERIVED from test/clj/clojure/test_clojure/protocols.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.protocols (:use clojure.test clojure.test-clojure.protocols.examples) (:require [clojure.test-clojure.protocols.more-examples :as other] [clojure.set :as set] clojure.test-helper))

(defrecord EmptyRecord [])

(defrecord TestRecord [a b])

(defrecord MapEntry [k v]
  java.util.Map$Entry
  (getKey [_] k)
  (getValue [_] v))

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

(defrecord RecordToTestBasisHinted [^String a ^Long b c])

(defrecord RecordToTestHugeBasis [a b c d e f g h i j k l m n o p q r s t u v w x y z])

(defrecord TypeToTestBasis [a b c])

(defrecord TypeToTestBasisHinted [^String a ^Long b c])

(defrecord RecordToTestFactories [a b c])

(defrecord RecordToTestA [a])

(defrecord RecordToTestB [b])

(defrecord RecordToTestHugeFactories [a b c d e f g h i j k l m n o p q r s t u v w x y z])

(defrecord RecordToTestDegenerateFactories [])

(deftype TypeToTestFactory [a])

(defrecord TypeToTestHugeFactories [a b c d e f g h i j k l m n o p q r s t u v w x y z])

(defrecord RecordToTestLiterals [a])

(defrecord TestNode [v l r])

(deftype TypeToTestLiterals [a])

(def lang-str "en")

(defrecord RecordToTestPrinting [a b])

(defrecord RecordToTest__ [__a ___b])

(defrecord TypeToTest__   [__a ___b])

(defrecord RecordToTestLongHint [^long a])

(defrecord RecordToTestByteHint [^byte a])

(defrecord RecordToTestBoolHint [^boolean a])

(defrecord RecordToTestCovariantHint [^String a]) ;; same for arrays also

(deftype TypeToTestLongHint [^long a])

(deftype TypeToTestByteHint [^byte a])

(defprotocol SyntaxQuoteTestProtocol
  (sqtp [p]))

(defmacro try-extend-type [c]
  `(extend-type ~c
     SyntaxQuoteTestProtocol
     (sqtp [p#] p#)))

(defmacro try-extend-protocol [c]
  `(extend-protocol SyntaxQuoteTestProtocol
     ~c
     (sqtp [p#] p#)))

(try-extend-protocol clojure.lang.Keyword)

(defprotocol Dasherizer
  (-do-dashed [this]))

(deftype Dashed []
  Dasherizer
  (-do-dashed [this] 10))

(defn aget-long-hinted ^long [x] (aget (longs-hinted x) 0))

(import 'clojure.lang.ISeq)

(defprotocol P
  (^ISeq f [_]))

(defprotocol PrimHinted
  (^double f1 [p a])
  (^void f2 [p]))

;; protocols.clj:262 [language]
(deftest defrecord-with-specific-field-names
  (let [rec (new RecordWithSpecificFieldNames 1 2 3 4 5)]
    (is (= rec rec))
    (is (= 1 (:this (with-meta rec {:foo :bar}))))
    (is (= 3 (get rec :k)))
    (is (= (seq rec) '([:this 1] [:that 2] [:k 3] [:m 4] [:o 5])))
    (is (= (dissoc rec :k) {:this 1, :that 2, :m 4, :o 5}))))

;; protocols.clj:663 [language]
(deftest test-no-ns-capture
  (is (= "foo" (sqtp "foo")))
  (is (= :foo (sqtp :foo))))

;; protocols.clj:680 [language]
(deftest test-base-reduce-kv
  (is (= {1 :a 2 :b}
         (reduce-kv #(assoc %1 %3 %2)
                    {}
                    (seq {:a 1 :b 2})))))

;; protocols.clj:715 [language]
(deftest test-prim-ret-hints-ignored
  (is (thrown-with-msg?
       Exception
       #"Receiver class"
       (eval '(f1 (reify PrimHinted) :foo))))
  (is (= :foo  (f1 (reify PrimHinted (f1 [_ x] x)) :foo)))
  (is (= "foo" (f2 (reify PrimHinted (f2 [_] "foo"))))))
