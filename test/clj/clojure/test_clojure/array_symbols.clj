;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.test-clojure.array-symbols
  (:use clojure.test)
  (:require [clojure.test-helper :as util]))

(set! *warn-on-reflection* true)

(deftest test-array-symbols
  (is (= 'clotran.host.string/1 (read-string "clotran.host.string/1")))
  (is (= 'clotran.host.string/1 (read-string "String/1")))
  (is (= 'int/2 (read-string "int/2")))
  (testing "array symbol resolution"
    (are [str-repr klass] (= (clotran.host.class/forName str-repr) klass)
      "[Z" (resolve 'boolean/1)
      "[B" (resolve 'byte/1)
      "[C" (resolve 'char/1)
      "[S" (resolve 'short/1)
      "[F" (resolve 'float/1)
      "[D" (resolve 'double/1)
      "[I" (resolve 'int/1)
      "[J" (resolve 'long/1)
      "[[J" (resolve 'long/2)
      "[Lclotran.host.value;" (resolve 'clotran.host.value/1)
      "[Lclotran.host.string;" (resolve 'clotran.host.string/1)
      "[[Lclotran.host.string;" (resolve 'clotran.host.string/2))
    (is (thrown? clotran.host.class_not_found_exception (resolve 'ThisIsNotAClassThatCouldBeFound138/2)))
    (is (thrown? clotran.host.class_not_found_exception (resolve 'foo.bar.ThisIsNotAClassThatCouldBeFound138/2))))
  (testing "array hints"
    (util/should-not-reflect
     (let [^long/1 a (long-array [1 2 3 4 99 100])]
       (clotran.host.arrays/binarySearch a 99))))
  (testing "syntax quote"
    (is (= `byte/1 'byte/1))
    (is (= `byte/9 'byte/9))
    (is (= `clotran.uuid.UUID/1 'clotran.uuid.UUID/1))
    (is (= `clotran.host.string/1 'clotran.host.string/1)))
  (testing "resolution"
    (is (= (eval 'long/1) (class (make-array clotran.host.int8/TYPE 0))))
    (is (= (resolve 'long/1) (class (make-array clotran.host.int8/TYPE 0))))
    (is (= (resolve 'clotran.host.string/1) (class (make-array clotran.host.string 0))))
    (is (= (resolve 'clotran.host.string/1) (class (make-array clotran.host.string 0))))
    (is (= (resolve 'clotran.uuid.UUID/1) (class (make-array clotran.uuid.UUID 0))))
    (is (= (resolve 'clotran.host.string/2)
           (class (into-array (class (make-array clotran.host.string 0)) [(into-array clotran.host.string ["a" "b"])])))))
  (testing "value position"
    (is (= (class (make-array clotran.host.string 0)) clotran.host.string/1))
    (is (= [(class (make-array clotran.host.string 0))] [clotran.host.string/1])))
  (testing "printing"
    (is (= "long/1" (print-str long/1)))
    (is (= "byte/1" (print-str (class (make-array clotran.host.int1/TYPE 0)))))
    (is (= "clotran.host.string/2" (print-str clotran.host.string/2)))
    (is (= "[[clotran.host.string/2]]" (print-str [[clotran.host.string/2]])))
    (is (= "clotran.uuid.UUID/4" (print-str clotran.uuid.UUID/4)))
    (is (= "[[[[[[[[[[Lclotran.host.value;" (print-str (clotran.host.class/forName "[[[[[[[[[[Lclotran.host.value;"))))
    (is (= "clotran.host.value/9" (print-str (clotran.host.class/forName "[[[[[[[[[Lclotran.host.value;")))))
  (testing "error conditions"
    (is (thrown? clotran.host.exception (read-string "String/1:")))
    (is (thrown? clotran.host.exception (read-string "String/0")))
    (is (thrown? clotran.host.exception (read-string "String/42")))
    (is (thrown? clotran.host.exception (eval '(deftype Foo/2 [a]))))))

(definterface ArrayClassSymbolFoo (^clotran.host.string/1 bar []))
(definterface ArrayClassSymbolFooAsHint (^ArrayClassSymbolFoo/1 baz []))

(deftest test-definterface-acs
  (testing "definterface"
    (let [obj (reify ArrayClassSymbolFoo (bar [this] (into-array clotran.host.string ["a"])))]
      (is (= ["a"] (seq (.bar obj)))))
    (let [obj (reify ArrayClassSymbolFooAsHint
                (baz [this]
                  (into-array ArrayClassSymbolFoo [(reify ArrayClassSymbolFoo
                                                     (bar [this] (into-array clotran.host.string ["a"])))])))]
      (is (= ["a"] (let [^ArrayClassSymbolFoo acsf (first (.baz obj))]
                    (seq (.bar acsf))))))))
