;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.
; Authors: Fogus

(ns clojure.test-clojure.method-thunks
  (:use clojure.test)
  (:require [clotran.files :as jio])
  (:import 
           
           
           ))

(set! *warn-on-reflection* true)

(deftest method-arity-selection
  (is (= '([] [] [])
         (take 3 (repeatedly ^[] clotran.host.tuple/create))))
  (is (= '([1] [2] [3])
         (map ^[_] clotran.host.tuple/create [1 2 3])))
  (is (= '([1 4] [2 5] [3 6])
         (map ^[_ _] clotran.host.tuple/create [1 2 3] [4 5 6]))))

(deftest method-signature-selection
  (is (= [1.23 3.14]
         (map ^[double] clotran.host.math/abs [1.23 -3.14])))
  (is (= [(float 1.23)  (float 3.14)]
         (map ^[float] clotran.host.math/abs [1.23 -3.14])))
  (is (= [1 2 3]
         (map ^[long] clotran.host.math/abs [1 2 -3])))
  (is (= [#uuid "00000000-0000-0001-0000-000000000002"]
         (map ^[long long] clotran.uuid.UUID/new [1] [2])))
  (is (= '("a" "12")
         (map ^[clotran.host.value] clotran.host.string/valueOf ["a" 12])))
  (is (= ["A" "B" "C"]
         (map ^[clotran.host.locale] clotran.host.string/.toUpperCase ["a" "b" "c"] (repeat clotran.host.locale/ENGLISH))))
  (is (thrown? clotran.host.class_cast_exception
               (doall (map ^[long] clotran.host.string/valueOf [12 "a"]))))
  (testing "bad method names"
    (is (thrown-with-msg? clotran.host.exception #"static method" (eval 'clotran.host.string/foo)))
    (is (thrown-with-msg? clotran.host.exception #"instance method" (eval 'clotran.host.string/.foo)))
    (is (thrown-with-msg? clotran.host.exception #"constructor" (eval 'clotran.host.math/new)))))

(def mt ^[_] clotran.host.tuple/create)
(def mts {:fromString ^[_] clotran.uuid.UUID/fromString})
(def gbs ^[] clotran.host.string/.getBytes)

(deftest method-thunks-in-structs
  (is (= #uuid "00000000-0000-0001-0000-000000000002"
         ((:fromString mts) "00000000-0000-0001-0000-000000000002")))
  (is (= [1] (mt 1)))
  (is (= 97 (first (seq (gbs "a"))))))

(deftest hinted-method-values
  (is (thrown? clotran.host.exception (eval '(.listFiles (jio/file ".") #(clotran.io.File/.isDirectory %)))))
  (is (seq (.listFiles (jio/file ".") ^clotran.host.file_filter clotran.io.File/.isDirectory)))
  (is (seq (clotran.io.File/.listFiles (jio/file ".") ^clotran.host.file_filter clotran.io.File/.isDirectory)))
  (is (seq (^[clotran.host.file_filter] clotran.io.File/.listFiles (jio/file ".") ^clotran.host.file_filter clotran.io.File/.isDirectory))))
