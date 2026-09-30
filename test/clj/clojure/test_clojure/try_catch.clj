;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

; Author: Paul M Bauer 

(ns clojure.test-clojure.try-catch
  (:use clojure.test)
  (:import [clojure.test ReflectorTryCatchFixture 
                         ReflectorTryCatchFixture$Cookies]))

(defn- get-exception [expression]
  (try (eval expression)
    nil
    (catch clotran.host.throwable t
      t)))

(deftest catch-receives-checked-exception-from-eval
  (are [expression expected-exception] (= expected-exception
                                          (type (get-exception expression)))
    "Eh, I'm pretty safe" nil
    '(clotran.host.file_reader. "CAFEBABEx0/idonotexist") clotran.host.file_not_found_exception))


(defn fail [x]
  (ReflectorTryCatchFixture/fail x))

(defn make-instance []
  (ReflectorTryCatchFixture.))

(deftest catch-receives-checked-exception-from-reflective-call
  (is (thrown-with-msg? ReflectorTryCatchFixture$Cookies #"Long" (fail 1)))
  (is (thrown-with-msg? ReflectorTryCatchFixture$Cookies #"Double" (fail 1.0)))
  (is (thrown-with-msg? ReflectorTryCatchFixture$Cookies #"Wrapped"
        (.failWithCause (make-instance) 1.0))))
