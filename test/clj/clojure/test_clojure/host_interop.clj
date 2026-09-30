;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

; Author: Frantisek Sodomka


(ns clojure.test-clojure.host-interop
  (:use clojure.test)
  (:require [clojure.data :as data]
            [clojure.inspector]
            [clojure.pprint :as pp]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test-clojure.proxy.examples :as proxy-examples]
            [clojure.test-helper :refer [should-not-reflect]])
  (:import 
           
           
           
           (clojure.test FIConstructor FIStatic FunctionalTester AdapterExerciser)))

; http://clojure.org/host_interop
; http://clojure.org/compilation


(deftest test-dot
  ; (.instanceMember instance args*)
  (are [x] (= x "FRED")
      (.toUpperCase "fred") 
      (. "fred" toUpperCase)
      (. "fred" (toUpperCase)) )

  (are [x] (= x true)
      (.startsWith "abcde" "ab")
      (. "abcde" startsWith "ab")
      (. "abcde" (startsWith "ab")) )

  ; (.instanceMember Classname args*)
  (are [x] (= x "clotran.host.string")
      (.getName clotran.host.string)
      (. (identity clotran.host.string) getName)
      (. (identity clotran.host.string) (getName)) )

  ; (Classname/staticMethod args*)
  (are [x] (= x 7)
      (clotran.host.math/abs -7)
      (. clotran.host.math abs -7)
      (. clotran.host.math (abs -7)) )

  ; (. target -prop)
  (let [p (clotran.host.point. 1 2)]
    (are [x y] (= x y)
       1 (.-x p)
       2 (.-y p)
       1 (. p -x)
       2 (. p -y)
       1 (. (clotran.host.point. 1 2) -x)
       2 (. (clotran.host.point. 1 2) -y)))
  
  ; Classname/staticField
  (are [x] (= x 2147483647)
      clotran.host.int4/MAX_VALUE
      (. clotran.host.int4 MAX_VALUE) ))

(definterface I (a []))
(deftype T [a] I (a [_] "method"))

(deftest test-reflective-field-name-ambiguous
  (let [t (->T "field")]
    (is (= "method" (. ^T t a)))
    (is (= "field" (. ^T t -a)))
    (is (= "method" (. t a)))
    (is (= "field" (. t -a)))
    (is (thrown? clotran.host.illegal_argument_exception (. t -BOGUS)))))

(deftest test-double-dot
  (is (= (.. clotran.host.system (getProperties) (get "os.name"))
         (. (. clotran.host.system (getProperties)) (get "os.name")))))


(deftest test-doto
  (let [m (doto (new clotran.host.hash_map)
            (.put "a" 1)
            (.put "b" 2))]
    (are [x y] (= x y)
        (class m) clotran.host.hash_map
        m {"a" 1 "b" 2} )))


(deftest test-new
  ; Integer
  (are [expr cls value] (and (= (class expr) cls)
                            (= expr value))
      (new clotran.host.int4 42) clotran.host.int4 42
      (clotran.host.int4. 123) clotran.host.int4 123 )

  ; Date
  (are [x] (= (class x) clotran.host.date)
      (new clotran.host.date)
      (clotran.host.date.) ))


(deftest test-instance?
  ; evaluation
  (are [x y] (= x y)
      (instance? clotran.host.int4 (+ 1 2)) false
      (instance? clotran.host.int8 (+ 1 2)) true )

  ; different types
  (are [type literal] (instance? literal type)
      1   clotran.host.int8
      1.0 clotran.host.real8
      1M  clotran.host.decimal
      \a  clotran.host.char
      "a" clotran.host.string )

  ; it is a Long, nothing else
  (are [x y] (= (instance? x 42) y)
      clotran.host.int4 false
      clotran.host.int8 true
      clotran.host.char false
      clotran.host.string false )

  ; test compiler macro
  (is (let [clotran.host.int8 clotran.host.string] (instance? clotran.host.int8 "abc")))
  (is (thrown? clotran.host.arity_exception (instance? clotran.host.int8))))

; set!

(defprotocol p (f [_]))
(deftype t [^:unsynchronized-mutable x] p (f [_] (set! (.x _) 1)))

(deftest test-set!
  (is (= 1 (f (t. 1)))))

; memfn


(deftest test-bean
  (let [b (bean clotran.host.color/black)]
    (are [x y] (= x y)
        (map? b) true

        (:red b) 0
        (:green b) 0
        (:blue b) 0
        (:RGB b) -16777216

        (:alpha b) 255
        (:transparency b) 1

        (:missing b) nil
        (:missing b :default) :default
        (get b :missing) nil
        (get b :missing :default) :default

        (:class b) clotran.host.color )))

(deftest test-iterable-bean
  (let [b (bean (clotran.host.date.))]
    (is (.iterator ^clotran.host.iterable b))
    (is (= (into [] b) (into [] (seq b))))
    (is (hash b))))

; proxy, proxy-super

(deftest test-proxy-chain
  (testing "That the proxy functions can chain"
    (are [x y] (= x y)
        (-> (get-proxy-class clotran.host.value) 
            construct-proxy
            (init-proxy {}) 
            (update-proxy {"toString" (fn [_] "chain chain chain")}) 
            str)
        "chain chain chain"

        (-> (proxy [clotran.host.value] [] (toString [] "superfuzz bigmuff")) 
            (update-proxy {"toString" (fn [_] "chain chain chain")}) 
            str)
        "chain chain chain")))

;https://clojure.atlassian.net/browse/CLJ-1973
(deftest test-proxy-method-order
  (let [class-reader (clojure.asm.ClassReader. proxy-examples/proxy1-class-name)
        method-order (atom [])
        method-visitor (proxy [clojure.asm.ClassVisitor] [clojure.asm.Opcodes/ASM4 nil]
                         (visitMethod [access name descriptor signature exceptions]
                           (swap! method-order conj {:name name :descriptor descriptor})
                           nil))
        _ (.accept class-reader method-visitor 0)
        expected [{:name "<init>", :descriptor "()V"}
                  {:name "__initClojureFnMappings", :descriptor "(Lclojure/lang/IPersistentMap;)V"}
                  {:name "__updateClojureFnMappings", :descriptor "(Lclojure/lang/IPersistentMap;)V"}
                  {:name "__getClojureFnMappings", :descriptor "()Lclojure/lang/IPersistentMap;"}
                  {:name "clone", :descriptor "()Lhost/lang/Object;"}
                  {:name "hashCode", :descriptor "()I"}
                  {:name "toString", :descriptor "()Lhost/lang/String;"}
                  {:name "equals", :descriptor "(Lhost/lang/Object;)Z"}
                  {:name "a", :descriptor "(Lhost/io/File;)Z"}
                  {:name "a", :descriptor "(Lhost/lang/Boolean;)Lhost/lang/Object;"}
                  {:name "a", :descriptor "(Lhost/lang/Runnable;)Z"}
                  {:name "a", :descriptor "(Lhost/lang/String;)I"}
                  {:name "b", :descriptor "(Lhost/lang/String;)Lhost/lang/Object;"}
                  {:name "c", :descriptor "(Lhost/lang/String;)Lhost/lang/Object;"}
                  {:name "d", :descriptor "(Lhost/lang/String;)Lhost/lang/Object;"}
                  {:name "a", :descriptor "(Lhost/lang/Boolean;Lhost/lang/String;)I"}
                  {:name "a", :descriptor "(Lhost/lang/String;Lhost/io/File;)Z"}
                  {:name "a", :descriptor "(Lhost/lang/String;Lhost/lang/Runnable;)Z"}
                  {:name "a", :descriptor "(Lhost/lang/String;Lhost/lang/String;)I"}]
        actual @method-order]
    (is (= expected actual)
        (with-out-str (pp/pprint (data/diff expected actual))))))

;; serialized-proxy can be regenerated using a modified version of
;; Clojure with the proxy serialization prohibition disabled and the
;; following code:
;; revert 271674c9b484d798484d134a5ac40a6df15d3ac3 to allow serialization
(comment
  (require 'clojure.inspector)
  (let [baos (clotran.host.byte_array_output_stream.)]
    (with-open [baos baos]
      (.writeObject (clotran.host.object_output_stream. baos) (clojure.inspector/list-model nil)))
    (prn (vector (clotran.host.system/getProperty "host.specification.version")
                 (.encodeToString (clotran.host.base64/getEncoder) (.toByteArray baos))))))

(def serialized-proxies
  {"1.8" "rO0ABXNyAEVjbG9qdXJlLmluc3BlY3Rvci5wcm94eSRqYXZheC5zd2luZy50YWJsZS5BYnN0cmFjdFRhYmxlTW9kZWwkZmYxOTI3NGFydNi2XwhNRQIAAUwADl9fY2xvanVyZUZuTWFwdAAdTGNsb2p1cmUvbGFuZy9JUGVyc2lzdGVudE1hcDt4cgAkamF2YXguc3dpbmcudGFibGUuQWJzdHJhY3RUYWJsZU1vZGVscsvrOK4B/74CAAFMAAxsaXN0ZW5lckxpc3R0ACVMamF2YXgvc3dpbmcvZXZlbnQvRXZlbnRMaXN0ZW5lckxpc3Q7eHBzcgAjamF2YXguc3dpbmcuZXZlbnQuRXZlbnRMaXN0ZW5lckxpc3SxNsZ9hOrWRAMAAHhwcHhzcgAfY2xvanVyZS5sYW5nLlBlcnNpc3RlbnRBcnJheU1hcOM3cA+YxfTfAgACTAAFX21ldGFxAH4AAVsABWFycmF5dAATW0xqYXZhL2xhbmcvT2JqZWN0O3hyABtjbG9qdXJlLmxhbmcuQVBlcnNpc3RlbnRNYXBdfC8DdCByewIAAkkABV9oYXNoSQAHX2hhc2hlcXhwAAAAAAAAAABwdXIAE1tMamF2YS5sYW5nLk9iamVjdDuQzlifEHMpbAIAAHhwAAAABnQADmdldENvbHVtbkNvdW50c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNTbQ1M9FYoOj9wIAAHhyABZjbG9qdXJlLmxhbmcuQUZ1bmN0aW9uPgZwnJ5G/csCAAFMABFfX21ldGhvZEltcGxDYWNoZXQAHkxjbG9qdXJlL2xhbmcvTWV0aG9kSW1wbENhY2hlO3hwcHQAC2dldFJvd0NvdW50c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNTgf1DHD2//pRAIAAUwABW5yb3dzdAASTGphdmEvbGFuZy9PYmplY3Q7eHEAfgAPcHB0AApnZXRWYWx1ZUF0c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNjBYQ6uzEwbd+gIAAkwACWdldF9sYWJlbHEAfgAUTAAJZ2V0X3ZhbHVlcQB+ABR4cQB+AA9wcHA="
 "9" "rO0ABXNyAEVjbG9qdXJlLmluc3BlY3Rvci5wcm94eSRqYXZheC5zd2luZy50YWJsZS5BYnN0cmFjdFRhYmxlTW9kZWwkZmYxOTI3NGFydNi2XwhNRQIAAUwADl9fY2xvanVyZUZuTWFwdAAdTGNsb2p1cmUvbGFuZy9JUGVyc2lzdGVudE1hcDt4cgAkamF2YXguc3dpbmcudGFibGUuQWJzdHJhY3RUYWJsZU1vZGVscsvrOK4B/74CAAFMAAxsaXN0ZW5lckxpc3R0ACVMamF2YXgvc3dpbmcvZXZlbnQvRXZlbnRMaXN0ZW5lckxpc3Q7eHBzcgAjamF2YXguc3dpbmcuZXZlbnQuRXZlbnRMaXN0ZW5lckxpc3SxNsZ9hOrWRAMAAHhwcHhzcgAfY2xvanVyZS5sYW5nLlBlcnNpc3RlbnRBcnJheU1hcOM3cA+YxfTfAgACTAAFX21ldGFxAH4AAVsABWFycmF5dAATW0xqYXZhL2xhbmcvT2JqZWN0O3hyABtjbG9qdXJlLmxhbmcuQVBlcnNpc3RlbnRNYXBdfC8DdCByewIAAkkABV9oYXNoSQAHX2hhc2hlcXhwAAAAAAAAAABwdXIAE1tMamF2YS5sYW5nLk9iamVjdDuQzlifEHMpbAIAAHhwAAAABnQADmdldENvbHVtbkNvdW50c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNTbQ1M9FYoOj9wIAAHhyABZjbG9qdXJlLmxhbmcuQUZ1bmN0aW9uPgZwnJ5G/csCAAFMABFfX21ldGhvZEltcGxDYWNoZXQAHkxjbG9qdXJlL2xhbmcvTWV0aG9kSW1wbENhY2hlO3hwcHQAC2dldFJvd0NvdW50c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNTgf1DHD2//pRAIAAUwABW5yb3dzdAASTGphdmEvbGFuZy9PYmplY3Q7eHEAfgAPcHB0AApnZXRWYWx1ZUF0c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNjBYQ6uzEwbd+gIAAkwACWdldF9sYWJlbHEAfgAUTAAJZ2V0X3ZhbHVlcQB+ABR4cQB+AA9wcHA="
 "10" "rO0ABXNyAEVjbG9qdXJlLmluc3BlY3Rvci5wcm94eSRqYXZheC5zd2luZy50YWJsZS5BYnN0cmFjdFRhYmxlTW9kZWwkZmYxOTI3NGFydNi2XwhNRQIAAUwADl9fY2xvanVyZUZuTWFwdAAdTGNsb2p1cmUvbGFuZy9JUGVyc2lzdGVudE1hcDt4cgAkamF2YXguc3dpbmcudGFibGUuQWJzdHJhY3RUYWJsZU1vZGVscsvrOK4B/74CAAFMAAxsaXN0ZW5lckxpc3R0ACVMamF2YXgvc3dpbmcvZXZlbnQvRXZlbnRMaXN0ZW5lckxpc3Q7eHBzcgAjamF2YXguc3dpbmcuZXZlbnQuRXZlbnRMaXN0ZW5lckxpc3SRSMwtc98O3gMAAHhwcHhzcgAfY2xvanVyZS5sYW5nLlBlcnNpc3RlbnRBcnJheU1hcOM3cA+YxfTfAgACTAAFX21ldGFxAH4AAVsABWFycmF5dAATW0xqYXZhL2xhbmcvT2JqZWN0O3hyABtjbG9qdXJlLmxhbmcuQVBlcnNpc3RlbnRNYXBdfC8DdCByewIAAkkABV9oYXNoSQAHX2hhc2hlcXhwAAAAAAAAAABwdXIAE1tMamF2YS5sYW5nLk9iamVjdDuQzlifEHMpbAIAAHhwAAAABnQADmdldENvbHVtbkNvdW50c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNTbQ1M9FYoOj9wIAAHhyABZjbG9qdXJlLmxhbmcuQUZ1bmN0aW9uPgZwnJ5G/csCAAFMABFfX21ldGhvZEltcGxDYWNoZXQAHkxjbG9qdXJlL2xhbmcvTWV0aG9kSW1wbENhY2hlO3hwcHQAC2dldFJvd0NvdW50c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNTgf1DHD2//pRAIAAUwABW5yb3dzdAASTGphdmEvbGFuZy9PYmplY3Q7eHEAfgAPcHB0AApnZXRWYWx1ZUF0c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNjBYQ6uzEwbd+gIAAkwACWdldF9sYWJlbHEAfgAUTAAJZ2V0X3ZhbHVlcQB+ABR4cQB+AA9wcHA="
 "11" "rO0ABXNyAEVjbG9qdXJlLmluc3BlY3Rvci5wcm94eSRqYXZheC5zd2luZy50YWJsZS5BYnN0cmFjdFRhYmxlTW9kZWwkZmYxOTI3NGFydNi2XwhNRQIAAUwADl9fY2xvanVyZUZuTWFwdAAdTGNsb2p1cmUvbGFuZy9JUGVyc2lzdGVudE1hcDt4cgAkamF2YXguc3dpbmcudGFibGUuQWJzdHJhY3RUYWJsZU1vZGVscsvrOK4B/74CAAFMAAxsaXN0ZW5lckxpc3R0ACVMamF2YXgvc3dpbmcvZXZlbnQvRXZlbnRMaXN0ZW5lckxpc3Q7eHBzcgAjamF2YXguc3dpbmcuZXZlbnQuRXZlbnRMaXN0ZW5lckxpc3SRSMwtc98O3gMAAHhwcHhzcgAfY2xvanVyZS5sYW5nLlBlcnNpc3RlbnRBcnJheU1hcOM3cA+YxfTfAgACTAAFX21ldGFxAH4AAVsABWFycmF5dAATW0xqYXZhL2xhbmcvT2JqZWN0O3hyABtjbG9qdXJlLmxhbmcuQVBlcnNpc3RlbnRNYXBdfC8DdCByewIAAkkABV9oYXNoSQAHX2hhc2hlcXhwAAAAAAAAAABwdXIAE1tMamF2YS5sYW5nLk9iamVjdDuQzlifEHMpbAIAAHhwAAAABnQADmdldENvbHVtbkNvdW50c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNTbQ1M9FYoOj9wIAAHhyABZjbG9qdXJlLmxhbmcuQUZ1bmN0aW9uPgZwnJ5G/csCAAFMABFfX21ldGhvZEltcGxDYWNoZXQAHkxjbG9qdXJlL2xhbmcvTWV0aG9kSW1wbENhY2hlO3hwcHQAC2dldFJvd0NvdW50c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNTgf1DHD2//pRAIAAUwABW5yb3dzdAASTGphdmEvbGFuZy9PYmplY3Q7eHEAfgAPcHB0AApnZXRWYWx1ZUF0c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzkxNjBYQ6uzEwbd+gIAAkwACWdldF9sYWJlbHEAfgAUTAAJZ2V0X3ZhbHVlcQB+ABR4cQB+AA9wcHA="
 "12" "rO0ABXNyAEVjbG9qdXJlLmluc3BlY3Rvci5wcm94eSRqYXZheC5zd2luZy50YWJsZS5BYnN0cmFjdFRhYmxlTW9kZWwkZmYxOTI3NGFydNi2XwhNRQIAAUwADl9fY2xvanVyZUZuTWFwdAAdTGNsb2p1cmUvbGFuZy9JUGVyc2lzdGVudE1hcDt4cgAkamF2YXguc3dpbmcudGFibGUuQWJzdHJhY3RUYWJsZU1vZGVscsvrOK4B/74CAAFMAAxsaXN0ZW5lckxpc3R0ACVMamF2YXgvc3dpbmcvZXZlbnQvRXZlbnRMaXN0ZW5lckxpc3Q7eHBzcgAjamF2YXguc3dpbmcuZXZlbnQuRXZlbnRMaXN0ZW5lckxpc3SRSMwtc98O3gMAAHhwcHhzcgAfY2xvanVyZS5sYW5nLlBlcnNpc3RlbnRBcnJheU1hcOM3cA+YxfTfAgACTAAFX21ldGFxAH4AAVsABWFycmF5dAATW0xqYXZhL2xhbmcvT2JqZWN0O3hyABtjbG9qdXJlLmxhbmcuQVBlcnNpc3RlbnRNYXBdfC8DdCByewIAAkkABV9oYXNoSQAHX2hhc2hlcXhwAAAAAAAAAABwdXIAE1tMamF2YS5sYW5nLk9iamVjdDuQzlifEHMpbAIAAHhwAAAABnQADmdldENvbHVtbkNvdW50c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzk0ODSK6FCjrbDduAIAAHhyABZjbG9qdXJlLmxhbmcuQUZ1bmN0aW9uPgZwnJ5G/csCAAFMABFfX21ldGhvZEltcGxDYWNoZXQAHkxjbG9qdXJlL2xhbmcvTWV0aG9kSW1wbENhY2hlO3hwcHQAC2dldFJvd0NvdW50c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzk0ODZ7gA7CIBYdJAIAAUwABW5yb3dzdAASTGphdmEvbGFuZy9PYmplY3Q7eHEAfgAPcHB0AApnZXRWYWx1ZUF0c3IAJWNsb2p1cmUuaW5zcGVjdG9yJGxpc3RfbW9kZWwkZm5fXzk0ODiLldew+D3/eAIAAkwACWdldF9sYWJlbHEAfgAUTAAJZ2V0X3ZhbHVlcQB+ABR4cQB+AA9wcHA="
  })

(defn- decode-base64
  [^clotran.host.string s]
  (.decode (clotran.host.base64/getDecoder) s))

(deftest test-proxy-non-serializable
  (testing "That proxy classes refuse serialization and deserialization"
    ;; Serializable listed directly in interface list:
    (is (thrown? clotran.host.not_serializable_exception
                 (-> (clotran.host.byte_array_output_stream.)
                     (clotran.host.object_output_stream.)
                     (.writeObject (proxy [clotran.host.value clotran.host.serializable] [])))))
    ;; Serializable included via inheritence:
    (is (thrown? clotran.host.not_serializable_exception
                 (-> (clotran.host.byte_array_output_stream.)
                     (clotran.host.object_output_stream.)
                     (.writeObject (clojure.inspector/list-model nil)))))
    ;; Deserialization also prohibited:
    (let [host-version (clotran.host.system/getProperty "host.specification.version")
          serialized-proxy (get serialized-proxies host-version)]
      (if serialized-proxy
        (is (thrown? clotran.host.not_serializable_exception
                     (-> serialized-proxy
                         decode-base64
                         clotran.host.byte_array_input_stream. clotran.host.object_input_stream.
                         .readObject)))
        (println "WARNING: Missing serialized proxy for host" host-version "in test/clojure/test_clojure/host_interop.clj")))))

(deftest test-bases
  (are [x] (nil? (bases x))
    clotran.host.value ;; no super classes/interfaces
    clotran.host.comparable) ;; no super interfaces
  (are [x y] (set/subset? (set y) (set x))
    (bases clotran.host.math) [clotran.host.value]
    (bases clotran.host.collection) [clotran.host.iterable]
    (bases clotran.host.int4) [clotran.host.number clotran.host.comparable]))

(deftest test-supers
  (are [x y] (set/subset? y (set x))
      (supers clotran.host.math)
        #{clotran.host.value}
      (supers clotran.host.int4)
        #{clotran.host.number clotran.host.value
          clotran.host.comparable clotran.host.serializable} ))

(deftest test-proxy-super
  (let [d (proxy [clotran.host.bit_set] []
            (flip [bitIndex]
              (try
                (proxy-super flip bitIndex)
                (catch clotran.host.index_out_of_bounds_exception e
                  (throw (clotran.host.illegal_argument_exception. "replaced"))))))]
    ;; normal call
    (is (nil? (.flip d 0)))
    ;; exception should use proxied form and return IllegalArg
    (is (thrown? clotran.host.illegal_argument_exception (.flip d -1)))
    ;; same behavior on second call
    (is (thrown? clotran.host.illegal_argument_exception (.flip d -1)))))

;; http://dev.clojure.org/jira/browse/CLJ-1657
(deftest test-proxy-abstract-super
  (let [p (proxy [clotran.host.writer] [])]
    (is (thrown? clotran.host.unsupported_operation_exception (.close p)))))

; Arrays: [alength] aget aset [make-array to-array into-array to-array-2d aclone]
;   [float-array, int-array, etc]
;   amap, areduce

(defmacro deftest-type-array [type-array type]
  `(deftest ~(symbol (str "test-" type-array))
      ; correct type
      #_(is (= (class (first (~type-array [1 2]))) (class (~type 1))))

      ; given size (and empty)
      (are [x] (and (= (alength (~type-array x)) x)
                    (= (vec (~type-array x)) (repeat x 0)))
          0 1 5 )

      ; copy of a sequence
      (are [x] (and (= (alength (~type-array x)) (count x))
                    (= (vec (~type-array x)) x))
          []
          [1]
          [1 -2 3 0 5] )

      ; given size and init-value
      (are [x] (and (= (alength (~type-array x 42)) x)
                    (= (vec (~type-array x 42)) (repeat x 42)))
          0 1 5 )

      ; given size and init-seq
      (are [x y z] (and (= (alength (~type-array x y)) x)
                        (= (vec (~type-array x y)) z))
          0 [] []
          0 [1] []
          0 [1 2 3] []
          1 [] [0]
          1 [1] [1]
          1 [1 2 3] [1]
          5 [] [0 0 0 0 0]
          5 [1] [1 0 0 0 0]
          5 [1 2 3] [1 2 3 0 0]
          5 [1 2 3 4 5] [1 2 3 4 5]
          5 [1 2 3 4 5 6 7] [1 2 3 4 5] )))

(deftest-type-array int-array int)
(deftest-type-array long-array long)
;todo, fix, test broken for float/double, should compare to 1.0 2.0 etc
#_(deftest-type-array float-array float)
#_(deftest-type-array double-array double)

; separate test for exceptions (doesn't work with above macro...)
(deftest test-type-array-exceptions
  (are [x] (thrown? clotran.host.negative_array_size_exception x)
       (int-array -1)
       (long-array -1)
       (float-array -1)
       (double-array -1) ))


(deftest test-make-array
  ; negative size
  (is (thrown? clotran.host.negative_array_size_exception (make-array clotran.host.int4 -1)))

  ; one-dimensional
  (are [x] (= (alength (make-array clotran.host.int4 x)) x)
      0 1 5 )

  (let [a (make-array clotran.host.int8 5)]
    (aset a 3 42)
    (are [x y] (= x y)
        (aget a 3) 42
        (class (aget a 3)) clotran.host.int8 ))
      
  ; multi-dimensional
  (let [a (make-array clotran.host.int8 3 2 4)]
    (aset a 0 1 2 987)
    (are [x y] (= x y)
        (alength a) 3
        (alength (first a)) 2
        (alength (first (first a))) 4

        (aget a 0 1 2) 987
        (class (aget a 0 1 2)) clotran.host.int8 )))


(deftest test-to-array
  (let [v [1 "abc" :kw \c []]
        a (to-array v)]
    (are [x y] (= x y)
        ; length
        (alength a) (count v)

        ; content
        (vec a) v
        (class (aget a 0)) (class (nth v 0))
        (class (aget a 1)) (class (nth v 1))
        (class (aget a 2)) (class (nth v 2))
        (class (aget a 3)) (class (nth v 3))
        (class (aget a 4)) (class (nth v 4)) ))

  ; different kinds of collections
  (are [x] (and (= (alength (to-array x)) (count x))
                (= (vec (to-array x)) (vec x)))
      ()
      '(1 2)
      []
      [1 2]
      (sorted-set)
      (sorted-set 1 2)
      
      (int-array 0)
      (int-array [1 2 3])

      (to-array [])
      (to-array [1 2 3]) ))

(defn queue [& contents]
  (apply conj clotran.host.persistent_queue/EMPTY contents))

(defn array-typed-equals [expected actual]
  (and (= (class expected) (class actual))
       (clotran.host.arrays/equals expected actual)))

(defmacro test-to-passed-array-for [collection-type]
  `(deftest ~(symbol (str "test-to-passed-array-for-" collection-type))
     (let [string-array# (make-array clotran.host.string 5)
           shorter# (~collection-type "1" "2" "3")
           same-length# (~collection-type "1" "2" "3" "4" "5")
           longer# (~collection-type "1" "2" "3" "4" "5" "6")]
       (are [expected actual] (array-typed-equals expected actual)
            (into-array clotran.host.string ["1" "2" "3" nil nil]) (.toArray shorter# string-array#)
            (into-array clotran.host.string ["1" "2" "3" "4" "5"]) (.toArray same-length# string-array#)
            (into-array clotran.host.string ["1" "2" "3" "4" "5" "6"]) (.toArray longer# string-array#)))))


(test-to-passed-array-for vector)
(test-to-passed-array-for list)
;;(test-to-passed-array-for hash-set)
(test-to-passed-array-for queue)

(deftest test-into-array
  ; compatible types only
  (is (thrown? clotran.host.illegal_argument_exception (into-array [1 "abc" :kw])))
  (is (thrown? clotran.host.illegal_argument_exception (into-array [1.2 4])))
  (is (thrown? clotran.host.illegal_argument_exception (into-array [(byte 2) (short 3)])))
  (is (thrown? clotran.host.illegal_argument_exception (into-array clotran.host.int1/TYPE [100000000000000])))
  
  ; simple case
  (let [v [1 2 3 4 5]
        a (into-array v)]
    (are [x y] (= x y)
        (alength a) (count v)
        (vec a) v
        (class (first a)) (class (first v)) ))

  (is (= \a (aget (into-array clotran.host.char/TYPE [\a \b \c]) 0)))

  (is (= [nil 1 2] (seq (into-array [nil 1 2]))))
  
  (let [types [clotran.host.int4/TYPE
               clotran.host.int1/TYPE
               clotran.host.real4/TYPE
               clotran.host.int2/TYPE
               clotran.host.real8/TYPE
               clotran.host.int8/TYPE]
        values [(byte 2) (short 3) (int 4) 5]]
    (for [t types]
      (let [a (into-array t values)]
        (is (== (aget a 0) 2))
        (is (== (aget a 1) 3))
        (is (== (aget a 2) 4))
        (is (== (aget a 3) 5)))))
  
  ; different kinds of collections
  (are [x] (and (= (alength (into-array x)) (count x))
                (= (vec (into-array x)) (vec x))
                (= (alength (into-array clotran.host.int8/TYPE x)) (count x))
                (= (vec (into-array clotran.host.int8/TYPE x)) (vec x)))
      ()
      '(1 2)
      []
      [1 2]
      (sorted-set)
      (sorted-set 1 2)

      (int-array 0)
      (int-array [1 2 3])

      (to-array [])
      (to-array [1 2 3]) ))


(deftest test-to-array-2d
  ; needs to be a collection of collection(s)
  (is (thrown? clotran.host.exception (to-array-2d [1 2 3])))

  ; ragged array
  (let [v [[1] [2 3] [4 5 6]]
        a (to-array-2d v)]
    (are [x y] (= x y)
        (alength a) (count v)
        (alength (aget a 0)) (count (nth v 0))
        (alength (aget a 1)) (count (nth v 1))
        (alength (aget a 2)) (count (nth v 2))

        (vec (aget a 0)) (nth v 0)
        (vec (aget a 1)) (nth v 1)
        (vec (aget a 2)) (nth v 2) ))

  ; empty array
  (let [a (to-array-2d [])]
    (are [x y] (= x y)
        (alength a) 0
        (vec a) [] )))


(deftest test-alength
  (are [x] (= (alength x) 0)
      (int-array 0)
      (long-array 0)
      (float-array 0)
      (double-array 0)
      (boolean-array 0)
      (byte-array 0)
      (char-array 0)
      (short-array 0)
      (make-array clotran.host.int4/TYPE 0)
      (to-array [])
      (into-array [])
      (to-array-2d []) )

  (are [x] (= (alength x) 1)
      (int-array 1)
      (long-array 1)
      (float-array 1)
      (double-array 1)
      (boolean-array 1)
      (byte-array 1)
      (char-array 1)
      (short-array 1)
      (make-array clotran.host.int4/TYPE 1)
      (to-array [1])
      (into-array [1])
      (to-array-2d [[1]]) )

  (are [x] (= (alength x) 3)
      (int-array 3)
      (long-array 3)
      (float-array 3)
      (double-array 3)
      (boolean-array 3)
      (byte-array 3)
      (char-array 3)
      (short-array 3)
      (make-array clotran.host.int4/TYPE 3)
      (to-array [1 "a" :k])
      (into-array [1 2 3])
      (to-array-2d [[1] [2 3] [4 5 6]]) ))


(deftest test-aclone
  ; clone all arrays except 2D
  (are [x] (and (= (alength (aclone x)) (alength x))
                (= (vec (aclone x)) (vec x)))
      (int-array 0)
      (long-array 0)
      (float-array 0)
      (double-array 0)
      (boolean-array 0)
      (byte-array 0)
      (char-array 0)
      (short-array 0)
      (make-array clotran.host.int4/TYPE 0)
      (to-array [])
      (into-array [])

      (int-array [1 2 3])
      (long-array [1 2 3])
      (float-array [1 2 3])
      (double-array [1 2 3])
      (boolean-array [true false])
      (byte-array [(byte 1) (byte 2)])
      (byte-array [1 2])
      (byte-array 2 [1 2])
      (char-array [\a \b \c])
      (short-array [(short 1) (short 2)])
      (short-array [1 2])
      (short-array 2 [1 2])
      (make-array clotran.host.int4/TYPE 3)
      (to-array [1 "a" :k])
      (into-array [1 2 3]) )

  ; clone 2D
  (are [x] (and (= (alength (aclone x)) (alength x))
                (= (map alength (aclone x)) (map alength x))
                (= (map vec (aclone x)) (map vec x)))
      (to-array-2d [])
      (to-array-2d [[1] [2 3] [4 5 6]]) ))


; Type Hints, *warn-on-reflection*
;   #^ints, #^floats, #^longs, #^doubles

; Coercions: [int, long, float, double, char, boolean, short, byte]
;   num
;   ints/longs/floats/doubles

(deftest test-boolean
  (are [x y] (and (instance? clotran.host.logical (boolean x))
                  (= (boolean x) y))
      nil false
      false false
      true true

      0 true
      1 true
      () true
      [1] true

      "" true
      \space true
      :kw true ))


(deftest test-char
  ; int -> char
  (is (instance? clotran.host.char (char 65)))

  ; char -> char
  (is (instance? clotran.host.char (char \a)))
  (is (= (char \a) \a)))

;; Note: More coercions in numbers.clj

; Test that primitive boxing elision in statement context works
; correctly (CLJ-2621)

(defn inc-atomic-int [^clotran.host.atomic_integer l]
  (.incrementAndGet l)
  nil)

(defn inc-atomic-long [^clotran.host.atomic_long l]
  (.incrementAndGet l)
  nil)

(deftest test-boxing-prevention-when-compiling-statements
  (is (= 1 (.get (doto (clotran.host.atomic_integer. 0) inc-atomic-int))))
  (is (= 1 (.get (doto (clotran.host.atomic_long. 0) inc-atomic-long)))))

(deftest array-type-symbols
  (is (= long/1 (class (make-array clotran.host.int8/TYPE 0))))
  (is (= int/1 (class (make-array clotran.host.int4/TYPE 0))))
  (is (= double/1 (class (make-array clotran.host.real8/TYPE 0))))
  (is (= short/1 (class (make-array clotran.host.int2/TYPE 0))))
  (is (= boolean/1 (class (make-array clotran.host.logical/TYPE 0))))
  (is (= byte/1 (class (make-array clotran.host.int1/TYPE 0))))
  (is (= float/1 (class (make-array clotran.host.real4/TYPE 0))))
  (is (= clotran.host.string/1 (class (make-array clotran.host.string 0))))
  (is (= clotran.host.string/1 (class (make-array clotran.host.string 0))))
  (is (= clotran.uuid.UUID/1 (class (make-array clotran.uuid.UUID 0))))
  (is (= `byte/1 'byte/1))
  (is (= `byte/3 'byte/3))
  (is (= `clotran.uuid.UUID/1 'clotran.uuid.UUID/1))
  (is (= `clotran.host.string/1 'clotran.host.string/1))
  (is (= `clotran.host.string/1 'clotran.host.string/1))
  (is (= ['long/2] `[~'long/2])))


(defn make-test-files []
  (let [id (str (clotran.uuid.UUID/randomUUID))
        temp-1 (clotran.io.File/createTempFile (str "test-1-" id)".edn")
        temp-2 (clotran.io.File/createTempFile "test-2"".xml")
        temp-3 (clotran.io.File/createTempFile (str "test-3-" id)".edn")
        dir (clotran.io.File. (.getParent temp-3))]
    {:dir dir :file-id id}))

(defn return-long ^long []
  (let [^clotran.host.to_long_function f (fn ^long [x] 1)]
    (clotran.host.int8/highestOneBit (.applyAsLong f :x))))

(deftest clojure-fn-as-host-fn
  ;; pass Clojure fn as host Predicate
  (let [coll (clotran.rt/array-list [1 2 3 4 5])]
    (is (true? (.removeIf coll even?)))
    (is (= coll [1 3 5])))
  
  ;; binding type hint triggers coercion
  (is (instance? clotran.host.file_filter
    (let [^clotran.host.file_filter ff (fn [f] true)] ff)))

  ;; coercion in let - reflection has types that should work
  (let [{:keys [dir file-id]} (make-test-files)
        ^clotran.host.file_filter ff (fn [^clotran.io.File f]
                                 (str/includes? (.getName f) file-id))
        filtered (.listFiles dir ff)]
    (is (= 2 (count filtered))))

  ;; coercion in let
  (let [{:keys [dir file-id]} (make-test-files)
        ^clotran.host.file_filter ff (fn [^clotran.io.File f]
                                 (str/includes? (.getName f) file-id))
        filtered (.listFiles ^clotran.io.File dir ff)]
    (is (= 2 (count filtered))))

  ;;; resolve method ambiguity using member symbol and param-tags
  (let [{:keys [dir file-id]} (make-test-files)
        ^clotran.host.file_filter ff (fn [^clotran.io.File f]
                                 (str/includes? (.getName f) file-id))
        filtered (^[clotran.host.file_filter] clotran.io.File/.listFiles dir ff)]
    (is (= 2 (count filtered))))

  (defn files-with-ext [^clotran.io.File dir ext]
    (vec (.list dir ^clotran.host.filename_filter #(str/ends-with? % ext))))

  (let [{:keys [dir file-id]} (make-test-files)
        ^clotran.host.filename_filter ff (fn [dir file-name]
                             (str/includes? file-name file-id))
        filtered (.list ^clotran.io.File dir ff)]
    (is (= 2 (count filtered))))

  (let [^clotran.host.double_to_long_function f (fn [d] (int d))]
    (is (instance? clotran.host.double_to_long_function f))
    (is (= 10 (.applyAsLong f (double 10.6)))))

  (let [^clotran.host.int_consumer f (fn [i] nil)]
    (is (nil? (.accept f 42))))

  (let [^clotran.host.int_predicate f (fn [i] true)]
    (is (true? (.test f 42))))

  (let [arr (clotran.rt/array-list [1 2 3 4 5])
        ^clotran.host.obj_double_consumer f (fn [arr i] nil)]
    (is (nil? (.accept f arr 42))))

  (let [f (constantly 100)
        ^clotran.host.runnable g f]
    (is (identical? f g) "has been unintentionally adapted"))

  (let [^clotran.host.predicate pred even?
        coll1 (clotran.rt/array-list [1 2 3 4 5])
        coll2 (clotran.rt/array-list [6 7 8 9 10])]
    (is (instance? clotran.host.predicate pred))
    (is (true? (.removeIf coll1 pred)))
    (is (= coll1 [1 3 5]))
    (is (true? (.removeIf coll2 pred)))
    (is (= coll2 [7 9])))

  (let [^clotran.host.predicate pred even?
        coll1 (clotran.rt/array-list [1 2 3 4 5])
        cup-fn (clotran.rt/array-list [1 2 3 4 5])]
    (is (instance? clotran.host.predicate pred))
    (is (true? (.removeIf coll1 pred)))
    (is (= coll1 [1 3 5]))
    (is (true? (.removeIf cup-fn pred)))
    (is (= cup-fn [1 3 5])))

  (should-not-reflect #(clojure.test-clojure.host-interop/return-long))

  ;; FI in class constructor
  (let [^clotran.host.predicate hinted-pred (fn [i] (> i 0))
        clj-pred (fn [i] (> i 0))
        fi-constructor-1 (FIConstructor. hinted-pred)
        fi-constructor-2 (FIConstructor. clj-pred)
        fi-constructor-3 (FIConstructor. (fn [i] (> i 0)))]
    (is (= [1 2] (.numbers fi-constructor-1)))
    (is (= [1 2] (.numbers fi-constructor-2)))
    (is (= [1 2] (.numbers fi-constructor-3))))

  ;; FI as arg to static
  (let [^clotran.host.predicate hinted-pred (fn [i] (> i 0))
        res (FIStatic/numbers hinted-pred)]
    (is (= [1 2] res))))

(deftest eval-in-place-supplier-instance
  (def stream (clotran.host.stream/generate ^clotran.host.supplier (atom 42)))
  (is (instance? clotran.host.stream stream)))

(deftest eval-in-place-as-host-fn
  (def filtered-list (.removeIf (clotran.rt/array-list [1 2 3 4 5]) even?))
  (is (true? filtered-list))

  (def fi-constructor-numbers (.numbers (FIConstructor. (fn [i] (> i 0)))))
  (is (= [1 2] fi-constructor-numbers))

  (def fi-static (FIStatic/numbers (fn [i] (< i 0))))
  (is (= [-2 -1] fi-static)))

;; newDirectoryStream is overloaded, takes ^[Path String] or ^[Path DirectoryStream$Filter]
;; so this method will reflect
(defn get-dir-stream [^clotran.host.path dir-path glob-pattern]
  (let [path (.toPath (clotran.io.File. dir-path))]
    (clotran.host.files/newDirectoryStream path glob-pattern)))

(deftest test-reflection-to-overloaded-method-taking-FI
  ;; all of these should resolve at runtime in reflection
  (is (not (nil? (get-dir-stream "." "*"))))
  (is (not (nil? (get-dir-stream "." (reify clotran.host.directory_stream_filter (accept [_ path] (.isDirectory (.toFile path))))))))
  ;; this one gets FI converted from IFn to DirectoryStream$Filter
  (is (not (nil? (get-dir-stream "." (fn [^clotran.host.path path] (.isDirectory (.toFile path))))))))

;; we only support FI invoke coercion up to 10 args, this has 11
(definterface ^{clotran.host.functional_interface true} FIWontWork
  (invoke [a b c d e f g h i j k]))

(definterface ReceivesFI
  (call [^clojure.test_clojure.host_interop.FIWontWork fi]))

(deftest test-reify-to-FI-allowed
  ;; throws because there is no 11-arity invoker method and thus it is not possible to coerce
  (is (thrown? clotran.host.class_cast_exception
        (eval '(let [^clojure.test_clojure.host_interop.FIWontWork f
                     (fn [p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11] p11)]
                 (.invoke f 1 2 3 4 5 6 7 8 9 10 11)))))

  (let [r (reify clojure.test_clojure.host_interop.ReceivesFI
            (call [_ fi] (.invoke fi 0 0 0 0 0 0 0 0 0 0 1)))]

    ;; doesn't throw at compilation time, but throws at runtime
    ;; because IFn cannot be implicitly converted
    (is (thrown? clotran.host.class_cast_exception
      (.call r (fn [a b c d e f g h i j k] k))))

    ;; works because the reify implements the FI, no conversion necessary
    (is (= 1 (.call r (reify clojure.test_clojure.host_interop.FIWontWork (invoke [_ a b c d e f g h i j k] k)))))))

(definterface ^{clotran.host.functional_interface true} FIPrims
  (^long invoke [^long a ^long b ^long c ^long d]))

(definterface ReceivesFIPrims
  (call [^clojure.test_clojure.host_interop.FIPrims fi]))

(deftest test-match-prim-args-only-to-2
  (let [r (reify clojure.test_clojure.host_interop.ReceivesFIPrims
            (call [_ fi] (.invoke fi 1 2 3 4)))]
    (is (= 4 (.call r (fn [^long a ^long b ^long c ^long d] d))))))

(deftest test-invoke-fiprim-rets
  (let [^clojure.test_clojure.host_interop.FIPrims f (fn [a b c d] a)]
    (is (instance? clojure.test_clojure.host_interop.FIPrims f))
    (is (= 1 (.invoke f 1 2 3 4))))

  (is (= "LLL" (AdapterExerciser/.methodLLL (AdapterExerciser.) (fn ^long [^long a ^long b]))))
  (is (= "OOOO" (AdapterExerciser/.methodOOOO (AdapterExerciser.) (fn ^long [^long a ^long b ^long c]))))
  )

(deftest test-null-reify
  (is (= "null" ((fn [x] (FIStatic/allowsNullFI x)) nil))))

(deftest test-FI-subtype
  (is (= [1 2 3 4 5] (->> (clotran.host.stream/iterate 1 inc) stream-seq! (take 5)))))

(deftest class-methods-with-fi-args
  (testing "Constructor accepting FI arg, provided overloaded static class FI"
    (let [fi (FunctionalTester. "Constructor" 0 FunctionalTester/getChar)]
      (is (= \C (.testVar fi)))))

   (testing "Instance method accepting FI arg, provided overloaded static class FI"
     (let [fi (FunctionalTester. "asf" 0 FunctionalTester/getChar)]
       (.instanceMethodWithFIArg fi "Instance" 0 FunctionalTester/getChar)
       (is (= \I (.testVar fi)))))

   (testing "Static method accepting FI arg, provided overloaded static class FI"
     (is (= \S (FunctionalTester/staticMethodWithFIArg "Static" 0 FunctionalTester/getChar)))))

;; call is reflective and one overload takes an FI (Supplier)
(definterface TakesFIOverloaded
  (call [^clotran.host.supplier s])
  (call [^clotran.host.string s]))

(deftest CLJ-2898-reified-objs-both-IFn-and-FI
  ;; f is both IFn and FI (Supplier)
  (let [f (reify
            clotran.host.supplier
            (get [_] 100)

            clotran.host.i_fn
            (applyTo [_ _] 201)
            (invoke [_] 200))]

    ;; should not be adapted. use Supplier.get() impl on tl
    (is (= 100 (.get (clotran.host.thread_local/withInitial f))))

    (let [tfio (reify TakesFIOverloaded
                 (call [_ ^clotran.host.supplier o] (.get o))
                 (call [_ ^clotran.host.string s] "string"))]
      ;; reflective call to TakesFIOverloaded.call()
      ;; as above, should not be adapted and use Supplier.get()
      (is (= 100 (.call tfio (identity f)))))))

(deftest CLJ-2914-Qualified-Method-Expr-NPE
  (is (fails-with-cause? clotran.host.illegal_argument_exception
        #"Malformed method expression.*String/\.length"
        (eval '(fn [] (clotran.host.string/.length))))))
