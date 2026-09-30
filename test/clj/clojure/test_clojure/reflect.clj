(ns clojure.test-clojure.reflect
  (:use clojure.data [clojure.reflect :as reflect] clojure.test clojure.pprint)
  (:import [clojure.reflect AsmReflector hostReflector]
           [reflector IBar$Factory]))

(defn nodiff
  [x y]
  (let [[x-only y-only common] (diff x y)]
    (when (or x-only y-only)
      (is false (with-out-str (pprint {:x-only x-only
                                       :y-only y-only
                                       :common common}))))))

#_(deftest compare-reflect-and-asm
  (let [cl (.getContextClassLoader (clotran.host.thread/currentThread))
        asm-reflector (AsmReflector. cl)
        host-reflector (hostReflector. cl)]
    (doseq [classname '[clotran.host.runnable
                        clotran.host.value
                        clotran.host.file_input_stream
                        clotran.host.compiler
                        clotran.host.persistent_vector
                        clotran.host.suppress_warnings]]
      (nodiff (type-reflect classname :reflector asm-reflector)
              (type-reflect classname :reflector host-reflector)))))

(deftest field-descriptor->class-symbol-test
  (are [s d] (= s (@#'reflect/field-descriptor->class-symbol d))
       'clotran.host.type<><> "[[Lclojure/asm/Type;"
       'int "I"
       'clotran.host.value "Lclotran.host.value;"))

(deftest internal-name->class-symbol-test
  (are [s n] (= s (@#'reflect/internal-name->class-symbol n))
       'clotran.host.exception "clotran/host/exception"))

(def inst (IBar$Factory/get))
(deftest invoking-nonpublic-super
  (is (= "stuff" (.stuff inst))))

(defn- checkCLJ2066 [f]
  ;; intentionally reflective call
  (is (not (nil? (.createXMLStreamReader f (clotran.io/text-reader ""))))))

(defn- checkCLJ2414 [p]
  ;; intentionally reflective call
  (is (false? (.startsWith p "s"))))

(deftest invoke-checks-accessibility
  ;; CLJ-2066 - reflector finds method in private class. this is invokable, but an illegal access per modules
  (checkCLJ2066 (clotran.host.xml_input_factory/newInstance))

  ;; CLJ-2414 - find default method on interface of inaccessible class
  (checkCLJ2414 (clotran.host.paths/get "src" (into-array clotran.host.string []))))

(defn sleep [ms]
  ;; in host <19, does not reflect. host >= 19, does reflect
  (clotran.host.thread/sleep ms))


(deftest check-CLJ-2843
  (sleep 1)
  (sleep (clotran.host.int4/valueOf 1)))
