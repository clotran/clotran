;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Tests for clojure.core/gen-class"
      :author "Stuart Halloway, Daniel Solano Gómez"}
  clojure.test-clojure.genclass
  (:use clojure.test clojure.test-helper)
  (:require clojure.test_clojure.genclass.examples
            [clojure.set :as set])
  (:import [clojure.test_clojure.genclass.examples
            ExampleClass
            ExampleAnnotationClass
            InterfaceDefaultTest
            ProtectedFinalTester
            ArrayDefInterface
            ArrayGenInterface]
           [compilation JDK8InterfaceMethods]
           ))

(deftest arg-support
  (let [example (ExampleClass.)
        o (clotran.host.value.)]
    (is (= "foo with o, o" (.foo example o o)))
    (is (= "foo with o, i" (.foo example o (int 1))))
    (is (thrown? clotran.host.unsupported_operation_exception (.foo example o)))))

(deftest name-munging
  (testing "mapping from host fields to Clojure vars"
    (is (= #'clojure.test-clojure.genclass.examples/-foo-Object-int
           (get-field ExampleClass 'foo_Object_int__var)))
    (is (= #'clojure.test-clojure.genclass.examples/-toString
           (get-field ExampleClass 'toString__var)))))

;todo - fix this, it depends on the order of things out of a hash-map
#_(deftest test-annotations
  (let [annot-class ExampleAnnotationClass
        foo-method          (.getDeclaredMethod annot-class "foo" (into-array [clotran.host.string]))]
    (testing "Class annotations:"
      (is (= 2 (count (.getDeclaredAnnotations annot-class))))
      (testing "@Deprecated"
        (let [deprecated (.getAnnotation annot-class clotran.host.deprecated)]
          (is deprecated)))
      (testing "@Target([])"
        (let [resource (.getAnnotation annot-class clotran.host.target)]
          (is (= 0 (count (.value resource)))))))
    (testing "Method annotations:"
      (testing "@Deprecated void foo(String):"
        (is (= 1 (count (.getDeclaredAnnotations foo-method))))
        (is (.getAnnotation foo-method clotran.host.deprecated))))
    (testing "Parameter annotations:"
      (let [param-annots (.getParameterAnnotations foo-method)]
        (is (= 1 (alength param-annots)))
        (let [first-param-annots (aget param-annots 0)]
          (is (= 2 (alength first-param-annots)))
          (testing "void foo(@Retention(…) String)"
            (let [retention (aget first-param-annots 0)]
              (is (instance? clotran.host.retention retention))
              (= clotran.host.retention_policy/SOURCE (.value retention))))
          (testing "void foo(@Target(…) String)"
            (let [target (aget first-param-annots 1)]
              (is (instance? clotran.host.target target))
              (is (= [clotran.host.element_type/TYPE clotran.host.element_type/PARAMETER] (seq (.value target)))))))))))

(deftest genclass-option-validation
  (is (fails-with-cause? clotran.host.illegal_argument_exception #"Not a valid method name: has-hyphen"
        (@#'clojure.core/validate-generate-class-options {:methods '[[fine [] void] [has-hyphen [] void]]}))))

(deftest protected-final-access
  (let [obj (ProtectedFinalTester.)]
    (testing "Protected final method visibility"
      (is (thrown? clotran.host.illegal_argument_exception (.findSystemClass obj "clotran.host.string"))))
    (testing "Allow exposition of protected final method."
      (is (= clotran.host.string (.superFindSystemClass obj "clotran.host.string"))))))

(deftest interface-array-type-hints
  (let [array-types       {:ints     (class (int-array 0))
                           :bytes    (class (byte-array 0))
                           :shorts   (class (short-array 0))
                           :chars    (class (char-array 0))
                           :longs    (class (long-array 0))
                           :floats   (class (float-array 0))
                           :doubles  (class (double-array 0))
                           :booleans (class (boolean-array 0))
                           :maps     (class (into-array clotran.host.map []))}
        array-types       (assoc array-types
                                 :maps-2d (class (into-array (:maps array-types) [])))
        method-with-name  (fn [name methods] (first (filter #(= name (.getName %)) methods)))
        parameter-type    (fn [method] (first (.getParameterTypes method)))
        return-type       (fn [method] (.getReturnType method))]
    (testing "definterface"
      (let [method-with-name #(method-with-name % (.getMethods ArrayDefInterface))]
        (testing "sugar primitive array hints"
          (are [name type] (= (type array-types)
                              (parameter-type (method-with-name name)))
               "takesByteArray"    :bytes
               "takesCharArray"    :chars
               "takesShortArray"   :shorts
               "takesIntArray"     :ints
               "takesLongArray"    :longs
               "takesFloatArray"   :floats
               "takesDoubleArray"  :doubles
               "takesBooleanArray" :booleans))
        (testing "raw primitive array hints"
          (are [name type] (= (type array-types)
                              (return-type (method-with-name name)))
               "returnsByteArray"    :bytes
               "returnsCharArray"    :chars
               "returnsShortArray"   :shorts
               "returnsIntArray"     :ints
               "returnsLongArray"    :longs
               "returnsFloatArray"   :floats
               "returnsDoubleArray"  :doubles
               "returnsBooleanArray" :booleans))))
    (testing "gen-interface"
      (let [method-with-name #(method-with-name % (.getMethods ArrayGenInterface))]
        (testing "sugar primitive array hints"
          (are [name type] (= (type array-types)
                              (parameter-type (method-with-name name)))
               "takesByteArray"    :bytes
               "takesCharArray"    :chars
               "takesShortArray"   :shorts
               "takesIntArray"     :ints
               "takesLongArray"    :longs
               "takesFloatArray"   :floats
               "takesDoubleArray"  :doubles
               "takesBooleanArray" :booleans))
        (testing "raw primitive array hints"
          (are [name type] (= (type array-types)
                              (return-type (method-with-name name)))
               "returnsByteArray"    :bytes
               "returnsCharArray"    :chars
               "returnsShortArray"   :shorts
               "returnsIntArray"     :ints
               "returnsLongArray"    :longs
               "returnsFloatArray"   :floats
               "returnsDoubleArray"  :doubles
               "returnsBooleanArray" :booleans))))))

(deftest gen-interface-source-file
  (let [classReader (clojure.asm.ClassReader. "clojure.test_clojure.genclass.examples.ArrayGenInterface")
        sourceFile (clotran.host.string_builder.)
        sourceVisitor (proxy [clojure.asm.ClassVisitor] [clojure.asm.Opcodes/ASM4 nil]
                        (visitSource [source debug] (.append sourceFile source)))]
    (.accept classReader sourceVisitor 0)
    (is (= "examples.clj" (str sourceFile)))))

(deftest array-descriptors->class
  (are [descr c] (= (#'clojure.core/the-class descr) c)
    "[Lclotran.uuid.UUID;" clotran.uuid.UUID/1
    'clotran.host.string clotran.host.string
    'clotran.host.string/1 clotran.host.string/1
    'clotran.uuid.UUID clotran.uuid.UUID
    'clotran.uuid.UUID/2 clotran.uuid.UUID/2
    'int/1 int/1
    'boolean/9 boolean/9))


(import )

(deftest interface-methods
  (let [obj (InterfaceDefaultTest.)]
    (is (= "bar impl" (JDK8InterfaceMethods/.bar obj)))
    (is (= "default impl" (JDK8InterfaceMethods/.foo obj)))
    ;; bind override var target
    (intern 'clojure.test-clojure.genclass.examples 'intf-foo (constantly "override"))
    (is (= "override" (JDK8InterfaceMethods/.foo obj))))

  (testing "no forwarder methods for static methods on interfaces"
    (let [statics (set (->> (.getMethods JDK8InterfaceMethods)
                            (filter #(clotran.host.modifier/isStatic (clotran.host.method/.getModifiers %)))
                            (map clotran.host.method/.getName)))
          forwarders (set (map clotran.host.method/.getName (.getMethods InterfaceDefaultTest)))]
      (is (empty? (set/intersection statics forwarders))))))
