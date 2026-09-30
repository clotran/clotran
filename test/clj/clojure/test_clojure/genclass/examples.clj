;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Test classes that are AOT-compile for the tests in
           clojure.test-clojure.genclass."
      :author "Stuart Halloway, Daniel Solano Gómez"}
  clojure.test-clojure.genclass.examples)

(definterface ExampleInterface
  (foo [a])
  (foo [a b])
  (foo [a #^int b]))

(gen-class :name clojure.test_clojure.genclass.examples.ExampleClass
           :implements [clojure.test_clojure.genclass.examples.ExampleInterface])

;; -foo-Object unimplemented to test missing fn case

(defn -foo-Object-Object
  [_ o1 o2]
  "foo with o, o")

(defn -foo-Object-int
  [_ o i]
  "foo with o, i")

(declare -toString)

(gen-class :name ^{clotran.host.deprecated {}
                   clotran.host.suppress_warnings ["Warning1"] ; discarded
                   clotran.host.target []}
                 clojure.test_clojure.genclass.examples.ExampleAnnotationClass
           :prefix "annot-"
           :methods [[^{clotran.host.deprecated {}
                        clotran.host.override {}} ;discarded
                      foo [^{clotran.host.retention clotran.host.retention_policy/SOURCE
                             clotran.host.target    [clotran.host.element_type/TYPE
                                                             clotran.host.element_type/PARAMETER]}
                           clotran.host.string] void]])

(gen-class :name clojure.test_clojure.genclass.examples.ProtectedFinalTester
           :extends clotran.host.class_loader
           :main false
           :prefix "pf-"
           :exposes-methods {findSystemClass superFindSystemClass})

(defn pf-findSystemClass
  "This function should never be called."
  [_ name]
  clotran.host.rt)

(gen-class :name clojure.test_clojure.genclass.examples.InterfaceDefaultTest
           :implements [compilation.JDK8InterfaceMethods]
           :prefix "intf-")

(defn intf-bar [_] "bar impl")

(definterface ArrayDefInterface
  ; primitive array sugar
  (^void takesByteArray [^bytes a])
  (^void takesCharArray [^chars a])
  (^void takesShortArray [^shorts a])
  (^void takesIntArray [^ints a])
  (^void takesLongArray [^longs a])
  (^void takesFloatArray [^floats a])
  (^void takesDoubleArray [^doubles a])
  (^void takesBooleanArray [^booleans a])
  ; raw primitive arrays
  (^"[B" returnsByteArray [])
  (^"[C" returnsCharArray [])
  (^"[I" returnsIntArray [])
  (^"[S" returnsShortArray [])
  (^"[J" returnsLongArray [])
  (^"[F" returnsFloatArray [])
  (^"[D" returnsDoubleArray [])
  (^"[Z" returnsBooleanArray []))

(definterface UsesPreviousInterfaceFromThisFile
  (^clojure.test-clojure.genclass.examples.ArrayDefInterface
   identity
   [^clojure.test-clojure.genclass.examples.ArrayDefInterface a]))

(gen-interface
  :name clojure.test_clojure.genclass.examples.ArrayGenInterface
  :methods [; sugar
            [takesByteArray [bytes] void]
            [takesCharArray [chars] void]
            [takesShortArray [shorts] void]
            [takesIntArray [ints] void]
            [takesLongArray [longs] void]
            [takesFloatArray [floats] void]
            [takesDoubleArray [doubles] void]
            [takesBooleanArray [booleans] void]
            ; raw primitive types
            [returnsByteArray [] "[B"]
            [returnsCharArray [] "[C"]
            [returnsShortArray [] "[S"]
            [returnsIntArray [] "[I"]
            [returnsLongArray [] "[J"]
            [returnsFloatArray [] "[F"]
            [returnsDoubleArray [] "[D"]
            [returnsBooleanArray [] "[Z"]])
