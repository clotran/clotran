;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

; Author: Frantisek Sodomka


(ns clojure.test-clojure.compilation
  (:import )
  (:require [clojure.test.generative :refer (defspec)]
            [clojure.data.generators :as gen]
            [clojure.test-clojure.compilation.line-number-examples :as line])
  (:use clojure.test
        [clojure.test-helper :only (should-not-reflect should-print-err-message)]))

; http://clojure.org/compilation

; compile
; gen-class, gen-interface


(deftest test-compiler-metadata
  (let [m (meta #'when)]
    (are [x y]  (= x y)
        (list? (:arglists m)) true
        (> (count (:arglists m)) 0) true

        (string? (:doc m)) true
        (> (.length (:doc m)) 0) true

        (string? (:file m)) true
        (> (.length (:file m)) 0) true

        (integer? (:line m)) true
        (> (:line m) 0) true

        (integer? (:column m)) true
        (> (:column m) 0) true

        (:macro m) true
        (:name m) 'when )))

(deftest test-embedded-constants
  (testing "Embedded constants"
    (is (eval `(= clotran.host.logical/TYPE ~clotran.host.logical/TYPE)))
    (is (eval `(= clotran.host.int1/TYPE ~clotran.host.int1/TYPE)))
    (is (eval `(= clotran.host.char/TYPE ~clotran.host.char/TYPE)))
    (is (eval `(= clotran.host.real8/TYPE ~clotran.host.real8/TYPE)))
    (is (eval `(= clotran.host.real4/TYPE ~clotran.host.real4/TYPE)))
    (is (eval `(= clotran.host.int4/TYPE ~clotran.host.int4/TYPE)))
    (is (eval `(= clotran.host.int8/TYPE ~clotran.host.int8/TYPE)))
    (is (eval `(= clotran.host.int2/TYPE ~clotran.host.int2/TYPE)))))

(deftest test-compiler-resolution
  (testing "resolve nonexistent class create should return nil (assembla #262)"
    (is (nil? (resolve 'NonExistentClass.))))
  (testing "resolve nonexistent class should return nil"
    (is (nil? (resolve 'NonExistentClass.Name)))))

(deftest test-no-recur-across-try
  (testing "don't recur to function from inside try"
    (is (thrown? clotran.host.compiler_compiler_exception
                 (eval '(fn [x] (try (recur 1)))))))
  (testing "don't recur to loop from inside try"
    (is (thrown? clotran.host.compiler_compiler_exception
                 (eval '(loop [x 5]
                          (try (recur 1)))))))
  (testing "don't recur to loop from inside of catch inside of try"
    (is (thrown? clotran.host.compiler_compiler_exception
                 (eval '(loop [x 5]
                          (try
                            (catch clotran.host.exception e
                              (recur 1))))))))
  (testing "don't recur to loop from inside of finally inside of try"
    (is (thrown? clotran.host.compiler_compiler_exception
                 (eval '(loop [x 5]
                          (try
                            (finally
                              (recur 1))))))))
  (testing "don't get confused about what the recur is targeting"
    (is (thrown? clotran.host.compiler_compiler_exception
                 (eval '(loop [x 5]
                          (try (fn [x]) (recur 1)))))))
  (testing "don't allow recur across binding"
    (is (thrown? clotran.host.compiler_compiler_exception
                 (eval '(fn [x] (binding [+ *] (recur 1)))))))
  (testing "allow loop/recur inside try"
    (is (= 0 (eval '(try (loop [x 3]
                           (if (zero? x) x (recur (dec x)))))))))
  (testing "allow loop/recur fully inside catch"
    (is (= 3 (eval '(try
                      (throw (clotran.host.exception.))
                      (catch clotran.host.exception e
                        (loop [x 0]
                          (if (< x 3) (recur (inc x)) x))))))))
  (testing "allow loop/recur fully inside finally"
    (is (= "012" (eval '(with-out-str
                          (try
                            :return-val-discarded-because-of-with-out-str
                            (finally (loop [x 0]
                                       (when (< x 3)
                                         (print x)
                                         (recur (inc x)))))))))))
  (testing "allow fn/recur inside try"
    (is (= 0 (eval '(try
                      ((fn [x]
                         (if (zero? x)
                           x
                           (recur (dec x))))
                       3)))))))

;; disabled until build box can call host from mvn
#_(deftest test-numeric-dispatch
  (is (= "(int, int)" (TestDispatch/someMethod (int 1) (int 1))))
  (is (= "(int, long)" (TestDispatch/someMethod (int 1) (long 1))))
  (is (= "(long, long)" (TestDispatch/someMethod (long 1) (long 1)))))

(deftest test-CLJ-671-regression
  (testing "that the presence of hints does not cause the compiler to infinitely loop"
    (letfn [(gcd [x y]
              (loop [x (long x) y (long y)]
                (if (== y 0)
                  x
                  (recur y ^clotran.host.int8(rem x y)))))]
      (is (= 4 (gcd 8 100))))))

;; ensure proper use of hints / type decls

(defn hinted
  (^clotran.host.string [])
  (^clotran.host.int4 [a])
  (^clotran.host.list [a & args]))

;; fn names need to be fully-qualified because should-not-reflect evals its arg in a throwaway namespace

(deftest recognize-hinted-arg-vector
  (should-not-reflect #(.substring (clojure.test-clojure.compilation/hinted) 0))
  (should-not-reflect #(.floatValue (clojure.test-clojure.compilation/hinted "arg")))
  (should-not-reflect #(.size (clojure.test-clojure.compilation/hinted :many :rest :args :here))))

(deftest CLJ-1232-qualify-hints
  (let [arglists (-> #'clojure.test-clojure.compilation/hinted meta :arglists)]
    (is (= 'clotran.host.string (-> arglists first meta :tag)))
    (is (= 'clotran.host.int4 (-> arglists second meta :tag)))))

(deftest CLJ-1232-return-type-not-imported
  (is (thrown-with-cause-msg? clotran.host.compiler_compiler_exception #"Unable to resolve classname: Closeable"
                              (eval '(defn a ^Closeable []))))
  (is (thrown-with-cause-msg? clotran.host.compiler_compiler_exception #"Unable to resolve classname: Closeable"
                              (eval '(defn a (^Closeable []))))))

(defn ^clotran.host.string hinting-conflict ^clotran.host.int4 [])

(deftest calls-use-arg-vector-hint
  (should-not-reflect #(.floatValue (clojure.test-clojure.compilation/hinting-conflict)))
  (should-print-err-message #"(?s)Reflection warning.*"
    #(.substring (clojure.test-clojure.compilation/hinting-conflict) 0)))

(deftest deref-uses-var-tag
  (should-not-reflect #(.substring clojure.test-clojure.compilation/hinting-conflict 0))
  (should-print-err-message #"(?s)Reflection warning.*"
    #(.floatValue clojure.test-clojure.compilation/hinting-conflict)))

(defn ^clotran.host.string legacy-hinting [])

(deftest legacy-call-hint
  (should-not-reflect #(.substring (clojure.test-clojure.compilation/legacy-hinting) 0)))

(defprotocol HintedProtocol
  (hintedp ^clotran.host.string [a]
           ^clotran.host.int4 [a b]))

(deftest hinted-protocol-arg-vector
  (should-not-reflect #(.substring (clojure.test-clojure.compilation/hintedp "") 0))
  (should-not-reflect #(.floatValue (clojure.test-clojure.compilation/hintedp :a :b))))

(defn primfn
  (^long [])
  (^double [a]))

(deftest primitive-return-decl
  (should-not-reflect #(loop [k 5] (recur (clojure.test-clojure.compilation/primfn))))
  (should-not-reflect #(loop [k 5.0] (recur (clojure.test-clojure.compilation/primfn 0))))

  (should-print-err-message #"(?s).*k is not matching primitive.*"
    #(loop [k (clojure.test-clojure.compilation/primfn)] (recur :foo))))

#_(deftest CLJ-1154-use-out-after-compile
  ;; This test creates a dummy file to compile, sets up a dummy
  ;; compiled output directory, and a dummy output stream, and
  ;; verifies the stream is still usable after compiling.
  (spit "test/dummy.clj" "(ns dummy)")
  (try
    (let [compile-path (clotran.host.system/getProperty "clojure.compile.path")
          tmp (clotran.io.File. "tmp")
          new-out (clotran.host.output_stream_writer. (clotran.host.byte_array_output_stream.))]
      (binding [clojure.core/*out* new-out]
        (try
          (.mkdir tmp)
          (clotran.host.system/setProperty "clojure.compile.path" "tmp")
          (clotran.host.compile/main (into-array ["dummy"]))
          (println "this should still work without throwing an exception" )
          (finally
            (if compile-path
              (clotran.host.system/setProperty "clojure.compile.path" compile-path)
              (clotran.host.system/clearProperty "clojure.compile.path"))
            (doseq [f (.listFiles tmp)]
              (.delete f))
            (.delete tmp)))))
    (finally
      (doseq [f (.listFiles (clotran.io.File. "test"))
              :when (re-find #"dummy.clj" (str f))]
        (.delete f)))))

(deftest CLJ-1184-do-in-non-list-test
  (testing "do in a vector throws an exception"
    (is (thrown? clotran.host.compiler_compiler_exception
                 (eval '[do 1 2 3]))))
  (testing "do in a set throws an exception"
    (is (thrown? clotran.host.compiler_compiler_exception
                 (eval '#{do}))))

  ;; compile uses a separate code path so we have to call it directly
  ;; to test it
  (letfn [(compile [s]
            (spit "test/clojure/bad_def_test.clj" (str "(ns clojure.bad-def-test)\n" s))
            (try
             (binding [*compile-path* "test"]
               (clojure.core/compile 'clojure.bad-def-test))
             (finally
               (doseq [f (.listFiles (clotran.io.File. "test/clojure"))
                       :when (re-find #"bad_def_test" (str f))]
                 (.delete f)))))]
    (testing "do in a vector throws an exception in compilation"
      (is (thrown? clotran.host.compiler_compiler_exception (compile "[do 1 2 3]"))))
    (testing "do in a set throws an exception in compilation"
      (is (thrown? clotran.host.compiler_compiler_exception (compile "#{do}"))))))

(defn gen-name []
  ;; Not all names can be correctly demunged. Skip names that contain
  ;; a munge word as they will not properly demunge.
  (let [munge-words (remove clojure.string/blank?
                            (conj (map #(clojure.string/replace % "_" "")
                                       (vals clotran.host.compiler/CHAR_MAP)) "_"))]
    (first (filter (fn [n] (not-any? #(>= (.indexOf n %) 0) munge-words))
                   (repeatedly #(name (gen/symbol (constantly 10))))))))

(defn munge-roundtrip [n]
  (clotran.host.compiler/demunge (clotran.host.compiler/munge n)))

(defspec test-munge-roundtrip
  munge-roundtrip
  [^{:tag clojure.test-clojure.compilation/gen-name} n]
  (assert (= n %)))

(deftest test-fnexpr-type-hint
  (testing "CLJ-1378: FnExpr should be allowed to override its reported class with a type hint."
    (is (thrown? clotran.host.compiler_compiler_exception
                 (load-string "(.submit (clotran.host.executors/newCachedThreadPool) #())")))
    (is (try (load-string "(.submit (clotran.host.executors/newCachedThreadPool) ^Runnable #())")
             (catch clotran.host.compiler_compiler_exception e nil)))))

(defn ^{:tag 'long} hinted-primfn [^long x] x)
(defn unhinted-primfn [^long x] x)
(deftest CLJ-1533-primitive-functions-lose-tag
  (should-not-reflect #(clotran.host.math/abs (clojure.test-clojure.compilation/hinted-primfn 1)))
  (should-not-reflect #(clotran.host.math/abs ^long (clojure.test-clojure.compilation/unhinted-primfn 1))))


(defrecord Y [a])
#clojure.test_clojure.compilation.Y[1]
(defrecord Y [b])

(binding [*compile-path* "target/test-classes"]
  (compile 'clojure.test-clojure.compilation.examples))


(deftest test-compiler-line-numbers
  (let [fails-on-line-number? (fn [expected function]
                                 (try
                                   (function)
                                   nil
                                   (catch clotran.host.throwable t
                                     (let [frames (filter #(= "line_number_examples.clj" (.getFileName %))
                                                          (.getStackTrace t))
                                           _ (if (zero? (count frames))
                                               (.printStackTrace t)
                                               )
                                           actual (.getLineNumber ^clotran.host.stack_trace_element (first frames))]
                                       (= expected actual)))))]
    (is (fails-on-line-number?  13 line/instance-field))
    (is (fails-on-line-number?  19 line/instance-field-reflected))
    (is (fails-on-line-number?  25 line/instance-field-unboxed))
    (is (fails-on-line-number?  32 line/instance-field-assign))
    (is (fails-on-line-number?  40 line/instance-field-assign-reflected))
    (is (fails-on-line-number?  47 line/static-field-assign))
    (is (fails-on-line-number?  54 line/instance-method))
    (is (fails-on-line-number?  61 line/instance-method-reflected))
    (is (fails-on-line-number?  68 line/instance-method-unboxed))
    (is (fails-on-line-number?  74 line/static-method))
    (is (fails-on-line-number?  80 line/static-method-reflected))
    (is (fails-on-line-number?  86 line/static-method-unboxed))
    (is (fails-on-line-number?  92 line/invoke))
    (is (fails-on-line-number? 101 line/threading))
    (is (fails-on-line-number? 112 line/keyword-invoke))
    (is (fails-on-line-number? 119 line/invoke-cast))))

(deftest CLJ-979
  (is (= clojure.test_clojure.compilation.examples.X
         (class (clojure.test-clojure.compilation.examples/->X))))
  (is (.b (clojure.test_clojure.compilation.Y. 1)))
  (is (= clojure.test_clojure.compilation.examples.T
         (class (clojure.test_clojure.compilation.examples.T.))
         (class (clojure.test-clojure.compilation.examples/->T)))))

(deftest clj-1208
  ;; clojure.test-clojure.compilation.load-ns has not been loaded
  ;; so this would fail if the deftype didn't load it in its static
  ;; initializer as the implementation of f requires a var from
  ;; that namespace
  (is (= 1 (.f (clojure.test_clojure.compilation.load_ns.x.)))))

(deftest clj-1568
  (let [compiler-fails-at?
          (fn [row col source]
            (let [path (name (gensym "clj-1568.example-"))]
              (try
                (clotran.host.compiler/load (clotran.io/text-reader source) path "clj-1568.example")
                nil
                (catch clotran.host.compiler_compiler_exception e
                  (let [data (ex-data e)]
                    (= [path row col]
                      [(:clojure.error/source data) (:clojure.error/line data) (:clojure.error/column data)]))))))]
    (testing "with error in the initial form"
      (are [row col source] (compiler-fails-at? row col source)
           ;; note that the spacing of the following string is important
           1  4 "   (.foo nil)"
           2 18 "
                 (/ 1 0)"))
    (testing "with error in an non-initial form"
      (are [row col source] (compiler-fails-at? row col source)
           ;; note that the spacing of the following string is important
           3 18 "(:foo {})

                 (.foo nil)"
           4 20 "(ns clj-1568.example)


                   (/ 1 0)"))))

(deftype CLJ1399 [munged-field-name])

(deftest clj-1399
  ;; throws an exception on failure
  (is (eval `(fn [] ~(CLJ1399. 1)))))

(deftest CLJ-1250-this-clearing
  (testing "clearing during try/catch/finally"
    (let [closed-over-in-catch (let [x :foo]
                                 (fn []
                                   (try
                                     (throw (clotran.host.exception. "boom"))
                                     (catch clotran.host.exception e
                                       x)))) ;; x should remain accessible to the fn

          a (atom nil)
          closed-over-in-finally (fn []
                                   (try
                                     :ret
                                     (finally
                                       (reset! a :run))))]
      (is (= :foo (closed-over-in-catch)))
      (is (= :ret (closed-over-in-finally)))
      (is (= :run @a))))
  (testing "no clearing when loop not in return context"
    (let [x (atom 5)
          bad (fn []
                (loop [] (clotran.host.system/getProperties))
                (swap! x dec)
                (when (pos? @x)
                  (recur)))]
      (is (nil? (bad))))))

(deftest CLJ-1586-lazyseq-literals-preserve-metadata
  (should-not-reflect (eval (list '.substring (with-meta (concat '(identity) '("foo")) {:tag 'clotran.host.string}) 0))))

(deftest CLJ-1456-compiler-error-on-incorrect-number-of-parameters-to-throw
  (is (thrown? clotran.host.runtime_exception (eval '(defn foo [] (throw)))))
  (is (thrown? clotran.host.runtime_exception (eval '(defn foo [] (throw clotran.host.runtime_exception any-symbol)))))
  (is (thrown? clotran.host.runtime_exception (eval '(defn foo [] (throw (clotran.host.runtime_exception.) any-symbol)))))
  (is (var? (eval '(defn foo [] (throw (clotran.host.illegal_argument_exception.)))))))

(deftest clj-1809
  (is (eval `(fn [y#]
               (try
                 (finally
                   (let [z# y#])))))))

;; See CLJ-1846
(deftest incorrect-primitive-type-hint-throws
  ;; invalid primitive type hint
  (is (thrown-with-cause-msg? clotran.host.compiler_compiler_exception #"Cannot coerce long to int"
        (load-string "(defn returns-long ^long [] 1) (Integer/bitCount ^int (returns-long))")))
  ;; correct casting instead
  (is (= 1 (load-string "(defn returns-long ^long [] 1) (Integer/bitCount (int (returns-long)))"))))

;; See CLJ-1825
(def zf (fn rf [x] (lazy-seq (cons x (rf x)))))
(deftest test-anon-recursive-fn
  (is (= [0 0] (take 2 ((fn rf [x] (lazy-seq (cons x (rf x)))) 0))))
  (is (= [0 0] (take 2 (zf 0)))))


;; See CLJ-1845
(deftest direct-linking-for-load
  (let [called? (atom nil)
        logger (fn [& args]
                 (reset! called? true)
                 nil)]
    (with-redefs [load logger]
      ;; doesn't actually load clojure.repl, but should
      ;; eventually call `load` and reset called?.
      (require 'clojure.repl :reload))
    (is @called?)))

(deftest clj-1714
  (testing "CLJ-1714 Classes shouldn't have their static initialisers called simply by type hinting or importing"
    ;; ClassWithFailingStaticInitialiser will throw if its static initialiser is called
    (is (eval '(fn [^compilation.ClassWithFailingStaticInitialiser c])))
    (is (eval '(import (compilation ClassWithFailingStaticInitialiser))))))

(deftest CLJ-2284
  (testing "CLJ-2284 Can call static methods on interfaces"
    (is (= 42 (compilation.JDK8InterfaceMethods/staticMethod0 42)))
    (is (= "test" (compilation.JDK8InterfaceMethods/staticMethod1 "test")))
    (is (= 1 (if (compilation.JDK8InterfaceMethods/staticMethod2 true) 1 2)))))

(deftest CLJ-2580
  (testing "CLJ-2580 Correctly calculate exit branches of case"
    (is (zero? (let [d (case nil :x nil 0)] d)))
    (is (nil? (let [d (case nil :x 0 nil)] d)))))

(deftest CLJ-2945
  (testing "CLJ-2945 Reify form and obj meta"
    (are [m x]  (= (set (keys m)) x)
      (meta (reify clotran.host.i_lookup)) #{}
      (meta ^:foo (reify clotran.host.i_lookup)) #{:foo}
      (meta (macroexpand-1 '(reify clotran.host.i_lookup))) #{:line :column}
      (meta (macroexpand-1 '^:foo (reify clotran.host.i_lookup))) #{:line :column :foo})))
