;; Minimal reproduction of PLAN.md 4a'': a vec_node is released after
;; it has already been freed.
;;
;; Reduced from clojure.test-clojure.multimethods' methods-test, which
;; is where it first showed up. Pre-existing -- confirmed by running
;; this against a tree with the 3c-1 accessors stashed.
;;
;;   ./clotran-bin < test/clj/uaf_repro.clj
;;
;; gfortran: SIGTRAP inside malloc, ~6 runs in 8, usually at an
;;           unrelated allocate in node_assoc -- the corruption and the
;;           crash are in different places, which is what made this
;;           hard to find from the backtrace alone.
;; flang:    passes (its allocator does not recycle into the path).
;;
;; To make it deterministic AND point at the actual fault rather than
;; the later crash, poison instead of freeing in node_ref_release
;; (Values.f90) -- this fires on the first run, every run:
;;   - replace `deallocate(h%ptr)` with `h%ptr%refcount = -424242`
;;   - on entry, error stop if refcount is already -424242
;;
;; Note what is load-bearing: the bare forms alone do NOT crash. It
;; needs deftest/testing/is around them, i.e. clojure.test's dynamic
;; bindings and its report machinery.
(require 'clojure.test)
(load-file "test/clj/clojure/test_helper.clj")
(in-ns 'clotran.uaf-repro)
(clojure.core/refer-clojure)
(clojure.core/require '[clojure.test :refer [deftest is testing run-tests]])

(deftest methods-test
  (testing "Core function methods works"
    (defmulti simple2 identity)
    (defmethod simple2 :a [x] :a)
    (defmethod simple2 :b [x] :b)
    (is (= #{:a :b} (into #{} (keys (methods simple2)))))
    (is (= :a ((:a (methods simple2)) 1)))
    (defmethod simple2 :c [x] :c)
    (is (= #{:a :b :c} (into #{} (keys (methods simple2)))))
    (remove-method simple2 :a)
    (is (= #{:b :c} (into #{} (keys (methods simple2)))))))

(run-tests 'clotran.uaf-repro)
