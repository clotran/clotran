;; DERIVED from upstream/clojure/test/clojure/test_clojure/agents.clj by upstream/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.agents (:use clojure.test))

(def fragile-wait 1000)

(def ^:dynamic *bind-me* :root-binding)

;; agents.clj:38 [concurrency]
(deftest default-modes
  (is (= :fail (error-mode (agent nil))))
  (is (= :continue (error-mode (agent nil :error-handler println)))))

;; agents.clj:42 [concurrency]
(deftest continue-handler
  (let [err (atom nil)
        agt (agent 0 :error-mode :continue :error-handler #(reset! err %&))]
    (send agt /)
    (is (true? (await-for fragile-wait agt)))
    (is (= 0 @agt))
    (is (nil? (agent-error agt)))
    (is (= agt (first @err)))
  (is (true? (instance? clotran.host.arithmetic_exception (second @err))))))
