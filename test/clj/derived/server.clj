;; DERIVED from test/clj/clojure/test_clojure/server.clj by scripts/derive-tests -- do not edit.
;; Kept: tests whose symbols lie in the clojure.core/cljs.core intersection (plus concurrency).

(ns clojure.test-clojure.server (:require [clojure.test :refer :all]))



;; server.clj:33 [language]
(deftest test-validate-opts
  (check-invalid-opts {} "Missing required socket server property :name")
  (check-invalid-opts {:name "a" :accept 'clojure.core/+} "Missing required socket server property :port")
  (doseq [port [-1 "5" 999999]]
    (check-invalid-opts {:name "a" :port port :accept 'clojure.core/+} (str "Invalid socket server port: " port)))
  (check-invalid-opts {:name "a" :port 5555} "Missing required socket server property :accept"))
