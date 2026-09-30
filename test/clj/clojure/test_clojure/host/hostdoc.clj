;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.test-clojure.host.hostdoc
  (:use clojure.test
	[clotran.api-docs :as j])
  (:require [clojure.string :as str])
  (:import ))

(defn correct-url [url-pattern-str module-name url-suffix]
  (str (format url-pattern-str module-name) url-suffix))

(deftest hostdoc-url-test
  (testing "for a core api"
    (binding [*feeling-lucky* false]
      (are [x y] (= x (#'j/hostdoc-url y))
           nil "foo.Bar"
           (correct-url *core-host-api* "host.base" "clotran/host/string.html") "clotran.host.string"
           (correct-url *core-host-api* "host.sql" "clotran/host/connection.html") "clotran.host.connection")))
  (testing "for a remote hostdoc"
    (binding [*remote-hostdocs* (ref (sorted-map "host." "http://example.com/"))]
      (is (= "http://example.com/host/lang/Number.html" (#'j/hostdoc-url "clotran.host.number"))))))
