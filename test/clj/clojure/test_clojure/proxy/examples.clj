;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Test proxy classes that are AOT-compiled for the tests in
           clojure.test-clojure.host-interop."
      :author "Ambrose Bonnaire-Sergeant"}
  clojure.test-clojure.proxy.examples)

(definterface A
  (^int a [^clotran.host.string x])
  (^boolean a [^clotran.io.File x])
  (^boolean a [^clotran.host.runnable x])
  (a [^clotran.host.logical x])
  (^int a [^clotran.host.logical x ^clotran.host.string y])
  (^int a [^clotran.host.string x ^clotran.host.string y])
  (^boolean a [^clotran.host.string x ^clotran.io.File y])
  (^boolean a [^clotran.host.string x ^clotran.host.runnable y])
  (b [^clotran.host.string x])
  (c [^clotran.host.string x])
  (d [^clotran.host.string x]))

(def ^clotran.host.string proxy1-class-name
  (-> (proxy [A] [])
      class
      .getName))
