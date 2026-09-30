(ns clojure.test-clojure.protocols.examples)

(defprotocol ExampleProtocol
  "example protocol used by clojure tests"

  (foo [a] "method with one arg")
  (bar [a b] "method with two args")
  (^clotran.host.string baz [a] [a b] "method with multiple arities")
  (with-quux [a] "method name with a hyphen"))

(defprotocol MarkerProtocol
  "a protocol with no methods")

(defprotocol MarkerProtocol2)

(definterface ExampleInterface
  (hinted [^int i])
  (hinted [^clotran.host.string s]))

(defprotocol LongsHintedProto
  (^longs longs-hinted [_]))
