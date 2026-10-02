;; Forms whose value real Clojure decides. scripts/oracle runs this file
;; through `clj` and through clotran and compares. No expected values
;; live here: clj supplies them. Setup forms (def, deftype, require)
;; run on both sides and are not compared. (expect-diff "why") before
;; a form says it MUST differ, and names the DEVIATIONS entry.
;;
;; Derived from language_test.clj on 2026-09-19; that file keeps the
;; checks only clotran can answer (Fortran arrays, clotran-type).

(deftype Point [x y]
  clotran.host.value
  (toString [this] (str "Point(" x "," y ")")))

(def p (->Point 3 4))

;; deftype field read
(.-x p)

;; deftype method sees fields as names
(.toString p)

;; deftype instance? by short name
(instance? Point p)

;; deftype is not map-like
(:x p)

;; reify closes over its scope
(str (let [f "foo"] (reify clotran.host.value (toString [this] f))))

(defprotocol Shape
  (area [s])
  (scale [s k]))

(deftype Rect [w h]
  Shape
  (area [_] (* w h))
  (scale [_ k] (Rect. (* w k) (* h k))))

(def r (->Rect 2 5))

;; protocol method on a deftype
(area r)

;; a method can construct its own type
(area (scale r 3))

;; satisfies? a protocol it declares
(satisfies? Shape r)

;; satisfies? one it does not
(satisfies? Shape p)

;; letfn mutual recursion
(letfn [(ev? [n] (if (zero? n) true (od? (dec n)))) (od? [n] (if (zero? n) false (ev? (dec n))))] [(ev? 10) (od? 10)])

;; letfn self recursion
(letfn [(f [n] (if (< n 2) 1 (* n (f (dec n)))))] (f 5))

;; map-indexed
(map-indexed vector [:a :b :c])

(defrecord P [a b])

(def rec (->P 1 2))

;; record keyword lookup
(:a rec)

;; record get
(get rec :a)

;; record get not-found
(get rec :nope :none)

;; record count
(count rec)

;; record seq
(seq rec)

;; record keys
(keys rec)

;; record vals
(vals rec)

;; record equality by value
(= (->P 1 2) (->P 1 2))

;; record inequality
(= (->P 1 2) (->P 1 9))

;; record?
(record? rec)

;; record assoc keeps type
(:a (assoc rec :a 9))

;; record assoc a new key
(:c (assoc rec :c 3))

;; record contains?
(contains? rec :a)

;; map-> factory
(:b (map->P {:a 1, :b 2}))

;; map-> extra keys
(:z (map->P {:a 1, :b 2, :z 9}))

;; identical? on equal collections
(identical? [1] [1])

;; = on equal collections
(= [1] [1])

;; identical? on interned keywords
(identical? :a :a)

;; identical? on the same object
(let [v [1]] (identical? v v))

;; symbol keeps its qualifier
(symbol "a.b.C/create")

;; namespace of that symbol
(namespace (symbol "a.b.C/create"))

;; name of that symbol
(name (symbol "a.b.C/create"))

;; keyword keeps its qualifier
(keyword "a/b")

;; str of a namespace
(str (the-ns (quote clojure.core)))

;; str of a namespace nested
(expect-diff "DEVIATIONS 21: a host object prints as #<kind ...>, not #object[...]")
(str [(the-ns (quote clojure.core))])

;; lazy seq = vector
(= (map inc [0 1]) [1 2])

;; vector = lazy seq
(= [1 2] (map inc [0 1]))

;; lazy seq = lazy seq
(= (map inc [0 1]) (map inc [0 1]))

;; list = vector
(= (list 1 2) [1 2])

;; seq of a string
(= (seq "ab") [\a \b])

;; seq of a map
(= (seq {:a 1}) [[:a 1]])

;; nested lazy
(= (map vector [1] [2]) [[1 2]])

;; shorter lazy seq
(= (map inc [0]) [1 2])

;; longer lazy seq
(= (map inc [0 1 2]) [1 2])

;; a set is not sequential
(= #{1 2} [1 2])

;; a string is not sequential
(= "ab" [\a \b])

;; nil is not an empty vector
(= nil [])

;; metadata does not change =
(= (with-meta [1 2] {:a 1}) [1 2])

;; infinite vs vector
(= (range) [1 2])

;; infinite sharing a prefix
(= (iterate inc 1) [1 2])

(require (quote [clojure.string :refer [join]]))

;; require :refer [sym]
(join "-" [1 2])

(require (quote [clojure.string :refer :all]))

;; require :refer :all
(capitalize "ab")

(require (quote [clojure.set :as st]))

;; require :as still works
(st/union #{1} #{2})

;; set = set
(= #{1 2} #{1 2})

;; set built vs literal
(= (conj #{1} 2) #{1 2})

;; sets differing
(= #{1} #{2})

;; sets sized apart
(= #{1} #{1 2})

;; empty sets
(= #{} #{})

;; collection in a set
(= #{[1]} #{[1]})

;; keyword on a map with meta
(:a (with-meta {:a 1} {:x 9}))

;; select-keys result is looked up
(:refer (select-keys {:refer [1], :as 2} (quote (:refer))))

;; update-vals
(update-vals {:a 1, :b 2} inc)

;; update-keys
(update-keys {:a 1} name)

;; parse-long
(parse-long "42")

;; parse-long nil
(parse-long "x")

;; parse-double
(parse-double "1.5")

;; parse-double nil
(parse-double "x")

;; parse-boolean
(parse-boolean "true")

;; parse-boolean nil
(parse-boolean "x")

;; NaN?
(NaN? (/ 0.0 0.0))

;; NaN? on a number
(NaN? 1.0)

;; infinite?
(infinite? (/ 1.0 0.0))

;; infinite? on a number
(infinite? 1.0)

;; delay
(let [n (atom 0) d (delay (swap! n inc))] [(realized? d) (clojure.core/deref d) (clojure.core/deref d) (realized? d) (clojure.core/deref n)])

;; force
(force (delay 7))

;; force a non-delay
(force 7)

;; hex
[31 31 -31]

;; octal
[63 63 0]

;; radix
[11 -11 35 11]

;; exponent
[1000.0 0.0015 1000.0]

;; exponent forms
[1000.0 10000.0 0.0]

;; plain
[42 -42 5.0 1.5]

;; .5 is a symbol
(symbol? (quote .5))

;; an N suffix reads
(number? (quote 42N))

;; an M suffix reads
(number? (quote 1.5M))

;; identities
[(+) (*) (+ 5) (* 5) (- 5)]

;; integer
[(+ 1 2) (- 5 2) (* 3 4) (+ 1 2 3 4) (- 10 1 2) (* 2 3 4)]

;; mixed
[(+ 1.5 2) (* 2.0 3) (- 5.5 1)]

;; mixed varargs
[(+ 1 2.5 3) (* 2 3 0.5) (- 10 1.5 2)]

;; one argument
[(+ 1.5) (- 1.5) (* 2.0)]

;; division
[(/ 4 2) (/ 100 5 2) (/ 4.0 2)]

;; quot rem mod
[(quot 7 2) (rem 7 2) (mod 7 2)]

;; ...negative
[(quot -7 2) (rem -7 2) (mod -7 2)]

;; ...on reals
[(quot 7.0 2) (rem 7.0 2) (mod 7.0 2)]

;; quot by zero
(try (quot 1 0) (catch clotran.host.throwable e :err))

;; = across types
(= 1 1.0)

;; == across types
(== 1 1.0)

;; == varargs
[(== 1 1.0 1) (== 1 2)]

;; comparisons
[(< 1 2.0) (> 3 2.5) (<= 2 2.0)]

;; min max abs
[(min 1 2.5) (max 1 2.5) (abs -3) (abs -3.5)]

;; inc dec
[(inc 1) (inc 1.5) (dec 1) (dec 1.5)]

(defstruct point :x :y)

;; struct
(struct point 1 2)

;; struct partial
(struct point 1)

;; struct-map
(struct-map point :x 1)

;; struct extra
(struct-map point :x 1 :z 9)

;; struct keys
(vec (keys (struct point 1 2)))

;; struct is a map
(map? (struct point 1 2))

;; struct assoc
(assoc (struct point 1 2) :z 3)

;; accessor
((accessor point :x) (struct point 1 2))

;; too many vals
(try (struct point 1 2 3) (catch clotran.host.throwable e :err))

;; not a basis key
(try (accessor point :q) (catch clotran.host.throwable e :err))

;; kwargs
((fn [& {:keys [a b]}] [a b]) :a 1 :b 2)

;; kwargs map
((fn [& {:keys [a b]}] [a b]) {:a 1, :b 2})

;; empty map
(= {} (apply hash-map []))

;; seq of strings
(pr-str (seq ["b" "a"]))

;; rest of strings
(pr-str (rest ["a" "b"]))

;; seq nests
(pr-str (seq [["a"]]))

;; a lazy seq
(pr-str (map identity ["a"]))

;; a seq has a type. clotran has ONE seq view where clj has
;; ChunkedSeq, StringSeq and the rest, so the name it answers is the
;; commonest of them.
(type (seq ["a"]))

;; class answers the class a literal names, so the two compare equal
[(= (class "a") clotran.host.string) (= (class 1) clotran.host.int8) (= (class 1.5) clotran.host.real8) (= (class \a) clotran.host.char)
 (= (class true) clotran.host.logical) (= (class :k) clotran.host.keyword) (= (class 'a) clotran.host.symbol)]

[(= (class []) clotran.host.persistent_vector) (= (class {}) clotran.host.persistent_array_map)
 (= (class #{}) clotran.host.persistent_hash_set) (= (class '(1)) clotran.host.persistent_list)
 (= (class (lazy-seq [1])) clotran.host.lazy_seq) (= (class (seq [1 2])) clotran.host.persistent_vector_chunked_seq)]

[(= (class (atom 1)) clotran.host.atom) (= (class (delay 1)) clotran.host.delay) (= (class #'first) clotran.host.var)
 (= (class #"x") clotran.host.pattern) (= (class *ns*) clotran.host.namespace) (= (class 1/2) clotran.host.ratio)]

;; which is what pprint's writers do
[(condp = (class "x") clotran.host.string :s clotran.host.int8 :l :other) (condp = (class 2) clotran.host.string :s clotran.host.int8 :l :other) (condp = (class 2.5) clotran.host.string :s clotran.host.int8 :l :other)]

;; nil has no class; type reads :type metadata first
[(class nil) (type (with-meta [] {:type :mine})) (= (type "a") clotran.host.string)]

;; instance? and supers agree with class
[(instance? (class "a") "a") (instance? (class []) []) (instance? (class 1) 1)
 (contains? (supers (class [])) clotran.host.i_persistent_collection) (contains? (supers (class "a")) clotran.host.char_sequence)
 (contains? (supers (class 1)) clotran.host.number) (contains? (supers (class (atom 1))) clotran.host.i_deref)]

;; a thrown thing's class is the one it was made with
[(= (class (ex-info "e" {})) clotran.host.exception_info) (= (class (clotran.host.exception. "e")) clotran.host.exception)
 (= (class (try (throw (clotran.host.illegal_argument_exception. "x")) (catch clotran.host.exception e e))) clotran.host.illegal_argument_exception)]

;; char readably
(pr-str \a)

;; char in a vector
(pr-str [\a \b])

;; char in a seq
(pr-str (seq [\a]))

;; named chars
[(pr-str \newline) (pr-str \space) (pr-str \tab)]

;; str of a char
(str \a)

;; compare numbers
[(compare 1 2) (compare 2 1) (compare 1 1)]

;; compare text
[(compare "a" "b") (compare :a :b) (compare \a \b)]

;; compare nil
[(compare nil 1) (compare 1 nil) (compare nil nil)]

;; compare bool
[(compare false true) (compare true false)]

;; compare vectors
[(compare [1] [2]) (compare [1 2] [1]) (compare [1 2] [1 2])]

;; compare refuses
(try (compare 1 "a") (catch clotran.host.throwable e :err))

;; sort numbers
(vec (sort [3 1 2]))

;; sort empty
(vec (sort []))

;; sort a list
(vec (sort (quote (3 1 2))))

;; sort strings
(vec (sort ["b" "a" "c"]))

;; sort keywords
(vec (sort [:b :a]))

;; sort vectors
(vec (sort [[2] [1]]))

;; sort with >
(vec (sort > [1 3 2]))

;; sort-by
(vec (sort-by - [1 3 2]))

;; sort is stable
(vec (sort-by first [[1 :a] [0 :x] [1 :b] [0 :y]]))

;; sort 50
(= (sort (range 49 -1 -1)) (range 50))

;; to-array is an array
(let [a (to-array [3 1 2])] [(alength a) (aget a 0)])

;; an array seqs
(vec (to-array [3 1 2]))

;; first of an array
(first (to-array [3 1 2]))

;; vector as a key
(get {[1] 2} [1])

;; map with a key
(= {[1] 2} {[1] 2})

;; set of a vector
(= #{[1]} #{[1]})

;; map as a key
[(get {{:a 1} :v} {:a 1}) (contains? #{{:a 1}} {:a 1})]

;; order of entries
(get {{:b 2, :a 1} :m} {:a 1, :b 2})

;; list and vector
[(= [1 2] (list 1 2)) (get {[1 2] :v} (list 1 2)) (get {(list 1 2) :v} [1 2])]

;; case on a map
(case {:a 1, :b 2} {:b 2, :a 1} :map :default)

;; case on a vector
(case [1 2] [1 2] :vec :default)

;; case on a set
(case #{1 2} #{1 2} :set :default)

;; still not equal
[(= #{1} [1]) (get {[1] :v} [2])]

;; large literals
[9999999999 2147483648 -9999999999]

;; very large
123456789012345

;; large arith
[(+ 9999999999 1) (* 3000000000 3) (- 0 9999999999)]

;; large hex
68719476735

;; large compare
[(= 9999999999 9999999999) (< 2147483647 2147483648)]

;; large as a key
(get {9999999999 :found} 9999999999)

;; large in a set
(contains? #{9999999999} 9999999999)

;; case on a large int
(case 9999999999 9999999999 :yes 1410065407 :collided :no)

;; ...and its old truncation
(case 1410065407 9999999999 :wrong 1410065407 :right :no)

;; ...across the sign flip
(case 2147483648 2147483648 :big -2147483648 :collided :no)

;; reduced
[(/ 2 4) 1/2 -1/3]

;; collapses
[(/ 4 2) (/ 6 3) (/ 0 5)]

;; sign
[(/ -1 3) (/ 1 -3)]

;; reciprocal
(/ 2)

;; inexact div
(/ 1 3)

;; div by zero
(try (/ 1 0) (catch clotran.host.throwable e :err))

;; ratio arith
[(+ 1/2 1/3) (- 1/2 1/3) (* 2/3 3/4)]

;; with integer
(+ 1/2 1)

;; a double wins
(+ 1/2 0.5)

;; ratio =
[(= 1/2 1/2) (= 1/2 0.5)]

;; ratio ==
[(== 1/2 0.5) (= 2 2)]

;; ratio order
(< 1/3 1/2)

;; ratio parts
[(numerator 3/4) (denominator 3/4)]

;; ratio?
[(ratio? 3/4) (ratio? 2) (ratio? 0.5)]

;; a ratio is a number
(number? 1/2)

;; prints as n/d
(pr-str 3/4)

;; ratio inc dec
[(inc 1/2) (dec 1/2)]

;; ratio abs
(abs -1/2)

;; ratio min max
[(min 1/2 1/3) (max 1/2 1/3)]

;; ratio quot rem
[(quot 7/2 1) (rem 7/2 1) (mod 7/2 1)]

;; ratio coerce
[(int 1/2) (double 1/2)]

;; ratio compare
[(compare 1/3 1/2) (compare 1/2 1/2)]

;; ratio signs
[(pos? 1/2) (neg? -1/2)]

(def cm (make-array clotran.host.int4/TYPE 2 3))

;; core alength
(alength cm)

;; core aget full
[(aget cm 1 2) (aget cm 0 0)]

(def crow (aget cm 0))

;; a row is an array
[(alength crow) (aget crow 0) (aget crow 2)]

;; row then index
(aget (aget cm 1) 2)

;; a row is a view
(aget cm 0 1)

(def cclone (aclone crow))

;; aclone of a row
[(alength cclone) (aget cclone 0) (aget crow 0) (aget cclone 1)]

(def cobj (make-array clotran.host.value 2))

;; object array
[(aget cobj 0) (aget cobj 1) (alength cobj)]

(def cdbl (make-array clotran.host.real8/TYPE 2))

;; double array
[(aget cdbl 0) (aget cdbl 1)]

;; print a function
(expect-diff "DEVIATIONS 21: a function prints as #<fn>")
(pr-str (fn [x] x))

;; a function in a vector
(expect-diff "DEVIATIONS 21: a function prints as #<fn>")
(pr-str [1 (fn [x] x) 2])

;; str of a function
(expect-diff "DEVIATIONS 21: a function prints as #<fn>")
(str (fn [x] x))

;; heterogeneous vector
(let [v [1 2 3 "a" (fn [x] x) :kw {:m 1} #{9} [0]]] [(count v) (nth v 3) ((nth v 4) 42)])

;; meta on a function
(meta (with-meta (fn [] 1) {:a 1}))

;; macroexpand-1 a macro
(macroexpand-1 (quote (when a b)))

;; macroexpand-1 not a macro
(macroexpand-1 (quote (inc 1)))

;; macroexpand-1 a symbol
(macroexpand-1 (quote foo))

;; macroexpand-1 .member
(macroexpand-1 (quote (.foo x 1 2)))

;; macroexpand-1 ctor
(macroexpand-1 (quote (clotran.host.string. "a")))

;; macroexpand stops at the top
(macroexpand (quote (when a (when b c))))

;; special-symbol? if
(special-symbol? (quote if))

;; special-symbol? amp
(special-symbol? (quote &))

;; special-symbol? a name
(special-symbol? (quote foo))

;; specials count
(count (. clotran.host.compiler specials))

;; discard in a vector
[1 3]

;; discard an argument
(+ 1 2)

;; discard at the end
(and true)

;; discard last in vector
[1 2]

;; discard a map pair
{:a 1, :c 3}

;; discard in a set
#{1 3}

;; two discards in a row
(list 3)

;; prime-suffixed symbol
(let [ss' 1 x'y 2] [ss' x'y])

;; quote still quotes
(quote (a (quote b)))

;; prime in a quoted name
(str (quote foo'))

;; the quote character
\'

;; #^ is the old ^
(:a (meta (quote (x))))

;; #^Tag
(:tag (meta (quote (x))))

;; #^:kw
(:dynamic (meta (quote (x))))

;; empty a vector
(empty [1 2])

;; empty a map
(empty {:a 1})

;; empty a map past eight entries (a HAMT here), and what into builds
;; on it -- it answered nil, and into a list (scripts/fuzz-spec)
[(empty (zipmap (range 10) (range 10))) (map? (into (empty (zipmap (range 10) (range 10))) {:a 1}))
 (meta (empty (with-meta (zipmap (range 10) (range 10)) {:m 1})))]

;; empty a set
(empty #{1})

;; empty a list
(empty (quote (1 2)))

;; empty a seq
(empty (seq [1 2]))

;; empty a lazy seq
(empty (lazy-seq [1 2]))

;; empty nil
(empty nil)

;; empty a number
(empty 1)

;; empty a string
(empty "ab")

;; empty keeps type
[(vector? (empty [1])) (map? (empty {:a 1})) (set? (empty #{1})) (list? (empty (quote (1))))]

;; swap-vals!
(let [a (atom 1)] [(swap-vals! a inc) (clojure.core/deref a)])

;; swap-vals! args
(let [a (atom 1)] [(swap-vals! a + 1 2 3 4) (clojure.core/deref a)])

;; swap-vals! conj
(let [a (atom [])] [(swap-vals! a conj :x) (clojure.core/deref a)])

;; reset-vals!
(let [a (atom 1)] [(reset-vals! a 9) (clojure.core/deref a)])

(defmulti ltest-area :shape)

(defmethod ltest-area :square [s] (* (:side s) (:side s)))

(defmethod ltest-area :circle [s] 3)

(defmethod ltest-area :default [s] :none)

;; methods
(count (methods ltest-area))

;; methods keys
(sort-by str (keys (methods ltest-area)))

;; get-method
((get-method ltest-area :square) {:side 4})

;; get-method default
((get-method ltest-area :hexagon) {})

;; prefers
(prefers ltest-area)

;; remove-method
(do (remove-method ltest-area :circle) (count (methods ltest-area)))

(require (quote clojure.math))

;; Math/E
(= clotran.host.math/E clojure.math/E)

;; Math/PI
(= clotran.host.math/PI clojure.math/PI)

;; sin
(clojure.math/sin 0.5)

;; sqrt
(clojure.math/sqrt 2)

;; cbrt of -8
(clojure.math/cbrt -8)

;; log10
(clojure.math/log10 1000)

;; hypot
(clojure.math/hypot 3 4)

;; pow
(clojure.math/pow 2 10)

;; tanh
(clojure.math/tanh 1)

;; rint
[(clojure.math/rint 2.5) (clojure.math/rint 3.5) (clojure.math/rint -2.5)]

;; round
[(clojure.math/round 2.5) (clojure.math/round -2.5) (clojure.math/round 2.4)]

;; signum
[(clojure.math/signum -3.0) (clojure.math/signum 0.0) (clojure.math/signum 4.0)]

;; ceil/floor
[(clojure.math/ceil 1.2) (clojure.math/floor -1.2)]

;; ulp
(clojure.math/ulp 1.0)

;; next-up
(clojure.math/next-up 1.0)

;; next-down
(clojure.math/next-down 1.0)

;; next-after
(clojure.math/next-after 1.0 2.0)

;; get-exponent
[(clojure.math/get-exponent 1.0) (clojure.math/get-exponent 8.0) (clojure.math/get-exponent 0.5)]

;; scalb
(clojure.math/scalb 3.0 4)

;; copy-sign
(clojure.math/copy-sign 3.0 -1.0)

;; IEEE-remainder
(clojure.math/IEEE-remainder 5.0 3.0)

;; expm1
(clojure.math/expm1 1.0E-9)

;; log1p
(clojure.math/log1p 1.0E-9)

;; to-radians
(clojure.math/to-radians 180.0)

;; to-degrees
(clojure.math/to-degrees clotran.host.math/PI)

;; exact arithmetic
[(clojure.math/add-exact 1 2) (clojure.math/subtract-exact 5 9) (clojure.math/multiply-exact 6 7) (clojure.math/increment-exact 1) (clojure.math/decrement-exact 1) (clojure.math/negate-exact 5)]

;; add-exact overflows
(try (clojure.math/add-exact clotran.host.int8/MAX_VALUE 1) :no (catch clotran.host.throwable e :threw))

;; multiply-exact overflows
(try (clojure.math/multiply-exact clotran.host.int8/MAX_VALUE 2) :no (catch clotran.host.throwable e :threw))

;; floor-div/mod
[(clojure.math/floor-div -7 2) (clojure.math/floor-mod -7 2)]

;; Math/abs
[(clotran.host.math/abs -3) (clotran.host.math/abs -3.5)]

;; format %s
(format "%s" "a")

;; format two
(format "%s-%s" :a 1)

;; format %d
(format "%d" 42)

;; width and flags
(format "%5d|%-5d|%05d" 42 42 42)

;; format %x %X %o
(format "%x %X %o" 255 255 8)

;; format %f
(format "%f" 1.5)

;; format precision
(format "%.2f" 3.14159)

;; float width
(format "%10.3f|%-10.3f|" 3.14159 3.14159)

;; format %e
(format "%e" 1234.5)

;; format %b
(format "%b %b %b %b" true false nil 0)

;; format %c
(format "%c" \a)

;; format %%
(format "100%%")

;; format %n
(format "a%nb")

;; format %S
(format "%S" "ab")

;; string precision
(format "%.2s" "abcdef")

;; format nil
(format "%s" nil)

;; format a vector
(format "%s" [1 2])

;; format like core_print
(format "0x%x " 255)

;; double range
(count (range 0.0 360.0 5.0))

;; a double range counts as it walks, step added to step: 11, not 10
[(count (range 0.0 1.0 0.1)) (count (range 1 0 -0.1)) (count (range 0.5 3))]

;; double range head
(take 5 (range 0.0 360.0 5.0))

;; fractional step
(range 0.0 1.0 0.25)

;; double end only
(range 2.5)

;; ratio step
(range 0 1 1/4)

;; ratio end
(range 0 5/2)

;; negative step
(range 10 0 -2)

;; negative double step
(range 10.0 0.0 -2.5)

;; integer range
(range 0 10 2)

;; empty range
(range 0 0)

;; infinite range
(take 3 (range))

;; count a long range
(count (range 8000))

;; count a long take
(count (take 8000 (range 50000)))

;; count a long map
(count (take 8000 (map inc (range 50000))))

;; count a long iterate
(count (take 8000 (iterate inc 0)))

;; iterate is Iterate, head and tail, to class and instance?
[(class (iterate inc 0)) (class (next (iterate inc 0))) (class (range)) (instance? clotran.host.iterate (iterate inc 0)) (instance? clotran.host.iterate (range 3))]

;; walk a long range
(do (dorun (range 8000)) :ok)

;; the last of a long range
(last (range 8000))

;; a whole double
(pr-str 2.0)

;; a negative double
(pr-str -3.5)

;; negative zero
(pr-str -0.0)

;; zero
(pr-str 0.0)

;; seventeen digits
(pr-str 0.479425538604203)

;; a third
(pr-str (/ 1.0 3.0))

;; pi
(pr-str 3.141592653589793)

;; one tenth
(pr-str 0.1)

;; just inside
[(pr-str 0.001) (pr-str 1000000.0)]

;; just outside
[(pr-str 1.0E-4) (pr-str 1.0E7)]

;; large
(pr-str 1.0E20)

;; the largest double
(pr-str clotran.host.real8/MAX_VALUE)

;; a subnormal
(pr-str 2.2250738585072014E-308)

;; reads back
(= (read-string (pr-str 0.479425538604203)) 0.479425538604203)

;; read a list
(read-string "(1 2 3)")

;; read a map
(read-string "{:a 1}")

;; read one form
(read-string "1 2 3")

;; read a keyword
(read-string ":kw")

;; a bad form throws
(try (read-string "(1") :no (catch clotran.host.throwable e :threw))

;; Long bounds
[clotran.host.int8/MAX_VALUE clotran.host.int8/MIN_VALUE]

;; Integer bounds
[clotran.host.int4/MAX_VALUE clotran.host.int4/MIN_VALUE]

;; Double bounds
(expect-diff "DEVIATIONS 27: the smallest subnormal prints 5.0E-324, clj prints 4.9E-324")
[clotran.host.real8/MAX_VALUE clotran.host.real8/MIN_VALUE]

;; Double exponents
[clotran.host.real8/MAX_EXPONENT clotran.host.real8/MIN_EXPONENT]

;; the non-finite constants
[(pr-str clotran.host.real8/POSITIVE_INFINITY) (pr-str clotran.host.real8/NEGATIVE_INFINITY) (pr-str ##NaN)]

(require (quote [clojure.string :as ltstr]))

;; split
(ltstr/split "a,b,c" #",")

;; split with a limit
(ltstr/split "a,b,c" #"," 2)

;; split drops trailing empties
(ltstr/split "a,b,c," #",")

;; split -1 keeps them
(ltstr/split "a,b,c," #"," -1)

;; split on empty pattern
(ltstr/split "abc" #"")

;; split-lines
(ltstr/split-lines "a\nb\r\nc")

;; reverse
(ltstr/reverse "abc")

;; re-quote-replacement
(ltstr/re-quote-replacement "a$b\\c")

;; index-of a char
[(ltstr/index-of "hello" \l) (ltstr/last-index-of "hello" \l)]

;; replace a pattern
(ltstr/replace "abc" #"b" "X")

;; replace with a fn
(ltstr/replace "abc" #"b" (fn [m] (ltstr/upper-case m)))

;; replace with groups
(ltstr/replace "Almost Pig Latin" #"\b(\w)(\w+)\b" "$2$1ay")

;; replace-first
(ltstr/replace-first "aaa" #"a" "X")

;; replace a char
(ltstr/replace "abc" \b \X)

;; replace a string
(ltstr/replace "abcabc" "bc" "X")

;; replace an empty pattern
(ltstr/replace "abc" #"" "-")

(ns lt.other)

(def ^:dynamic *lt-counter* :unbound)

(defn lt-with [f] (binding [*lt-counter* 7] (f)))

(defn lt-peek [] *lt-counter*)

(in-ns 'user)

;; binding across namespaces
(lt.other/lt-with lt.other/lt-peek)

;; and it unwinds
(lt.other/lt-peek)

;; keyword on a set
(:at #{:colon :at})

;; get on a set
(get #{:at} :at)

;; get on a set misses
(:zz #{:at})

;; get with not-found
(get #{:at} :zz :d)

;; maps still work
[(get {:a 1} :a) (:a {:a 1})]

;; indexOf a code
(.indexOf "abcabc" (int \b))

;; indexOf a string
(.indexOf "abcabc" "b")

;; indexOf from
(.indexOf "abcabc" "b" 2)

;; indexOf misses
(.indexOf "abc" "z")

;; index-of a char
[(clojure.string/index-of "hello" \l) (clojure.string/index-of "hello" "l" 3) (clojure.string/last-index-of "hello" \l)]

;; into-array length
(alength (into-array [1 2 3]))

;; into-array element
(aget (into-array [1 2 3]) 1)

;; into-array seq
(seq (into-array [:x :y]))

;; an empty into-array
(alength (into-array []))

;; into-array with a type
(vec (into-array clotran.host.string ["a" "b"]))

;; an empty stack trace
(expect-diff "DEVIATIONS 31: stack traces are empty until PLAN.md step 5 gives the evaluator frames")
(alength (.getStackTrace (clotran.host.exception. "x")))

;; Throwable->map
(:cause (Throwable->map (clotran.host.exception. "boom")))

;; ex-data
(ex-data (ex-info "m" {:a 1}))

;; ex-message
(ex-message (ex-info "m" {:a 1}))

;; instance?
(instance? clotran.host.exception_info (ex-info "m" {}))

;; catch it by its full name
(try (throw (ex-info "m" {:a 1})) (catch clotran.host.exception_info e (ex-data e)))

;; a plain exception has no data
(ex-data (clotran.host.exception. "plain"))

;; a proxy method
(.toString (proxy [clotran.host.value] [] (toString [] "hello")))

;; str goes through it
(str (proxy [clotran.host.value] [] (toString [] "world")))

;; a closure
(let [n 5] (.toString (proxy [clotran.host.value] [] (toString [] (str n)))))

;; arguments
(expect-diff "DEVIATIONS 28: proxy accepts methods no superclass declares; Clojure refuses")
(let [q (proxy [clotran.host.value] [] (greet [n] (str "hi " n)) (two [a b] (+ a b)))] [(.greet q "x") (.two q 1 2)])

;; nested arities
(expect-diff "DEVIATIONS 28: proxy accepts methods no superclass declares; Clojure refuses")
(let [m (proxy [clotran.host.value] [] (f ([] 0) ([a] a) ([a b] (+ a b))))] [(.f m) (.f m 7) (.f m 3 4)])

;; this is implicit
(expect-diff "DEVIATIONS 28: proxy accepts methods no superclass declares; Clojure refuses")
(let [s (proxy [clotran.host.value] [] (me [] this))] (identical? s (.me s)))

;; threading
(.. "abc" toString toString)

;; with arguments
(.. "hello" (substring 1) (substring 1))

;; a plain member still works
(.toString "x")

;; .. expands to .
(macroexpand-1 (quote (.. a b)))

;; assoc a vector
(assoc [1 2] 0 9)

;; assoc appends at the end
(assoc [nil] 1 2)

;; assoc into an empty vector
(assoc [] 0 :x)

;; assoc past the end throws
(try (assoc [1] 5 :x) (catch clotran.host.throwable e :threw))

;; assoc-in through a vector
(assoc-in [[1]] [0 0] 9)

;; update a vector
(update [1 2] 0 inc)

;; contains? an index
[(contains? [1 2] 0) (contains? [1 2] 1) (contains? [1 2] 5) (contains? [1 2] -1)]

;; get by index
[(get [1 2] 0) (get [1 2] 5) (get [1 2] 5 :d) (get [1 2] :k)]

;; a string too
[(contains? "ab" 0) (contains? "ab" 9) (get "ab" 0) (get "ab" 9)]

;; String.contains
[(.contains "abc" "b") (.contains "abc" "z")]

;; conj nil onto a map
(conj {:a 1} nil)

;; merge with nil
[(merge {:a 1} nil) (merge nil nil)]

(require (quote [clojure.data :as ltdata]))

;; diff of maps
(ltdata/diff {:a 1} {:a 1, :b 2})

;; diff of vectors
(ltdata/diff [1 2] [1 3])

;; diff of sets
(ltdata/diff #{1 2} #{3 2})

;; diff of unlike things
(ltdata/diff {:a 1} :b)

;; diff of equals
(ltdata/diff 1 1)

;; diff nested
(ltdata/diff {:a {:b 1, :c 2}} {:a {:b 1, :c 3}})

(defn ltf0 [] 0)

(defn ltf1 [a] a)

(defn ltfm ([a] 1) ([a b] 2))

;; the message says how many
(try (ltf0 1) (catch clotran.host.throwable e (boolean (re-find #"Wrong number of args \(1\) passed to" (.getMessage e)))))

;; and which function
(try (ltf0 1) (catch clotran.host.throwable e (boolean (re-find #"ltf0" (.getMessage e)))))

;; too few
(try (ltf1) (catch clotran.host.throwable e (boolean (re-find #"Wrong number of args \(0\)" (.getMessage e)))))

;; a multi-arity fn
(try (ltfm 1 2 3) (catch clotran.host.throwable e (boolean (re-find #"Wrong number of args \(3\)" (.getMessage e)))))

;; catchable as ArityException
(try (ltf0 1) :no (catch clotran.host.arity_exception e :arity))

;; and as IllegalArgumentException
(try (ltf0 1) :no (catch clotran.host.illegal_argument_exception e :iae))

;; the right arities still work
[(ltfm 1) (ltfm 1 2)]

;; an explicit mode
(error-mode (agent 1 :error-mode :continue))

;; a validator does not change the mode
(error-mode (agent 1 :validator pos?))

;; a countdown latch
(let [l (clotran.host.count_down_latch. 2)] (.countDown l) (.getCount l))

;; a validator the state already fails is refused
(try (set-validator! (atom -1) pos?) :no (catch clotran.host.illegal_state_exception e :refused))

;; a PrintWriter shares its writer
(let [s (clotran.host.string_writer.) p (clotran.host.print_writer. s)] (.write p "hi") (str s))

;; and can stand in for *err*
(let [s (clotran.host.string_writer.) p (clotran.host.print_writer. s)] (binding [*err* p] (.write *err* "boom")) (str s))

;; require it
(require (quote clojure.core))

;; use it
(use (quote clojure.core))

;; and core still works
(+ 1 2)

;; N equals the plain integer
(= 1N 1)

;; M does not
(= 1M 1)

;; M equals itself
[(= 45M 45M) (= 1.5M 1.5M)]

;; a decimal is truthy
(cond 0M :a true :b)

;; arithmetic
[(+ 1N 1) (* 2M 3M)]

;; comparison
[(= 1N 1N) (< 1N 2N) (zero? 0M)]

;; negatives
[(- 0 2N) -3.5M]

;; read-string too
(read-string "1N")

;; not every N is a suffix
(map str [(quote aN) (quote Nx) (quote x1N)])

;; Long.
(clotran.host.int8. 1)

;; String.
(clotran.host.string. "x")

;; Integer.
(clotran.host.int4. 5)

;; Double.
(clotran.host.real8. 1.5)

;; Boolean.
(clotran.host.logical. true)

;; Character.
(clotran.host.char. \a)

;; Long. parses
(clotran.host.int8. "12")

;; Double. parses
(clotran.host.real8. "1.5")

;; Boolean. parses
[(clotran.host.logical. "true") (clotran.host.logical. "no")]

;; a bad parse throws
(try (clotran.host.int8. "zz") :no (catch clotran.host.throwable e :threw))

;; the box is the value
[(= (clotran.host.int8. 1) 1) (= (clotran.host.string. "x") "x")]

;; print-dup a double
(binding [*print-dup* true] (pr-str 1.5))

;; print-dup an integer
(binding [*print-dup* true] (pr-str 1))

;; print-dup a string
(binding [*print-dup* true] (pr-str "x"))

;; print-dup a char
(binding [*print-dup* true] (pr-str \a))

;; print-dup a boolean
(binding [*print-dup* true] (pr-str true))

;; print-dup nil
(binding [*print-dup* true] (pr-str nil))

;; print-dup a keyword
(binding [*print-dup* true] (pr-str :k))

;; print-dup a vector
(binding [*print-dup* true] (pr-str [1 2]))

;; print-dup a set
(binding [*print-dup* true] (pr-str #{1}))

;; print-method unchanged
[(pr-str 1) (pr-str 1.5) (pr-str "x") (pr-str [1 2]) (pr-str \newline) (pr-str {:a 1})]

;; and for seqs
[(pr-str (quote (1 2))) (pr-str #{1}) (pr-str (seq [1 2])) (pr-str (lazy-seq [1]))]

;; isNaN and isInfinite

;; the non-finite doubles print
[(pr-str ##NaN) (pr-str ##Inf) (pr-str ##-Inf)]

;; a list hashes as a vector
[(= (hash []) (hash (quote ()))) (= (hash [1]) (hash (quote (1)))) (= (hash [1 2]) (hash (quote (1 2))))]

;; a seq view too
[(= (hash (seq [1 2])) (hash [1 2])) (= (hash (rest [1 2 3])) (hash [2 3]))]

;; small integers do not collide with nil
(= (hash 2) (hash nil))

;; nor with each other
(= (count (set (map hash (range 20)))) 20)

;; pprint, through the real pretty writer: a proxy over Writer and IDeref
(require (quote clojure.pprint))

(with-out-str (clojure.pprint/pprint [1 2]))

(with-out-str (clojure.pprint/pprint (vec (range 40))))

(with-out-str (clojure.pprint/pprint {:a [1 2 3] :b "s" :c {:d (range 5)}}))

(with-out-str (clojure.pprint/pprint (quote (defn f [x] (let [y (* x 2)] (if (> y 10) :big :small))))))

;; twelve wide strings, so the block breaks (a 12-entry MAP would be a hash
;; map in clj and iterate in a different order: values, not text)
(with-out-str (clojure.pprint/pprint (vec (map #(apply str (repeat 8 (char (+ 97 %)))) (range 12)))))

(with-out-str (clojure.pprint/print-table [{:a 1 :b 2} {:a 3 :b 4}]))

;; reduce over a range, a vector and a list goes through the host's own
;; .reduce (IReduceInit), as LongRange.reduce and PersistentVector.reduce
;; do in clj; a reduced value stops it and is unwrapped
[(reduce + (range 100000)) (reduce + 5 (range 3)) (reduce + (range 0)) (reduce + [])
 (reduce + 1.5 (range 0.5 3)) (reduce + (range 10 0 -3)) (reduce conj [] (quote (1 2 3)))
 (reduce (fn [a x] (if (> x 3) (reduced a) (+ a x))) (range 10)) (reduce (fn [a x] (reduced :first)) 0 [1 2])
 (reduce max [3 9 2]) (reduce + (rest (range 5))) (reduce + (next (range 5)))]

[(instance? clotran.host.i_reduce_init (range 3)) (instance? clotran.host.i_reduce_init [1]) (instance? clotran.host.i_reduce_init (list 1))
 (instance? clotran.host.i_reduce_init (map inc [1])) (= (class (range 3)) clotran.host.long_range) (seq? (range 3)) (counted? [1])]

;; chunked seqs: a vector's seq and a range hand out chunks, map and
;; friends build ChunkedConses through a chunk buffer, as in clj
[(chunked-seq? (seq [1 2 3])) (chunked-seq? (range 5)) (chunked-seq? (seq (range 5))) (chunked-seq? (map inc [1 2]))
 (chunked-seq? (seq (map inc (range 100)))) (chunked-seq? (list 1 2)) (chunked-seq? (seq "ab")) (chunked-seq? nil)]

[(count (chunk-first (seq [1 2 3]))) (.nth (chunk-first (seq [1 2 3])) 1) (count (chunk-first (seq (range 100))))
 (count (chunk-first (seq (range 10)))) (seq (chunk-rest (seq (range 40)))) (chunk-next (seq [1 2]))]

[(into [] (map inc (range 100))) (vec (map inc (range 33))) (filter even? (range 70)) (keep #(when (odd? %) %) (range 50))
 (for [x (range 40) :when (even? x)] (* x x)) (map-indexed vector (range 35)) (map + (range 10) (range 5))]

[(reduce + (map inc (range 100))) (count (concat (range 40) [1 2])) (last (map inc (range 100))) (nth (map inc (range)) 100)
 (take 3 (map inc (range))) (first (filter #(> % 40) (range))) (rest (seq (map inc [1 2 3]))) (next (seq (map inc [1])))]

;; a seq whose tail is not realised hashes by identity, and map's own
;; chunk-cons is handed an unrealised rest, so this is the common case
(expect-diff "DEVIATIONS 35: an unrealised seq hashes by identity")
(= (hash (seq (map inc [1 2 3]))) (hash [2 3 4]))

;; ...while one that IS realised to the end hashes as the sequence
[(= (hash (doall (seq (map inc [1 2 3])))) (hash [2 3 4])) (= (hash (seq [2 3 4])) (hash (list 2 3 4)))]

[(= (map inc [1 2 3]) [2 3 4]) (= (seq (map inc (range 40))) (range 1 41))
 (pr-str (map inc (range 5))) (str (seq (map inc [1 2]))) (empty (seq (map inc [1 2]))) (with-out-str (doseq [x (range 40)] (print x)))]

[(count (chunk-first (seq (range 0.5 10.5)))) (map inc (range 0.5 4)) (map inc (range 10 0 -3)) (map inc (range 1/3 1 1/3))
 (sequential? (seq (map inc [1 2]))) (seq? (seq (map inc [1 2]))) (= (class (seq (map inc (range 5)))) clotran.host.chunked_cons)]

;; the clock exists (ClojureScript has system-time)
(pos? (clotran.host.system/nanoTime))

(number? (read-string (re-find #"[0-9.]+" (with-out-str (time nil)))))

;; futures and promises: core.clj's own definitions over the host's
;; tasks (tasks.inc), each on a thread of its own (PLAN.md step 14f)
@(future (+ 1 2))

(let [p (promise)] (deliver p 42) @p)

(let [p (promise)] (future (deliver p 42)) @p)

(let [p (promise)] [(realized? p) (do (deliver p 1) (realized? p)) @p])

(let [p (promise)] (deliver p 1) (deliver p 2) @p)

(deref (promise) 10 :t)

(pmap inc [1 2 3])

(pvalues 1 2)

(pcalls #(+ 1 1) #(+ 2 2))

(let [f (future 1)] [@f (future-done? f) (future-cancelled? f) (future-cancel f) (realized? f)])

(let [a (future (reduce + (range 20000)) 1) b (future 2)] (+ @a @b))

(try @(future (throw (ex-info "x" {}))) (catch clotran.host.execution_exception e :ee))

;; a timed deref: the value when it comes in time, the default when it
;; cannot -- each with a certain answer. It was (deref (future (reduce +
;; (range 300000)) 1) 1 :t), whose answer was whether the sum beat 1 ms
;; on the machine that day: 1 until the gate ran its halves at once.
(deref (future 1) 10000 :t)

(deref (future (clotran.host.thread/sleep 5000) 1) 10 :t)

(let [p (promise) f (future @p)] (deliver p :v) @f)

(let [p1 (promise) p2 (promise) f (future (deliver p2 (inc @p1)) :done)] (deliver p1 41) [@p2 @f])

(binding [*print-length* 3] @(future *print-length*))

;; dynamic bindings are per thread (Var.dvals): a future sees its maker's
;; through binding-conveyor-fn, and a binding in one thread is not seen
;; by another
(binding [*print-length* 3] [@(future *print-length*) (thread-bound? #'*print-length*) (get (get-thread-bindings) #'*print-length*)])

(let [p (promise) q (promise)] (future (binding [*print-level* 7] (deliver p *print-level*) @q)) [@p *print-level* (do (deliver q 1) *print-level*)])

(binding [*print-length* 1] (set! *print-length* 2) [*print-length* (binding [*print-length* 3] (set! *print-length* 4) *print-length*) *print-length*])

[((bound-fn [] *print-length*)) (binding [*print-length* 9] ((bound-fn [] *print-length*)))]

(let [fs (mapv (fn [k] (future (with-out-str (dotimes [i 200] (print k))))) (range 8))] (mapv (comp count set deref) fs))

(let [fs (mapv (fn [k] (future (mapv #(str "k" (* k %)) (range 300)))) (range 1 9))] (= (mapv deref fs) (mapv (fn [k] (mapv #(str "k" (* k %)) (range 300))) (range 1 9))))

(let [a (atom 1)] [(compare-and-set! a 1 2) @a (compare-and-set! a 1 3) @a])

(take 2 (pmap inc (range)))

@(future (+ @(future 1) @(future 2)))

(count (map deref (doall (map #(future (* % %)) (range 100)))))

;; (def name "doc" init): the docstring is :doc metadata, not the value
(do (def dx "a doc" 1) [dx (:doc (meta #'dx))])

(do (def dy "just a value") dy)

;; a protocol method spelt with a dash is a method when written as a call
(do (defprotocol PD (-pname [x])) (deftype TD [] PD (-pname [_] :td)) (-pname (TD.)))

(do (deftype TF [x]) [(.-x (TF. 3)) (. (TF. 4) -x)])

;; sequence, eduction, iterator-seq, volatile! and the buffering
;; transducers: the RT pieces ClojureScript writes in Clojure, written
;; in Clojure here too (clotran.rt), reached as clj members
(sequence (map inc) [1 2 3])

(take 3 (sequence (map inc) (range)))

(sequence (map +) [1 2 3] [10 20 30])

(sequence (partition-all 2) [1 2 3 4 5])

(sequence (comp (filter odd?) (map inc)) (range 10))

(sequence (comp (take 3) (map inc)) (range))

(sequence (map inc) nil)

(into [] (partition-all 2) (range 5))

(into [] (partition-by odd?) [1 3 2 4])

(transduce (partition-all 3) conj (range 7))

(into [] (eduction (map inc) (filter even?) (range 10)))

(seq (eduction (map inc) [1 2]))

(vec (eduction (take 2) [5 6 7]))

(reduce + (eduction (map inc) (range 5)))

(reduce + 100 (eduction (map inc) (range 5)))

(let [v (volatile! 1)] (vswap! v inc) [@v (volatile? v) (volatile? (atom 1)) (vreset! v 9) @v])

(iterator-seq (.iterator (clotran.rt/array-list [1 2 3])))

(sort (shuffle [3 1 2 5 4]))

(count (shuffle (range 10)))

(into [] (distinct) [1 2 1 3 2])

(into [] (dedupe) [1 1 2 2 1])

(into [] (interpose :x) [1 2 3])

;; sorted maps and sets: the array map with its keys in comparator order
(sorted-map 3 :c 1 :a 2 :b)

(seq (sorted-map 3 :c 1 :a 2 :b))

(sorted-set 3 1 2)

(sorted-map-by > 1 :a 3 :c 2 :b)

(sorted-set-by > 1 3 2)

(assoc (sorted-map 1 :a 3 :c) 2 :b)

(assoc (sorted-map 1 :a 3 :c) 3 :C)

(dissoc (sorted-map 1 :a 2 :b 3 :c) 2)

(into (sorted-map) {5 :e 1 :a 3 :c})

(into (sorted-set) (range 20 0 -1))

(count (into (sorted-map) (map (fn [i] [i i]) (range 100))))

(get (sorted-map-by (fn [a b] (compare (str a) (str b))) :a 1) :a)

(subseq (sorted-set 1 2 3 4 5) > 2)

(subseq (sorted-set 1 2 3 4 5) >= 2 < 4)

(subseq (sorted-map 1 :a 2 :b 3 :c) < 3)

(rsubseq (sorted-set 1 2 3 4 5) < 3)

(rsubseq (sorted-map 1 :a 2 :b 3 :c) >= 2)

(subseq (sorted-map-by > 1 :a 2 :b 3 :c) > 2)

(rseq (sorted-map 1 :a 2 :b))

(rseq [1 2 3])

(rseq [])

(rseq (sorted-set 1 2 3))

(first (sorted-set 3 1 2))

[(sorted? (sorted-map)) (sorted? {}) (sorted? (sorted-set)) (reversible? [1]) (reversible? (sorted-set)) (reversible? {})]

(= (sorted-map 1 2) {1 2})

(sorted? (empty (sorted-map)))

(conj (sorted-set 5 1) 3)

(disj (sorted-set 1 2 3) 2)

(contains? (sorted-set 1 2 3) 2)

[(keys (sorted-map 2 :b 1 :a)) (vals (sorted-map 2 :b 1 :a))]

(try (sorted-set 1 "a") (catch clotran.host.class_cast_exception e :cce))

(reduce-kv (fn [acc k v] (conj acc k)) [] (sorted-map 3 :c 1 :a))

(map key (subseq (sorted-map 1 :a 2 :b 3 :c 4 :d) >= 2 <= 3))

;; #(...) parameters are gensyms: a p1 of the program's own is not shadowed
(let [p1 even?] ((fn [& args] (every? #(p1 %) args)) 2 4))

((every-pred even? number?) 2 4 6 8)

((some-fn even?) 1 3 5 6)

;; metadata rides through the collection operations, and a def's Var
;; carries :name, :ns, :line and :column
(meta (assoc (with-meta {} {:a 1}) :k 1))

(meta (reduce (fn [m i] (assoc m i i)) (with-meta {} {:a 1}) (range 20)))

(meta (conj (with-meta [] {:a 1}) 1))

(meta (into (with-meta {} {:a 1}) {:k 2}))

(meta (disj (with-meta #{1 2} {:a 1}) 1))

(meta (pop (with-meta [1 2] {:a 1})))

(meta (empty (with-meta [1 2] {:a 1})))

(meta (assoc (with-meta [1 2] {:a 1}) 0 9))

(do (def mm-doc "d" 1) [(select-keys (meta #'mm-doc) [:name :doc]) (integer? (:line (meta #'mm-doc))) (integer? (:column (meta #'mm-doc)))])

(do (def ^:private mm-priv 1) [(:private (meta #'mm-priv)) (:name (meta #'mm-priv)) (= *ns* (:ns (meta #'mm-priv)))])

;; the errors arithmetic and compare raise carry clj's classes
(try (quot 9 0) (catch clotran.host.arithmetic_exception e :arith))

(try (mod 9 0) (catch clotran.host.arithmetic_exception e :arith))

(try (/ 1 0) (catch clotran.host.arithmetic_exception e :arith))

(try (* clotran.host.int8/MAX_VALUE 2) (catch clotran.host.arithmetic_exception e :arith))

(try (inc clotran.host.int8/MAX_VALUE) (catch clotran.host.arithmetic_exception e :arith))

(try (compare #{1} #{2}) (catch clotran.host.class_cast_exception e :cce))

(try (compare {} {}) (catch clotran.host.class_cast_exception e :cce))

(try (sort [1 :a]) (catch clotran.host.class_cast_exception e :cce))

(try (compare {:a 1} {:a 1}) (catch clotran.host.class_cast_exception e :cce))

(try (- clotran.host.int8/MIN_VALUE) (catch clotran.host.arithmetic_exception e :arith))

[(unchecked-add clotran.host.int8/MAX_VALUE 1) (unchecked-inc clotran.host.int8/MAX_VALUE) (unchecked-multiply clotran.host.int8/MAX_VALUE 2) (unchecked-dec clotran.host.int8/MIN_VALUE) (unchecked-subtract clotran.host.int8/MIN_VALUE 1)]

[(+ 1 2 3) (- 10 1 2) (* 2 3 4) (- 5) (inc 1) (dec 1) (+ 1.5 2) (* 2 1/3)]

;; the small members the language suite named: (Object.) as a sentinel, the bit tests, long-array and double-array
(let [o (clotran.host.value.)] [(= o o) (= o (clotran.host.value.)) (instance? clotran.host.value o)])

(get-in {:a {:b 1}} [:a :c] :nope)

(get-in {:a {:b nil}} [:a :b] :nope)

[(bit-test 5 0) (bit-test 5 1) (bit-set 1 2) (bit-clear 7 1) (bit-flip 2 1)]

(vec (long-array [1 2 3]))

(vec (long-array 3))

(vec (long-array 2 7))

(vec (double-array [1.5 2.5]))

(aget (long-array [4 5 6]) 1)

;; the seq library's edges: reduced unwraps wherever deref reaches it,
;; keys and vals of an empty map are nil, seq of a non-seqable throws,
;; cycle is lazy and empty for an empty coll, with-meta on a seq holds
@(reduced 1)

(reduce (fn [a x] (reduced :done)) 0 (range))

(transduce (take 1) conj [] (seq [1 2 3]))

(reductions (constantly (reduced :x)) (range))

(reduce-kv (fn [acc k v] (reduced (+ acc k))) 0 {1 2})

(partitionv 2 [1 2 3 4 5])

(partitionv-all 4 2 [1 2 3 4 5 6 7 8 9])

[(keys {}) (vals {}) (keys (sorted-map)) (keys {1 2}) (vals {1 2})]

(try (first 1) (catch clotran.host.illegal_argument_exception e :iae))

(try (next :k) (catch clotran.host.illegal_argument_exception e :iae))

(try (cons 1 2) (catch clotran.host.illegal_argument_exception e :iae))

(try (get-in {:a 1} 5) (catch clotran.host.illegal_argument_exception e :iae))

[(first nil) (first "ab") (seq nil) (cons 1 nil) (cons 1 "ab") (next [1])]

[(cycle []) (take 5 (cycle [1 2]))]

(take 2 (cycle (map #(/ 42 %) '(2 1 0))))

(transduce (take 5) + 2 (cycle [3 7]))

(meta (with-meta (seq [1 2]) {:a 1}))

(meta (sort (with-meta (range 10) {:a true})))

(meta (sort-by :a (with-meta (seq [{:a 5} {:a 2}]) {:a true})))

;; refusals: a stack is a vector, a list or a seq; an empty one cannot
;; pop; a string or an array cannot be conj'd onto; a vector called out
;; of range throws; a sorted collection admits only what compare orders
(try (pop #{1}) (catch clotran.host.class_cast_exception e :cce))

(try (peek {:a 1}) (catch clotran.host.class_cast_exception e :cce))

(try (pop []) (catch clotran.host.illegal_state_exception e :ise))

(try (pop ()) (catch clotran.host.illegal_state_exception e :ise))

(try (pop! (transient [])) (catch clotran.host.illegal_state_exception e :ise))

[(pop [1 2]) (pop '(1 2)) (peek [1 2]) (peek '(1 2)) (peek []) (pop nil) (peek nil)]

(try (pop (seq [1 2])) (catch clotran.host.class_cast_exception e :cce))

(try (conj "" \a) (catch clotran.host.class_cast_exception e :cce))

(try (conj (into-array []) 1) (catch clotran.host.class_cast_exception e :cce))

(try ([1 2] 7) (catch clotran.host.index_out_of_bounds_exception e :ioobe))

(try ([1 2] -1) (catch clotran.host.index_out_of_bounds_exception e :ioobe))

[({:a 1} :a) ({:a 1} :b 2) (#{:a} :a) ((transient #{:a}) :b 2) ({:a nil} :a 2)]

(try (< 1 "a") (catch clotran.host.class_cast_exception e :cce))

(try (+ "ab" "cd") (catch clotran.host.class_cast_exception e :cce))

(try (inc "a") (catch clotran.host.class_cast_exception e :cce))

(try (max 1 "a") (catch clotran.host.class_cast_exception e :cce))

(try (== 1 :a) (catch clotran.host.class_cast_exception e :cce))

[(get #{:a} :b 1) (get (transient #{:a}) :b 1) ((transient #{:a}) :b 1)]

[(find [1 2] 0) (find [1 2] 5) (find {:a 1} :a)]

(try (sorted-set ()) (catch clotran.host.class_cast_exception e :cce))

(try (sorted-set {}) (catch clotran.host.class_cast_exception e :cce))

(try (sorted-map [1] 1 #{} 2) (catch clotran.host.class_cast_exception e :cce))

(try (assoc (sorted-map) () 1) (catch clotran.host.class_cast_exception e :cce))

(try (sorted-set-by < 1 "a") (catch clotran.host.exception e :ex))

[(sorted-set nil) (sorted-set 1.5 1) (sorted-set "b" "a") (sorted-set [2] [1])]

;; \u escapes in strings, and a method called on nil is a
;; NullPointerException, which is how clojure.string's fns fail on nil
"Aé x"

(= "A" "A")

(do (require 'clojure.string) (try (clojure.string/upper-case nil) (catch clotran.host.null_pointer_exception e :npe)))

(do (require 'clojure.string) (try (clojure.string/reverse nil) (catch clotran.host.null_pointer_exception e :npe)))

(do (require 'clojure.string) (try (clojure.string/split nil #"-") (catch clotran.host.null_pointer_exception e :npe)))

(do (require 'clojure.string) (try (clojure.string/capitalize nil) (catch clotran.host.null_pointer_exception e :npe)))

(do (require 'clojure.string) (try (clojure.string/trim nil) (catch clotran.host.null_pointer_exception e :npe)))

(do (require 'clojure.string) (try (clojure.string/replace nil #"a" "b") (catch clotran.host.null_pointer_exception e :npe)))

(try (.toUpperCase nil) (catch clotran.host.null_pointer_exception e :npe))

(try (subs nil 0 1) (catch clotran.host.null_pointer_exception e :npe))

[@(future 1) (count (pmap inc [1 2 3]))]

;; a host error is an exception with a message; a symbol is callable;
;; keyword arguments merge a trailing map; a keyword called with the
;; wrong count is an ArityException; and the small edges the suite named
(try (first 1) (catch clotran.host.runtime_exception e (boolean (.getMessage e))))

(try (get-in {:a 1} 5) (catch clotran.host.exception e (boolean (re-find #"ISeq" (.getMessage e)))))

['b {'b 2}]

('b {'b 2})

('c {'b 2} :none)

(let [addn (fn [n & {:keys [a b] :or {a 0 b 0}}] (+ n a b))] [(addn 100 :a 1 {:b 2}) (addn 100 :a 1) (addn 100 {:a 5 :b 2})])

(try (:kw) (catch clotran.host.illegal_argument_exception e (.getMessage e)))

(try (apply :foo/bar (range 20)) (catch clotran.host.illegal_argument_exception e (.getMessage e)))

(try (apply :foo/bar (range 21)) (catch clotran.host.illegal_argument_exception e (.getMessage e)))

[(parse-long "9223372036854775807") (parse-long "-9223372036854775808") (parse-long "+42") (parse-long "x")]

(pr-str #'pr-str)

(ex-data (ex-info "message" nil))

(try (eval '(throw)) (catch clotran.host.runtime_exception e :rt))

(try (.jump "foo" 1) (catch clotran.host.exception e (boolean (re-find #"No matching method.*taking 1 arg" (.getMessage e)))))

(reduce-kv + 10 [2 4 6])

(reduce-kv (fn [acc i x] (if (= i 1) (reduced acc) (+ acc x))) 0 [5 6 7])

[(= [1 2 3 4 5] (eduction (map inc) (range 5))) (= (eduction (map inc) []) []) (= [1] (eduction (map inc) [5]))]

[(clojure.math/floor-div clotran.host.int8/MIN_VALUE -1) (clojure.math/floor-div -7 2) (clojure.math/floor-div 7 -2)]

[(= ##Inf (clojure.math/ulp ##Inf)) (= clotran.host.real8/MIN_VALUE (clojure.math/ulp 0.0)) (clojure.math/ulp 1.0)]

(NaN? (clojure.math/IEEE-remainder 2 0.0))

;; the operations a metadata-carrying collection answers, and the
;; metadata it keeps -- dissoc on one answered it UNCHANGED
(let [m (with-meta {:a 1 :b 2} {:m 1})] [(dissoc m :a) (meta (dissoc m :a)) (dissoc m :zz) (assoc m :c 3) (meta (assoc m :c 3)) (get m :a) (m :a) (:a m) (count m) (contains? m :a) (find m :a) (keys m) (vals m) (seq m) (merge m {:c 3}) (update m :a inc) (select-keys m [:a]) (= m {:a 1 :b 2}) (empty m) (meta (empty m)) (into m [[:z 9]]) (meta (into m [[:z 9]])) (reduce-kv (fn [acc k v] (+ acc v)) 0 m) (dissoc m :a :b)])

(let [v (with-meta [1 2 3] {:m 1})] [(conj v 4) (meta (conj v 4)) (pop v) (meta (pop v)) (peek v) (nth v 0) (v 1) (subvec v 1) (count v) (first v) (rest v) (next v) (= v [1 2 3]) (= v '(1 2 3)) (reduce + v) (into v [4]) (meta (into v [4])) (map inc v) (assoc v 0 9) (meta (assoc v 0 9)) (empty v) (meta (empty v)) (vec v) (set v) (sort v) (apply + v) (empty? v) (str v)])

(let [s (with-meta #{1 2} {:m 1})] [(disj s 1) (meta (disj s 1)) (conj s 3) (meta (conj s 3)) (contains? s 1) (s 1) (get s 2) (count s) (= s #{1 2}) (empty s) (meta (empty s)) (seq (sort s))])

(let [l (with-meta '(1 2) {:m 1})] [(conj l 0) (meta (conj l 0)) (pop l) (peek l) (first l) (rest l) (count l) (= l [1 2]) (vec l)])

(do (defrecord R2 [a b]) (let [r (->R2 1 2)] [(map? (dissoc r :a)) (record? (dissoc r :a)) (dissoc r :a) (= (dissoc r :zz) r) (assoc r :c 3) (:a (assoc r :c 3)) (into {} r)]))

;; auto-resolved keywords read against the current namespace, and its aliases
(let [k (read-string "::b")] [(pr-str k) (namespace k) (name k) (= k :user/b) (keyword? k)])

(require '[clojure.string :as s])

(let [k (read-string "::s/x")] [(pr-str k) (namespace k) (= k :clojure.string/x) (try (read-string "::clojure.core/y") (catch clotran.host.exception e :invalid))])

(try (read-string "::nope/x") (catch clotran.host.exception e (boolean (re-find #"Invalid token" (.getMessage e)))))

(binding [*ns* (find-ns 'clojure.string)] (read-string "::q"))

(try (derive :user/a :user/b) (derive :user/b :user/a) (catch clotran.host.exception e (.getMessage e)))

;; a namespace carries metadata
(do (alter-meta! *ns* assoc :k 1) [(:k (meta *ns*)) (instance? clotran.host.i_meta *ns*)])

(do (def stub-me :orig) (let [p (promise)] (try (with-redefs [stub-me :temp] (deliver p stub-me) (throw (clotran.host.exception. "x"))) (catch clotran.host.exception e nil)) [@p stub-me]))

(let [m (into (sorted-map) '{1 a, 2 b, 3 c, 4 d})] [(reduce-kv str "" m) (reduce-kv (fn [acc k v] (reduced (+ acc k))) 0 m)])

[(instance? clotran.host.ikv_reduce {}) (instance? clotran.host.ikv_reduce []) (instance? clotran.host.ikv_reduce (sorted-map))]

;; a map entry keeps its type through seqs and find; conj and assoc on one make a vector
[(map-entry? (first {1 2})) (map-entry? [1 2]) (map-entry? (find {1 2} 1)) (map-entry? (find [5 6] 1)) (map-entry? (conj (first {1 2}) 3)) (map-entry? (assoc (first {1 2}) 0 9)) (vector? (first {1 2})) (map-entry? (first (seq (sorted-map 1 2)))) (map-entry? (first (rseq (sorted-map 1 2)))) (map-entry? (first (subseq (sorted-map 1 2) > 0))) (map-entry? (nth (seq {1 2 3 4}) 1)) (map-entry? (first (reduce conj [] {1 2}))) (map-entry? (first (into [] {1 2}))) (map-entry? (first (map identity {1 2}))) (map-entry? (first (vec {1 2}))) (map-entry? (clotran.host.map_entry/create 1 2)) (= [1 2] (first {1 2})) (key (first {1 2})) (val (clotran.host.map_entry/create 1 2))]

(require 'clojure.walk)

(let [f (fn [e] (if (and (vector? e) (not (map-entry? e))) (apply list e) e))] (clojure.walk/postwalk f [:html {:a ["b" 1]} ""]))

;; a keyword called with a default, on any collection
[(:b #{:a} 1) (:b (transient #{:a}) 1) (:a {:a nil} 1) (:b {:a 1} 1) (:b (transient {:a 1}) 1) (:a #{:a} 1)]

;; an error is an instance of its class, and of what catch would take it under
(let [e (try (/ 1 0) (catch clotran.host.exception e e))] [(instance? clotran.host.arithmetic_exception e) (instance? clotran.host.runtime_exception e) (instance? clotran.host.illegal_argument_exception e) (instance? clotran.host.exception e) (instance? clotran.host.throwable e) (instance? clotran.host.value e)])

;; isAssignableFrom, and extend's refusal of a type that implements the protocol inline
(do (defprotocol PP (pp [x])) (deftype TT [] PP (pp [_] 1)) [(extends? PP TT) (satisfies? PP (TT.)) (try (extend TT PP {:pp (fn [_] 2)}) :extended (catch clotran.host.illegal_argument_exception e (boolean (re-find #"already directly implements" (.getMessage e)))))])

[(.isAssignableFrom clotran.host.value clotran.host.string) (.isAssignableFrom clotran.host.i_persistent_vector clotran.host.persistent_vector) (.isAssignableFrom clotran.host.string clotran.host.value) (.isAssignableFrom clotran.host.i_persistent_map clotran.host.persistent_tree_map) (.isAssignableFrom clotran.host.i_persistent_map clotran.host.persistent_vector) (.isAssignableFrom clotran.host.string clotran.host.string)]

;; the root of a Var under a binding: bindRoot, alter-var-root and def reach the root, the binding shows
(do (def ^:dynamic dv 1) [(binding [dv 2] (with-redefs [dv 3] [dv (.getRawRoot #'dv)])) dv (binding [dv 2] (alter-var-root #'dv inc) [dv (.getRawRoot #'dv)]) dv (binding [dv 5] (def dv 7) [dv (.getRawRoot #'dv)]) dv (binding [dv 8] (binding [dv 9] (with-redefs [dv 10] dv))) dv])

;; Long/valueOf with the wrong count fails in the Reflector's words
(try (eval '(clotran.host.int8/valueOf)) (catch clotran.host.exception e (boolean (re-find #"No matching method.*taking 0 args" (.getMessage (or (.getCause e) e))))))

(try (eval '(clotran.host.int8/valueOf :a :b :c)) (catch clotran.host.exception e (boolean (re-find #"No matching method.*taking 3 args" (.getMessage (or (.getCause e) e))))))

;; in-ns under a binding of *ns* changes the binding, not the root
(binding [*ns* *ns*] (in-ns 'oracle-tmp-ns) (def in-tmp 1) [(ns-name *ns*) (some? (ns-resolve 'oracle-tmp-ns 'in-tmp))])

(ns-name *ns*)

;; a qualified symbol is not a local
[(try (eval '(let* [a/x 1] x)) (catch clotran.host.exception e :threw)) (try (eval '(loop* [a/x 1] x)) (catch clotran.host.exception e :threw)) (let [/ 1] /)]

;; case keys its table with Util.hash, which is hashCode: 1 and
;; -9223372034707292159 collide and the condp under the key tells them apart
[(case 1 1 :long -9223372034707292159 :big :else) (case -9223372034707292159 1 :long -9223372034707292159 :big :else) (case 4294967297 4294967297 :big :else) (case 1 4294967297 :big 1 :one :else) (case "a" "a" :s :else) (case :k :k :kw :else) (case 7 (1 7) :either :else) (case 'x (x y) :sym :else) (case 3 (1 7) :either :else)]

;; a cause
(let [e (ex-info "outer" {:o 1} (ex-info "inner" {:i 2}))] [(ex-message (ex-cause e)) (ex-data (ex-cause e)) (ex-cause (ex-cause e)) (ex-message (.getCause e)) (ex-data e)])

(let [{:keys [cause via]} (Throwable->map (clotran.host.exception. "I am not a number" (clotran.host.exception. "double two")))] [cause (mapv :message via) (count via) (vector? via)])

(let [{:keys [cause via]} (Throwable->map (clotran.host.exception. "alone"))] [cause (mapv :message via)])

;; a macro called with the wrong count says the count the caller wrote
(defmacro m0 [] 1)

(defmacro m1 [a] a)

[(try (macroexpand '(m0 1)) (catch clotran.host.arity_exception e (.getMessage e))) (try (macroexpand '(m1 1 2)) (catch clotran.host.arity_exception e (.getMessage e))) (macroexpand '(m1 5))]

;; a private Var is not reachable by its qualified name from another namespace; #'ns/x still is
(ns other-ns)

(def ^:private secret 1)

(in-ns 'user)

(try (eval 'other-ns/secret) (catch clotran.host.exception e (boolean (re-find #"not public" (.getMessage (or (.getCause e) e))))))

@#'other-ns/secret

;; find-ns does not create, so the-ns and alias can refuse
[(find-ns 'nope-ns) (try (alias 'bogus 'epicfail) (catch clotran.host.exception e (.getMessage e))) (some? (find-ns 'clojure.core))]

;; Math edges
(require 'clojure.math)

[(NaN? (clojure.math/pow 1.0 ##Inf)) (NaN? (clojure.math/pow -1.0 ##-Inf)) (clojure.math/pow 2.0 ##Inf) (clojure.math/pow 2.0 3.0) (clojure.math/get-exponent ##NaN) (clojure.math/get-exponent ##Inf) (clojure.math/get-exponent 0.0) (clojure.math/get-exponent 1.0) (clojure.math/get-exponent 1024.5) (clojure.math/get-exponent 4.9E-324) (NaN? (clojure.math/next-after 1 ##NaN)) (clojure.math/next-after 1.0 ##Inf)]

;; find answers the map's own key, metadata and all
(let [k (with-meta 'k {:a "A"}) m {k 1} big (into {} (map (fn [i] [i i]) (range 40))) bk (with-meta 'bk {:b 1})] [(meta (key (find m 'k))) (meta (key (find (assoc big bk 9) 'bk))) (meta (key (find (sorted-map k 1) 'k))) (find m 'k)])

;; a record: conj through its own cons, its own metadata, and what it is an instance of
(defrecord Foo [a b c])

(require 'clojure.walk)

[(conj (->Foo 1 2 3) [:x 1]) (record? (conj (->Foo 1 2 3) [:x 1])) (meta (with-meta (->Foo 1 2 3) {:m 1})) (coll? (->Foo 1 2 3)) (map? (->Foo 1 2 3)) (associative? (->Foo 1 2 3)) (seqable? (->Foo 1 2 3)) (counted? (->Foo 1 2 3)) (clojure.walk/walk identity identity (->Foo 1 2 3)) (meta (clojure.walk/postwalk identity (with-meta (->Foo 1 2 3) {:m 1}))) (into (->Foo 1 2 3) {:d 4}) (= (->Foo 1 2 3) (conj (->Foo 1 2 3) [:a 1])) (:a (conj (->Foo 1 2 3) {:a 9})) (meta (conj (with-meta (->Foo 1 2 3) {:m 1}) [:d 4]))]

;; remove-ns takes a namespace out of the registry, and refuses clojure.core
(do (create-ns 'temp-ns) [(some? (find-ns 'temp-ns)) (some? (remove-ns 'temp-ns)) (find-ns 'temp-ns) (remove-ns 'temp-ns)])

(try (remove-ns 'clojure.core) (catch clotran.host.illegal_argument_exception e (.getMessage e)))

;; seqable? is RT.canSeq
[(seqable? nil) (seqable? 1) (seqable? "s") (seqable? [1]) (seqable? {}) (seqable? #{}) (seqable? '(1)) (seqable? (range 3)) (seqable? (->Foo 1 2 3)) (seqable? (eduction (map inc) [1])) (seqable? :k) (seqable? 'x) (seqable? (fn []))]

;; multimethods dispatch with isa? over the hierarchy; preferences resolve what isa? cannot,
;; and two matches with no preference are the ambiguity error
(do (derive :user/rect :user/shape) nil)

(defmulti bar (fn [x y] [x y]))

(defmethod bar [:user/rect :user/shape] [x y] :rect-shape)

(defmethod bar [:user/shape :user/rect] [x y] :shape-rect)

[(try (bar :user/rect :user/rect) (catch clotran.host.illegal_argument_exception e (boolean (re-find #"Multiple methods in multimethod 'bar' match dispatch value" (.getMessage e))))) (prefers bar) (bar :user/rect :user/shape) (bar :user/shape :user/rect) (bar :user/rect :user/other)]

(do (prefer-method bar [:user/rect :user/shape] [:user/shape :user/rect]) nil)

[(bar :user/rect :user/rect) (prefers bar) (try (prefer-method bar [:user/shape :user/rect] [:user/rect :user/shape]) (catch clotran.host.illegal_state_exception e (boolean (re-find #"Preference conflict" (.getMessage e)))))]

(do (derive :user/parent-1 :user/grandparent-1) (derive :user/parent-2 :user/grandparent-2) (derive :user/child :user/parent-1) (derive :user/child :user/parent-2) nil)

(defmulti indirect-1 keyword)

(do (prefer-method indirect-1 :user/parent-1 :user/grandparent-2) nil)

(defmethod indirect-1 :user/parent-1 [_] :p1)

(defmethod indirect-1 :user/parent-2 [_] :p2)

(indirect-1 :user/child)

(defmulti indirect-2 keyword)

(do (prefer-method indirect-2 :user/grandparent-1 :user/parent-2) nil)

(defmethod indirect-2 :user/parent-1 [_] :p1)

(defmethod indirect-2 :user/parent-2 [_] :p2)

(indirect-2 :user/child)

(def local-h (-> (make-hierarchy) (derive :parent-1 :grandparent-1) (derive :parent-2 :grandparent-2) (derive :child :parent-1) (derive :child :parent-2)))

(defmulti indirect-3 keyword :hierarchy #'local-h)

(do (prefer-method indirect-3 :parent-1 :grandparent-2) nil)

(defmethod indirect-3 :parent-1 [_] :p1)

(defmethod indirect-3 :parent-2 [_] :p2)

[(indirect-3 :child) (indirect-3 :parent-2) (try (indirect-3 :nobody) (catch clotran.host.illegal_argument_exception e (boolean (re-find #"No method in multimethod 'indirect-3' for dispatch value: :nobody" (.getMessage e)))))]

;; a method on an ancestor applies, the default when none does, and a later derive is seen
(defmulti area :shape)

(defmethod area :user/shape [s] :generic)

(defmethod area :default [s] :none)

[(area {:shape :user/rect}) (area {:shape :user/shape}) (area {:shape :user/other}) (do (derive :user/other :user/shape) (area {:shape :user/other})) (some? (get-method area :user/rect)) (some? (get-method area :user/nobody)) (= (get-method area :user/nobody) (get-method area :default))]

(defmulti simple1 identity)

(defmethod simple1 :a [x] :a)

[(count (methods simple1)) (do (remove-all-methods simple1) (count (methods simple1))) (prefers simple1) (try (simple1 :a) (catch clotran.host.illegal_argument_exception e :no-method))]

;; the class keywords are classes to isa?, and an interface has parents
[(class? (class {})) (class? :foo) (class? :user/rect) (isa? (class {}) clotran.host.i_persistent_map) (isa? (class []) clotran.host.i_persistent_map) (isa? (class "") clotran.host.value) (contains? (supers clotran.host.i_persistent_vector) clotran.host.i_persistent_collection) (isa? clotran.host.i_persistent_map clotran.host.i_persistent_collection) (isa? clotran.host.i_persistent_vector clotran.host.sequential)]

(binding [*print-dup* true] (pr-str [{:a 1} [1] '(1) #{1} "s" 1.5 \c :k 'sym nil true]))

;; syntax-quote leaves a dotted symbol as written -- a class name, as Compiler.resolveSymbol takes it
(let [x 1] [(pr-str `(clojure.core clotran.host.map foo.bar/baz x)) (pr-str `clojure.string) (pr-str `clotran.host.string)])

;; str of nested collections goes through the native printer: nothing lost between a key and a map value
[(str {:data {:x 1}}) (str {:abcdef {:x 1}}) (str {"data" {:x 1}}) (str [{:data 1}]) (str {:a [1 {:b 2}]}) (str {"a" 1}) (str ["a" \b]) (str '("a")) (str #{"a"})]

;; def of a name this namespace only refers interns a Var HERE and leaves the referred one alone
(ns shadow-ns)

(defn- num [m k] :mine)

[(num {} :a) (str (:ns (meta (ns-resolve 'shadow-ns 'num)))) (clojure.core/num 5) (= #'clojure.core/num (ns-resolve 'clojure.core 'num))]

(in-ns 'user)

;; apply hands a variadic fn its rest unrealised (RestFn.applyTo); a
;; fixed arity, a native or a keyword still takes the arguments spread.
(apply (fn [a & r] [a (take 3 r)]) 1 (range))
(apply (fn [a b & r] [a b (take 3 r)]) (range))
(apply (fn [a b & r] [a b r]) 1 2 3 4 [5 6])
(apply (fn [a b & r] [a b r]) 1 2 3 4 [])
(apply (fn [a b & r] [a b r]) 1 [2])
(apply (fn ([a] [:one a]) ([a & r] [:more a r])) [1])
(apply (fn ([a] [:one a]) ([a & r] [:more a r])) [1 2])
(apply (fn ([a] [:one a]) ([a & r] [:more a r])) 1 [])
(apply (fn [& r] r) nil)
(apply (fn [& r] r) [])
(apply (fn [& r] (count r)) 1 2 (range 3))
(try (apply (fn [a b] [a b]) [1]) (catch clotran.host.arity_exception e :arity))
(try (apply (fn [a b & r] [a b]) [1]) (catch clotran.host.arity_exception e :arity))
(let [a (atom 0)] (apply (fn [x & r] x) (map (fn [i] (swap! a inc) i) (range 100))) @a)
(deref (future (apply (fn [x & r] (take 2 r)) (range))) 1000 :timeout)

;; strings are characters (DEVIATIONS 41): counted, indexed, sliced and
;; searched by code point, with the Character predicates ICU's
[(count "\u2002ab") (count "é") (.length "é") (subs "é" 0 1) (.charAt "\u2002x" 1) (int (.charAt "\u2002x" 0)) (int \u2002) (= "\u2002" (str \u2002)) (str \o101) (int \u00e9)]
[(clojure.string/triml "\u2002 \tbar") (clojure.string/trimr "bar\t \u2002") (clojure.string/trim "\u2000bar\t \u2002") (clojure.string/blank? "\u2002") (clojure.string/blank? "\u00a0")]
[(nth "aé" 1) (.indexOf "aéb" "b") (clojure.string/upper-case "éa") (clojure.string/lower-case "ÉA") (vec "aé") (seq "aé") (clojure.string/reverse "aé") (last "aé") (get "aé" 1) (contains? "aé" 1) (contains? "aé" 2) (clojure.string/capitalize "élan")]
[(clotran.host.char/isWhitespace \u2002) (clotran.host.char/isWhitespace \u00a0) (clotran.host.char/isLetter \é) (clotran.host.char/isLetter \u2002) (clotran.host.char/toUpperCase \é) (clotran.host.char/isLetter \A) (clotran.host.char/isWhitespace \space) (clotran.host.char/isWhitespace \a) (clotran.host.char/toLowerCase \É)]
[(re-find #"é" "aéb") (clojure.string/index-of "aéb" "b") (.substring "aéb" 2) (re-seq #".\d" "é1x2") (clojure.string/replace "aéb" #"é" "E") (clojure.string/replace "aébé" "é" "<$0>") (clojure.string/last-index-of "éaéb" "é") (clojure.string/index-of "éaéb" "é" 1) (clojure.string/split "éaéb" #"é") (clojure.string/split "aébéc" #"")]
[(pr-str "é") (pr-str \é) (pr-str \u2002) (clojure.string/escape "aé" {\é "E"}) (.toUpperCase "é") (subs "aéb" 1) (subs "aéb" 1 2) (subs "aéb" 3) (try (subs "aéb" 4) (catch clotran.host.string_index_out_of_bounds_exception e :oob)) (try (subs "aéb" 2 1) (catch clotran.host.string_index_out_of_bounds_exception e :oob)) (.substring "aéb" 1 3) (map int "aé") (apply str (map char [233 65]))]
[(re-matches #".." "aé") (re-matches #".." "aéb") (let [m (re-matcher #"é" "aébé")] (re-find m) [(.start m) (.end m)]) (clojure.string/replace-first "aébé" #"é" "E") (clojure.string/split-lines "é\nb") (clojure.string/includes? "aéb" "é") (clojure.string/starts-with? "éa" "é") (clojure.string/ends-with? "aé" "é") (let [m (re-matcher #"é" "aébé")] (re-find m) (let [sb (clotran.host.string_buffer.)] (.appendReplacement m sb "E") (.appendTail m sb) (str sb)))]
(expect-diff "DEVIATIONS 14: ICU's \\s is Unicode, clj's regex's is ASCII")
(clojure.string/split "a\u2002b" #"\s")
(expect-diff "DEVIATIONS 14: ICU's \\w is Unicode, clj's regex's is ASCII")
(re-find #"\w+" "héllo")
(expect-diff "DEVIATIONS 14: ICU's (?i) folds Unicode, clj's regex's folds ASCII")
(re-find #"(?i)É" "xé")
(expect-diff "DEVIATIONS 41: a code point off the BMP is one character here, a surrogate pair there")
[(count "😀") (int (first "😀"))]

;; A lazy seq carried through a throw is still there in the handler:
;; raising an error must not force it (it would cache as empty).
(try (throw (ex-info "b" {:s (map inc [1 2 3])})) (catch clotran.host.exception e (vec (:s (ex-data e)))))
(let [l (lazy-seq (cons 1 (lazy-seq (cons 2 nil))))] [(try (throw (ex-info "b" {:s l})) (catch clotran.host.exception e (vec (:s (ex-data e))))) (vec l)])
(try (throw (ex-info "b" {:s (filter odd? (range 6))})) (catch clotran.host.exception e (count (:s (ex-data e)))))
[(counted? "ab") (counted? [1]) (counted? {}) (counted? (range 3)) (coll? "ab") (bounded-count 2 "abc")]
[(resolve 'nil?) (resolve 'fn) (resolve 'if) (resolve 'no-such-name-here) (ns-resolve 'clojure.string 'join) (ns-resolve *ns* 'inc)]

;; #:ns{...} -- a namespaced map, read and printed as clojure.main does
[(pr-str #:a{:b 1 :c/d 2 :_/e 3}) (= #:u{:n 1} {:u/n 1}) (pr-str {:u/n 1}) (pr-str #:n{:a #:o{:b 1}}) *print-namespace-maps* (vec (keys #:a{:b 1 :c/d 2 :_/e 3})) (pr-str (read-string "#:q{:a 1}")) (pr-str #:u{})]

;; clojure.spec.alpha and core.specs.alpha, vendored (PROVENANCE.md) and
;; consulted before every macro expansion, as Compiler.checkSpecs does
(require '[clojure.spec.alpha :as sa])
(sa/def :user/n int?)
(sa/def :user/pair (sa/cat :a :user/n :b string?))
(sa/def :user/m (sa/keys :req [:user/n]))
[(sa/valid? :user/n 1) (sa/valid? :user/n "x") (sa/conform :user/pair [1 "x"]) (sa/conform :user/pair [1 2]) (sa/valid? :user/m {:user/n 1}) (sa/valid? :user/m {}) (sa/conform (sa/or :i int? :s string?) "a") (sa/conform (sa/* int?) [1 2]) (sa/conform (sa/nilable int?) nil) (sa/conform (sa/and int? even?) 2) (sa/conform (sa/coll-of int?) [1 2]) (sa/conform (sa/map-of keyword? int?) {:a 1}) (sa/conform (sa/tuple int? string?) [1 "a"]) (sa/valid? (sa/? int?) []) (sa/conform (sa/alt :i int? :s string?) [1]) (sa/conform (sa/+ int?) [1 2 3])]
(sa/explain-str :user/n "x")
(map :path (:clojure.spec.alpha/problems (sa/explain-data :user/pair [1 2])))
[(sa/valid? :clojure.core.specs.alpha/binding-form '[a b & c :as d]) (sa/valid? :clojure.core.specs.alpha/binding-form :a) (sa/conform :clojure.core.specs.alpha/defn-args '(foo "doc" [a b] (+ a b)))]
(sa/describe :user/pair)
(sa/form :user/pair)
[(sa/conform (sa/spec (sa/cat :a int?)) [1]) (sa/unform :user/pair (sa/conform :user/pair [1 "x"])) (sa/valid? (sa/every int?) [1 2 3]) (sa/conform (sa/merge (sa/keys :req [:user/n]) (sa/keys :opt [:user/x])) {:user/n 1}) (sa/conform (sa/conformer #(if (int? %) (inc %) :clojure.spec.alpha/invalid)) 1) (some? (sa/regex? (sa/cat))) (some? (sa/spec? (sa/spec int?))) (sa/assert int? 1)]
(try (eval '(fn "a" a)) (catch clotran.host.exception e [(instance? clotran.host.exception e) (.getMessage (.getCause e)) (map (juxt :path :pred) (:clojure.spec.alpha/problems (ex-data (.getCause e))))]))
(try (eval '(let [:a 1] a)) (catch clotran.host.exception e (.getMessage (.getCause e))))
(try (eval '(let [a/x 1, [y] [1]] x)) (catch clotran.host.exception e (.getMessage (.getCause e))))
(try (eval '(let [[:a] [1]] a)) (catch clotran.host.exception e (.getMessage (.getCause e))))
(try (eval '(defn)) (catch clotran.host.exception e (.getMessage (.getCause e))))
(try (eval '(ns foo.bar (:require [clojure.string :as]))) (catch clotran.host.exception e (.getMessage (.getCause e))))
[(instance? clotran.host.i_obj (reify)) (meta (with-meta (reify) {:a 1})) (isa? (class (reify)) clotran.host.value) (ifn? #{1}) (ifn? {}) (ifn? []) (ifn? :a) (ifn? 'a) (ifn? #'first) (ifn? 1) (fn? #{1}) (fn? first) (#(identity {:a % :b #{%}}) 1) (map-entry? (clotran.host.map_entry. 1 2)) (key (clotran.host.map_entry. 1 2)) (string? (str (clotran.uuid.UUID/randomUUID))) (= (clotran.uuid.UUID/randomUUID) (clotran.uuid.UUID/randomUUID))]

;; BigInt: 1N is its own type, exact at any size, and `+'` promotes
;; into it (DEVIATIONS 26, 30)
[(pr-str 1N) (str 1N) (pr-str [1N]) (= 1N 1) (== 1N 1) (= 1N 1.0) (== 1N 1.0) (= (hash 1N) (hash 1)) (pr-str -42N) (pr-str 0N)]
[(+ 1N 1) (- 1N 2N) (* 99999999999999999999N 99999999999999999999N) (+ 1N 1.5) (* 1N 0) (- 1N) (+ 1N 1N) (- 1N 1N)]
[(< 1N 2) (> 2N 1) (zero? 0N) (pos? 1N) (neg? -1N) (max 1N 2) (min 1N 2) (compare 1N 2) (compare 2N 1) (compare 1N 1) (< 9223372036854775807N 9223372036854775808N)]
[(integer? 1N) (int? 1N) (number? 1N) (rational? 1N) (decimal? 1N) (float? 1N) (ratio? 1N) (even? 2N) (odd? 3N) (even? 10000000000000000000N)]
[(+' 1 1) (+' 9223372036854775807 1) (*' 4611686018427387904 4) (inc' 9223372036854775807) (dec' -9223372036854775808) (-' 1 2) (reduce *' 1 (range 1 26))]
[(bigint 1) (bigint "12") (bigint 5/2) (bigint 1N) (bigint 12345678901234567890) (long 1N) (double 1N) (int 5N) (str 1N)]
[(quot 10N 3) (rem 10N 3) (mod -7N 3) (quot -10N 3) (rem -10N 3) (quot 18446744073709551616N 4) (rem 18446744073709551616N 7)]
[(/ 1N 3) (/ 4N 2) (/ 10N 4) (* 2N 1/2) (+ 1/2 1N) (- 1N 1/2) (try (/ 1N 0) (catch clotran.host.arithmetic_exception e :divide-by-zero))]
[(pr-str 12345678901234567890) (read-string "42N") (apply + [1N 2N]) (reduce + 0N [1N 2N]) (sort [2 1N 3N]) (vec (repeat 2 1N)) (pr-str {1N 2N})]
(let [m (into {} (map vector (range 40) (range 40)))] [(get m 1N) (contains? #{1N} 1) (count (set [1 1N])) (= {1N :a} {1 :a})])
(loop [i 0 acc 1N] (if (< i 25) (recur (inc i) (* acc (inc i))) acc))
;; a BigInt remainder makes a Ratio of BigInts (DEVIATIONS 26, closed 2026-10-01)
(try (/ 99999999999999999999N 7) (catch clotran.host.arithmetic_exception e :no-big-ratio))
(expect-diff "DEVIATIONS 30: one big integer type, so biginteger answers a BigInt and prints 1N")
(pr-str (biginteger 1))
[(nth [10 20 30] 1N) (get [10 20 30] 1N) (subs "abcd" 1N 3N) (take 2N [1 2 3 4]) (repeat 2N :x) (nthrest [1 2 3] 1N) (abs -123N) (abs 5N) (= (range 1N 4N) (range 1 4))]
[(try (bit-and 3N 1) (catch clotran.host.illegal_argument_exception e :not-supported)) (try (bit-shift-left 1N 2) (catch clotran.host.illegal_argument_exception e :not-supported)) (bit-and 3 1)]

;; a class is a value of its own, named and printed as clj names it
[(class 1) (class "a") (class []) (class {}) (class :k) (class nil) (class (class 1)) (pr-str (class 1)) (str (class 1)) (class? (class 1)) (keyword? (class 1))]
[(= (class 1) clotran.host.int8) (= (class "a") clotran.host.string) (identical? (class 1) (class 1)) (instance? clotran.host.int8 1) (instance? clotran.host.value 1) (instance? clotran.host.char_sequence "a") (isa? (class 1) clotran.host.value) (isa? clotran.host.int8 clotran.host.number)]
[(resolve 'clotran.host.string) (resolve 'clotran.host.persistent_vector) (resolve 'NonExistentClass.Name) (resolve 'NonExistentClass.) (pr-str {(class 1) :a}) (get {(class 1) :a} clotran.host.int8) (class (class clotran.host.int8))]
(expect-diff "DEVIATIONS 34: supers is the short chain clotran models, not clj's two dozen")
(let [m (sort-by str (supers (class {})))] (vec m))
(do (deftype CPoint [x y]) (defrecord CRec [a b]) [(str (class (->CRec 1 2))) (= (class (->CRec 1 2)) (class (->CRec 3 4))) (= (->CRec 1 2) (->CRec 1 2)) (resolve 'CRec)])

;; BigDecimal: 1.0M is its own type and its own equality category, and
;; the SCALE is part of the value (DEVIATIONS 30)
[(pr-str 1.0M) (str 1.0M) (pr-str 1M) (pr-str -3.50M) (pr-str 0M) (pr-str 0.001M) (pr-str 0.0000001M) (pr-str 1e10M) (pr-str 1.5e-10M) (pr-str 1.0e3M) (pr-str 100M)]
[(= 1.0M 1.0) (= 1.0M 1M) (== 1.0M 1M) (= 1M 1) (== 1M 1) (= 1M 1N) (== 1M 1N) (= (hash 1M) (hash 1.0M)) (count (set [1M 1.0M])) (get {1M :a} 1.0M) (count (set [1 1.0 1.0M 1N]))]
[(decimal? 1M) (number? 1M) (rational? 1M) (float? 1M) (integer? 1M) (int? 1M) (ratio? 1M) (zero? 0M) (pos? 1M) (neg? -1M)]
[(pr-str (+ 1M 1)) (pr-str (+ 1.5M 2.25M)) (pr-str (* 1.5M 2.25M)) (pr-str (- 1M 2M)) (pr-str (+ 0.1M 0.2M)) (pr-str (* 0.1M 0.1M)) (pr-str (* 1M 0.1M)) (pr-str (- 1M)) (pr-str (+ 1M 1N)) (pr-str (+ 1M 1/2)) (pr-str (* 1M 1/2))]
[(+ 1M 1.0) (* 2M 3.0) (pr-str (/ 1M 2)) (pr-str (/ 1M 8)) (pr-str (/ 100M 4)) (pr-str (/ 1.0M 2)) (pr-str (/ 10M 4))]
[(pr-str (quot 10.5M 3)) (pr-str (rem 10.5M 3)) (pr-str (mod -7M 3)) (pr-str (inc 1M)) (pr-str (dec 1M)) (pr-str (abs -1.5M)) (compare 1M 2M) (compare 1.0M 1M) (< 1M 2M) (pr-str (max 1M 2M))]
[(pr-str (bigdec 1)) (pr-str (bigdec 1.5)) (pr-str (bigdec "2.50")) (pr-str (bigdec 1N)) (pr-str (bigdec 1/2)) (pr-str (bigdec 1M)) (bigint 2.5M) (long 2.5M) (double 1.5M) (int 2M)]
[(transduce (dedupe) conj [1 1.0 1.0M 1N]) (distinct [1 1.0 1.0M 1N]) (pr-str (sort [2M 1M 1.5M]))]
(expect-diff "DEVIATIONS 43: *math-context* is decimal128 here, so this answers rather than throwing")
(try (/ 1M 3) (catch clotran.host.arithmetic_exception e :non-terminating))
(try (even? 2M) (catch clotran.host.illegal_argument_exception e :not-an-integer))
[(sorted-set 0M) (sorted-set 1M 1M) (sorted-set 1N 2N) (sorted-set 1 1.5M 2N) (sorted-map 1M :a) (pr-str (sort [2M 1M 1.5M])) (pr-str (sort [2N 1N 3]))]
[(bound? (var map)) (.isBound (var map)) (bound? (var map) (var inc))]

;; with-precision, which the derived suite cannot see: `with-precision`
;; is not in cljs.core, so the clojure/cljs intersection leaves it out
;; and these are the only tests it has (DEVIATIONS 30, 43)
[(with-precision 4 (+ 3.5555555M 1)) (with-precision 6 (+ 3.5555555M 1)) (with-precision 2 (* 1.11M 2)) (with-precision 10 (/ 1M 3)) (with-precision 5 (* 1.23456M 1M)) (with-precision 3 (/ 2M 3)) (with-precision 1 (+ 999.9M 0))]
[(with-precision 6 :rounding CEILING (+ 3.5555555M 1)) (with-precision 6 :rounding FLOOR (+ 3.5555555M 1)) (with-precision 6 :rounding HALF_UP (+ 3.5555555M 1)) (with-precision 6 :rounding HALF_DOWN (+ 3.5555555M 1)) (with-precision 6 :rounding HALF_EVEN (+ 3.5555555M 1)) (with-precision 6 :rounding UP (+ 3.5555555M 1)) (with-precision 6 :rounding DOWN (+ 3.5555555M 1)) (with-precision 6 :rounding UNNECESSARY (+ 3.5555M 1))]
[(with-precision 6 :rounding CEILING (- 0M 3.5555555M)) (with-precision 6 :rounding FLOOR (- 0M 3.5555555M)) (with-precision 1 :rounding HALF_EVEN (+ 2.5M 0)) (with-precision 1 :rounding HALF_EVEN (+ 3.5M 0)) (with-precision 1 :rounding HALF_DOWN (+ 2.5M 0))]
[(with-precision 10 (/ 1M 8)) (with-precision 10 (/ 100M 4)) (with-precision 34 (/ 1M 2))]
(try (with-precision 3 :rounding UNNECESSARY (+ 3.5555M 1)) (catch clotran.host.arithmetic_exception e (.getMessage e)))
(binding [*math-context* (clotran.host.math_context. 8)] (+ 3.55555555555555M 1))
(binding [*math-context* nil] (try (/ 1M 3) (catch clotran.host.arithmetic_exception e (.getMessage e))))

;; and the default that makes clotran answer where Clojure raises
(expect-diff "DEVIATIONS 43: *math-context* is decimal128 here, so a decimal division answers instead of throwing")
(try (/ 1M 3) (catch clotran.host.arithmetic_exception e :throws))
(expect-diff "DEVIATIONS 43: *math-context* has a value here and is nil in Clojure")
(pr-str *math-context*)

;; THE INTERSECTION, name by name. upstream/derive-tests filters Clojure's
;; own deftests; it never enumerated the intersection itself, so a name
;; Rich only exercises from a clj-shaped test had nothing testing it
;; here. These are those names.
[(any? 1) (char? \a) (double? 1.0) (ident? 'a) (ident? :a) (indexed? [1]) (inst? 1) (nat-int? 0) (neg-int? -1) (pos-int? 1) (delay? (delay 1)) (distinct? 1 2) (reduced? (reduced 1)) (tagged-literal? (tagged-literal 'x 1))]
[(qualified-ident? 'a/b) (qualified-keyword? :a/b) (qualified-symbol? 'a/b) (simple-ident? 'a) (simple-keyword? :a) (simple-symbol? 'a) (uri? 1) (uuid? 1) (uuid? (random-uuid)) (string? (str (random-uuid))) (uuid? (parse-uuid "11111111-2222-3333-4444-555555555555"))]
[(bit-and-not 7 2) (bit-not 0) (bit-or 1 2) (bit-xor 3 1) (unsigned-bit-shift-right -1 60)]
[(unchecked-byte 300) (unchecked-char 65) (unchecked-short 70000) (unchecked-long 5) (unchecked-double 5) (unchecked-float 5) (unchecked-negate 5) (unchecked-inc-int 5) (unchecked-dec-int 5) (unchecked-negate-int 5) (unchecked-subtract-int 5 2) (unchecked-divide-int 7 2) (unchecked-remainder-int 7 2)]
[(alength (int-array 3)) (alength (object-array 3)) (aget (int-array [1 2 3]) 1) (aget (object-array [:a :b]) 0) (vec (int-array [1 2 3])) (alength (float-array 2)) (alength (byte-array 2)) (vec (char-array [\a \b])) (vec (boolean-array 2)) (alength (ints (int-array 2)))]
[(vec (amap (int-array [1 2 3]) i a (* 2 (aget a i)))) (vec (booleans (boolean-array [true false]))) (vec (floats (float-array [1.0 2.0]))) (vec (shorts (short-array [1 2]))) ((memfn toUpperCase) "ab") (comment 1 2) (vec (bytes (byte-array [1 2])))]
[(mapv vec (to-array-2d [[1 2] [3 4]])) (mapv vec (to-array-2d [[1 2] [3]])) (count (to-array-2d [])) (mapv vec (to-array-2d (list (list :a) (list :b :c))))]
[(vec (keep-indexed (fn [i x] (when (odd? i) x)) [:a :b :c :d])) (list* 1 [2 3]) (not-empty []) (not-empty [1]) (vec (remove odd? [1 2 3 4])) (count (repeatedly 3 (constantly 1))) (vec (replicate 3 :x)) (splitv-at 2 [1 2 3 4]) (vec (take-last 2 [1 2 3 4])) (vec (tree-seq vector? seq [1 [2 3]])) (trampoline (fn [] (fn [] 42)))]
[(ancestors :user/none) (descendants :user/none) (let [h (derive (make-hierarchy) :user/a :user/b)] [(contains? (ancestors h :user/a) :user/b) (contains? (descendants h :user/b) :user/a) (contains? (ancestors (underive h :user/a :user/b) :user/a) :user/b)])]
(require 'clojure.set)
[(pos? (count (ns-publics 'clojure.set))) (contains? (ns-interns 'clojure.set) 'union) (map? (ns-imports 'clojure.core)) (contains? (ns-publics 'clojure.core) 'map)]
(let [n (create-ns 'oracle-unmap-ns)] (intern n 'gone 1) [(contains? (ns-publics n) 'gone) (do (ns-unmap n 'gone) (contains? (ns-publics n) 'gone))])
[(= (hash-ordered-coll [1 2]) (hash-ordered-coll '(1 2))) (= (hash-unordered-coll #{1 2}) (hash-unordered-coll #{2 1})) (integer? (hash-combine 1 2))]
[((memoize inc) 1) (munge "a-b") (doto [1] count) (locking (clotran.host.value.) 42) (symbol? (gensym)) (let [a (atom 1)] (reset-meta! a {:b 2}) (meta a)) (munge "a-b?") (munge 'a*b)]
[(with-out-str (pr 1 2)) (println-str 1) (prn-str 1) (with-out-str (flush)) (<= 0.0 (rand) 1.0) (<= 0 (rand-int 5) 4) (count (random-sample 1.0 [1 2 3]))]
[(let [a (atom 0) seen (atom nil)] (add-watch a :k (fn [k r o n] (reset! seen n))) (reset! a 5) (remove-watch a :k) (reset! a 9) [@seen @a])]
[(let [f (fn [x] x)] [(add-tap f) (tap> :hello) (remove-tap f)])]
[(re-pattern "a+") (str (re-pattern "a+")) (vec (re-seq (re-pattern "a+") "aa b aaa"))]
[(vector? (destructure '[[a b] [1 2]])) (reduced? (ensure-reduced 1)) (unreduced (reduced 1)) (unreduced 1)]
[(let [t (transient [1 2])] (assoc! t 0 9) (persistent! t)) (let [t (transient {:a 1})] (dissoc! t :a) (persistent! t))]
[(do (defprotocol OP (om [x])) (extend-type clotran.host.string OP (om [_] :s)) (extend-protocol OP clotran.host.int8 (om [_] :l)) [(om "x") (om 1)])]
[(let [a (double-array [1.0 2.0])] (areduce a i ret 0.0 (+ ret (aget a i))))]

;;; ---- the portable libraries, by namespace ---------------------------
;;;
;;; Every name in these resolves (all 458 library publics do), which is
;;; a weaker claim than every name WORKING. clojure.zip in particular
;;; answered nil from branch? until a collection literal started
;;; carrying its metadata, and nothing in the derived suite could see
;;; it: Clojure's own zip tests contain no deftest.

(require 'clojure.zip)
[(-> (clojure.zip/vector-zip [1 [2 3] 4]) clojure.zip/down clojure.zip/right clojure.zip/down clojure.zip/node)
 (-> (clojure.zip/vector-zip [1 2]) clojure.zip/down (clojure.zip/edit inc) clojure.zip/root)
 (vec (-> (clojure.zip/seq-zip '(1 (2 3))) clojure.zip/down clojure.zip/rights))
 (-> (clojure.zip/vector-zip [1]) clojure.zip/down (clojure.zip/insert-right 2) clojure.zip/root)
 (clojure.zip/node (clojure.zip/xml-zip {:tag :a :content [{:tag :b}]}))]
[(loop [l (clojure.zip/vector-zip [1 [2 [3]] 4]) acc []]
   (if (clojure.zip/end? l) acc (recur (clojure.zip/next l) (conj acc (clojure.zip/node l)))))
 (-> (clojure.zip/vector-zip [[1 2] 3]) clojure.zip/down clojure.zip/down clojure.zip/right clojure.zip/lefts vec)
 (-> (clojure.zip/vector-zip [1 2 3]) clojure.zip/down clojure.zip/rightmost clojure.zip/node)
 (-> (clojure.zip/vector-zip [1 2]) clojure.zip/down clojure.zip/remove clojure.zip/root)
 (-> (clojure.zip/vector-zip [1]) clojure.zip/down (clojure.zip/replace 9) clojure.zip/root)
 (clojure.zip/path (-> (clojure.zip/vector-zip [[1]]) clojure.zip/down clojure.zip/down))]

(require 'clojure.data)
[(clojure.data/diff {:a 1 :b 2} {:a 1 :c 3})
 (clojure.data/diff [1 2 3] [1 9 3])
 (clojure.data/diff #{1 2} #{2 3})
 (clojure.data/diff 1 1)
 (clojure.data/diff nil {:a 1})
 (clojure.data/diff {:a {:b 1 :c 2}} {:a {:b 1 :c 9}})]

(require 'clojure.template)
[(clojure.template/apply-template '[x] '(+ x 1) [5])
 (clojure.template/apply-template '[x y] '(list x y x) [1 2])
 (with-out-str (clojure.template/do-template [x y] (print x y) 1 2 3 4))]

(require 'clojure.datafy)
[(clojure.datafy/datafy {:a 1})
 (clojure.datafy/datafy [1 2])
 (clojure.datafy/nav [1 2] 0 1)
 (clojure.datafy/datafy (with-meta [1] {`clojure.core.protocols/datafy (fn [x] :custom)}))
 (clojure.datafy/nav (with-meta [1] {`clojure.core.protocols/nav (fn [c k v] [:nav k v])}) 0 9)]

(require 'clojure.pprint)
[(with-out-str (clojure.pprint/pprint [1 2 3]))
 (clojure.pprint/cl-format nil "~D" 2000000)
 (clojure.pprint/cl-format nil "~:D" 2000000)
 (clojure.pprint/cl-format nil "~A and ~S" "x" "x")
 (clojure.pprint/cl-format nil "~{~A~^, ~}" [1 2 3])
 (clojure.pprint/cl-format nil "~5,'0D" 42)
 (clojure.pprint/cl-format nil "~R" 42)
 (clojure.pprint/cl-format nil "~:(~A~)" "hello world")]
[(with-out-str (clojure.pprint/print-table [{:a 1 :b 2} {:a 3 :b 4}]))
 (with-out-str (binding [clojure.pprint/*print-right-margin* 10] (clojure.pprint/pprint (range 12))))
 (with-out-str (clojure.pprint/with-pprint-dispatch clojure.pprint/code-dispatch (clojure.pprint/pprint '(defn f [x] x))))
 (clojure.pprint/cl-format nil "~,2F" 3.14159)
 (with-out-str (clojure.pprint/pprint {:a 1}))]

;;; Metadata on a collection LITERAL: Clojure's Compiler wraps the
;;; vector, map and set literals in a MetaExpr, so the map is evaluated
;;; and the collection carries it. clojure.zip is built on it.
[(meta ^{:a 1} [1]) (meta ^{:a 1} {:k 1}) (meta ^{:a 1} #{1}) (meta ^:foo [1])
 (let [f inc] ((:a (meta ^{:a f} [1])) 5)) (meta [1]) (:tag (meta ^clotran.host.string [1]))]

(require 'clojure.edn)
[(clojure.edn/read-string "{:a [1 2] :b #{3}}")
 (clojure.edn/read-string "(1 2 3)")
 (clojure.edn/read-string {:readers {'x (fn [v] [:tagged v])}} "#x 5")
 (clojure.edn/read-string {:default (fn [t v] [t v])} "#unknown 5")
 (clojure.edn/read-string nil)
 (clojure.edn/read-string "nil")
 (try (clojure.edn/read-string "#unknown 5") (catch clotran.host.throwable e (.getMessage e)))]
[(clojure.edn/read-string {:readers {'a (fn [v] {:a v}) 'b (fn [v] [:b v])}} "#a #b 1")
 (clojure.edn/read-string {:readers {'t (fn [v] (count v))}} "[#t [1 2] #t {:x 1}]")
 (clojure.edn/read-string {:readers {'t (fn [v] (count v))}} "#{#t [1 2]}")
 (clojure.edn/read-string {:readers {'t (fn [v] (count v))}} "(#t [1 2 3])")
 (clojure.edn/read-string "1/2") (clojure.edn/read-string "3.5M")
 (clojure.edn/read-string "7N") (clojure.edn/read-string ":a/b")
 (clojure.edn/read-string "\"a\nb\"")]
[(clojure.edn/read-string "#uuid \"00000000-0000-0000-0000-000000000000\"")]

;;; Type hints change behaviour, not only speed. A ^long or ^double
;;; parameter or return converts by RT.longCast/doubleCast after a
;;; checkCast to Number (Compiler.emitUnboxArg); an array hint is a
;;; checkcast where the value is USED as an array, so an unused or
;;; counted parameter never notices. Compared by exception class.
(defn hint-t [f] (try (let [v (f)] [v (.getSimpleName (class v))])
                      (catch clotran.host.throwable e [:threw (.getSimpleName (class e))])))
[(long 1.9) (long -1.9) (long 7/2) (long \a) (double 3) (double 1/4)
 (unchecked-long 1.9) (unchecked-long 1e30) (unchecked-long -1e30) (unchecked-long ##NaN)
 (hint-t #(long "x")) (hint-t #(long nil)) (hint-t #(long 1e30)) (hint-t #(double "x")) (hint-t #(double nil))]
[(hint-t #((fn [^long n] n) 1.5)) (hint-t #((fn [^double x] x) 2)) (hint-t #((fn [^long n] n) 7/2))
 (hint-t #((fn [^long n] n) \a)) (hint-t #((fn [^long n] n) "x")) (hint-t #((fn [^long n] n) nil))
 (hint-t #((fn ^long [x] x) 1.5)) (hint-t #((fn ^double [x] x) 2))
 (hint-t #((fn ([^long n] n) ([^long n m] m)) 1.5)) (hint-t #(((fn [^long n] (fn [] n)) 2.5)))
 (hint-t #((fn [^clotran.host.string s ^long n] [s n]) "x" 1.5))]
[(hint-t #((fn [^doubles a] :ok) [1 2])) (hint-t #((fn [^doubles a] (aget a 0)) [1 2]))
 (hint-t #((fn [^doubles a] (alength a)) [1 2])) (hint-t #((fn [^doubles a] (aset a 0 1.0)) [1 2]))
 (hint-t #((fn [^longs a] (aget a 0)) (double-array [1.5]))) (hint-t #((fn [^doubles a] (aget a 0)) (long-array [3])))
 (hint-t #((fn [^doubles a] (aget a 0)) nil)) (hint-t #((fn [^ints a] (aget a 0)) (long-array [3])))
 (hint-t #((fn [^objects a] (aget a 0)) (long-array [3]))) (hint-t #(let [^doubles a [1 2]] (aget a 0)))
 (hint-t #((fn [^doubles a] (let [a [1]] (nth a 0))) (double-array 1)))
 (hint-t #((fn [^doubles a] (aget a 0)) (double-array [2.5])))]
(expect-diff "DEVIATIONS 48: recur to a ^long local with a double is a compile error in clj, a conversion here")
[(hint-t #((fn [^long n acc] (if (< n 1) acc (recur (- n 0.5) (conj acc n)))) 2 []))]
(expect-diff "DEVIATIONS 48: a primitive hint on a let local is an UnsupportedOperationException in clj")
[(hint-t #(let [^long x 1.5] x))]
[(hint-t #((fn [^doubles a] (aset a 0 2)) (double-array 1)))]

;;; Regex past the Basic Multilingual Plane. ICU reports offsets in
;;; UTF-16 units and clotran indexes by character (DEVIATIONS 41); the
;;; shim counts one into the other, and without it every match after an
;;; emoji was shifted -- (re-find #"x" "👋x") was "". Arabic is here as
;;; a right-to-left script in the Basic Plane, for contrast.
[(re-find #"x" "👋x") (re-seq #"." "a👋b") (re-seq #"\p{So}" "hi 👋🏽 👨‍👩‍👧 🇯🇵 ✅")
 (re-seq #"\X" "hi 👋🏽 👨‍👩‍👧 🇯🇵 ✅") (re-find #"(\S+) (x)" "👋🏽 x")
 (clojure.string/split "a👋b👋c" #"👋") (clojure.string/replace "👋x👋y" #"[xy]" "!")
 (clojure.string/replace "👋ab" #"(a)(b)" "$2$1") (re-matches #"(.)(.)" "👋🇯")]
[(re-seq #"\p{L}+" "مرحبا بالعالم ١٢٣") (re-seq #"\p{IsArabic}+" "مرحبا بالعالم ١٢٣")
 (re-seq #"\p{Nd}+" "مرحبا ١٢٣") (clojure.string/upper-case "istanbul ı")
 (sort ["b" "ä" "a" "z" "é"])]

;;; load-file restores *ns*, as Compiler.load binds it: the loaded file's
;;; (ns ...) does not leak into the forms after it.
[(do (load-file "test/clj/load_file_sample.clj") (str *ns*)) @(resolve 'load-file-sample/x)]

;;; Arithmetic errors say what clj says. Long overflow is
;;; Math.addExact's "long overflow" on every path (Numbers); an index
;;; out of range is ArrayIndexOutOfBoundsException naming both numbers --
;;; for a slice of a multi-dimensional array too, which once answered nil.
(defn msg-of [f] (try (f) :no-throw (catch clotran.host.throwable e [(.getSimpleName (class e)) (.getMessage e)])))
[(msg-of #(+ clotran.host.int8/MAX_VALUE 1)) (msg-of #(* clotran.host.int8/MAX_VALUE 2)) (msg-of #(inc clotran.host.int8/MAX_VALUE))
 (msg-of #(dec clotran.host.int8/MIN_VALUE)) (msg-of #(- clotran.host.int8/MIN_VALUE)) (msg-of #(int 3000000000))
 (msg-of #(aget (long-array [5 6]) 2)) (msg-of #(aget (double-array [1.0]) -1))
 (msg-of #(aset (long-array [5 6]) 2 1)) (msg-of #(long 1.0E30))
 (let [f (fn [a b] (quot a b))] (msg-of #(f 7 0))) (let [f (fn [a b] (mod a b))] (msg-of #(f 7 0)))]
(expect-diff "DEVIATIONS 51: literal longs compile to clj's primitive quot, whose zero divisor is clj's \"/ by zero\"")
[(msg-of #(quot 7 0)) (msg-of #(rem 7 0))]
[(msg-of #(subs "ab" 0 3)) (msg-of #(subs "ab" 3)) (msg-of #(subs "ab" 1 0)) (msg-of #(subs "héllo" 1 3))]

;;; Arrays: an array is an instance of its array class, and a negative
;;; size is clj's NegativeArraySizeException naming the size.
[(instance? (class (double-array 0)) (double-array 2)) (instance? (class (long-array 0)) (long-array 1))
 (msg-of #(double-array -1)) (msg-of #(long-array -3))]

;;; An array's class is clj's name for it, one per element type and
;;; rank, and prints as Clojure prints it (it was one class, and printing
;;; it crashed).
[(map #(str (class %)) [(double-array 1) (long-array 1) (int-array 1) (float-array 1) (boolean-array 1) (object-array 1) (make-array clotran.host.int4/TYPE 2 3)])
 (pr-str (class (double-array 1))) (pr-str (class (make-array clotran.host.int4/TYPE 2 3))) (pr-str (class (object-array 1)))
 (instance? (class (double-array 0)) (double-array 2)) (instance? (class (long-array 0)) (double-array 2))
 (.isArray (class (long-array 1))) (= (class (double-array 1)) (class (double-array 5)))]
[(map #(str (class %)) [(short-array 1) (byte-array 1) (char-array 1)]) (bytes? (byte-array 1))]

;;; Runtime.availableProcessors is the machine's, as clj's is
;;; (sysconf through Threads.f90); pmap's look-ahead is sized by it.
[(.availableProcessors (clotran.host.runtime/getRuntime))]

;; protocol dispatch picks the implementation Clojure picks: a chunked
;; seq reduces through InternalReduce's IChunkedSeq implementation
(let [p clojure.core.protocols/InternalReduce, ic (get (:impls p) clotran.host.i_chunked_seq)]
  [(= ic (find-protocol-impl p (seq (map inc (range 3)))))
   (= ic (find-protocol-impl p (seq (range 3))))
   (= ic (find-protocol-impl p (cons 1 nil)))])
(reduce + (map inc (range 1000)))
;; a seq that is NOT chunked reduces too (it once looped forever)
[(reduce conj [:init] (seq {1 1 2 2})) (reduce conj [:init] (seq "ab")) (reduce conj [:init] (seq (sorted-map 1 1)))]
(reduce (fn [a x] (if (> x 5) (reduced a) (+ a x))) 0 (map inc (range 100)))
;; a chunk's .reduce hands back a Reduced as it is, as ArrayChunk.reduce does
(let [c (chunk-first (seq [1 2 3]))] [(reduced? (.reduce c (fn [a x] (reduced a)) 0)) (.reduce c + 0)])
(transduce (take 5) + (cycle [1]))

;; transient vectors (PersistentVector.f90): made in O(1) over the vector
;; they come from, appended to in place, built into a tree by persistent!
[(instance? clotran.host.i_editable_collection []) (class (transient [])) (instance? clotran.host.i_transient_vector (transient []))]

(persistent! (reduce conj! (transient []) (range 70)))

(let [v (vec (range 40)) t (transient v)] (conj! t :a) (assoc! t 0 :z 41 :end) [(persistent! t) v])

(let [t (transient [1 2 3])] [(count t) (nth t 1) (get t 5 :nf) (nth t 9 :d) (count (pop! t)) (persistent! (pop! (pop! t)))])

(try (let [t (transient [1])] (persistent! t) (conj! t 2)) (catch clotran.host.throwable e [(.getName (class e)) (.getMessage e)]))

(try (pop! (transient [])) (catch clotran.host.throwable e [(.getName (class e)) (.getMessage e)]))

(try (assoc! (transient [1]) :k 2) (catch clotran.host.throwable e [(.getName (class e)) (.getMessage e)]))

[(into [] (map inc (range 5))) (into [1 2] [3 4]) (into (vec (range 100)) [:x]) (= (into [] (range 5000)) (range 5000))]

[(mapv inc (range 40)) (filterv even? (range 20)) (meta (into (with-meta [1] {:m 1}) [2]))]

(let [v (persistent! (reduce conj! (transient []) (range 1100)))] [(count v) (nth v 0) (nth v 1023) (nth v 1024) (nth v 1099) (count (conj v :n)) (peek (pop v))])

(let [m (zipmap (range 3000) (range 3000))] [(reduce + (map val m)) (count (seq m)) (every? map-entry? m) (= (set (keys m)) (set (range 3000))) (count (rest (seq m)))])

(let [s (set (range 2000))] [(reduce + (seq s)) (count (rest (seq s))) (count (next (next (seq s))))])

[(seq "héllo") (count (seq (apply str (repeat 3000 "é")))) (nth (seq "abç") 2) (rest "ab") (map int "aé") (seq "") (first "ç") (reduce str (seq "xyz"))]

(count (doall (for [i (range 5000)] (re-find (re-pattern (str "b \\+ " i "\\b")) (str "b + " (* 2 i))))))

(let [tv (transient [1 2 3])] [(get tv 0) (get tv 4 :foo) (contains? tv 0) (contains? tv 3) (find tv 0) (find tv -1) (counted? tv) (empty? tv) (empty? (transient [])) (instance? clotran.host.indexed tv)])

[(/ 3/4 5) (/ 3/4 1/5) (/ 5 3/4) (/ 3/4 5.0) (/ 1 3/4) (/ 1/2 1/2) (* 8 1/2) (+ 1/2 1/2) (- 3/2 1/2) (* 0 1/2) (/ 2 1/2) (/ 4 2) (rem 1 1/2) (quot -7/2 2)]

[(conj (range 3) 9) (conj (concat [1 2] [3 4]) 5) (conj (map inc [1 2]) 0) (list? (conj '(1 2) 0)) (apply map * [[1 2] [1 2] [1 2] [1 2]]) (apply interleave [[:a :b] [1 2] ["x" "y"]])]

[(nth [nil] 0 :d) (nth nil 5 :d) (nth nil 5) (nth '(1 nil) 1 :d) (nth [1] 5 :d)]

(try (nth [1 2] 5) (catch clotran.host.index_out_of_bounds_exception e :oob))

(try (nth (range 3) 5) (catch clotran.host.index_out_of_bounds_exception e :oob))

(try (nth {:a 1} 0) (catch clotran.host.unsupported_operation_exception e :unsupported))

[(conj {} (seq {:a 1 :b 2})) (conj {} (first {:z 9})) (conj {} nil) (conj {} ()) (into {} [[:a 1] (first {:b 2})])]

(try (conj {} [:a 1 :b]) (catch clotran.host.illegal_argument_exception e :iae))

(try (conj {:a 1} '(:b 2)) (catch clotran.host.class_cast_exception e :cce))

(try (into {} ['(:a "a")]) (catch clotran.host.class_cast_exception e :cce))

[(int \a) (byte \a) (pos? 1N) (neg? -1.5M) (zero? 0/1)]

(try (zero? nil) (catch clotran.host.null_pointer_exception e :npe))

(try (pos? {}) (catch clotran.host.class_cast_exception e :cce))

(try (int "1") (catch clotran.host.class_cast_exception e :cce))

(try (unchecked-int "1") (catch clotran.host.class_cast_exception e :cce))

[(let [k (keyword "a" "b/c")] [k (namespace k) (name k) (= k :a/b/c)]) (let [s (symbol "a" "b/c")] [s (namespace s) (name s)]) (symbol :a/b) (symbol :dog) (keyword nil "x") (symbol nil "x")]

(try (keyword 'user "abc") (catch clotran.host.class_cast_exception e :cce))

(try (name 2) (catch clotran.host.class_cast_exception e :cce))

(try (namespace "a/b") (catch clotran.host.class_cast_exception e :cce))

[(compare "abc" "abf") (compare "ab" "abcd") (compare "ab" (str "ab" (char 1))) (compare "é" "e") (compare :a/b :b) (compare :z/a :a/z) (compare (quote a/b) (quote a/c)) (sort ["b" "ab" "a"])]

[(realized? (lazy-seq [1])) (realized? (delay 1)) (realized? (iterate inc 1))]

(try (realized? [1]) (catch clotran.host.class_cast_exception e :cce))

(try (realized? (range 5)) (catch clotran.host.class_cast_exception e :cce))

(try (merge-with + 1 {:a 1}) (catch clotran.host.illegal_argument_exception e :iae))

(try (hash-map :a) (catch clotran.host.illegal_argument_exception e :iae))

(try (sorted-map :a) (catch clotran.host.illegal_argument_exception e :iae))

(try (subseq [1 2 3 4] > 2) (catch clotran.host.class_cast_exception e :cce))

(try (create-ns "my-ns") (catch clotran.host.class_cast_exception e :cce))

(try (count 1) (catch clotran.host.unsupported_operation_exception e :uoe))

(try (contains? 1 :a) (catch clotran.host.illegal_argument_exception e :iae))

[(count nil) (contains? nil :a) (contains? (to-array [1 2]) 1) (get 1 :a :d) (clotran.host.system/getenv "")]

(let [xs (map #(mod (* % 7919) 10007) (range 3000)) s (into (sorted-set) xs) s2 (reduce disj s (range 0 10007 3))] [(count s) (first s) (last s) (take 5 (rseq s)) (nth (seq s) 1234) (count s2) (take 5 s2) (take 5 (rseq s2)) (subseq s >= 100 < 110) (rsubseq s > 100 <= 110) (count (reduce disj s xs))])

(let [m (into (sorted-map) (map (fn [x] [x (* x x)]) (range 2000)))] [(get m 500) (find m 42) (take 3 (subseq m > 1990)) (take 3 (rsubseq m < 10)) (count (reduce dissoc m (range 0 2000 2))) (first (into (sorted-map-by >) m))])

[(get (sorted-map nil 1) nil) (contains? (sorted-map nil 1) nil) (find (sorted-map nil 1) nil) (sorted-map nil 1 0 2) (dissoc (sorted-map 1 1 2 2) 3) (assoc (sorted-map 1 1) 1 2)]

(mapv hash [nil true 0 1 -1 42 9223372036854775807 1.5 -0.0 ##NaN 1/2 -3/4 1N 100000000000000000000N 1.50M 100M 0M \a "" "a" "héllo" "日本" :a :a/b 'x 'ns/x [] [1 2] '(1 2) () {} {:a 1} #{} #{1 2 3} (first {:a 1})])

[(seq #{7 6 5}) (seq (set (range 10))) (keys (zipmap (range 12) (range 12))) (seq (hash-map :a 1 :b 2 :c 3)) (seq #{:a :b :c :d}) (vec (set ["x" "y" "z" "w"])) (= (hash (zipmap (range 20) (range 20))) (hash (into {} (map vector (range 20) (range 20)))))]

[(boolean (re-find #"#object\[[\w.]+ 0x[0-9a-f]+ \{:status :ready, :val 1\}\]" (pr-str (reduced 1)))) (class (reduced 1)) (map? (reduced 1)) (pr-str (tagged-literal 'js [1 2])) (class (ref 1)) (class (agent 1)) (instance? clotran.host.atom (ref 1)) (list? (cons 1 '(2))) (list? (cons 1 nil)) (list? (conj '(2) 1)) (class (cons 1 '(2)))]

(with-local-vars [w 0 z 5] (dotimes [_ 3] (var-set w (inc @w))) [@w @z])

(do (defmacro oracle-locals [] (vec (sort (map str (keys &env))))) [(let [x 1 y 2] (oracle-locals)) ((fn [a] (let [b 2] (oracle-locals))) 1)])

(try ({:a 1}) (catch clotran.host.arity_exception e :arity))

(try ([1] 0 1) (catch clotran.host.arity_exception e :arity))

(try (transient '(1 2)) (catch clotran.host.class_cast_exception e :cce))

[(unchecked-int 1e10) (unchecked-int -1e10) (unchecked-long 1e30) (unchecked-byte 1e10) (quote @x) (quote ~x) (quote ~@x) (ns-unmap *ns* 'oracle-nope)]

(let [calls (atom [])] (sorted-map-by (fn [a b] (swap! calls conj [a b]) (compare a b)) "a" 1 "b" 2) @calls)

;; a file of each side's own, under this checkout's build/: the two sides
;; run at once (scripts/oracle), and so do make crosscheck's two halves;
;; the answer is the contents, never the path
(let [p (str "build/oracle-io-" (clotran.host.system/getProperty "clj's vm.name") ".txt")] (spit p "hello\nworld\n") (spit p "more" :append true) [(slurp p) (with-open [r (clotran.files/reader p)] (vec (line-seq r)))])

(try (require 'oracle.no-such-lib) (catch clotran.host.io_exception e :io))

(do (def oracle-v 1) (set-validator! #'oracle-v (fn [x] (< x 3))) (alter-var-root #'oracle-v inc) (try (alter-var-root #'oracle-v inc) (catch clotran.host.illegal_state_exception e [:invalid oracle-v])))

[(keys (seq {:a 1 :b 2})) (vals (take 1 {:a 1})) (keys ())]

[(let [a (byte-array 2)] (aset a 0 (byte 5)) (vec a)) (let [a (short-array 2)] (aset a 0 (short 5)) (vec a)) (let [a (char-array 2)] (aset a 0 \x) (vec a)) (let [a (float-array 2)] (aset a 0 (float 1.5)) (vec a))]

[(try (let [a (byte-array 2)] (aset a 0 5)) (catch clotran.host.illegal_argument_exception e :iae)) (try (let [a (short-array 2)] (aset a 0 (byte 5))) (catch clotran.host.illegal_argument_exception e :iae)) (let [a (int-array 2)] (aset a 0 (short 5)) (vec a))]

[(let [a (byte-array 2)] (aset-byte a 0 1) (aset-byte a 1 -1) (vec a)) (vec (byte-array [1 200 -129 127 128 255 256])) (vec (short-array [1 70000 -32769])) (vec (map #(bit-and % 0xff) (byte-array [-128 -1 0 127]))) (seq (byte-array 3)) (try (byte 200) (catch clotran.host.illegal_argument_exception e :iae)) (unchecked-byte 200) (unchecked-short 70000) (vec (aclone (byte-array [1 -1])))]

[(str (class (aget (byte-array 1) 0))) (str (class (aget (short-array 1) 0))) (str (class (aget (char-array 1) 0))) (str (class (aget (float-array 1) 0))) (str (class (byte 1))) (str (class (short 1))) (str (class (int 1))) (str (class (+ (byte 1) 1))) (= (byte 1) 1) (hash (byte 1)) (instance? clotran.host.int1 (byte 1)) (instance? clotran.host.int8 (byte 1)) (instance? clotran.host.number (short 1)) (instance? clotran.host.real4 (float 1))]

[(count (range 5)) (count (range 0 10 3)) (count (range 10 0 -3)) (count (range 1.0 2.0 0.3)) (count (rest (range 100))) (count (drop 40 (range 100))) (count (range 5 5)) (count (range -3)) (count (range 0 10 4)) (count (range 0 -10 -4)) (count (range 1/2 3 1/2)) (count (take 70 (range 100))) (count (range 1000000)) (bounded-count 10 (range 1000000)) (count (map inc (range 100000)))]

[(nth (iterate inc 0) 100000) (take 3 (iterate inc 0)) (nth (iterate #(* 2 %) 1) 62) (count (take 1000 (iterate inc 0))) (last (range 100000)) (nth (map inc (range 100000)) 99999) (nth (range 10) 3 :d) (nth (iterate inc 0) 5 :d) (nth '(1 2) 5 :d) (realized? (rest (iterate inc 0)))]

[(boolean (re-find #"^[\w.]+@[0-9a-f]+$" (str (map inc [1 2])))) (str (range 3)) (str (cons 1 nil)) (boolean (re-find #"(?i)lazy_?seq@" (str (take 2 (iterate inc 0))))) (boolean (re-find #"(?i)lazy_?seq@" (str (lazy-seq [1]))))]

[(format "%x" (byte -128)) (format "%x" (short -1)) (format "%X" (int -1)) (format "%o" (byte -1)) (format "%x" -1) (format "%d" (byte 5))]

[(try (hash-ordered-coll 1) (catch clotran.host.class_cast_exception e :cce)) (try (hash-unordered-coll "12") (catch clotran.host.class_cast_exception e :cce)) (try (hash-ordered-coll nil) (catch clotran.host.throwable e :npe)) (hash-ordered-coll [1 2]) (hash-unordered-coll #{1 2}) (hash-ordered-coll (list 1 2))]

[(:author (meta (find-ns 'clojure.core))) (:doc (meta (find-ns 'clojure.core)))]

[(reduce (fn [a b] (+ a b)) (eduction (map inc) (range 3))) (reduce (fn [a b] (+ a b)) (eduction (map inc) [7])) (reduce (fn [a b] (if (> b 2) (reduced a) (+ a b))) (eduction (map inc) (range 10)))]

[(str (parse-uuid "B6883C0A-0342-4007-9966-BC2DFA6B109E")) (uuid? (parse-uuid "b6883c0a-0342-4007-9966-bc2dfa6b109e")) (uuid? "x") (parse-uuid "foo") (parse-uuid "") (= (parse-uuid "b6883c0a-0342-4007-9966-bc2dfa6b109e") #uuid "b6883c0a-0342-4007-9966-bc2dfa6b109e") (pr-str #uuid "17392216-6ca5-491a-b38c-0000000920ba") (uuid? (random-uuid)) (count (str (random-uuid))) (instance? clotran.uuid.UUID (random-uuid))]

[(read-string "#uuid \"17392216-6ca5-491a-b38c-0000000920ba\"") (binding [*data-readers* {'oracle-dbl (fn [x] (* 2 x))}] (read-string "#oracle-dbl 21")) (try (read-string "#oracle-nope [1]") (catch clotran.host.throwable e :no-reader)) '[#uuid "17392216-6ca5-491a-b38c-0000000920ba" {:k #uuid "17392216-6ca5-491a-b38c-0000000920ba"}] (tagged-literal 'js [1 2]) (tagged-literal? (tagged-literal 'js [1 2]))]

[(do (def oracle-unb) (str (class oracle-unb))) (str oracle-unb) (try (oracle-unb) (catch clotran.host.illegal_state_exception e :unbound-call)) (bound? #'oracle-unb) (do (def ^:dynamic oracle-dyn) (binding [oracle-dyn 1] oracle-dyn))]

[(load-string "(+ 1 2)") (load-string "(def oracle-ls 5) oracle-ls") (load-string "")]

[(try (eval '(apply and [true])) (catch clotran.host.throwable e :macro-value)) (try (eval '(map or [true] [false])) (catch clotran.host.throwable e :macro-value)) (try (eval '(var user/oracle-no-such-var)) (catch clotran.host.throwable e :no-var))]

[(:a (meta (with-meta (reify clotran.host.value) {:a 1}))) (try (with-meta (clotran.files/file ".") {:a 1}) (catch clotran.host.class_cast_exception e :cce))]

(try (let [f (fn f [n] (f (inc n)))] (f 0)) (catch clotran.host.stack_overflow_error e :so))

[(= (hash [1 2 3]) (hash-ordered-coll [1 2 3])) (= (hash #{1 2}) (hash-unordered-coll #{1 2})) (= (hash {:a 1}) (hash-unordered-coll {:a 1})) (hash-ordered-coll (map inc [1 2])) (hash-unordered-coll [1 1])]

[(with-redefs [first last] (first [1 2])) ((with-redefs [first last] #(first [1 2]))) (do (defn oracle-ten [] 10) (with-redefs [oracle-ten (fn [] 11)] (oracle-ten))) (oracle-ten) (with-redefs [first last] (last [1 2 3])) (with-redefs [rest butlast] (vec (map inc [1 2 3])))]

[(do (defmacro oracle-mac [] 1) (with-redefs [oracle-mac (constantly 2)] (oracle-mac))) (do (defn oracle-inl {:inline (fn [_] 1)} [_] 1) (with-redefs [oracle-inl (constantly 2)] (oracle-inl :foo))) (with-redefs [oracle-inl (constantly 2)] (vec (map oracle-inl [:a :b])))]

[(:file (meta #'map)) (:file (meta #'clojure.string/join)) *1 *2 *3 *e (bound? #'*1) (read-string "\\\\\\\\") (map str (read-string "[\\\\\\\\ \\newline \\ ]")) (str (class (clotran.files/file "x"))) (instance? clotran.io.File (clotran.files/file "x"))]

[(try (eval 'user.OracleNoSuch) (catch clotran.host.throwable e :err)) (try (eval 'no.such.Klass) (catch clotran.host.throwable e :err)) (do (defrecord OracleRec [a]) (str (eval 'user.OracleRec))) (some? (eval 'clojure.core.protocols.CollReduce)) (str clotran.host.date)]

[(let [m (transient {:x 1 :y 2 :z 3})] (dissoc! m :x) (persistent! m)) (persistent! (reduce conj! (transient {}) [[:a 1] [:b 2]])) (persistent! (assoc! (transient {}) :k 7)) (persistent! (disj! (conj! (transient #{1 2}) 3) 1)) (let [t (transient #{1 2})] [(count t) (contains? t 1) (get t 2) (find (transient {:a 1}) :a) (get (transient {:a 1}) :a)]) (str (class (transient {:a 1}))) (str (class (transient (hash-map :a 1)))) (str (class (transient #{1}))) (try (let [t (transient {})] (persistent! t) (assoc! t :a 1)) (catch clotran.host.illegal_access_error e :used-after)) (instance? clotran.host.i_editable_collection {}) (instance? clotran.host.i_editable_collection (sorted-map)) (try (transient (sorted-set)) (catch clotran.host.class_cast_exception e :cce))]

(defrecord OracleMP [a b])

[(map->OracleMP {:a 1 :b 2 :z 9}) (OracleMP/create (with-meta {:a 1 :b 2} {:m 1})) (meta (with-meta {:a 1} nil)) (str (class (with-meta {:a 1} nil))) (instance? clotran.host.map_equivalence {}) (instance? clotran.host.map_equivalence (sorted-map)) (instance? clotran.host.map_equivalence (->OracleMP 1 2)) [((transient {:a 1}) :a) (:a (transient {:a 1})) ((transient #{:a}) :b 2) (get (transient #{:a}) :a)]]

[(let [r (ref 0)] (dosync (alter r inc) (alter r inc)) @r) (try (alter (ref 0) inc) (catch clotran.host.illegal_state_exception e :no-tx)) (try (ref-set (ref 0) 5) (catch clotran.host.illegal_state_exception e :no-tx)) (try (dosync (io! 1)) (catch clotran.host.illegal_state_exception e :io-in-tx)) (let [r (ref 1)] (try (dosync (ref-set r 5) (throw (ex-info "x" {}))) (catch clotran.host.exception e @r))) (let [r (ref 1)] (dosync (ref-set r 5) [@r (ensure r)])) (let [r (ref 1) w (atom [])] (add-watch r :k (fn [k _ o n] (swap! w conj [o n]))) (dosync (alter r + 10) (commute r * 2)) [@r @w]) (let [r (ref 1 :validator pos?)] [(try (dosync (ref-set r -1)) (catch clotran.host.illegal_state_exception e :invalid)) @r]) (let [a (ref 100) b (ref 0)] (dosync (alter a - 30) (alter b + 30)) [@a @b]) (ref-history-count (ref 1)) (ref-min-history (ref 1)) (ref-max-history (ref 1))]


[(str (class (eduction (map inc) [1 2]))) (instance? clojure.core.Eduction (eduction [1])) (pr-str (eduction (map inc) [1 2])) (try (count (eduction (map inc) [1 2])) (catch clotran.host.unsupported_operation_exception e (.getMessage e))) (count (reify clotran.host.i_persistent_collection clotran.host.seqable (seq [_] (seq [1 2 3])))) (try (count (reify clotran.host.seqable (seq [_] (seq [1 2 3])))) (catch clotran.host.unsupported_operation_exception e :unsupported)) (count (reify clotran.host.counted (count [_] 7))) (reduce + (eduction (map inc) [1 2])) (reduce + 10 (eduction (map inc) [1 2])) (into [] (eduction (map inc) (filter even?) (range 10))) (seq (eduction (map inc) [1 2])) (sequential? (eduction [1 2]))]

;; the promoting operators on machine integers: a long stays a long
;; and the big path is for the one value that overflows (inc' went
;; through decimal strings for every element of (range))
[(-' -9223372036854775808) (*' -9223372036854775808 -1) (+' 1 2 3) (-' 10 3 2) (*' 2 3 4) (inc' 5) (dec' 5) (class (inc' 5)) (class (+' 1 2)) (class (+' 9223372036854775807 1)) (+' 1N 1) (+' 1.5 1) (-' 1/2 1) (+' 9223372036854775807 -1) (*' 3037000500 3037000500) (*' 3037000499 3037000499)]

;; core's one-line wrappers ((fn [coll] (. RT (first coll)))) are called
;; as their builtin when the arity matches; a wrong arity is still the
;; fn's error, and a wrapper passed as a value still works
[(try (first) (catch clotran.host.arity_exception e :arity)) (try (first [1] [2]) (catch clotran.host.arity_exception e :arity)) (try (next) (catch clotran.host.arity_exception e :arity)) (map first [[1] [2 3] nil]) (apply first [[5 6]]) (reduce (fn [a x] (conj a (first x))) [] [[1] [2]]) (let [f rest] (f [1 2 3])) ((comp first rest) [1 2 3]) (apply cons 0 [[1 2]])]

;; apply over a long lazy take: the dot call's argument vector no
;; longer holds the head (it held every cell, 452 MB at 1e6)
[(apply + (take 300000 (range))) (apply (fn [& more] (reduce + more)) (take 300000 (range))) (apply max (take 1000 (iterate inc 0))) (apply str (take 5 (cycle "ab")))]

;; lazy-seq's expansion (new LazySeq (fn* [] ...)) is the lazy node
[(take 5 ((fn step [i] (lazy-seq (cons i (step (inc i))))) 0)) (realized? (lazy-seq nil)) (let [s (lazy-seq [1 2])] [(realized? s) (first s) (realized? s)]) (seq (lazy-seq (lazy-seq nil))) (let [n (atom 0) s (lazy-seq (swap! n inc) [1])] (doall s) (doall s) @n) (try (doall (lazy-seq (throw (ex-info "t" {})))) (catch clotran.host.exception e (ex-message e))) (seq (clotran.host.lazy_seq. (fn [] [1 2])))]

;; fn bodies run as flat instructions (flat.inc): builtin calls by
;; register, the integer fast path and its overflow, a three-argument
;; host call on locals (it was handed nil while the fast path was
;; being written), clearing, loops and arities
(defn flat-rt3 [m k v] (clotran.host.rt/assoc m k v))
(defn flat-mix [x y] [(+ x y) (- x 1) (< x y) (inc x) (dec y) (* x y) (= x x) (zero? (- x x)) (pos? y) (neg? (- x y))])
(defn flat-ovf [x] [(try (inc x) (catch clotran.host.arithmetic_exception e :ovf)) (try (+ x 1) (catch clotran.host.arithmetic_exception e :ovf)) (try (* x 2) (catch clotran.host.arithmetic_exception e :ovf)) (try (- (- x) 2) (catch clotran.host.arithmetic_exception e :ovf))])
(defn flat-clear [s] [(first s) (count s) (vec (rest s))])
(defn flat-loop [n] (loop [i 0 acc []] (if (< i n) (recur (inc i) (conj acc (* i i))) acc)))
(defn flat-var ([] (flat-var 1)) ([a] (flat-var a 2)) ([a b & more] [a b more]))

[(flat-rt3 {} :a 1) (flat-mix 3 4) (flat-mix 2.5 1) (flat-ovf clotran.host.int8/MAX_VALUE) (flat-ovf 5) (flat-clear (map inc [1 2 3])) (flat-loop 5) (flat-var) (flat-var 1 2 3 4)]

;; unchecked-inc/dec wrap; the flat fast path leaves the one wrapping
;; value to the builtin
[(unchecked-inc clotran.host.int8/MAX_VALUE) (unchecked-dec clotran.host.int8/MIN_VALUE) (let [x 5] (unchecked-inc x)) (let [f (fn [x] (unchecked-dec x))] (f clotran.host.int8/MIN_VALUE)) (let [n 3] (loop [i 0 acc []] (if (< i n) (recur (unchecked-inc i) (conj acc i)) acc)))]

;; first/next/rest/seq answered inline where the slot is already there
;; (flat.inc flat_seq_op): nil, lists, realised, empty and delegating cells
(defn flat-seqops [x] [(first x) (next x) (rest x) (seq x)])
(defn flat-realized [s] (doall s) (flat-seqops s))
[(flat-seqops nil) (flat-seqops '()) (flat-seqops '(1)) (flat-seqops '(1 2)) (flat-realized (lazy-seq nil)) (flat-realized (lazy-seq (cons 1 nil))) (flat-realized (map inc [1 2 3])) (flat-realized (take 2 (range))) (flat-realized (lazy-seq (lazy-seq [1 2]))) (let [[f n r s] (flat-seqops (iterate inc 0))] [f (take 3 n) (take 3 r) (take 3 s)]) (let [s (map inc [1 2])] [(identical? (seq s) (seq s)) (class (seq s))])]

;; forcing in the loop (flat.inc flat_force): a self-referential seq,
;; one seq forced from four futures, a thunk answering a lazy seq, a
;; thunk run once however often it is walked
(def flat-fibs (lazy-cat [0 1] (map + flat-fibs (rest flat-fibs))))
(defn flat-shared [] (let [s (map (fn [x] (clotran.host.thread/sleep 1) (* x x)) (range 20)) fs (doall (for [_ (range 4)] (future (reduce + s))))] (mapv deref fs)))
(defn flat-nested [] (let [s ((fn step [i] (lazy-seq (when (< i 5) (lazy-seq (cons i (step (inc i))))))) 0)] [(first s) (next s) (seq s) (rest (rest s))]))
(defn flat-once [] (let [n (atom 0) s ((fn step [i] (lazy-seq (swap! n inc) (when (< i 3) (cons i (step (inc i)))))) 0)] (dorun s) (dorun s) [(vec s) @n]))
[(take 10 flat-fibs) (flat-shared) (flat-nested) (flat-once)]

(defn flat-throwing [] (let [n (atom 0) s (lazy-seq (swap! n inc) (throw (ex-info "t" {})))] [(try (first s) (catch clotran.host.exception e (ex-message e))) (try (next s) (catch clotran.host.exception e (ex-message e))) (try (seq s) (catch clotran.host.exception e :again)) @n]))
(expect-diff "DEVIATIONS 59: a lazy-seq thunk keeps its captures after it throws")
(flat-throwing)

;; chunked-seq?, seq? and reduced? on every kind (is_instance answers
;; these three from the value's kind), a deftype implementing ISeq
;; among them
(deftype FlatSeqT [] clotran.host.i_seq (first [_] 1) (next [_] nil) (more [_] ()) (cons [this x] this) (seq [this] this) (count [_] 1) (empty [_] ()) (equiv [_ o] false))
(for [x [nil 1 "s" [1] '(1) () (list) (lazy-seq nil) (lazy-seq [1]) (seq [1 2]) (seq (range 3)) (range 3) (map inc [1]) (seq {:a 1}) (cons 1 nil) (cons 1 [2]) (reduced 1) {:a 1} #{1} (with-meta '(1) {:m 1}) (->FlatSeqT)]] [(chunked-seq? x) (seq? x) (reduced? x)])

;; (instance? C x) with a class literal is the type test, not a call
;; through the Var (InstanceOfExpr): with-redefs does not reach it, and
;; a class in a local still calls the Var
[(with-redefs [instance? (fn [c x] :redef)] (instance? clotran.host.string "a")) (with-redefs [instance? (fn [c x] :redef)] (let [c clotran.host.string] (instance? c "a"))) (instance? clotran.host.string 1) (let [f instance?] (f clotran.host.number 1))]

;; try/catch/finally and case compiled flat (flat.inc fc_try, fc_case):
;; catch order, finally on every road, a catch that throws, nesting, a
;; try in a loop, errors from callees and host calls, case tables
(defn flat-try1 [x] (let [log (atom [])] [(try (swap! log conj :body) (when x (throw (ex-info "boom" {:x x}))) :ok (catch clotran.host.exception_info e (swap! log conj :ei) [:ei (ex-message e) (ex-data e)]) (catch clotran.host.exception e (swap! log conj :ex) :ex) (finally (swap! log conj :fin))) @log]))
(defn flat-try2 [] (let [log (atom [])] [(try (try (/ 1 0) (catch clotran.host.arithmetic_exception e (swap! log conj :inner) (throw (ex-info "again" {}))) (finally (swap! log conj :inner-fin))) (catch clotran.host.exception e (swap! log conj :outer) (ex-message e))) @log]))
(defn flat-try3 [] (let [log (atom [])] [(try (try (throw (clotran.host.illegal_state_exception. "no")) (finally (swap! log conj :fin))) (catch clotran.host.illegal_state_exception e (.getMessage e))) @log]))
(defn flat-try4 [n] (loop [i 0 acc []] (if (< i n) (recur (inc i) (conj acc (try (if (odd? i) (throw (clotran.host.exception. (str i))) i) (catch clotran.host.exception e (keyword (.getMessage e)))))) acc)))
(defn flat-thrower [x] (throw (ex-info "from callee" {:v x})))
(defn flat-try5 [] [(try (flat-thrower 1) (catch clotran.host.exception e (:v (ex-data e)))) (try (nth [1 2] 5) (catch clotran.host.index_out_of_bounds_exception e :oob)) (try (.substring "abc" 5) (catch clotran.host.exception e :sub)) (try (first 5) (catch clotran.host.illegal_argument_exception e :iae))])
(defn flat-try6 [] (try (try (throw (ex-info "kept" {:k 1})) (catch clotran.host.arithmetic_exception e :wrong)) (catch clotran.host.exception e [(ex-message e) (ex-data e)])))
(defn flat-try7 [] (let [a (atom 0)] [(try 1 (finally (swap! a inc))) (try (try (throw (clotran.host.exception. "x")) (catch clotran.host.exception e (throw (clotran.host.exception. "y"))) (finally (swap! a + 10))) (catch clotran.host.exception e (.getMessage e))) @a]))
(defn flat-case [x] (case x 1 :one 2 :two (3 4) :three-four "s" :str :k :kw [1 2] :vec nil :nil :default))
(defn flat-case2 [x] (case x (1 2 3) :small 100 :hundred -1 :neg))
[(flat-try1 nil) (flat-try1 1) (flat-try2) (flat-try3) (flat-try4 6) (flat-try5) (flat-try6) (flat-try7) (mapv flat-case [1 2 3 4 "s" :k [1 2] nil 9 "t"]) (mapv flat-case2 [1 3 100 -1]) (try (flat-case2 7) (catch clotran.host.illegal_argument_exception e (.getMessage e)))]

;; protocol dispatch through the cache (DEVIATIONS 13, resolved): per
;; class, nil and Object, records and types, re-extension, via metadata
(defprotocol FP (fp [x]) (fp2 [x y]))
(extend-protocol FP clotran.host.int8 (fp [x] [:long x]) (fp2 [x y] [:long2 x y]) clotran.host.string (fp [x] [:str x]) (fp2 [x y] :s2) nil (fp [x] :nil) (fp2 [x y] :nil2) clotran.host.value (fp [x] :obj) (fp2 [x y] :obj2))
(defrecord FR [a] FP (fp [_] [:rec a]) (fp2 [_ y] [:rec2 a y]))
(deftype FT [] FP (fp [_] :type) (fp2 [_ y] :type2))
(defprotocol FM :extend-via-metadata true (fm [x]))
(extend-protocol FM clotran.host.int8 (fm [x] :long-fm))
(def r1 (mapv fp [1 "a" nil :k 2 "b" (->FR 1) (FT.) 1.5 [1] nil 3]))
(extend-protocol FP clotran.host.int8 (fp [x] [:long-again x]) (fp2 [x y] [:long2-again x y]))
(def r2 (mapv fp [1 2 "a"]))
(def r3 [(fp2 1 2) (fp2 "x" 1) (fp2 (->FR 5) 6) (fm 1) (fm (with-meta [1] {(quote user/fm) (fn [_] :via-meta)})) (try (fm "x") (catch clotran.host.illegal_argument_exception e :no-impl))])
[r1 r2 r3]

;; a record's declared field by keyword is read from the field (inst_lookup);
;; hidden fields, extension keys, qualified keys and defaults as valAt
(defrecord BR [a b])
[(:__extmap (->BR 1 2)) (:__meta (->BR 1 2)) (:a (assoc (->BR 1 2) :c 3)) (:c (assoc (->BR 1 2) :c 3)) (get (->BR 1 nil) :b :nf) (get (->BR 1 2) :z :nf) (:user/a (->BR 1 2)) (:a (with-meta (->BR 1 2) {:m 1}))]

;; StringBuilder appends are buffered and joined on a read
;; (gc_sb_append/gc_sb_flush): reads between appends, reverse, str,
;; join, with-out-str, pr-str
(defn sbt [] (let [sb (clotran.host.string_builder. "ab")] (.append sb "cd") (.append sb 1) (let [l1 (.length sb) s1 (str sb)] (.append sb \x) (.append sb [1 2]) [l1 s1 (.toString sb) (.length sb) (str (.reverse (clotran.host.string_builder. "héllo"))) (str (doto (clotran.host.string_builder.) (.append "a") (.append "b")))])))
[(sbt) (str "a" 1 nil :k [1] "é") (clojure.string/join "," (range 12)) (clojure.string/join [1 2 3]) (with-out-str (print "x") (println "y" 1) (pr [1 "a"])) (pr-str {:a [1 2] :b "s"}) (count (pr-str (vec (range 3000)))) (apply str (repeat 40 "ab")) (format "%s-%d" "x" 3) (str (reduce (fn [sb i] (.append sb i)) (clotran.host.string_builder.) (range 20)))]

;; instance? on the scalar classes, answered from tag and width; the two
;; big integers are one type here (DEVIATIONS: one big integer type)
(for [x [nil 1 (int 1) (short 1) (byte 1) 1.5 (float 1.5) 1M 1/2 "s" \c :k 'sym true [1] (with-meta 'm {:a 1})]]   [(instance? clotran.host.int8 x) (instance? clotran.host.int4 x) (instance? clotran.host.int2 x) (instance? clotran.host.int1 x) (instance? clotran.host.bigint x) (instance? clotran.host.bigint x) (instance? clotran.host.string x) (instance? clotran.host.number x) (instance? clotran.host.real8 x) (instance? clotran.host.char x) (instance? clotran.host.keyword x) (instance? clotran.host.symbol x) (integer? x) (number? x) (string? x) (int? x) (double? x)]) 

;; regex over an all-ASCII subject by byte spans (matcher_ascii): re-seq,
;; groups, replace with $n, split, appendReplacement; non-ASCII subjects
;; keep the counted road
[(re-seq #"\d+" "a1 22 333 b") (re-seq #"(\w)(\d)" "a1 b2 c3") (re-find #"é(.)" "xxéy") (re-seq #"." "aé😀b") (re-find #"(x)?y" "y") (let [m (re-matcher #"(\d)(\d)?" "1 23")] [(re-find m) (re-find m) (re-find m)]) (re-matches #"(a)(b)" "ab") (clojure.string/replace "a1b22" #"\d+" "#") (clojure.string/split "a,b,,c" #",") (count (re-seq #"\d+" (clojure.string/join " " (range 1000))))]
[(clojure.string/replace "a1b22c333" #"(\d)(\d)?" "<$1|$2>") (clojure.string/replace-first "aXbXc" #"X" "-") (clojure.string/replace "abc" #"" "-") (clojure.string/replace "日本語" #"本" "x") (clojure.string/split "a1b2c3" #"\d") (clojure.string/split "a1b2c3" #"\d" 2) (clojure.string/split "é,ü,,x" #",") (let [m (re-matcher #"(\d)" "a1b2") sb (clotran.host.string_buffer.)] (while (.find m) (.appendReplacement m sb "<$1>")) (.appendTail m sb) (str sb)) (clojure.string/replace "x.y" #"\." "\\$")]

;; (:k x) from the register (flat.inc), and assoc! on a transient map
;; straight to the map's assoc (tmap_op)
(defrecord KR [a])
[(:a {:a 1}) (:z {:a 1}) (:a nil) (:a #{:a}) (:a (sorted-map :a 3)) (:a (->KR 5)) (:q (assoc (->KR 5) :q 6)) (:a (transient {:a 7})) (:a [1 2]) (:a "s") (:a (with-meta {:a 9} {:m 1})) (map :a [{:a 1} nil {:b 2}]) (try (:a) (catch clotran.host.arity_exception e :arity))]
[(persistent! (assoc! (transient {}) :a 1)) (persistent! (reduce (fn [m i] (assoc! m i (* i i))) (transient {}) (range 20))) (frequencies [1 2 1 3 1]) (group-by odd? (range 6)) (let [t (transient {:a 1})] (persistent! t) (try (assoc! t :b 2) (catch clotran.host.throwable e (class e)))) (persistent! (assoc! (transient {:a nil}) :a 1 :b 2))]

;; records by value in maps and sets, their hash clj's, assoc on a
;; declared field without the method (record_field_index)
(defrecord RA [a b])
(def r (with-meta (->RA 1 2) {:m 1}))
[(assoc r :a 9) (meta (assoc r :a 9)) (assoc r :c 3) (:c (assoc r :c 3)) (assoc (assoc r :c 3) :b 5) (= (assoc r :a 1) r) (= (hash (assoc r :a 7)) (hash (->RA 7 2))) (class (assoc r :a 9)) (record? (assoc r :b nil)) (assoc r :user/a 1) (dissoc (assoc r :a 9) :a) (update r :a inc) (assoc-in {:x r} [:x :b] 0) (into {} (assoc r :a 3))]
(let [big (into {} (map (fn [i] [(->RA i 0) i]) (range 20))) small {(->RA 5 0) 5} s (set (map #(->RA % 0) (range 20)))] [(get big (->RA 5 0)) (get small (->RA 5 0)) (contains? s (->RA 7 0)) (count (set [(->RA 1 1) (->RA 1 1)])) (count (into #{} (map (fn [_] (->RA 1 1)) (range 20))))])
[(hash (->RA 7 2)) (hash (assoc (->RA 1 2) :a 7)) (hash (with-meta (->RA 7 2) {:m 1})) (.equals (->RA 7 2) (->RA 7 2))]

;; a deftype's equals and hasheq are its = and hash (DEVIATIONS 60)
(do (deftype VP [x] clotran.host.value (equals [_ o] (and (instance? VP o) (= x (.-x o)))) (hashCode [_] (hash x)) clotran.host.i_hash_eq (hasheq [_] (hash x))) [(= (VP. 1) (VP. 1)) (count (set [(VP. 1) (VP. 1)]))])

;; a def, a swap! and a letfn beside a loop's recur (node_has_recur: only
;; a recur INSIDE a nested node keeps an arity a tree)
(defn lr [n] (loop [i 0 acc []] (if (< i n) (do (def lr-last i) (recur (inc i) (conj acc i))) acc)))
(defn lf [n] (loop [i 0] (if (< i n) (letfn [(g [x] (* 2 x))] (recur (+ i (g 1)))) i)))
[(lr 3) lr-last (lf 3) (let [a (atom 0)] (loop [i 0] (when (< i 3) (swap! a inc) (recur (inc i)))) @a)]

;; clojure.repl loads (its source-fn names proxy-super), so require's
;; :rename can refer a var under another name
(require '[clojure.repl :as r :refer [doc] :rename {doc d}])
[(resolve 'd) (resolve 'r/dir-fn) (sort (clojure.repl/dir-fn 'clojure.set))]

;; a method an interface declares ^void answers nil wherever it is
;; implemented (record_void_methods); pprint's ppflush is one, so pprint is nil
(definterface IV (^void f [x]) (g [x]))
(deftype TV [a] IV (f [_ x] (+ a x)) (g [_ x] (+ a x)))
[(.f (TV. 1) 2) (.g (TV. 1) 2) (.f (reify IV (f [_ x] x) (g [_ x] x)) 3) (.f (proxy [IV] [] (f [x] x)) 4) (instance? IV (TV. 1))]
(with-out-str (prn (clojure.pprint/pprint {:a 1})))
(import )
(import  )

;; to-array answers an Object[] as itself (RT.toArray), so sort-by on
;; an array sorts it in place
(let [h (to-array "Hello") x (to-array [32 -5 4 11]) y (sort-by - x)] [(identical? (to-array h) h) (seq y) (seq x) (identical? (to-array (int-array 2)) (int-array 2))])
;; assoc on a vector throws clj's classes
(mapv #(try (assoc [1 2 3] % 0) (catch clotran.host.exception e (class e))) [0 3 4 -1 :a])

;; a list read from a file has {:line :column} metadata (LispReader),
;; merged into any ^ gave it; a vector does not, nor a read-string list
[(meta '(a b)) (meta '^:foo (a b)) (meta (second '(x ^{:k 1} (a b)))) (meta '[a b]) (meta (read-string "(a b)")) (meta (macroexpand-1 '(-> 1 (+ 2))))]
(binding [*print-meta* true] (pr-str (:arglists (meta #'defmacro))))
;; a def evaluated from a form with no file position takes the
;; top-level form's line and file (DefExpr's LINE and SOURCE_PATH)
(let [m (meta (eval (read-string "(def oracle-def-pos 1)")))] [(:line m) (:column m) (string? (:file m))])

;; the tokens LispReader.matchSymbol refuses, and the ones it takes
(mapv #(try (read-string %) (catch clotran.host.exception e :invalid)) ["://" ":a/" ":/a" "a/" "/a" "a//" ":a//" ":///" "///" "a///" "a/b/" "a:" ":a:" "a::b" "a:/b" "a/:b" ":1a" "a/1" ":a/1" "String/1" "/" ":/" "clojure.core//" ":a:b" "a:b:c/d" "abc/de:f" "a/b:"])

;; array classes by symbol: CLJ-2807's Sym/N, and clj descriptor
(let [e (comp eval read-string)] [(mapv e ["int/1" "double/2" "clotran.host.string/1" "(= int/1 (class (int-array 1)))" "(instance? long/1 (long-array 2))"]) (mapv #(resolve (symbol %)) ["int/1" "[I" "[[D" "[Lclotran.host.string;" "long/3" "[Lno.Such;" "[Q"])])
(try (resolve (symbol "no.such.Klass/1")) (catch clotran.host.class_not_found_exception e (.getMessage e)))

;; fn? answered from the value's kind (trampoline asks it every bounce)
(mapv fn? [inc (fn []) #(identity 1) :k {} #{} [] (with-meta (fn []) {:a 1}) print-method 'x nil (var inc) (reify clotran.host.i_fn (invoke [_] 1))])
(trampoline (fn f [n] (if (pos? n) #(f (dec n)) n)) 10000)

;; & is an ordinary local in let* and loop* at 1.12.6 (LetExpr.Parser
;; has no rule against it; only the interim branch added one)
[(let* [& 42] &) (loop* [& 1] &)]

;; read over a stream takes one form's characters and no more (clotran.io
;; lisp-read): a token stops at whitespace or a macro character, which is
;; pushed back; strings, regexes and collections end at their closers
(defn forms-of [s]
  (let [r (clotran.io/pushback-reader (clotran.io/text-reader s))]
    (loop [acc []]
      (let [x (try (read r false :oracle-eof) (catch clotran.host.exception e [:threw (.getMessage e)]))]
        (if (or (= x :oracle-eof) (and (vector? x) (= :threw (first x)))) (conj acc x) (recur (conj acc x)))))))
[(forms-of "(+ 1 2) [3 4] {:a 1}") (forms-of "abc,def ;comment\n  :kw 12N 1.5M 3/4 ##Inf")]
(forms-of "\"str (with) \\\" quote\" \\( \\) \\space \\a")
(mapv str (forms-of "#\"re\\\"g\" #\"x\""))
(forms-of "'x @d ^:m [e] #'f")
[(forms-of "#_ skipped kept #_#_ a b c [1 #_2 3]") (forms-of "#{1 2} #:ns{:a 1}") (forms-of "#! shebang line\n(x)") (forms-of "a(b)c")]
[(forms-of "(unclosed") (forms-of ")") (forms-of "\"open string")]
[(let [r (clotran.io/pushback-reader (clotran.io/text-reader "sym rest"))] [(read r) (slurp r)]) (let [r (clotran.io/pushback-reader (clotran.io/text-reader "(a) rest"))] [(read r) (slurp r)]) (read {:eof :done} (clotran.io/pushback-reader (clotran.io/text-reader "  ")))]
(with-in-str "1 2\n3" [(read) (read-line) (read-line)])
(with-in-str "a\nb" [(read-line) (read-line) (read-line)])
[(line-seq (clotran.host.buffered_reader. (clotran.io/text-reader "x\ny"))) (slurp (clotran.io/text-reader "abc")) (load-string "(+ 1 2) (* 2 3)")]
(let [r (clotran.io/line-numbering-reader (clotran.io/text-reader "a\r\nb\nc"))] [(read r) (.getLineNumber r) (read r) (.getLineNumber r) (read r)])
(let [r (clotran.io/line-numbering-reader (clotran.io/text-reader "  (+ 1\n 2) tail"))] (read+string r))
[(.trim "\u0001 a b \t\n") (.trim "") (.trim "   ")]

;; a capitalized name that is no class and no Var is unresolved, not a class
[(try (eval '(instance? Nonexistent 1)) (catch clotran.host.throwable e :unresolved))
 (try (eval 'Nonexistent) (catch clotran.host.throwable e :unresolved))]

;; a catch of a class there is not is a compile error, not a clause that never matches
(try (eval '(try 5 (catch Nonexistent e 1))) (catch clotran.host.throwable e :unresolved))

;; a directory walked as file-seq walks it: the directory first, then what it holds
(let [fs (file-seq (clotran.files/file "test/clj/derived"))]
  [(.isDirectory (first fs)) (count (filter #(.isFile %) fs))
   (take 3 (sort (map #(.getName %) (filter #(.isFile %) fs))))
   (.getName (clotran.files/file "a/b.cljf")) (.exists (clotran.files/file "no/such")) (.isFile (clotran.files/file "Makefile"))])

;; a shift by 64 or more follows clotran's host, Fortran (all bits out), where clj's takes the count mod 64
(expect-diff "DEVIATIONS 69: shifts follow Fortran past 63")
[(bit-shift-left 1 64) (bit-shift-right -8 65)]
;; and below 64 they agree
[(bit-shift-left 1 63) (bit-shift-right -1 63) (unsigned-bit-shift-right -1 60) (bit-shift-left 3 62)]

;; count answers clotran's one integer, not clj's host's boxed int
(expect-diff "DEVIATIONS 71: count and int answer a long")
[(class (count [1])) (class (int 1))]

;; the vector's own pop (a path copied, a level collapsed), subvec as a
;; view and rseq as an index counting down (model/vector.lisp): each was
;; a rebuild, O(n)
(let [v (vec (range 100)) w (vec (range 1025))]
  [(pop v) (pop [1]) (pop (vec (range 33))) (count (pop w)) (nth (pop w) 1023) (conj (pop w) :x) (pop (pop (vec (range 1057))))
   (subvec v 10 20) (subvec v 0 0) (subvec v 99) (conj (subvec v 10 20) :a) (assoc (subvec v 10 20) 0 :z) (pop (subvec v 10 20))
   (subvec (subvec v 10 50) 5 10) (conj (subvec v 0 100) :end) (hash (subvec v 2 5)) (reduce + (subvec v 10 20)) (seq (subvec v 95))
   (conj (subvec (conj (vec (range 31)) 31) 30) :q) (reduce conj (subvec v 90) (range 5)) (subvec (pop (vec (range 70))) 60)
   (rseq [1 2 3]) (take 3 (rseq v)) (count (rseq v)) (hash (rseq [1 2 3])) (into [] (rseq (vec (range 40)))) (vec (rseq (subvec v 0 5)))
   (meta (pop (with-meta [1 2] {:m 1}))) (= (rseq [1 2 3]) '(3 2 1)) (chunked-seq? (rseq v)) (chunked-seq? (seq v))])

;; a string's count, characters and slices read in place through its
;; index (GC.f90 str_index, model/string.lisp): non-ASCII text, indices
;; on both sides of the every-32nd marks
(let [u (str "héllo wörld ß " (apply str (repeat 70 "ü")) "end") a (apply str (repeat 100 "ab"))]
  [(count u) (count a) (nth u 0) (nth u 1) (nth u 12) (nth u 33) (nth u 86) (subs u 5) (subs u 10 20) (subs u 13 14) (subs u 50) (subs u 32 33) (subs u 31 65) (subs a 63 65)
   (.length u) (.charAt u 13) (.substring u 2 9) (get u 13) (get u 999) (contains? u 13) (contains? u 87) (first u) (rest "abc") (count (seq u)) (nth (seq u) 40)
   (reverse "aéß") (apply str (seq u)) (frequencies "héé") (subs "" 0 0) (last u) (nth a 199) (subs a 199) (seq "") (vec "éü")])

;; seqs over maps and sets are cursors (Eval.f90 cursor_seq): first is O(log n)
;; where a snapshot of every entry made it O(n); keys, vals and seq walk one order
(let [hm (zipmap (range 1000) (map #(* 2 %) (range 1000))) hs (set (range 0 3000 3)) sm (into (sorted-map) (map vector (range 500) (range 500))) ss (into (sorted-set) (range 0 1000 7)) am {:a 1 :b 2 :c 3}]
  [(sort (map key (seq hm))) (= (keys hm) (map key (seq hm))) (= (vals hm) (map val (seq hm))) (count (seq hm)) (count (rest (seq hm)))
      (sort (seq hs)) (count (seq hs)) (= (seq hs) (seq hs))
      (first sm) (take 5 sm) (take 3 (rseq sm)) (count (seq sm)) (last sm) (nth (seq sm) 250) (subseq sm >= 100 < 105) (rsubseq sm > 100 <= 105)
      (first ss) (take 4 (rseq ss)) (subseq ss > 500) (count (rsubseq ss < 500)) (reduce + (map val sm)) (reduce + ss)
      (seq am) (first am) (rest am) (count (seq am)) (seq {}) (seq #{}) (seq (sorted-map)) (rseq (sorted-map))
      (= (seq sm) (map vector (range 500) (range 500))) (hash (seq sm)) (hash (seq ss)) (hash (seq am))
      (map-entry? (first sm)) (map-entry? (first hm)) (vec (seq (sorted-map :b 2 :a 1))) (into [] (rseq (sorted-set 3 1 2)))
      (seq (dissoc sm 0)) (count (seq (into (sorted-map) (map vector (range 100) (range 100)))))
      (let [m (reduce dissoc hm (range 0 1000 2))] [(count (seq m)) (sort (keys m)) (= (keys m) (map key (seq m)))])
      (sort-by str (seq (hash-map nil 1 false 2 "a" 3)))])

;; a sorted map thinned by dissoc is rebalanced (Assoc.f90 st_rebalance,
;; model/btree.lisp): every node but the root half full, so its height
;; follows what it holds now, not what it once held
(let [xs (map #(mod (* % 7919) 100003) (range 20000))
      m (into (sorted-map) (map vector xs xs)) m2 (reduce dissoc m (take 19950 xs))
      s (into (sorted-set) xs) s2 (reduce disj s (take-nth 3 xs))]
  [(count m2) (seq m2) (first m2) (last m2) (subseq m2 > 50000) (rseq m2) (get m2 (nth xs 19990)) (get m2 (nth xs 5))
   (count s2) (take 10 s2) (take 10 (rseq s2)) (= (seq s2) (sort (remove (set (take-nth 3 xs)) xs)))
   (let [m3 (reduce dissoc m xs)] [(count m3) (seq m3) (assoc m3 1 2)])
   (reduce + (vals (reduce (fn [a k] (if (even? k) (dissoc a k) (assoc a (- k) k))) m xs)))])

;; a ratio less the smallest long is the exact ratio here; clj's host
;; negates the long first and overflows
(expect-diff "DEVIATIONS 72: a ratio less the smallest long is exact")
[(- -7/2 -9223372036854775808) (- 1/2 -9223372036854775808)]
;; and two longs overflow in both, as the docstring says
(try (- 0 -9223372036854775808) (catch clotran.host.arithmetic_exception e :overflow))

;; a deftype names itself inside its own methods, as clj's compile stub
;; lets it (scripts/fuzz-spec found UUID could not)
(do (deftype OrU [s] clotran.host.value (toString [_] (str (instance? OrU 1) (instance? OrU (OrU. 2)))))
    (str (OrU. "a")))

;; a deftype's equals and hashCode are its = and hash, as a map key and
;; in a set too (Util.equiv, Util.hasheq)
(do (deftype OrE [s] clotran.host.value
      (equals [_ o] (and (instance? OrE o) (= s (.-s ^OrE o))))
      (hashCode [_] (hash s)))
    [(= (OrE. 1) (OrE. 1)) (= (OrE. 1) (OrE. 2)) (= (hash (OrE. 1)) (hash (OrE. 1))) (hash (OrE. 7))
     (get {(OrE. 1) :v} (OrE. 1)) (count (set [(OrE. 1) (OrE. 1) (OrE. 2)]))])

;; and its compareTo is its compare, and sort's order
(do (deftype OrC [n] clotran.host.comparable (compareTo [_ o] (compare n (.-n ^OrC o))))
    [(compare (OrC. 1) (OrC. 2)) (map #(.-n ^OrC %) (sort [(OrC. 3) (OrC. 1) (OrC. 2)]))])

;; a UUID is not a map, and hashes and orders as clj's does: by its two
;; halves, signed
(let [a #uuid "8e0fb45a-eeb5-4a87-a9ff-cc5db1da66a0" b #uuid "0e0fb45a-eeb5-4a87-a9ff-cc5db1da66a0"]
  [(hash a) (hash b) (compare a b) (sort [a b]) (map? a) (record? a) (coll? a) (uuid? a)
   (= a (parse-uuid (str a))) (get {a 1} (parse-uuid (str a))) (str a)])

;; a collection's str is pr's text: print-method for what is inside, and
;; *print-namespace-maps* (RT.printString; scripts/fuzz-print)
[(str [#uuid "868251a8-16ad-4b97-a908-35edc4322e81"]) (str #{{(quote zbc/t) -78272966N}}) (str {:a "x"}) (str [1N 1.5M 1/2 \b "a"])]

;; a #tag inside a map inside a set is read every time: the scan for one
;; walked a seq it had not rooted, and under GC lost it (check-oracle-gc)
(let [s "#{#{-0.34521484375 :x+_M/_k \\r} {iGC7*-/U #uuid \"c88db98e-a03a-46b0-9a05-261c339effc7\"}}"]
  (frequencies (for [_ (range 40)] (= (read-string s) (read-string s)))))
