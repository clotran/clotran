;; Forms whose value real Clojure decides. scripts/oracle runs this file
;; through `clj` and through clotran and compares. No expected values
;; live here: clj supplies them. Setup forms (def, deftype, require)
;; run on both sides and are not compared. (expect-diff "why") before
;; a form says it MUST differ, and names the DEVIATIONS entry.
;;
;; Derived from language_test.clj on 2026-09-19; that file keeps the
;; checks only clotran can answer (Fortran arrays, clotran-type).

(deftype Point [x y]
  Object
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
(str (let [f "foo"] (reify Object (toString [this] f))))

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
(try (quot 1 0) (catch Throwable e :err))

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
(try (struct point 1 2 3) (catch Throwable e :err))

;; not a basis key
(try (accessor point :q) (catch Throwable e :err))

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

;; a seq has a type. It PRINTS differently -- a class here is a keyword,
;; and clotran has one seq view where the JVM has ChunkedSeq, StringSeq
;; and the rest -- but compares equal to the literal, below.
(expect-diff "DEVIATIONS 34: a class is a keyword and prints as one")
(type (seq ["a"]))

;; class answers the class a literal names, so the two compare equal
[(= (class "a") String) (= (class 1) Long) (= (class 1.5) Double) (= (class \a) Character)
 (= (class true) Boolean) (= (class :k) clojure.lang.Keyword) (= (class 'a) clojure.lang.Symbol)]

[(= (class []) clojure.lang.PersistentVector) (= (class {}) clojure.lang.PersistentArrayMap)
 (= (class #{}) clojure.lang.PersistentHashSet) (= (class '(1)) clojure.lang.PersistentList)
 (= (class (lazy-seq [1])) clojure.lang.LazySeq) (= (class (seq [1 2])) clojure.lang.PersistentVector$ChunkedSeq)]

[(= (class (atom 1)) clojure.lang.Atom) (= (class (delay 1)) clojure.lang.Delay) (= (class #'first) clojure.lang.Var)
 (= (class #"x") java.util.regex.Pattern) (= (class *ns*) clojure.lang.Namespace) (= (class 1/2) clojure.lang.Ratio)]

;; which is what pprint's writers do
[(condp = (class "x") String :s Long :l :other) (condp = (class 2) String :s Long :l :other) (condp = (class 2.5) String :s Long :l :other)]

;; nil has no class; type reads :type metadata first
[(class nil) (type (with-meta [] {:type :mine})) (= (type "a") String)]

;; instance? and supers agree with class
[(instance? (class "a") "a") (instance? (class []) []) (instance? (class 1) 1)
 (contains? (supers (class [])) clojure.lang.IPersistentCollection) (contains? (supers (class "a")) CharSequence)
 (contains? (supers (class 1)) Number) (contains? (supers (class (atom 1))) clojure.lang.IDeref)]

;; a thrown thing's class is the one it was made with
[(= (class (ex-info "e" {})) clojure.lang.ExceptionInfo) (= (class (Exception. "e")) Exception)
 (= (class (try (throw (IllegalArgumentException. "x")) (catch Exception e e))) IllegalArgumentException)]

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
(try (compare 1 "a") (catch Throwable e :err))

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
(try (/ 1 0) (catch Throwable e :err))

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
(expect-diff "DEVIATIONS 30: no BigInt, so quot of a ratio is a long not 3N")
[(quot 7/2 1) (rem 7/2 1) (mod 7/2 1)]

;; ratio coerce
[(int 1/2) (double 1/2)]

;; ratio compare
[(compare 1/3 1/2) (compare 1/2 1/2)]

;; ratio signs
[(pos? 1/2) (neg? -1/2)]

(def cm (make-array Integer/TYPE 2 3))

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

(def cobj (make-array Object 2))

;; object array
[(aget cobj 0) (aget cobj 1) (alength cobj)]

(def cdbl (make-array Double/TYPE 2))

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
(macroexpand-1 (quote (String. "a")))

;; macroexpand stops at the top
(macroexpand (quote (when a (when b c))))

;; special-symbol? if
(special-symbol? (quote if))

;; special-symbol? amp
(special-symbol? (quote &))

;; special-symbol? a name
(special-symbol? (quote foo))

;; specials count
(count (. clojure.lang.Compiler specials))

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
(= Math/E clojure.math/E)

;; Math/PI
(= Math/PI clojure.math/PI)

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
(clojure.math/to-degrees Math/PI)

;; exact arithmetic
[(clojure.math/add-exact 1 2) (clojure.math/subtract-exact 5 9) (clojure.math/multiply-exact 6 7) (clojure.math/increment-exact 1) (clojure.math/decrement-exact 1) (clojure.math/negate-exact 5)]

;; add-exact overflows
(try (clojure.math/add-exact Long/MAX_VALUE 1) :no (catch Throwable e :threw))

;; multiply-exact overflows
(try (clojure.math/multiply-exact Long/MAX_VALUE 2) :no (catch Throwable e :threw))

;; floor-div/mod
[(clojure.math/floor-div -7 2) (clojure.math/floor-mod -7 2)]

;; Math/abs
[(Math/abs -3) (Math/abs -3.5)]

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
(pr-str Double/MAX_VALUE)

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
(try (read-string "(1") :no (catch Throwable e :threw))

;; Long bounds
[Long/MAX_VALUE Long/MIN_VALUE]

;; Long size
[Long/SIZE Long/BYTES]

;; Integer bounds
[Integer/MAX_VALUE Integer/MIN_VALUE]

;; Short bounds
[Short/MAX_VALUE Short/MIN_VALUE]

;; Byte bounds
[Byte/MAX_VALUE Byte/MIN_VALUE]

;; Double bounds
(expect-diff "DEVIATIONS 27: the smallest subnormal prints 5.0E-324, Java prints 4.9E-324")
[Double/MAX_VALUE Double/MIN_VALUE]

;; Double exponents
[Double/MAX_EXPONENT Double/MIN_EXPONENT]

;; the non-finite constants
[(pr-str Double/POSITIVE_INFINITY) (pr-str Double/NEGATIVE_INFINITY) (pr-str Double/NaN)]

;; compare
[(Double/compare 1.0 2.0) (Double/compare 2.0 1.0) (Double/compare 1.0 1.0)]

;; compare signed zero
[(Double/compare -0.0 0.0) (Double/compare 0.0 -0.0) (Double/compare -0.0 -0.0)]

;; compare NaN
[(Double/compare Double/NaN 1.0) (Double/compare 1.0 Double/NaN) (Double/compare Double/NaN Double/NaN) (Double/compare Double/NaN Double/POSITIVE_INFINITY)]

;; Long compare
[(Long/compare 1 2) (Long/compare 2 1) (Long/compare 1 1)]

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
(vec (into-array String ["a" "b"]))

;; an empty stack trace
(expect-diff "DEVIATIONS 31: stack traces are empty until PLAN.md step 5 gives the evaluator frames")
(alength (.getStackTrace (Exception. "x")))

;; Throwable->map
(:cause (Throwable->map (Exception. "boom")))

;; ex-data
(ex-data (ex-info "m" {:a 1}))

;; ex-message
(ex-message (ex-info "m" {:a 1}))

;; instance?
(instance? clojure.lang.ExceptionInfo (ex-info "m" {}))

;; catch it by its full name
(try (throw (ex-info "m" {:a 1})) (catch clojure.lang.ExceptionInfo e (ex-data e)))

;; a plain exception has no data
(ex-data (Exception. "plain"))

;; a proxy method
(.toString (proxy [Object] [] (toString [] "hello")))

;; str goes through it
(str (proxy [Object] [] (toString [] "world")))

;; a closure
(let [n 5] (.toString (proxy [Object] [] (toString [] (str n)))))

;; arguments
(expect-diff "DEVIATIONS 28: proxy accepts methods no superclass declares; Clojure refuses")
(let [q (proxy [Object] [] (greet [n] (str "hi " n)) (two [a b] (+ a b)))] [(.greet q "x") (.two q 1 2)])

;; nested arities
(expect-diff "DEVIATIONS 28: proxy accepts methods no superclass declares; Clojure refuses")
(let [m (proxy [Object] [] (f ([] 0) ([a] a) ([a b] (+ a b))))] [(.f m) (.f m 7) (.f m 3 4)])

;; this is implicit
(expect-diff "DEVIATIONS 28: proxy accepts methods no superclass declares; Clojure refuses")
(let [s (proxy [Object] [] (me [] this))] (identical? s (.me s)))

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
(try (assoc [1] 5 :x) (catch Throwable e :threw))

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
(try (ltf0 1) (catch Throwable e (boolean (re-find #"Wrong number of args \(1\) passed to" (.getMessage e)))))

;; and which function
(try (ltf0 1) (catch Throwable e (boolean (re-find #"ltf0" (.getMessage e)))))

;; too few
(try (ltf1) (catch Throwable e (boolean (re-find #"Wrong number of args \(0\)" (.getMessage e)))))

;; a multi-arity fn
(try (ltfm 1 2 3) (catch Throwable e (boolean (re-find #"Wrong number of args \(3\)" (.getMessage e)))))

;; catchable as ArityException
(try (ltf0 1) :no (catch clojure.lang.ArityException e :arity))

;; and as IllegalArgumentException
(try (ltf0 1) :no (catch IllegalArgumentException e :iae))

;; the right arities still work
[(ltfm 1) (ltfm 1 2)]

;; an explicit mode
(error-mode (agent 1 :error-mode :continue))

;; a validator does not change the mode
(error-mode (agent 1 :validator pos?))

;; a countdown latch
(let [l (java.util.concurrent.CountDownLatch. 2)] (.countDown l) (.getCount l))

;; a validator the state already fails is refused
(try (set-validator! (atom -1) pos?) :no (catch IllegalStateException e :refused))

;; a PrintWriter shares its writer
(let [s (java.io.StringWriter.) p (java.io.PrintWriter. s)] (.write p "hi") (str s))

;; and can stand in for *err*
(let [s (java.io.StringWriter.) p (java.io.PrintWriter. s)] (binding [*err* p] (.write *err* "boom")) (str s))

;; RT/print is readable
(let [s (java.io.StringWriter.)] (clojure.lang.RT/print "x" s) (str s))

;; RT/print a collection
(let [s (java.io.StringWriter.)] (clojure.lang.RT/print [1 "a"] s) (str s))

;; RT/print to *out*
(with-out-str (clojure.lang.RT/print :k *out*))

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
(expect-diff "DEVIATIONS 30: 1N is a long and 1M a double")
[(+ 1N 1) (* 2M 3M)]

;; comparison
[(= 1N 1N) (< 1N 2N) (zero? 0M)]

;; negatives
(expect-diff "DEVIATIONS 30: 1N is a long and 1M a double")
[(- 0 2N) -3.5M]

;; read-string too
(expect-diff "DEVIATIONS 30: 1N is a long and 1M a double")
(read-string "1N")

;; not every N is a suffix
(map str [(quote aN) (quote Nx) (quote x1N)])

;; Long.
(Long. 1)

;; String.
(String. "x")

;; Integer.
(Integer. 5)

;; Double.
(Double. 1.5)

;; Boolean.
(Boolean. true)

;; Character.
(Character. \a)

;; Long. parses
(Long. "12")

;; Double. parses
(Double. "1.5")

;; Boolean. parses
[(Boolean. "true") (Boolean. "no")]

;; a bad parse throws
(try (Long. "zz") :no (catch Throwable e :threw))

;; the box is the value
[(= (Long. 1) 1) (= (String. "x") "x")]

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
[(.isNaN ##NaN) (.isNaN 1.0) (.isInfinite ##Inf) (.isInfinite 1.0)]

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
;; map on the JVM and iterate in a different order: values, not text)
(with-out-str (clojure.pprint/pprint (vec (map #(apply str (repeat 8 (char (+ 97 %)))) (range 12)))))

(with-out-str (clojure.pprint/print-table [{:a 1 :b 2} {:a 3 :b 4}]))

;; reduce over a range, a vector and a list goes through the host's own
;; .reduce (IReduceInit), as LongRange.reduce and PersistentVector.reduce
;; do on the JVM; a reduced value stops it and is unwrapped
[(reduce + (range 100000)) (reduce + 5 (range 3)) (reduce + (range 0)) (reduce + [])
 (reduce + 1.5 (range 0.5 3)) (reduce + (range 10 0 -3)) (reduce conj [] (quote (1 2 3)))
 (reduce (fn [a x] (if (> x 3) (reduced a) (+ a x))) (range 10)) (reduce (fn [a x] (reduced :first)) 0 [1 2])
 (reduce max [3 9 2]) (reduce + (rest (range 5))) (reduce + (next (range 5)))]

[(instance? clojure.lang.IReduceInit (range 3)) (instance? clojure.lang.IReduceInit [1]) (instance? clojure.lang.IReduceInit (list 1))
 (instance? clojure.lang.IReduceInit (map inc [1])) (= (class (range 3)) clojure.lang.LongRange) (seq? (range 3)) (counted? [1])]

;; chunked seqs: a vector's seq and a range hand out chunks, map and
;; friends build ChunkedConses through a chunk buffer, as on the JVM
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
 (sequential? (seq (map inc [1 2]))) (seq? (seq (map inc [1 2]))) (= (class (seq (map inc (range 5)))) clojure.lang.ChunkedCons)]

;; the clock exists (ClojureScript has system-time)
(pos? (System/nanoTime))

(pos? (System/currentTimeMillis))

(number? (read-string (re-find #"[0-9.]+" (with-out-str (time nil)))))

;; futures and promises: core.clj's own definitions over the host's
;; tasks (tasks.inc); one OS thread, so a future runs until it blocks
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

(let [a (future (Thread/sleep 5) 1) b (future 2)] (+ @a @b))

(try @(future (throw (ex-info "x" {}))) (catch java.util.concurrent.ExecutionException e :ee))

(deref (future (Thread/sleep 200) 1) 1 :t)

(let [p (promise) f (future @p)] (deliver p :v) @f)

(let [p1 (promise) p2 (promise) f (future (deliver p2 (inc @p1)) :done)] (deliver p1 41) [@p2 @f])

(binding [*print-length* 3] @(future *print-length*))

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
;; in Clojure here too (clotran.rt), reached as the JVM members
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

(iterator-seq (.iterator (java.util.ArrayList. [1 2 3])))

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

(try (sorted-set 1 "a") (catch ClassCastException e :cce))

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

;; the errors arithmetic and compare raise carry the JVM's classes
(try (quot 9 0) (catch ArithmeticException e :arith))

(try (mod 9 0) (catch ArithmeticException e :arith))

(try (/ 1 0) (catch ArithmeticException e :arith))

(try (* Long/MAX_VALUE 2) (catch ArithmeticException e :arith))

(try (inc Long/MAX_VALUE) (catch ArithmeticException e :arith))

(try (compare #{1} #{2}) (catch ClassCastException e :cce))

(try (compare {} {}) (catch ClassCastException e :cce))

(try (sort [1 :a]) (catch ClassCastException e :cce))

(try (compare {:a 1} {:a 1}) (catch ClassCastException e :cce))

(try (- Long/MIN_VALUE) (catch ArithmeticException e :arith))

[(unchecked-add Long/MAX_VALUE 1) (unchecked-inc Long/MAX_VALUE) (unchecked-multiply Long/MAX_VALUE 2) (unchecked-dec Long/MIN_VALUE) (unchecked-subtract Long/MIN_VALUE 1)]

[(+ 1 2 3) (- 10 1 2) (* 2 3 4) (- 5) (inc 1) (dec 1) (+ 1.5 2) (* 2 1/3)]

;; the small members the language suite named: :keys! destructuring,
;; (Object.) as a sentinel, the bit tests, long-array and double-array
(let [o (Object.)] [(= o o) (= o (Object.)) (instance? Object o)])

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

(try (first 1) (catch IllegalArgumentException e :iae))

(try (next :k) (catch IllegalArgumentException e :iae))

(try (cons 1 2) (catch IllegalArgumentException e :iae))

(try (get-in {:a 1} 5) (catch IllegalArgumentException e :iae))

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
(try (pop #{1}) (catch ClassCastException e :cce))

(try (peek {:a 1}) (catch ClassCastException e :cce))

(try (pop []) (catch IllegalStateException e :ise))

(try (pop ()) (catch IllegalStateException e :ise))

(try (pop! (transient [])) (catch IllegalStateException e :ise))

[(pop [1 2]) (pop '(1 2)) (peek [1 2]) (peek '(1 2)) (peek []) (pop nil) (peek nil)]

(try (pop (seq [1 2])) (catch ClassCastException e :cce))

(try (conj "" \a) (catch ClassCastException e :cce))

(try (conj (into-array []) 1) (catch ClassCastException e :cce))

(try ([1 2] 7) (catch IndexOutOfBoundsException e :ioobe))

(try ([1 2] -1) (catch IndexOutOfBoundsException e :ioobe))

[({:a 1} :a) ({:a 1} :b 2) (#{:a} :a) ((transient #{:a}) :b 2) ({:a nil} :a 2)]

(try (< 1 "a") (catch ClassCastException e :cce))

(try (+ "ab" "cd") (catch ClassCastException e :cce))

(try (inc "a") (catch ClassCastException e :cce))

(try (max 1 "a") (catch ClassCastException e :cce))

(try (== 1 :a) (catch ClassCastException e :cce))

[(get #{:a} :b 1) (get (transient #{:a}) :b 1) ((transient #{:a}) :b 1)]

[(find [1 2] 0) (find [1 2] 5) (find {:a 1} :a)]

(try (sorted-set ()) (catch ClassCastException e :cce))

(try (sorted-set {}) (catch ClassCastException e :cce))

(try (sorted-map [1] 1 #{} 2) (catch ClassCastException e :cce))

(try (assoc (sorted-map) () 1) (catch ClassCastException e :cce))

(try (sorted-set-by < 1 "a") (catch Exception e :ex))

[(sorted-set nil) (sorted-set 1.5 1) (sorted-set "b" "a") (sorted-set [2] [1])]

;; \u escapes in strings, and a method called on nil is a
;; NullPointerException, which is how clojure.string's fns fail on nil
"Aé x"

(= "A" "A")

(do (require 'clojure.string) (try (clojure.string/upper-case nil) (catch NullPointerException e :npe)))

(do (require 'clojure.string) (try (clojure.string/reverse nil) (catch NullPointerException e :npe)))

(do (require 'clojure.string) (try (clojure.string/split nil #"-") (catch NullPointerException e :npe)))

(do (require 'clojure.string) (try (clojure.string/capitalize nil) (catch NullPointerException e :npe)))

(do (require 'clojure.string) (try (clojure.string/trim nil) (catch NullPointerException e :npe)))

(do (require 'clojure.string) (try (clojure.string/replace nil #"a" "b") (catch NullPointerException e :npe)))

(try (.toUpperCase nil) (catch NullPointerException e :npe))

(try (subs nil 0 1) (catch NullPointerException e :npe))

[@(future 1) (count (pmap inc [1 2 3])) (pos? (.availableProcessors (Runtime/getRuntime)))]

;; a host error is an exception with a message; a symbol is callable;
;; keyword arguments merge a trailing map; a keyword called with the
;; wrong count is an ArityException; and the small edges the suite named
(try (first 1) (catch RuntimeException e (boolean (.getMessage e))))

(try (get-in {:a 1} 5) (catch Exception e (boolean (re-find #"ISeq" (.getMessage e)))))

['b {'b 2}]

('b {'b 2})

('c {'b 2} :none)

(let [addn (fn [n & {:keys [a b] :or {a 0 b 0}}] (+ n a b))] [(addn 100 :a 1 {:b 2}) (addn 100 :a 1) (addn 100 {:a 5 :b 2})])

(try (:kw) (catch IllegalArgumentException e (.getMessage e)))

(try (apply :foo/bar (range 20)) (catch IllegalArgumentException e (.getMessage e)))

(try (apply :foo/bar (range 21)) (catch IllegalArgumentException e (.getMessage e)))

[(parse-long "9223372036854775807") (parse-long "-9223372036854775808") (parse-long "+42") (parse-long "x")]

(pr-str #'pr-str)

(ex-data (ex-info "message" nil))

(try (eval '(throw)) (catch RuntimeException e :rt))

(try (.jump "foo" 1) (catch Exception e (boolean (re-find #"No matching method.*taking 1 arg" (.getMessage e)))))

(reduce-kv + 10 [2 4 6])

(reduce-kv (fn [acc i x] (if (= i 1) (reduced acc) (+ acc x))) 0 [5 6 7])

[(= [1 2 3 4 5] (eduction (map inc) (range 5))) (= (eduction (map inc) []) []) (= [1] (eduction (map inc) [5]))]

[(clojure.math/floor-div Long/MIN_VALUE -1) (clojure.math/floor-div -7 2) (clojure.math/floor-div 7 -2)]

[(= ##Inf (clojure.math/ulp ##Inf)) (= Double/MIN_VALUE (clojure.math/ulp 0.0)) (clojure.math/ulp 1.0)]

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

(let [k (read-string "::s/x")] [(pr-str k) (namespace k) (= k :clojure.string/x) (try (read-string "::clojure.core/y") (catch Exception e :invalid))])

(try (read-string "::nope/x") (catch Exception e (boolean (re-find #"Invalid token" (.getMessage e)))))

(binding [*ns* (find-ns 'clojure.string)] (read-string "::q"))

(try (derive :user/a :user/b) (derive :user/b :user/a) (catch Exception e (.getMessage e)))

;; a namespace carries metadata
(do (alter-meta! *ns* assoc :k 1) [(:k (meta *ns*)) (instance? clojure.lang.IMeta *ns*)])

(do (def stub-me :orig) (let [p (promise)] (try (with-redefs [stub-me :temp] (deliver p stub-me) (throw (Exception. "x"))) (catch Exception e nil)) [@p stub-me]))

(let [m (into (sorted-map) '{1 a, 2 b, 3 c, 4 d})] [(reduce-kv str "" m) (reduce-kv (fn [acc k v] (reduced (+ acc k))) 0 m)])

[(instance? clojure.lang.IKVReduce {}) (instance? clojure.lang.IKVReduce []) (instance? clojure.lang.IKVReduce (sorted-map))]
