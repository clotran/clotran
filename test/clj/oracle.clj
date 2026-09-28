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

;; a seq has a type. clotran has ONE seq view where the JVM has
;; ChunkedSeq, StringSeq and the rest, so the name it answers is the
;; commonest of them.
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

;; Integer bounds
[Integer/MAX_VALUE Integer/MIN_VALUE]

;; Double bounds
(expect-diff "DEVIATIONS 27: the smallest subnormal prints 5.0E-324, Java prints 4.9E-324")
[Double/MAX_VALUE Double/MIN_VALUE]

;; Double exponents
[Double/MAX_EXPONENT Double/MIN_EXPONENT]

;; the non-finite constants
[(pr-str Double/POSITIVE_INFINITY) (pr-str Double/NEGATIVE_INFINITY) (pr-str ##NaN)]

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

(try @(future (throw (ex-info "x" {}))) (catch java.util.concurrent.ExecutionException e :ee))

(deref (future (reduce + (range 300000)) 1) 1 :t)

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

[@(future 1) (count (pmap inc [1 2 3]))]

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

;; a map entry keeps its type through seqs and find; conj and assoc on one make a vector
[(map-entry? (first {1 2})) (map-entry? [1 2]) (map-entry? (find {1 2} 1)) (map-entry? (find [5 6] 1)) (map-entry? (conj (first {1 2}) 3)) (map-entry? (assoc (first {1 2}) 0 9)) (vector? (first {1 2})) (map-entry? (first (seq (sorted-map 1 2)))) (map-entry? (first (rseq (sorted-map 1 2)))) (map-entry? (first (subseq (sorted-map 1 2) > 0))) (map-entry? (nth (seq {1 2 3 4}) 1)) (map-entry? (first (reduce conj [] {1 2}))) (map-entry? (first (into [] {1 2}))) (map-entry? (first (map identity {1 2}))) (map-entry? (first (vec {1 2}))) (map-entry? (clojure.lang.MapEntry/create 1 2)) (= [1 2] (first {1 2})) (key (first {1 2})) (val (clojure.lang.MapEntry/create 1 2))]

(require 'clojure.walk)

(let [f (fn [e] (if (and (vector? e) (not (map-entry? e))) (apply list e) e))] (clojure.walk/postwalk f [:html {:a ["b" 1]} ""]))

;; a keyword called with a default, on any collection
[(:b #{:a} 1) (:b (transient #{:a}) 1) (:a {:a nil} 1) (:b {:a 1} 1) (:b (transient {:a 1}) 1) (:a #{:a} 1)]

;; an error is an instance of its class, and of what catch would take it under
(let [e (try (/ 1 0) (catch Exception e e))] [(instance? ArithmeticException e) (instance? RuntimeException e) (instance? IllegalArgumentException e) (instance? Exception e) (instance? Throwable e) (instance? Object e)])

;; isAssignableFrom, and extend's refusal of a type that implements the protocol inline
(do (defprotocol PP (pp [x])) (deftype TT [] PP (pp [_] 1)) [(extends? PP TT) (satisfies? PP (TT.)) (try (extend TT PP {:pp (fn [_] 2)}) :extended (catch IllegalArgumentException e (boolean (re-find #"already directly implements" (.getMessage e)))))])

[(.isAssignableFrom Object String) (.isAssignableFrom clojure.lang.IPersistentVector clojure.lang.PersistentVector) (.isAssignableFrom String Object) (.isAssignableFrom clojure.lang.IPersistentMap clojure.lang.PersistentTreeMap) (.isAssignableFrom clojure.lang.IPersistentMap clojure.lang.PersistentVector) (.isAssignableFrom String String)]

;; the root of a Var under a binding: bindRoot, alter-var-root and def reach the root, the binding shows
(do (def ^:dynamic dv 1) [(binding [dv 2] (with-redefs [dv 3] [dv (.getRawRoot #'dv)])) dv (binding [dv 2] (alter-var-root #'dv inc) [dv (.getRawRoot #'dv)]) dv (binding [dv 5] (def dv 7) [dv (.getRawRoot #'dv)]) dv (binding [dv 8] (binding [dv 9] (with-redefs [dv 10] dv))) dv])

;; Long/valueOf with the wrong count fails in the Reflector's words
(try (eval '(Long/valueOf)) (catch Exception e (boolean (re-find #"No matching method.*taking 0 args" (.getMessage (or (.getCause e) e))))))

(try (eval '(Long/valueOf :a :b :c)) (catch Exception e (boolean (re-find #"No matching method.*taking 3 args" (.getMessage (or (.getCause e) e))))))

;; in-ns under a binding of *ns* changes the binding, not the root
(binding [*ns* *ns*] (in-ns 'oracle-tmp-ns) (def in-tmp 1) [(ns-name *ns*) (some? (ns-resolve 'oracle-tmp-ns 'in-tmp))])

(ns-name *ns*)

;; a qualified symbol is not a local
[(try (eval '(let* [a/x 1] x)) (catch Exception e :threw)) (try (eval '(loop* [a/x 1] x)) (catch Exception e :threw)) (let [/ 1] /)]

;; case keys its table with Util.hash, which is hashCode: 1 and
;; -9223372034707292159 collide and the condp under the key tells them apart
[(case 1 1 :long -9223372034707292159 :big :else) (case -9223372034707292159 1 :long -9223372034707292159 :big :else) (case 4294967297 4294967297 :big :else) (case 1 4294967297 :big 1 :one :else) (case "a" "a" :s :else) (case :k :k :kw :else) (case 7 (1 7) :either :else) (case 'x (x y) :sym :else) (case 3 (1 7) :either :else)]

;; a cause
(let [e (ex-info "outer" {:o 1} (ex-info "inner" {:i 2}))] [(ex-message (ex-cause e)) (ex-data (ex-cause e)) (ex-cause (ex-cause e)) (ex-message (.getCause e)) (ex-data e)])

(let [{:keys [cause via]} (Throwable->map (Exception. "I am not a number" (Exception. "double two")))] [cause (mapv :message via) (count via) (vector? via)])

(let [{:keys [cause via]} (Throwable->map (Exception. "alone"))] [cause (mapv :message via)])

;; a macro called with the wrong count says the count the caller wrote
(defmacro m0 [] 1)

(defmacro m1 [a] a)

[(try (macroexpand '(m0 1)) (catch clojure.lang.ArityException e (.getMessage e))) (try (macroexpand '(m1 1 2)) (catch clojure.lang.ArityException e (.getMessage e))) (macroexpand '(m1 5))]

;; a private Var is not reachable by its qualified name from another namespace; #'ns/x still is
(ns other-ns)

(def ^:private secret 1)

(in-ns 'user)

(try (eval 'other-ns/secret) (catch Exception e (boolean (re-find #"not public" (.getMessage (or (.getCause e) e))))))

@#'other-ns/secret

;; find-ns does not create, so the-ns and alias can refuse
[(find-ns 'nope-ns) (try (alias 'bogus 'epicfail) (catch Exception e (.getMessage e))) (some? (find-ns 'clojure.core))]

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

(try (remove-ns 'clojure.core) (catch IllegalArgumentException e (.getMessage e)))

;; seqable? is RT.canSeq
[(seqable? nil) (seqable? 1) (seqable? "s") (seqable? [1]) (seqable? {}) (seqable? #{}) (seqable? '(1)) (seqable? (range 3)) (seqable? (->Foo 1 2 3)) (seqable? (eduction (map inc) [1])) (seqable? :k) (seqable? 'x) (seqable? (fn []))]

;; multimethods dispatch with isa? over the hierarchy; preferences resolve what isa? cannot,
;; and two matches with no preference are the ambiguity error
(do (derive :user/rect :user/shape) nil)

(defmulti bar (fn [x y] [x y]))

(defmethod bar [:user/rect :user/shape] [x y] :rect-shape)

(defmethod bar [:user/shape :user/rect] [x y] :shape-rect)

[(try (bar :user/rect :user/rect) (catch IllegalArgumentException e (boolean (re-find #"Multiple methods in multimethod 'bar' match dispatch value" (.getMessage e))))) (prefers bar) (bar :user/rect :user/shape) (bar :user/shape :user/rect) (bar :user/rect :user/other)]

(do (prefer-method bar [:user/rect :user/shape] [:user/shape :user/rect]) nil)

[(bar :user/rect :user/rect) (prefers bar) (try (prefer-method bar [:user/shape :user/rect] [:user/rect :user/shape]) (catch IllegalStateException e (boolean (re-find #"Preference conflict" (.getMessage e)))))]

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

[(indirect-3 :child) (indirect-3 :parent-2) (try (indirect-3 :nobody) (catch IllegalArgumentException e (boolean (re-find #"No method in multimethod 'indirect-3' for dispatch value: :nobody" (.getMessage e)))))]

;; a method on an ancestor applies, the default when none does, and a later derive is seen
(defmulti area :shape)

(defmethod area :user/shape [s] :generic)

(defmethod area :default [s] :none)

[(area {:shape :user/rect}) (area {:shape :user/shape}) (area {:shape :user/other}) (do (derive :user/other :user/shape) (area {:shape :user/other})) (some? (get-method area :user/rect)) (some? (get-method area :user/nobody)) (= (get-method area :user/nobody) (get-method area :default))]

(defmulti simple1 identity)

(defmethod simple1 :a [x] :a)

[(count (methods simple1)) (do (remove-all-methods simple1) (count (methods simple1))) (prefers simple1) (try (simple1 :a) (catch IllegalArgumentException e :no-method))]

;; the class keywords are classes to isa?, and an interface has parents
[(class? (class {})) (class? :foo) (class? :user/rect) (isa? (class {}) clojure.lang.IPersistentMap) (isa? (class []) clojure.lang.IPersistentMap) (isa? (class "") Object) (contains? (supers clojure.lang.IPersistentVector) clojure.lang.IPersistentCollection) (isa? clojure.lang.IPersistentMap clojure.lang.IPersistentCollection) (isa? clojure.lang.IPersistentVector clojure.lang.Sequential)]

(binding [*print-dup* true] (pr-str [{:a 1} [1] '(1) #{1} "s" 1.5 \c :k 'sym nil true]))

;; syntax-quote leaves a dotted symbol as written -- a class name, as Compiler.resolveSymbol takes it
(let [x 1] [(pr-str `(clojure.core java.util.Map foo.bar/baz x)) (pr-str `clojure.string) (pr-str `String)])

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
(try (apply (fn [a b] [a b]) [1]) (catch clojure.lang.ArityException e :arity))
(try (apply (fn [a b & r] [a b]) [1]) (catch clojure.lang.ArityException e :arity))
(let [a (atom 0)] (apply (fn [x & r] x) (map (fn [i] (swap! a inc) i) (range 100))) @a)
(deref (future (apply (fn [x & r] (take 2 r)) (range))) 1000 :timeout)

;; strings are characters (DEVIATIONS 41): counted, indexed, sliced and
;; searched by code point, with the Character predicates ICU's
[(count "\u2002ab") (count "é") (.length "é") (subs "é" 0 1) (.charAt "\u2002x" 1) (int (.charAt "\u2002x" 0)) (int \u2002) (= "\u2002" (str \u2002)) (str \o101) (int \u00e9)]
[(clojure.string/triml "\u2002 \tbar") (clojure.string/trimr "bar\t \u2002") (clojure.string/trim "\u2000bar\t \u2002") (clojure.string/blank? "\u2002") (clojure.string/blank? "\u00a0")]
[(nth "aé" 1) (.indexOf "aéb" "b") (clojure.string/upper-case "éa") (clojure.string/lower-case "ÉA") (vec "aé") (seq "aé") (clojure.string/reverse "aé") (last "aé") (get "aé" 1) (contains? "aé" 1) (contains? "aé" 2) (clojure.string/capitalize "élan")]
[(Character/isWhitespace \u2002) (Character/isWhitespace \u00a0) (Character/isLetter \é) (Character/isLetter \u2002) (Character/toUpperCase \é) (Character/isLetter \A) (Character/isWhitespace \space) (Character/isWhitespace \a) (Character/toLowerCase \É)]
[(re-find #"é" "aéb") (clojure.string/index-of "aéb" "b") (.substring "aéb" 2) (re-seq #".\d" "é1x2") (clojure.string/replace "aéb" #"é" "E") (clojure.string/replace "aébé" "é" "<$0>") (clojure.string/last-index-of "éaéb" "é") (clojure.string/index-of "éaéb" "é" 1) (clojure.string/split "éaéb" #"é") (clojure.string/split "aébéc" #"")]
[(pr-str "é") (pr-str \é) (pr-str \u2002) (clojure.string/escape "aé" {\é "E"}) (.toUpperCase "é") (subs "aéb" 1) (subs "aéb" 1 2) (subs "aéb" 3) (try (subs "aéb" 4) (catch StringIndexOutOfBoundsException e :oob)) (try (subs "aéb" 2 1) (catch StringIndexOutOfBoundsException e :oob)) (.substring "aéb" 1 3) (map int "aé") (apply str (map char [233 65]))]
[(re-matches #".." "aé") (re-matches #".." "aéb") (let [m (re-matcher #"é" "aébé")] (re-find m) [(.start m) (.end m)]) (clojure.string/replace-first "aébé" #"é" "E") (clojure.string/split-lines "é\nb") (clojure.string/includes? "aéb" "é") (clojure.string/starts-with? "éa" "é") (clojure.string/ends-with? "aé" "é") (let [m (re-matcher #"é" "aébé")] (re-find m) (let [sb (StringBuffer.)] (.appendReplacement m sb "E") (.appendTail m sb) (str sb)))]
(expect-diff "DEVIATIONS 14: ICU's \\s is Unicode, java.util.regex's is ASCII")
(clojure.string/split "a\u2002b" #"\s")
(expect-diff "DEVIATIONS 14: ICU's \\w is Unicode, java.util.regex's is ASCII")
(re-find #"\w+" "héllo")
(expect-diff "DEVIATIONS 14: ICU's (?i) folds Unicode, java.util.regex's folds ASCII")
(re-find #"(?i)É" "xé")
(expect-diff "DEVIATIONS 41: a code point off the BMP is one character here, a surrogate pair there")
[(count "😀") (int (first "😀"))]

;; A lazy seq carried through a throw is still there in the handler:
;; raising an error must not force it (it would cache as empty).
(try (throw (ex-info "b" {:s (map inc [1 2 3])})) (catch Exception e (vec (:s (ex-data e)))))
(let [l (lazy-seq (cons 1 (lazy-seq (cons 2 nil))))] [(try (throw (ex-info "b" {:s l})) (catch Exception e (vec (:s (ex-data e))))) (vec l)])
(try (throw (ex-info "b" {:s (filter odd? (range 6))})) (catch Exception e (count (:s (ex-data e)))))
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
(try (eval '(fn "a" a)) (catch Exception e [(instance? Exception e) (.getMessage (.getCause e)) (map (juxt :path :pred) (:clojure.spec.alpha/problems (ex-data (.getCause e))))]))
(try (eval '(let [:a 1] a)) (catch Exception e (.getMessage (.getCause e))))
(try (eval '(let [a/x 1, [y] [1]] x)) (catch Exception e (.getMessage (.getCause e))))
(try (eval '(let [[:a] [1]] a)) (catch Exception e (.getMessage (.getCause e))))
(try (eval '(defn)) (catch Exception e (.getMessage (.getCause e))))
(try (eval '(ns foo.bar (:require [clojure.string :as]))) (catch Exception e (.getMessage (.getCause e))))
[(instance? clojure.lang.IObj (reify)) (meta (with-meta (reify) {:a 1})) (isa? (class (reify)) Object) (ifn? #{1}) (ifn? {}) (ifn? []) (ifn? :a) (ifn? 'a) (ifn? #'first) (ifn? 1) (fn? #{1}) (fn? first) (#(identity {:a % :b #{%}}) 1) (map-entry? (clojure.lang.MapEntry. 1 2)) (key (clojure.lang.MapEntry. 1 2)) (string? (str (java.util.UUID/randomUUID))) (= (java.util.UUID/randomUUID) (java.util.UUID/randomUUID))]

;; BigInt: 1N is its own type, exact at any size, and `+'` promotes
;; into it (DEVIATIONS 26, 30)
[(pr-str 1N) (str 1N) (pr-str [1N]) (= 1N 1) (== 1N 1) (= 1N 1.0) (== 1N 1.0) (= (hash 1N) (hash 1)) (pr-str -42N) (pr-str 0N)]
[(+ 1N 1) (- 1N 2N) (* 99999999999999999999N 99999999999999999999N) (+ 1N 1.5) (* 1N 0) (- 1N) (+ 1N 1N) (- 1N 1N)]
[(< 1N 2) (> 2N 1) (zero? 0N) (pos? 1N) (neg? -1N) (max 1N 2) (min 1N 2) (compare 1N 2) (compare 2N 1) (compare 1N 1) (< 9223372036854775807N 9223372036854775808N)]
[(integer? 1N) (int? 1N) (number? 1N) (rational? 1N) (decimal? 1N) (float? 1N) (ratio? 1N) (even? 2N) (odd? 3N) (even? 10000000000000000000N)]
[(+' 1 1) (+' 9223372036854775807 1) (*' 4611686018427387904 4) (inc' 9223372036854775807) (dec' -9223372036854775808) (-' 1 2) (reduce *' 1 (range 1 26))]
[(bigint 1) (bigint "12") (bigint 5/2) (bigint 1N) (bigint 12345678901234567890) (long 1N) (double 1N) (int 5N) (str 1N)]
[(quot 10N 3) (rem 10N 3) (mod -7N 3) (quot -10N 3) (rem -10N 3) (quot 18446744073709551616N 4) (rem 18446744073709551616N 7)]
[(/ 1N 3) (/ 4N 2) (/ 10N 4) (* 2N 1/2) (+ 1/2 1N) (- 1N 1/2) (try (/ 1N 0) (catch ArithmeticException e :divide-by-zero))]
[(pr-str 12345678901234567890) (read-string "42N") (apply + [1N 2N]) (reduce + 0N [1N 2N]) (sort [2 1N 3N]) (vec (repeat 2 1N)) (pr-str {1N 2N})]
(let [m (into {} (map vector (range 40) (range 40)))] [(get m 1N) (contains? #{1N} 1) (count (set [1 1N])) (= {1N :a} {1 :a})])
(loop [i 0 acc 1N] (if (< i 25) (recur (inc i) (* acc (inc i))) acc))
(expect-diff "DEVIATIONS 26: a Ratio's parts are 64-bit, so a BigInt remainder has nowhere to go")
(try (/ 99999999999999999999N 7) (catch ArithmeticException e :no-big-ratio))
(expect-diff "DEVIATIONS 30: one big integer type, so biginteger answers a BigInt and prints 1N")
(pr-str (biginteger 1))
[(nth [10 20 30] 1N) (get [10 20 30] 1N) (subs "abcd" 1N 3N) (take 2N [1 2 3 4]) (repeat 2N :x) (nthrest [1 2 3] 1N) (abs -123N) (abs 5N) (= (range 1N 4N) (range 1 4))]
[(try (bit-and 3N 1) (catch IllegalArgumentException e :not-supported)) (try (bit-shift-left 1N 2) (catch IllegalArgumentException e :not-supported)) (bit-and 3 1)]

;; a class is a value of its own, named and printed as the JVM names it
[(class 1) (class "a") (class []) (class {}) (class :k) (class nil) (class (class 1)) (pr-str (class 1)) (str (class 1)) (class? (class 1)) (keyword? (class 1))]
[(= (class 1) Long) (= (class "a") String) (identical? (class 1) (class 1)) (instance? Long 1) (instance? Object 1) (instance? CharSequence "a") (isa? (class 1) Object) (isa? Long Number)]
[(resolve 'String) (resolve 'clojure.lang.PersistentVector) (resolve 'NonExistentClass.Name) (resolve 'NonExistentClass.) (pr-str {(class 1) :a}) (get {(class 1) :a} Long) (class (class Long))]
(expect-diff "DEVIATIONS 34: supers is the short chain clotran models, not the JVM's two dozen")
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
(try (/ 1M 3) (catch ArithmeticException e :non-terminating))
(try (even? 2M) (catch IllegalArgumentException e :not-an-integer))
[(sorted-set 0M) (sorted-set 1M 1M) (sorted-set 1N 2N) (sorted-set 1 1.5M 2N) (sorted-map 1M :a) (pr-str (sort [2M 1M 1.5M])) (pr-str (sort [2N 1N 3]))]
[(bound? (var map)) (.isBound (var map)) (bound? (var map) (var inc))]

;; with-precision, which the derived suite cannot see: `with-precision`
;; is not in cljs.core, so the clojure/cljs intersection leaves it out
;; and these are the only tests it has (DEVIATIONS 30, 43)
[(with-precision 4 (+ 3.5555555M 1)) (with-precision 6 (+ 3.5555555M 1)) (with-precision 2 (* 1.11M 2)) (with-precision 10 (/ 1M 3)) (with-precision 5 (* 1.23456M 1M)) (with-precision 3 (/ 2M 3)) (with-precision 1 (+ 999.9M 0))]
[(with-precision 6 :rounding CEILING (+ 3.5555555M 1)) (with-precision 6 :rounding FLOOR (+ 3.5555555M 1)) (with-precision 6 :rounding HALF_UP (+ 3.5555555M 1)) (with-precision 6 :rounding HALF_DOWN (+ 3.5555555M 1)) (with-precision 6 :rounding HALF_EVEN (+ 3.5555555M 1)) (with-precision 6 :rounding UP (+ 3.5555555M 1)) (with-precision 6 :rounding DOWN (+ 3.5555555M 1)) (with-precision 6 :rounding UNNECESSARY (+ 3.5555M 1))]
[(with-precision 6 :rounding CEILING (- 0M 3.5555555M)) (with-precision 6 :rounding FLOOR (- 0M 3.5555555M)) (with-precision 1 :rounding HALF_EVEN (+ 2.5M 0)) (with-precision 1 :rounding HALF_EVEN (+ 3.5M 0)) (with-precision 1 :rounding HALF_DOWN (+ 2.5M 0))]
[(with-precision 10 (/ 1M 8)) (with-precision 10 (/ 100M 4)) (with-precision 34 (/ 1M 2))]
(try (with-precision 3 :rounding UNNECESSARY (+ 3.5555M 1)) (catch ArithmeticException e (.getMessage e)))
(binding [*math-context* (java.math.MathContext. 8)] (+ 3.55555555555555M 1))
(binding [*math-context* nil] (try (/ 1M 3) (catch ArithmeticException e (.getMessage e))))

;; and the default that makes clotran answer where Clojure raises
(expect-diff "DEVIATIONS 43: *math-context* is decimal128 here, so a decimal division answers instead of throwing")
(try (/ 1M 3) (catch ArithmeticException e :throws))
(expect-diff "DEVIATIONS 43: *math-context* has a value here and is nil in Clojure")
(pr-str *math-context*)

;; THE INTERSECTION, name by name. scripts/derive-tests filters Clojure's
;; own deftests; it never enumerated the intersection itself, so a name
;; Rich only exercises from a JVM-shaped test had nothing testing it
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
[((memoize inc) 1) (munge "a-b") (doto [1] count) (locking (Object.) 42) (symbol? (gensym)) (let [a (atom 1)] (reset-meta! a {:b 2}) (meta a)) (munge "a-b?") (munge 'a*b)]
[(with-out-str (pr 1 2)) (println-str 1) (prn-str 1) (with-out-str (flush)) (<= 0.0 (rand) 1.0) (<= 0 (rand-int 5) 4) (count (random-sample 1.0 [1 2 3]))]
[(let [a (atom 0) seen (atom nil)] (add-watch a :k (fn [k r o n] (reset! seen n))) (reset! a 5) (remove-watch a :k) (reset! a 9) [@seen @a])]
[(let [f (fn [x] x)] [(add-tap f) (tap> :hello) (remove-tap f)])]
[(re-pattern "a+") (str (re-pattern "a+")) (vec (re-seq (re-pattern "a+") "aa b aaa"))]
[(vector? (destructure '[[a b] [1 2]])) (reduced? (ensure-reduced 1)) (unreduced (reduced 1)) (unreduced 1)]
(expect-diff "DEVIATIONS 11: a transient IS the persistent collection, so assoc! does not mutate in place")
[(let [t (transient [1 2])] (assoc! t 0 9) (persistent! t)) (let [t (transient {:a 1})] (dissoc! t :a) (persistent! t))]
[(do (defprotocol OP (om [x])) (extend-type String OP (om [_] :s)) (extend-protocol OP Long (om [_] :l)) [(om "x") (om 1)])]
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
 (let [f inc] ((:a (meta ^{:a f} [1])) 5)) (meta [1]) (:tag (meta ^String [1]))]

(require 'clojure.edn)
[(clojure.edn/read-string "{:a [1 2] :b #{3}}")
 (clojure.edn/read-string "(1 2 3)")
 (clojure.edn/read-string {:readers {'x (fn [v] [:tagged v])}} "#x 5")
 (clojure.edn/read-string {:default (fn [t v] [t v])} "#unknown 5")
 (clojure.edn/read-string nil)
 (clojure.edn/read-string "nil")
 (try (clojure.edn/read-string "#unknown 5") (catch Throwable e (.getMessage e)))]
[(clojure.edn/read-string {:readers {'a (fn [v] {:a v}) 'b (fn [v] [:b v])}} "#a #b 1")
 (clojure.edn/read-string {:readers {'t (fn [v] (count v))}} "[#t [1 2] #t {:x 1}]")
 (clojure.edn/read-string {:readers {'t (fn [v] (count v))}} "#{#t [1 2]}")
 (clojure.edn/read-string {:readers {'t (fn [v] (count v))}} "(#t [1 2 3])")
 (clojure.edn/read-string "1/2") (clojure.edn/read-string "3.5M")
 (clojure.edn/read-string "7N") (clojure.edn/read-string ":a/b")
 (clojure.edn/read-string "\"a\nb\"")]
(expect-diff "DEVIATIONS 12: java.util.UUID is not a type here, so a uuid IS its text -- the same answer parse-uuid gives")
[(clojure.edn/read-string "#uuid \"00000000-0000-0000-0000-000000000000\"")]

;;; Type hints change behaviour, not only speed. A ^long or ^double
;;; parameter or return converts by RT.longCast/doubleCast after a
;;; checkCast to Number (Compiler.emitUnboxArg); an array hint is a
;;; checkcast where the value is USED as an array, so an unused or
;;; counted parameter never notices. Compared by exception class.
(defn hint-t [f] (try (let [v (f)] [v (.getSimpleName (class v))])
                      (catch Throwable e [:threw (.getSimpleName (class e))])))
[(long 1.9) (long -1.9) (long 7/2) (long \a) (double 3) (double 1/4)
 (unchecked-long 1.9) (unchecked-long 1e30) (unchecked-long -1e30) (unchecked-long ##NaN)
 (hint-t #(long "x")) (hint-t #(long nil)) (hint-t #(long 1e30)) (hint-t #(double "x")) (hint-t #(double nil))]
[(hint-t #((fn [^long n] n) 1.5)) (hint-t #((fn [^double x] x) 2)) (hint-t #((fn [^long n] n) 7/2))
 (hint-t #((fn [^long n] n) \a)) (hint-t #((fn [^long n] n) "x")) (hint-t #((fn [^long n] n) nil))
 (hint-t #((fn ^long [x] x) 1.5)) (hint-t #((fn ^double [x] x) 2))
 (hint-t #((fn ([^long n] n) ([^long n m] m)) 1.5)) (hint-t #(((fn [^long n] (fn [] n)) 2.5)))
 (hint-t #((fn [^String s ^long n] [s n]) "x" 1.5))]
[(hint-t #((fn [^doubles a] :ok) [1 2])) (hint-t #((fn [^doubles a] (aget a 0)) [1 2]))
 (hint-t #((fn [^doubles a] (alength a)) [1 2])) (hint-t #((fn [^doubles a] (aset a 0 1.0)) [1 2]))
 (hint-t #((fn [^longs a] (aget a 0)) (double-array [1.5]))) (hint-t #((fn [^doubles a] (aget a 0)) (long-array [3])))
 (hint-t #((fn [^doubles a] (aget a 0)) nil)) (hint-t #((fn [^ints a] (aget a 0)) (long-array [3])))
 (hint-t #((fn [^objects a] (aget a 0)) (long-array [3]))) (hint-t #(let [^doubles a [1 2]] (aget a 0)))
 (hint-t #((fn [^doubles a] (let [a [1]] (nth a 0))) (double-array 1)))
 (hint-t #((fn [^doubles a] (aget a 0)) (double-array [2.5])))]
(expect-diff "DEVIATIONS 48: recur to a ^long local with a double is a compile error on the JVM, a conversion here")
[(hint-t #((fn [^long n acc] (if (< n 1) acc (recur (- n 0.5) (conj acc n)))) 2 []))]
(expect-diff "DEVIATIONS 48: a primitive hint on a let local is an UnsupportedOperationException on the JVM")
[(hint-t #(let [^long x 1.5] x))]
(expect-diff "DEVIATIONS 48: aset on a ^doubles array with a long finds no method on the JVM")
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

;;; Arithmetic errors say what the JVM says. Long overflow is
;;; Math.addExact's "long overflow" on every path (Numbers.java); an index
;;; out of range is ArrayIndexOutOfBoundsException naming both numbers --
;;; for a slice of a multi-dimensional array too, which once answered nil.
(defn msg-of [f] (try (f) :no-throw (catch Throwable e [(.getSimpleName (class e)) (.getMessage e)])))
[(msg-of #(+ Long/MAX_VALUE 1)) (msg-of #(* Long/MAX_VALUE 2)) (msg-of #(inc Long/MAX_VALUE))
 (msg-of #(dec Long/MIN_VALUE)) (msg-of #(- Long/MIN_VALUE)) (msg-of #(int 3000000000))
 (msg-of #(aget (long-array [5 6]) 2)) (msg-of #(aget (double-array [1.0]) -1))
 (msg-of #(aset (long-array [5 6]) 2 1)) (msg-of #(long 1.0E30))
 (let [f (fn [a b] (quot a b))] (msg-of #(f 7 0))) (let [f (fn [a b] (mod a b))] (msg-of #(f 7 0)))]
(expect-diff "DEVIATIONS 51: literal longs compile to the JVM's primitive quot, whose zero divisor is Java's \"/ by zero\"")
[(msg-of #(quot 7 0)) (msg-of #(rem 7 0))]
[(msg-of #(subs "ab" 0 3)) (msg-of #(subs "ab" 3)) (msg-of #(subs "ab" 1 0)) (msg-of #(subs "héllo" 1 3))]

;;; Arrays: an array is an instance of its array class, and a negative
;;; size is Java's NegativeArraySizeException naming the size.
[(instance? (class (double-array 0)) (double-array 2)) (instance? (class (long-array 0)) (long-array 1))
 (msg-of #(double-array -1)) (msg-of #(long-array -3))]

;;; An array's class is the JVM's name for it, one per element type and
;;; rank, and prints as Clojure prints it (it was one class, and printing
;;; it crashed).
[(map #(str (class %)) [(double-array 1) (long-array 1) (int-array 1) (float-array 1) (boolean-array 1) (object-array 1) (make-array Integer/TYPE 2 3)])
 (pr-str (class (double-array 1))) (pr-str (class (make-array Integer/TYPE 2 3))) (pr-str (class (object-array 1)))
 (instance? (class (double-array 0)) (double-array 2)) (instance? (class (long-array 0)) (double-array 2))
 (.isArray (class (long-array 1))) (= (class (double-array 1)) (class (double-array 5)))]
(expect-diff "DEVIATIONS 45: short, byte and char arrays have their storage kind's class")
[(map #(str (class %)) [(short-array 1) (byte-array 1) (char-array 1)]) (bytes? (byte-array 1))]

;;; Runtime.availableProcessors is the machine's, as the JVM's is
;;; (sysconf through Threads.f90); pmap's look-ahead is sized by it.
[(.availableProcessors (Runtime/getRuntime))]

;; protocol dispatch picks the implementation Clojure picks: a chunked
;; seq reduces through InternalReduce's IChunkedSeq implementation
(let [p clojure.core.protocols/InternalReduce, ic (get (:impls p) clojure.lang.IChunkedSeq)]
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
[(instance? clojure.lang.IEditableCollection []) (class (transient [])) (instance? clojure.lang.ITransientVector (transient []))]

(persistent! (reduce conj! (transient []) (range 70)))

(let [v (vec (range 40)) t (transient v)] (conj! t :a) (assoc! t 0 :z 41 :end) [(persistent! t) v])

(let [t (transient [1 2 3])] [(count t) (nth t 1) (get t 5 :nf) (nth t 9 :d) (count (pop! t)) (persistent! (pop! (pop! t)))])

(try (let [t (transient [1])] (persistent! t) (conj! t 2)) (catch Throwable e [(.getName (class e)) (.getMessage e)]))

(try (pop! (transient [])) (catch Throwable e [(.getName (class e)) (.getMessage e)]))

(try (assoc! (transient [1]) :k 2) (catch Throwable e [(.getName (class e)) (.getMessage e)]))

[(into [] (map inc (range 5))) (into [1 2] [3 4]) (into (vec (range 100)) [:x]) (= (into [] (range 5000)) (range 5000))]

[(mapv inc (range 40)) (filterv even? (range 20)) (meta (into (with-meta [1] {:m 1}) [2]))]

(let [v (persistent! (reduce conj! (transient []) (range 1100)))] [(count v) (nth v 0) (nth v 1023) (nth v 1024) (nth v 1099) (count (conj v :n)) (peek (pop v))])

(let [m (zipmap (range 3000) (range 3000))] [(reduce + (map val m)) (count (seq m)) (every? map-entry? m) (= (set (keys m)) (set (range 3000))) (count (rest (seq m)))])

(let [s (set (range 2000))] [(reduce + (seq s)) (count (rest (seq s))) (count (next (next (seq s))))])

[(seq "héllo") (count (seq (apply str (repeat 3000 "é")))) (nth (seq "abç") 2) (rest "ab") (map int "aé") (seq "") (first "ç") (reduce str (seq "xyz"))]

(count (doall (for [i (range 5000)] (re-find (re-pattern (str "b \\+ " i "\\b")) (str "b + " (* 2 i))))))

(let [tv (transient [1 2 3])] [(get tv 0) (get tv 4 :foo) (contains? tv 0) (contains? tv 3) (find tv 0) (find tv -1) (counted? tv) (empty? tv) (empty? (transient [])) (instance? clojure.lang.Indexed tv)])

[(/ 3/4 5) (/ 3/4 1/5) (/ 5 3/4) (/ 3/4 5.0) (/ 1 3/4) (/ 1/2 1/2) (* 8 1/2) (+ 1/2 1/2) (- 3/2 1/2) (* 0 1/2) (/ 2 1/2) (/ 4 2) (rem 1 1/2) (quot -7/2 2)]

[(conj (range 3) 9) (conj (concat [1 2] [3 4]) 5) (conj (map inc [1 2]) 0) (list? (conj '(1 2) 0)) (apply map * [[1 2] [1 2] [1 2] [1 2]]) (apply interleave [[:a :b] [1 2] ["x" "y"]])]

[(nth [nil] 0 :d) (nth nil 5 :d) (nth nil 5) (nth '(1 nil) 1 :d) (nth [1] 5 :d)]

(try (nth [1 2] 5) (catch IndexOutOfBoundsException e :oob))

(try (nth (range 3) 5) (catch IndexOutOfBoundsException e :oob))

(try (nth {:a 1} 0) (catch UnsupportedOperationException e :unsupported))

[(conj {} (seq {:a 1 :b 2})) (conj {} (first {:z 9})) (conj {} nil) (conj {} ()) (into {} [[:a 1] (first {:b 2})])]

(try (conj {} [:a 1 :b]) (catch IllegalArgumentException e :iae))

(try (conj {:a 1} '(:b 2)) (catch ClassCastException e :cce))

(try (into {} ['(:a "a")]) (catch ClassCastException e :cce))

[(int \a) (byte \a) (pos? 1N) (neg? -1.5M) (zero? 0/1)]

(try (zero? nil) (catch NullPointerException e :npe))

(try (pos? {}) (catch ClassCastException e :cce))

(try (int "1") (catch ClassCastException e :cce))

(try (unchecked-int "1") (catch ClassCastException e :cce))

[(let [k (keyword "a" "b/c")] [k (namespace k) (name k) (= k :a/b/c)]) (let [s (symbol "a" "b/c")] [s (namespace s) (name s)]) (symbol :a/b) (symbol :dog) (keyword nil "x") (symbol nil "x")]

(try (keyword 'user "abc") (catch ClassCastException e :cce))

(try (name 2) (catch ClassCastException e :cce))

(try (namespace "a/b") (catch ClassCastException e :cce))

[(compare "abc" "abf") (compare "ab" "abcd") (compare "ab" (str "ab" (char 1))) (compare "é" "e") (compare :a/b :b) (compare :z/a :a/z) (compare (quote a/b) (quote a/c)) (sort ["b" "ab" "a"])]

[(realized? (lazy-seq [1])) (realized? (delay 1)) (realized? (iterate inc 1))]

(try (realized? [1]) (catch ClassCastException e :cce))

(try (realized? (range 5)) (catch ClassCastException e :cce))

(try (merge-with + 1 {:a 1}) (catch IllegalArgumentException e :iae))

(try (hash-map :a) (catch IllegalArgumentException e :iae))

(try (sorted-map :a) (catch IllegalArgumentException e :iae))

(try (subseq [1 2 3 4] > 2) (catch ClassCastException e :cce))

(try (create-ns "my-ns") (catch ClassCastException e :cce))

(try (count 1) (catch UnsupportedOperationException e :uoe))

(try (contains? 1 :a) (catch IllegalArgumentException e :iae))

[(count nil) (contains? nil :a) (contains? (to-array [1 2]) 1) (get 1 :a :d) (System/getenv "")]

(let [xs (map #(mod (* % 7919) 10007) (range 3000)) s (into (sorted-set) xs) s2 (reduce disj s (range 0 10007 3))] [(count s) (first s) (last s) (take 5 (rseq s)) (nth (seq s) 1234) (count s2) (take 5 s2) (take 5 (rseq s2)) (subseq s >= 100 < 110) (rsubseq s > 100 <= 110) (count (reduce disj s xs))])

(let [m (into (sorted-map) (map (fn [x] [x (* x x)]) (range 2000)))] [(get m 500) (find m 42) (take 3 (subseq m > 1990)) (take 3 (rsubseq m < 10)) (count (reduce dissoc m (range 0 2000 2))) (first (into (sorted-map-by >) m))])

[(get (sorted-map nil 1) nil) (contains? (sorted-map nil 1) nil) (find (sorted-map nil 1) nil) (sorted-map nil 1 0 2) (dissoc (sorted-map 1 1 2 2) 3) (assoc (sorted-map 1 1) 1 2)]

(mapv hash [nil true 0 1 -1 42 9223372036854775807 1.5 -0.0 ##NaN 1/2 -3/4 1N 100000000000000000000N 1.50M 100M 0M \a "" "a" "héllo" "日本" :a :a/b 'x 'ns/x [] [1 2] '(1 2) () {} {:a 1} #{} #{1 2 3} (first {:a 1})])

[(seq #{7 6 5}) (seq (set (range 10))) (keys (zipmap (range 12) (range 12))) (seq (hash-map :a 1 :b 2 :c 3)) (seq #{:a :b :c :d}) (vec (set ["x" "y" "z" "w"])) (= (hash (zipmap (range 20) (range 20))) (hash (into {} (map vector (range 20) (range 20)))))]

[(boolean (re-find #"#object\[clojure.lang.Reduced 0x[0-9a-f]+ \{:status :ready, :val 1\}\]" (pr-str (reduced 1)))) (class (reduced 1)) (map? (reduced 1)) (pr-str (tagged-literal 'js [1 2])) (class (ref 1)) (class (agent 1)) (instance? clojure.lang.Atom (ref 1)) (list? (cons 1 '(2))) (list? (cons 1 nil)) (list? (conj '(2) 1)) (class (cons 1 '(2)))]

(with-local-vars [w 0 z 5] (dotimes [_ 3] (var-set w (inc @w))) [@w @z])

(do (defmacro oracle-locals [] (vec (sort (map str (keys &env))))) [(let [x 1 y 2] (oracle-locals)) ((fn [a] (let [b 2] (oracle-locals))) 1)])

(try ({:a 1}) (catch clojure.lang.ArityException e :arity))

(try ([1] 0 1) (catch clojure.lang.ArityException e :arity))

(try (transient '(1 2)) (catch ClassCastException e :cce))

[(unchecked-int 1e10) (unchecked-int -1e10) (unchecked-long 1e30) (unchecked-byte 1e10) (quote @x) (quote ~x) (quote ~@x) (ns-unmap *ns* 'oracle-nope)]

(let [calls (atom [])] (sorted-map-by (fn [a b] (swap! calls conj [a b]) (compare a b)) "a" 1 "b" 2) @calls)

(do (spit "/tmp/clotran-oracle-io.txt" "hello\nworld\n") (spit "/tmp/clotran-oracle-io.txt" "more" :append true) [(slurp "/tmp/clotran-oracle-io.txt") (with-open [r (clojure.java.io/reader "/tmp/clotran-oracle-io.txt")] (vec (line-seq r)))])

(try (require 'oracle.no-such-lib) (catch java.io.IOException e :io))

(do (def oracle-v 1) (set-validator! #'oracle-v (fn [x] (< x 3))) (alter-var-root #'oracle-v inc) (try (alter-var-root #'oracle-v inc) (catch IllegalStateException e [:invalid oracle-v])))

[(keys (seq {:a 1 :b 2})) (vals (take 1 {:a 1})) (keys ())]
