;; Host-level checks with core.clj loaded, run by `make test`.
;;
;; What is here is what real Clojure CANNOT answer: Fortran arrays,
;; `clotran-type`, and blocks that mix setup with assertions. Everything
;; real Clojure can answer lives in oracle.clj, where `clj` supplies the
;; expected value (scripts/oracle) and nothing is typed in by hand --
;; because 14 of the 477 hand-typed expectations that used to live here
;; turned out to be clotran's answer, not Clojure's. Before adding a
;; check here, ask whether it belongs in oracle.clj instead.
;;
;; The contract with the Makefile is the last line: this prints
;; LANGUAGE TESTS PASSED only when nothing failed, and `make test`
;; greps for it. A crash part-way through therefore fails the gate too,
;; which is the point -- a missing marker is a failure, not a pass.

(def ^:dynamic *failures* (atom 0))

(defn check [label got want]
  (if (= got want)
    (println "ok   -" label)
    (do (swap! *failures* inc)
        (println "FAIL -" label "got" (pr-str got) "want" (pr-str want)))))

;;; ---- the break protocol -------------------------------------------
;;
;; A break is the paused state as DATA: why, where, and one frame per
;; call still pending, each with its locals BY NAME. Host check: real
;; Clojure has no clotran-break, and the frame names are ours.

(defn brk-inner [a b] (let [sum (+ a b) label "mid"] (clotran-break)))
(defn brk-outer [coll] (let [n (count coll)] (brk-inner n 41)))
(def brk (brk-outer [1 2 3]))

(check "a break says why" (:reason brk) :break)
(check "a break has a frame per call" (count (:frames brk)) 2)
(check "the innermost call is first" (:fn (first (:frames brk))) "user/brk-inner")
(check "its caller is under it" (:fn (second (:frames brk))) "user/brk-outer")
;; Where each is: the call it is waiting on -- (clotran-break) on line
;; 30 and (brk-inner n 41) on line 31 of this file -- not its body.
(check "a frame is where its pending call is" (map (juxt :line :col) (:frames brk)) [[30 54] [31 46]])
;; A step stops at a fn's entry, before any call is pending: that
;; frame is where its body begins, the (let ...) at column 23.
(def brk-entry (atom nil))
(binding [*clotran-break-handler* (fn [b] (case (:reason b)
                                            :step (do (reset! brk-entry b) :continue)
                                            :break (if @brk-entry :continue :step-in)))]
  ((fn [] (clotran-break) (brk-inner 1 2))))
(check "a frame just entered is where its body begins" (map (juxt :fn :line :col) (take 1 (:frames @brk-entry)))
       [["user/brk-inner" 30 23]])
;; One frame serves every arity of a fn, so the other arities' slots
;; exist and read nil; they are not this frame's locals.
(defn brk-arity ([a] (clotran-break)) ([a b] (clotran-break)))
(check "a frame reports its own arity's locals" (:env (first (:frames (brk-arity 1)))) (quote {a 1}))
(check "and the other arity its own" (:env (first (:frames (brk-arity 1 2)))) (quote {a 1, b 2}))
(def brk-cap (let [k :kept] (fn ([a] (clotran-break)) ([a b] (clotran-break k)))))
(check "a capture is every arity's local" (:env (first (:frames (brk-cap 1)))) (quote {a 1, k :kept}))
;; a call in tail position keeps ITS OWN frame -- Clojure eliminates no
;; tail call, and a caller's locals are what a break is for
(check "a frame names its locals" (contains? (:env (first (:frames brk))) (quote sum)) true)
(check "and carries their values" (get (:env (first (:frames brk))) (quote sum)) 44)
(check "a string local too" (get (:env (first (:frames brk))) (quote label)) "mid")
;; a local ALREADY READ for the last time reads nil: the frame really
;; has dropped it, which is what the clearing pass is for and what
;; CLOTRAN_KEEP_LOCALS=1 turns off for a debugging run
(check "the caller's locals are named" (contains? (:env (second (:frames brk))) (quote n)) true)
(check "...and a cleared one reads nil" (get (:env (second (:frames brk))) (quote n)) nil)
(check "a frame knows its line" (number? (:line (first (:frames brk)))) true)
(check "and its file" (string? (:file (first (:frames brk)))) true)

;; an error takes one too, once capture is on
(defn brk-boom [x] (let [doubled (* x 2)] (.nosuchmember doubled)))
(clotran-break-on! true)
(def brk-caught (try (brk-boom 21) (catch clotran.host.throwable t :caught)))
(def brk-err (clotran-last-break))
(clotran-break-on! false)

(check "the error was still caught" brk-caught :caught)
(check "an error breaks too" (:reason brk-err) :error)
(check "with the message" (string? (:message brk-err)) true)
(check "and the failing frame" (:fn (first (:frames brk-err))) "user/brk-boom")
(check "with its locals named" (contains? (:env (first (:frames brk-err))) (quote doubled)) true)

;; The resuming half. A handler Var gets the state and answers a
;; command, and the command is what the break is worth. Host check: the
;; Var, the commands and the frame names are all ours.
(check "without a handler the state itself is the answer" (:reason (brk-outer [1])) :break)
(check "a handler's {:continue v} is the break's value"
       (binding [*clotran-break-handler* (fn [b] {:continue (count (:frames b))})] (brk-outer [1 2 3]))
       2)
(check ":continue alone is nil"
       (binding [*clotran-break-handler* (fn [b] :continue)] (brk-outer [1])) nil)
(check ":abort throws at the break"
       (binding [*clotran-break-handler* (fn [b] :abort)]
         (try (brk-outer [1]) (catch clotran.host.throwable t (re-find #"aborted at break" (str t)))))
       "aborted at break")
(check "a handler that throws, throws at the break"
       (binding [*clotran-break-handler* (fn [b] (throw (ex-info "from the handler" {:k 1})))]
         (try (brk-outer [1]) (catch clotran.host.throwable t (:k (ex-data t)))))
       1)
(check "a break inside the handler is only a snapshot"
       (binding [*clotran-break-handler* (fn [b] {:continue (:reason ((fn [] (clotran-break))))})] (brk-outer [1]))
       :break)

;; Stepping counts CALLS, the events this executor has. From a stop: in
;; = the next call anywhere; over = the next call this frame's fn or
;; its callers make, so it walks this body without descending; out =
;; the next call once this frame has returned. The handler answers each
;; stop from a queue and records what it saw.
(defn st-leaf [x] (inc x))
(defn st-mid [x] (st-leaf (st-leaf x)))
(defn st-top [] (clotran-break) (st-mid 1) (st-leaf 5))
(defn st-run [cmds]
  (let [seen (atom []) q (atom cmds)]
    (binding [*clotran-break-handler*
              (fn [b] (swap! seen conj [(:reason b) (:fn (first (:frames b))) (get (:env (first (:frames b))) 'x)])
                (let [c (first @q)] (swap! q rest) (or c :continue)))]
      (st-top))
    @seen))
(check ":step-in stops at every call, the callee on top with its argument"
       (st-run [:step-in :step-in :step-in :step-in])
       [[:break "user/st-top" nil] [:step "user/st-mid" 1] [:step "user/st-leaf" 1]
        [:step "user/st-leaf" 2] [:step "user/st-leaf" 5]])
(check ":step-over at st-mid's entry walks st-mid's own calls"
       (st-run [:step-in :step-over])
       [[:break "user/st-top" nil] [:step "user/st-mid" 1] [:step "user/st-leaf" 1]])
(check ":step-out at st-mid's entry stops at st-top's next call"
       (st-run [:step-in :step-out])
       [[:break "user/st-top" nil] [:step "user/st-mid" 1] [:step "user/st-leaf" 5]])
(def st-stray (atom nil))
(binding [*clotran-break-handler* (fn [b] :step-in)] ((fn [] (clotran-break))))
(binding [*clotran-break-handler* (fn [b] (reset! st-stray (:reason b)) :continue)] (st-leaf 1))
(check "a step the form did not reach does not wait for the next form" @st-stray nil)

;; An error break: the throw is in progress, every command lets it go
;; on, and a step asked for there is dropped -- it would otherwise fire
;; at the binding's own pop-thread-bindings call.
(def eb-seen (atom nil))
(clotran-break-on! true)
(def eb-result (binding [*clotran-break-handler* (fn [b] (reset! eb-seen [(:reason b) (:fn (first (:frames b)))]) :step-in)]
                 (try (brk-boom 21) (catch clotran.host.throwable t :caught))))
(clotran-break-on! false)
(check "an error break reaches the handler" @eb-seen [:error "user/brk-boom"])
(check "and the error still goes on to its catch" eb-result :caught)

;;; ---- reader conditionals ------------------------------------------

;; The feature is :cljf. A branch nobody selects is read and dropped, so
;; the :cljs one may hold #js. This file is .clj and the conditional is
;; still read: clotran reads #? in every file (DEVIATIONS 33).

(check "reader conditional" #?(:clj :clj-side :cljs #js {} :cljf :fortran) :fortran)
(check "reader conditional splice" [1 #?@(:cljf [2 3]) 4] [1 2 3 4])
#?(:cljs (this-form-is-never-read))

;;; ---- deftype ----------------------------------------------------

(deftype Point [x y]
  clotran.host.value
  (toString [this] (str "Point(" x "," y ")")))

(def p (->Point 3 4))

;; A deftype is NOT a map, and must not pretend to be one.

;;; ---- reify ------------------------------------------------------

;; The example from reify's own docstring.

;;; ---- protocols on a deftype -------------------------------------

(defprotocol Shape
  (area [s])
  (scale [s k]))

(deftype Rect [w h]
  Shape
  (area [_] (* w h))
  (scale [_ k] (Rect. (* w k) (* h k))))

(def r (->Rect 2 5))


;;; ---- letfn ------------------------------------------------------


;;; ---- defrecord --------------------------------------------------
;;
;; Each of these answered a WRONG value rather than failing, before the
;; generic operations learned to ask an instance for its own method.

(defrecord P [a b])

(def rec (->P 1 2))


;;; ---- identical? -------------------------------------------------
;;
;; Reference identity, NOT =. Sharing the = builtin made the first of
;; these true, and made a record's equiv call itself until the stack
;; ran out.


;;; ---- symbol / keyword names -------------------------------------


;;; ---- namespaces as strings --------------------------------------
;;
;; Namespace.toString is its NAME, which is what namespace-munge reads
;; and therefore what deftype builds a class name out of. Nested, it
;; keeps the print form instead, because a collection's toString prints
;; its elements.


;;; ---- sequential equality ----------------------------------------
;;
;; A lazy seq is Sequential, so it is equal to a vector of the same
;; elements. This walks element at a time rather than counting
;; first, which is what both Clojure (ASeq.equiv) and ClojureScript
;; (equiv-sequential) do, and is why the infinite cases below
;; terminate instead of realising forever.

;; Not Sequential, so not equal however the elements line up.
;; Metadata is invisible to equality, as it is in Clojure.
;; INFINITE on one side, and these must RETURN. They do because the
;; count shortcut is taken only when both sides are counted.

;;; ---- require :refer ----------------------------------------------
;;
;; `require` silently ignored :refer. load-lib guards the call with
;; (when (or use (:refer filter-opts)) ...), and filter-opts comes
;; from select-keys, which ends (with-meta ret (meta map)) -- so the
;; keyword was looked up in the metadata WRAPPER and answered nil.
;; Whole test files then died on (deftest ...) having interned
;; nothing.

(require (quote [clojure.string :refer [join]]))
(require (quote [clojure.string :refer :all]))
(require (quote [clojure.set :as st]))

;; Set equality: other must be a set, same count, every element
;; contained. A set used to fall past that to reference equality, so
;; two literals spelled the same way were not equal.
;; A collection as an ELEMENT used to match by identity, so this was
;; false. It is structural now -- see the collections-as-keys section
;; below, which is where the rest of that case lives.
;; The underlying bug, directly.

;;; ---- the core.clj tail -------------------------------------------
;;
;; None of these existed while core.clj stopped at form 708. They are
;; the last sixteen forms, and the nil-on-bad-input cases matter:
;; parse-long is written as (try (Long/valueOf s) (catch
;; NumberFormatException _ nil)), so it depends on the exception
;; having a TYPE a catch clause can name.

;; A delay runs its body ONCE, on the first deref.

;;; ---- native arrays ------------------------------------------------
;;
;; A REAL Fortran array: contiguous, column-major, declared kind, at an
;; address the collector never moves -- the one thing this host has
;; that clj does not, and the reason the collector is non-moving.
;;
;; In a `fortran` namespace rather than clojure.core, because these are
;; not Clojure's array functions with a different implementation: they
;; take a Fortran KIND NAME rather than a class. SEAMS.md asked for
;; fortran.* to mean exactly this.

(alias 'f 'fortran)

(def arr (f/make-array "real8" 3))
(check "array kind"    (f/array-kind arr) "real8")
(check "array length"  (f/alength arr) 3)
(check "array shape"   (f/array-shape arr) [3])
;; Zero-filled, not whatever the allocator left behind.
(check "fresh array is zeroed" (f/aget arr 1) 0.0)
(do (f/aset arr 0 1.5) (f/aset arr 2 3.25))
(check "aset then aget" [(f/aget arr 0) (f/aget arr 2)] [1.5 3.25])

;; Rank is not special-cased: subscripts are per DIMENSION and the
;; flattening is column-major, done in one place.
(def m2 (f/make-array "int4" 2 3))
(check "rank-2 shape"  (f/array-shape m2) [2 3])
;; alength is the OUTER length, not the element count: clj says
;; (alength (make-array Integer/TYPE 2 3)) is 2, because a clj [[I
;; is an array of 2 rows. Ours is one rank-2 block, so the same
;; answer comes from the first extent.
(check "rank-2 length" (f/alength m2) 2)
(do (f/aset m2 1 2 7))
(check "rank-2 aset/aget" [(f/aget m2 1 2) (f/aget m2 0 0)] [7 0])

;; Loud, not silent, on the two ways to get it wrong.
(check "out of bounds" (try (f/aget arr 9) (catch clotran.host.throwable e :err)) :err)
(check "unknown kind"  (try (f/make-array "nope" 2) (catch clotran.host.throwable e :err)) :err)

;; A `value` array holds clotran values, so its storage is a GC run
;; rather than a raw buffer -- otherwise the collector would free its
;; elements out from under it.
(def va (f/make-array "value" 2))
(do (f/aset va 0 :hello))
(check "value array" [(f/aget va 0) (f/aget va 1)] [:hello nil])

;;; ---- numeric literals --------------------------------------------
;;
;; Clojure's reader has three patterns (LispReader 70-74) and
;; clotran had only "all digits" and "digits with a dot". Every value
;; below is what `clj` printed for the same literal. The two that were
;; SILENTLY WRONG rather than merely unsupported are 077, which read as
;; 77, and .5, which read as 0.5 instead of interning a symbol.
;;
;; The literals that must be REFUSED live in test/f/reader_test.f90:
;; a reader error aborts this whole file, so they cannot be asserted
;; here.

;; floatPat needs a digit BEFORE the dot, so this is a name.

;; A number Clojure reads that clotran has no TYPE for must NOT be a
;; reader error. It was, briefly, and the cost was out of all
;; proportion: clotran aborts a whole file on a reader error, so one
;; 2/3 took every form after it down, across the 12 of Clojure's 67
;; test namespaces that contain a ratio literal -- 766 passing
;; assertions became 223, control.clj alone losing 153.
;;
;; These two used to assert that 42N and 1.5M read as SYMBOLS,
;; which is what clotran did and what stood as the falsification.
;; They are numbers now -- see the N and M suffixes further down --
;; so what is left to guard is only that neither RAISES, since a
;; reader error here stops this whole file loading and takes the
;; gate red.

;;; ---- arithmetic ---------------------------------------------------
;;
;; Every expected value here is what `clj` printed for the same form.
;; The bugs these caught were not subtle: +, -, * and quot/rem all read
;; the integer field only, so a real operand contributed ZERO --
;; (* 2.0 3) answered 0, (quot 7.0 2) answered 0. `/` and inc/dec were
;; always right, which is what made it look fine in passing.
;;
;; The lesson for the next function: test VALUES against clj, not just
;; that a form is accepted. The reader work before this checked 29
;; literals and never once checked that arithmetic on them was right.

;; Contagion: one double makes the whole result a double.
;; One argument goes through (cast Number x), a host member that was
;; missing entirely -- (+ 1.5) failed with "no such member".

;; / is the one that already handled reals. (/ 1 0) throws but
;; (/ 1.0 0) is ##Inf -- they are not the same rule.
;; quot and rem DO throw on a zero divisor, doubles included.

;; = is Object.equals, == is numeric VALUE. They disagree here, and
;; clotran answered = for both.

;;; ---- struct maps ---------------------------------------------------
;;
;; A struct map IS a map. PersistentStructMap in clj is a storage
;; optimisation -- one shared key basis plus a flat value array, so N
;; instances do not each carry their keys -- and nothing about its
;; behaviour differs. So clotran's structs are its maps, and the basis
;; is a vector of the keys.
;;
;; This is not a curiosity: clojure/pprint.clj uses defstruct, and
;; clojure.test-clojure.reflect does (:use clojure.pprint), so without
;; it neither loads. Every value below is what `clj` printed.

(defstruct point :x :y)
;; An unsupplied basis key is PRESENT and nil, not absent.
;; ...and a key outside the basis is allowed.

;; Keyword-argument destructuring reaches two host members nothing else
;; did -- PersistentArrayMap/EMPTY and createAsIfByAssoc. EMPTY was
;; missing outright; createAsIfByAssoc was wired to hash-map, which
;; takes its keys and values as separate arguments where this takes one
;; collection of them, so it made a map OF the collection.

;;; ---- print-method finds its host type ------------------------------
;;
;; Three tables have to spell a type the same way: type_name, which
;; names the value; host_super, which maps that name to the host
;; classes a method may be registered on; and the class literal in
;; (defmethod print-method C ...), which is the key the method lands
;; under. Where they disagreed, print-method found nothing, fell to
;; :default, and reached print-simple -- which does not quote.
;;
;; Two disagreements, both one word:
;;   OBJ_SEQ had NO name at all and answered "object"
;;   host_super said "lazy" where type_name says "lazy-seq"
;;   host_super said "clotran.host.char" but a class literal
;;     strips that prefix, so the method key is :Character
;;
;; Nothing about the printer itself was wrong, which is why the values
;; were right the whole time and only the display was not.

;; A seq view now has a type at all. The NAME is clotran's own --
;; clj answers clotran.host.persistent_vector_chunked_seq here, since
;; clotran's classes are its tags -- but it has to be the name
;; is_instance already expected, or the two disagree about one value.

;; Characters: the method that knows \\newline never ran, so a
;; newline character printed as an actual newline.
;; str is the unreadable one, and still is.

;;; ---- sort, and compare underneath it ------------------------------
;;
;; `sort` is (let [a (to-array coll)] (. clotran.host.arrays (sort a cmp))
;; (seq a)) -- so it needed four things clotran did not have: a real
;; mutable array from to-array, arrays that seq, Arrays/sort itself,
;; and a `compare` that works on more than numbers.
;;
;; That last one mattered most: compare answered 0 for anything
;; non-numeric, so (sort ["b" "a"]) would have come back in its
;; original order and reported no error at all.
;;
;; Compared as VALUES rather than printed text: a seq of strings still
;; prints unreadably, which is a separate print-method bug.

;; A vector compares by COUNT first, then element by element.

;; A comparator that answers a BOOLEAN is a predicate -- AFunction
;; treats true as "less" -- which is what makes (sort > coll) work.
;; Clojure promises stability: equal elements keep their order.
;; Big enough to exercise the merge rather than the base case.
;; Built with (range) descending rather than (reverse ...): an
;; earlier test in this file does (require [clojure.string :refer
;; :all]), which shadows core reverse with the StringBuilder one.

;; to-array now answers a REAL array, and an array seqs as its
;; elements -- both needed by sort, and both wrong before.

;;; ---- collections as keys -------------------------------------------
;;
;; A collection used to hash and compare by its POOL SLOT, so an equal
;; key built somewhere else missed. `=` was structural all along, which
;; is what made it confusing: the value compared equal and the lookup
;; still failed.
;;
;; Hash and equality have to agree exactly -- a structural hash with an
;; identity equality puts one key in a trie twice -- so both are
;; installed together through gc_set_coll_ops, against deep_equal,
;; which is the equality `=` already used.

;; Entry order must not matter: two equal maps may hand back their
;; entries differently, so their hash is a sum rather than a fold.
;; A list and a vector of the same elements are equal, so they must
;; hash alike and be interchangeable as keys.
;; case* buckets by hash, so it was failing for the same reason.
;; ...and things that are NOT equal must still miss.

;;; ---- 64-bit integers -----------------------------------------------
;;
;; Clojure's default integer is `long`, and clotran's was Fortran's
;; default `integer` -- 32 bits. A literal past 2^31 was truncated on
;; the way in and nothing said so: 9999999999 read back as 1410065407,
;; and 2147483648 as -2147483648. The real beside it in gc_value had
;; been widened to real(8) years earlier on exactly this argument.
;;
;; Width has to hold all the way through: the literal is accumulated
;; digit by digit in the reader, stored in the value, and summed in
;; the accumulator. A 32-bit link anywhere truncates, so each of these
;; exercises a different one.

;; The radix forms share the reader's accumulator.
;; Equal values must still hash equal now that the hash folds 64 bits
;; into 32 -- a map keyed on a large integer finds it again.
;; case* buckets integer keys by a 32-bit hash, and ival_of still
;; narrows to build it. That is safe only because the bucket is
;; followed by a real equality check -- these pair each value with the
;; 32-bit truncation it used to collapse to, so a narrowing that
;; reached the comparison would pick the wrong branch.

;;; ---- ratios --------------------------------------------------------
;;
;; Exact rational arithmetic -- the thing (/ 1 3) needs to stop being
;; 0.3333333333. Every value below is what `clj` printed.
;;
;; A ratio is an IMMEDIATE here: numerator in the int field,
;; denominator in the field a heap reference would use, so it costs no
;; allocation and the collector never sees one. It is always in normal
;; form, which is what lets equality compare the two fields directly.

;; Normalized on construction: reduced, sign on the numerator, and
;; never denominator 1 -- Clojure collapses that to an integer.

;; Contagion is double > ratio > integer.

;; = is by type, == is by value -- and 2/1 never exists to be compared.


;; Everything else that takes a number has to know about the third
;; kind too. Each of these was wrong once: inc/dec dropped a ratio to
;; a double, quot/rem read it as its numerator alone, and int handed
;; it straight back unconverted.

;;; ---- Clojure's OWN array API ------------------------------------
;;
;; Not f/make-array: clojure.core's make-array/aget/aset/alength,
;; running unmodified over the Fortran backing. They are written
;; against clotran.host.array and clotran.host.rt, so making
;; those work is what lets core.clj's array code run rather than be
;; shadowed. Every expected value below is what `clj` printed for
;; the same forms.
;;
;; aset-int, not aset: on a primitive array clj's Array/set
;; refuses a boxed Long, so real Clojure throws here too.

(def cm (make-array clotran.host.int4/TYPE 2 3))
(do (aset-int cm 0 0 10) (aset-int cm 0 1 11) (aset-int cm 0 2 12)
    (aset-int cm 1 0 20) (aset-int cm 1 1 21) (aset-int cm 1 2 22))
;; The OUTER length -- 2 rows -- not 6 elements.

;; core.clj's aget is ([array idx & idxs] (apply aget (aget array idx) idxs)),
;; so (aget cm 0) MUST hand back something that is itself an array.
(def crow (aget cm 0))
;; and it is a VIEW, not a copy -- writing through it is visible in
;; the parent. This is the assertion that fails if slices ever start
;; copying.
(do (aset-int crow 1 999))

;; aclone takes the shape of the VIEW, not of the buffer behind it,
;; and shares nothing with it afterwards.
(def cclone (aclone crow))
(do (aset-int cclone 0 -1))

;; An Object array is the `value` kind: it holds clotran values, so
;; plain aset works and a fresh slot reads nil, not 0.
(def cobj (make-array clotran.host.value 2))
(do (aset cobj 0 :hello))

(def cdbl (make-array clotran.host.real8/TYPE 2))
(do (aset-double cdbl 1 2.5))

;;; ---- printing a function -----------------------------------------
;;
;; (prn (fn [x] x)) used to SEGFAULT. print-method's :default is
;;   (if (instance? IObj o) (print-method (vary-meta o ...) w)
;;                          (print-simple o w))
;; and clotran claimed a closure was IObj while having no
;; print-method dispatch could reach -- so :default called itself on
;; the same object until the stack ran out. DEVIATIONS 23.

;; A vector really does hold anything, which is the thing that
;; turned this up.
;; with-meta on a function still works -- it does not consult the
;; instance? answer that changed.


;;; ---- macroexpand-1 and special-symbol? ---------------------------
;; Compiler.macroexpand1 is ONE step and does not descend, which is
;; what makes it different from the analysis pass clotran already
;; had. Every expectation below was run through `clj` first.

;; macroexpand loops to a fixed point but still does not descend --
;; the inner `when` survives.

;; Clojure's list, 24 entries -- not clotran's own special forms.


;;; ---- #_ discard ------------------------------------------------
;; #_ is a kind of WHITESPACE, not a form that reads as nothing --
;; which only shows at the end of a collection, where there is no
;; following form to pair it with. Values checked against `clj`.



;;; ---- the quote is not a delimiter --------------------------------
;; isTerminatingMacro excludes #, % and ' -- so a prime suffix is part
;; of the name, the way ss' and x' are written in Clojure's own suite.



;;; ---- reader metadata --------------------------------------------
;; Checked against `clj` by KEY, not by whole map: Clojure's reader
;; also attaches :line and :column, which clotran does not track.

;; A VECTOR is metadata too -- ^[long] is 1.12's param-tags.
(check "^[long] is param-tags"  (:param-tags (meta (quote ^[long] (x)))) '[long])


;;; ---- empty ------------------------------------------------------
;; core.clj's `empty` is (.empty coll) behind an instance? guard, so
;; the answer keeps the collection's CATEGORY and a non-collection
;; answers nil rather than erroring. All checked against `clj`.



;;; ---- swap-vals!, reset-vals!, and the multimethod table ----------
;; All of these are core.clj reaching for a host member it declares in
;; its own type hints. Values from `clj`.


(defmulti ltest-area :shape)
(defmethod ltest-area :square [s] (* (:side s) (:side s)))
(defmethod ltest-area :circle [s] 3)
(defmethod ltest-area :default [s] :none)

;; get-method answers what WOULD apply, so an unregistered value finds
;; the default rather than nil.
;; preferMethod records nothing here (DEVIATIONS 8), so the table is
;; empty rather than absent.


;;; ---- clotran.host.math ---------------------------------------------
;; clojure/math.clj is a thin wrapper over clotran.host.math, so the whole
;; namespace rests on these. Every expectation below is `clj`'s answer,
;; bit for bit -- the awkward ones (ulp, next-up, IEEE-remainder,
;; get-exponent) come out of Fortran's spacing/nearest/exponent
;; intrinsics rather than a libm binding.
;;
;; Math permits up to 1 ulp of error, and exp is where clotran and the
;; clj use it: (m/exp 1) differs in the last bit. Nothing here asserts
;; on that one.

(require (quote clojure.math))



;; rint rounds HALF TO EVEN, which neither truncation nor
;; round-half-away gives.

;; expm1 and log1p keep their digits near zero, where exp(x)-1 would
;; lose all of them.

;; The *Exact family throws where ordinary arithmetic wraps.
;; Floor division, not truncation.

;; Math/abs is overloaded in clj: a long stays a long.


;;; ---- format -----------------------------------------------------
;; core.clj's `format` is (String/format fmt (to-array args)), so this
;; is clotran.host.formatter -- the subset Clojure's own source and suite
;; actually write. Every line checked against `clj`.

;; %b is false only for nil and false -- 0 is true.
;; String.valueOf(null) is "null", not Clojure's nil.
;; core_print's own use of it.


;;; ---- range over more than longs ---------------------------------
;; core.clj picks between LongRange/create and Range/create on
;; (int? x); clotran has one builtin behind both, and it used to read
;; the integer field regardless -- so every bound of a double range
;; read as 0 and it yielded zeros forever. Values from `clj`.

;; A ratio step stays exact rather than becoming a double.


;;; ---- long lazy sequences ----------------------------------------
;; These are GC tests wearing Clojure clothes. Each of them realises
;; far more cells than the heap holds at once, so the collector runs
;; many times mid-walk; every one of them answered a SMALLER, WRONG
;; number before the roots in range_cell, iterate_cell and the static
;; call path were fixed.
;;
;; 8000 is chosen, not more: it is past the point where the first
;; failure appeared (about 5800), and these are a GATE -- the whole
;; file runs under both compilers on every commit, and clotran walks
;; a lazy cell in milliseconds, not microseconds. A bigger number
;; would buy no more confidence and cost minutes.



;;; ---- printing doubles -------------------------------------------
;; Double.toString: the SHORTEST decimal that reads back as the same
;; double, plain while 1e-3 <= |d| < 1e7 and scientific outside that.
;; The old printer wrote ten fixed decimals, so 0.479425538604203 came
;; out as 0.4794255386 -- a different double -- and Double/MAX_VALUE
;; overran the buffer outright. Every line below is `clj`'s output.

;; The round trip is the point: these need all their digits.
;; The plain/scientific boundary is 1e-3 and 1e7, not Fortran's.

;;; ---- read-string ------------------------------------------------
;; (RT/readString s) reads ONE form and ignores what follows.


;;; ---- the boxed number classes -----------------------------------
;; Long/MAX_VALUE and its neighbours, and Double.compare -- the TOTAL
;; order, which ranks -0.0 below 0.0 and NaN above everything, neither
;; of which < can say. Values from `clj`.

;; NaN is greater than everything, and equal to itself.


;;; ---- clojure.string's host members -------------------------------
;; clojure.string is written entirely against clj's regex's
;; Pattern and Matcher plus StringBuilder, so none of split, replace
;; or reverse worked without them. Every expectation is `clj`'s.

(require (quote [clojure.string :as ltstr]))

;; A positive limit caps the parts and the last keeps the rest unsplit.
;; No limit drops trailing empties; -1 keeps them.


;; $1 and $2 name groups -- the one place a replacement is not literal.


;;; ---- a delay that threw -----------------------------------------
;; Delay.deref catches the throwable, drops the thunk and rethrows the
;; SAME object on every later deref -- so the body runs once whether it
;; returned or threw. Values from `clj`.

(let [n (atom 0)
      d (delay (swap! n inc) (throw (clotran.host.exception. "broken")))
      tc (fn [] (try @d (catch clotran.host.exception e e)))
      r1 (tc)]
  (check "a delay's exception is an exception" (instance? clotran.host.exception r1) true)
  (check "the same exception comes back"       (identical? r1 (tc)) true)
  (check "the body ran once"                   @n 1)
  (check "the message survives"                (.getMessage r1) "broken")
  (check "a thrown delay is realized"          (realized? d) true))
(let [ok (delay 42)]
  (check "an ordinary delay"  [@ok @ok (realized? ok)] [42 42 true]))


;;; ---- (var x) resolves where the code was written -----------------
;; resolve_var reads the defining namespace out of the enclosing
;; frame, and the `var` special form was handing it the FORM instead --
;; so a (binding [x ...]) inside one namespace, called from another,
;; looked x up in the CALLER's namespace and failed. clojure.test's own
;; (binding [*report-counters* ...]) is exactly that, which is why
;; run-tests reported nothing from a foreign namespace.

(ns lt.other)
(def ^:dynamic *lt-counter* :unbound)
(defn lt-with [f] (binding [*lt-counter* 7] (f)))
(defn lt-peek [] *lt-counter*)
(in-ns 'user)



;;; ---- a set answers a lookup --------------------------------------
;; A set's contents live one slot down, and get/keyword lookup never
;; unwrapped them -- so (get #{:at} :at) and (:at #{:at}) both answered
;; nil where Clojure answers :at. cl_format.clj asks exactly that of
;; its allowed-flags set for every directive it compiles, so every flag
;; looked illegal and clojure.pprint would not load at all.


;;; ---- indexOf takes a character CODE ------------------------------
;; String.indexOf is overloaded on (int ch) as well as (String), and
;; cl_format.clj writes (.indexOf s (int \~)) to find its directives.
;; Searching for the TEXT "126" never found one, so every format string
;; compiled to itself and cl-format returned the format unchanged.



;;; ---- arrays, and the exceptions that ask for one -----------------
;; .getStackTrace answered an empty VECTOR, and Throwable->map asks
;; (alength st) straight after -- so every printed exception, and every
;; thrown-with-cause-msg? in Clojure's suite, died on "alength: not an
;; array" rather than on anything real. There is no stack trace to
;; report here; there is an empty array.

;; The component type is read and discarded -- there are no primitive
;; component types here (DEVIATIONS 24).

;;; ---- ExceptionInfo -----------------------------------------------
;; It does not end in "Exception", so it was not recognised as a
;; throwable class at all -- and a catch naming it in full could not
;; match a throw that named it short.



;;; ---- proxy -------------------------------------------------------
;; `proxy` is a MACRO in Clojure, in core_proxy.clj, which is not
;; vendored -- it is written against the class loader. clojure.pprint's
;; writers are proxies, so without it the pretty printer cannot exist.
;; Here it is a special form built on reify's machinery, with the two
;; differences proxy has: `this` is implicit, and arities nest inside
;; one method form.
;;
;; Only the first three are `clj`'s answers. The rest declare methods
;; the superclass does not, which real Clojure REJECTS -- there is no
;; class to check against here, so clotran accepts them. DEVIATIONS 28.


;; Several arities inside ONE method form, which reify writes as
;; several forms.
;; `this` is bound without being named.

;;; ---- `..` is a macro, not a member access ------------------------
;; Clojure never has to say so: Compiler.macroexpand1 asks isMacro
;; before it reaches the dot sugar, and `..` is a macro. clotran asks
;; the other way round -- equivalent for every other name, since .foo
;; is never a macro, and wrong for exactly this one, where
;; (.. a getClass isArray) read as the member "." on a.



;;; ---- a vector is associative by index ----------------------------
;; All four of these came out of one namespace, clojure.data, which is
;; written entirely against them: assoc on a vector answered NIL,
;; get and contains? by index answered nothing, and conj of nil onto a
;; map added a nil entry. Values from `clj`.

;; An index equal to the count APPENDS -- the one place assoc grows a
;; vector. Past that it throws.

;; .contains on a String is still substring containment -- the two
;; methods share a name and the argument tells them apart.

;; APersistentMap.cons walks (seq o), and the seq of nil is nil, so a
;; map comes back unchanged. (merge m nil) is (conj m nil).

;;; ---- protocols see the host supertypes ---------------------------
;; core.clj's `supers` is built from .getInterfaces, and answering an
;; empty one sent EVERY protocol dispatch to its (impl Object)
;; fallback. clojure.data's equality-partition called a map an :atom
;; even though clotran.host.map was in the impls map all along.

(require (quote [clojure.data :as ltdata]))



;;; ---- a bad arity is an ArityException -----------------------------
;; clotran said "no matching arity" through its internal error map,
;; which no (catch SomeClass e) could match and which did not say how
;; many arguments arrived or to whom. Clojure's wording, class and
;; catchability, all checked against `clj`.

(defn ltf0 [] 0)
(defn ltf1 [a] a)
(defn ltfm ([a] 1) ([a b] 2))

;; ArityException extends IllegalArgumentException, which Clojure's own
;; suite relies on.


;;; ---- agents, validators and latches ------------------------------
;; core.clj's `agent` sets an error mode on its very first line, so
;; nothing about agents worked at all. An action runs on the agent's
;; own thread (DEVIATIONS 29 resolved), so a check waits with `await`,
;; or polls agent-error where the agent is about to fail: await on a
;; failed agent is Clojure's error, and so is the send await-for makes
;; when the action has already failed -- which it had, under the gate's
;; load. Values from `clj`. These live here and

(defn- wait-fail [a] (loop [i 0] (when (and (nil? (agent-error a)) (< i 300)) (clotran.host.thread/sleep 10) (recur (inc i)))))
;; not in oracle.clj because a `send` keeps clj's agent pool alive and
;; scripts/oracle would never see clj exit.

(let [a (agent 1)]
  (check "a new agent fails by default" (error-mode a) :fail)
  (send a inc) (await a)
  (check "send"                @a 2)
  (send a + 10) (await a)
  (check "send with arguments" @a 12)
  (send a (fn [x & ys] (apply + x ys)) 1 2 3) (await a)
  (check "send with several"   @a 18))

(let [b (agent 1)]
  (send b (fn [x] (throw (clotran.host.exception. "boom"))))
  (wait-fail b)
  (check "a failed agent keeps its value" @b 1)
  (check "and records the error"          (.getMessage (agent-error b)) "boom")
  (check "and refuses more work"
         (try (send b inc) :no (catch clotran.host.throwable e :refused)) :refused)
  (restart-agent b 5)
  (check "restart clears it"   [@b (agent-error b)] [5 nil])
  (send b inc) (await b)
  (check "and it works again"  @b 6))

;; An error handler makes the default mode :continue, so the agent
;; carries on as if nothing happened.
(let [c (agent 1 :error-handler (fn [ag e] nil))]
  (check "a handler means continue" (error-mode c) :continue)
  (send c (fn [x] (throw (clotran.host.exception. "oops"))))
  (send c inc) (await c)
  (check "a continuing agent is not failed" (agent-error c) nil)
  (check "and takes more work"      @c 2))

(let [d (agent 0 :error-mode :continue)]
  (send d (fn [_] (throw (ex-info "boom" {}))))
  (send d + 5) (await d)
  (check ":error-mode :continue skips the failure" [@d (agent-error d)] [5 nil]))

;; Actions run in send order, one at a time, and watches see each one
;; -- Agent.doRun notifies them whether or not the state changed, so
;; await's own latch action fires them too, but only after the latch
;; has let await return, so the two we can count on are the first two.
(let [e (agent 0) seen (atom [])]
  (add-watch e :w (fn [_ _ o n] (swap! seen conj n)))
  (send e inc) (send e + 10) (await e)
  (check "watches fire per action, in order" [@e (subvec @seen 0 2)] [11 [1 11]]))

(let [g (agent [])]
  (dotimes [i 20] (send g conj i))
  (await g)
  (check "twenty sends land in order" @g (vec (range 20))))

;; Agent.dispatchAction: a send made INSIDE an action is held until the
;; action ends -- released when it succeeds, dropped when it throws --
;; and one made inside a transaction is held until the commit and
;; dropped by an abort. An error handler's own sends go out at once.
;; Values from clj -M on the same forms, with (shutdown-agents) after.
(let [a (agent 0) b (agent 0)]
  (send a (fn [x] (send b inc) (throw (ex-info "x" {}))))
  (wait-fail a) (clotran.host.thread/sleep 100)
  (check "a send from an action that throws is dropped" [@b (some? (agent-error a))] [0 true]))
(let [a (agent 0) b (agent 0)]
  (send a (fn [x] (send b inc) (inc x)))
  (await a) (await b)
  (check "a send from an action that succeeds goes out after it" [@a @b] [1 1]))
(let [a (agent 0) inside (atom nil)]
  (dosync (send a inc) (clotran.host.thread/sleep 50) (reset! inside @a))
  (await a)
  (check "a send inside dosync waits for the commit" [@inside @a] [0 1]))
(let [a (agent 0)]
  (try (dosync (send a inc) (throw (ex-info "abort" {}))) (catch clotran.host.exception e nil))
  (clotran.host.thread/sleep 100)
  (check "and an aborted transaction drops it" @a 0))
(let [a (agent 0) b (agent 0)]
  (let [c (agent 0 :error-handler (fn [ag e] (send b + 10)))]
    (send c (fn [_] (throw (ex-info "y" {}))))
    (clotran.host.thread/sleep 200) (await b)
    (check "an error handler's send goes out at once" @b 10)))

;; Agent.restart: the actions queued behind a failure are kept and
;; resume on restart unless :clear-actions; an agent that has not
;; failed refuses, and the validator judges the new state first.
(let [a (agent 0)]
  (send a (fn [x] (clotran.host.thread/sleep 200) (throw (ex-info "x" {}))))
  (send a + 5)
  (wait-fail a)
  (restart-agent a 10) (await a)
  (check "restart resumes the queued actions" @a 15))
(let [a (agent 0)]
  (send a (fn [x] (clotran.host.thread/sleep 200) (throw (ex-info "x" {}))))
  (send a + 5)
  (wait-fail a)
  (restart-agent a 10 :clear-actions true) (await a)
  (check ":clear-actions drops them" @a 10))
(check "restart of a working agent refuses"
       (try (restart-agent (agent 0) 1) (catch clotran.host.runtime_exception e (.getMessage e)))
       "Agent does not need a restart")
(let [a (agent 1 :validator pos?)]
  (send a (fn [_] (throw (ex-info "x" {}))))
  (wait-fail a)
  (check "restart validates the new state and keeps the failure"
         [(try (restart-agent a -1) (catch clotran.host.exception e (.getMessage e))) (some? (agent-error a)) @a]
         ["Invalid reference state" true 1]))

;; A latch is a counter when there is one thread.

;;; ---- set-validator! ----------------------------------------------
;; Every reference type takes one, and a refusal leaves the reference
;; alone rather than writing a bad value.

(let [v (atom 1)]
  (set-validator! v pos?)
  (check "the validator is remembered" (nil? (get-validator v)) false)
  (check "reset! is refused"  (try (reset! v -1) :no (catch clotran.host.illegal_state_exception e :invalid)) :invalid)
  (check "and the value stands" @v 1)
  (check "swap! is refused"   (try (swap! v - 5) :no (catch clotran.host.illegal_state_exception e :invalid)) :invalid)
  (check "still stands"       @v 1)
  (check "a good value goes through" (do (reset! v 7) @v) 7))
;; Clojure validates the CURRENT value on the way in.


;;; ---- clojure.core is already loaded ------------------------------
;; (require 'clojure.core) reached clotran's loader and re-read the
;; whole file, re-evaluating every definition against a namespace that
;; already had them -- and died partway with an arity error. Clojure
;; answers nil and changes nothing. Clojure's own test helper opens
;; every temporary namespace with (clojure.core/use 'clojure.core), so
;; nothing written through eval-in-temp-ns ran at all.



;;; ---- the N and M suffixes ----------------------------------------
;; Clojure reads 1N as a BigInt and 1M as a BigDecimal. clotran has
;; neither and used to read both as SYMBOLS, so (cond 0M :a true :b)
;; was "unable to resolve symbol" rather than :a.
;;
;; Each drops to the nearest thing clotran has, chosen by what `=` then
;; says: 1N is an integer because (= 1N 1) is true in Clojure, and 1M is
;; a DOUBLE because (= 1M 1) is false there -- reading 45M as the
;; integer 45 would have made it true. DEVIATIONS 30.

;; A letter that is not a suffix still makes a symbol, and a token that
;; is neither is still a reader error.


;;; ---- the boxing constructors -------------------------------------
;; (Long. 1) is 1 and (String. "x") is "x": in clj these wrap a
;; primitive in an object, and there is no unboxed number here to wrap.
;; What they still have to do is CONVERT, because (Long. "12") parses.
;; Every line below is `clj`'s answer.



;;; ---- the host supertype chain ------------------------------------
;; host_super feeds multimethod dispatch, and it was picked by index
;; with two silent holes: entries keyed "float" and "bool" where
;; type_name says "double" and "boolean" -- so a double and a boolean
;; had NO supertypes -- and an Object fallback at index 4 that only a
;; type with exactly three supertypes ever reached. print-dup on a
;; double was "No method in multimethod for dispatch value: :double".
;;
;; Order is specific-to-general, because dispatch takes the first
;; match: print-dup has a method on Long and another on Number, and
;; only Long's prints 1 rather than #=(clotran.host.int8. "1").
;; All checked against `clj`.

;; core_print registers print-dup on PersistentVector and
;; PersistentHashSet by NAME, and only those print plainly.

;; print-method still finds what it found before.
;; Double's own predicates, which print-method asks of it.


;;; ---- hash follows equality ---------------------------------------
;; Clojure guarantees (= a b) implies (= (hash a) (hash b)). Three
;; things broke it, and `case` is where they showed, because case
;; dispatches on the hash:
;;
;;   - the cons walk stopped on KIND, and the empty tail is itself a
;;     cons, so every list hashed one extra nil -- (hash '(1)) came out
;;     equal to (hash [1 2]).
;;   - a seq VIEW was not structural at all, so it hashed by identity
;;     while comparing equal to its vector.
;;   - the tag was XORed straight onto the value, and the tags are
;;     small integers, so (hash 2) was 0 -- the same as (hash nil),
;;     because GCT_INT is 2.


;;; ---- case ---------------------------------------------------------
;; case compiles to a lookup keyed on the hash, with a shift and mask
;; when the constants have to be squeezed together. The shift is
;; ARITHMETIC in core.clj -- (bit-shift-right x shift) propagates the
;; sign -- and Fortran's ishft fills with zeros, so a negative hash
;; landed in a different bucket at runtime than the macro put it in.
;; A case small enough to need no shift hid it completely.

(let [two 2
      f #(case %
           1 :number
           "foo" :string
           \a :char
           pow :symbol
           :zap :keyword
           (2 \b "bar") :one-of-many
           [1 2] :sequential-thing
           {:a 2} :map
           {:r 2 :d 2} :droid
           #{2 3 4 5} :set
           [1 [[[2]]]] :deeply-nested
           nil :nil
           :default)]
  (check "case over many kinds of constant"
         (mapv f [1 "foo" \a :zap 'pow 2 \b "bar" [1 2] (list 1 2) [1 two]
                  {:a 2} #{2 3 4 5} #{2 3 4 5 6} {:r 2 :d 2} [1 [[[two]]]] nil 42])
         [:number :string :char :keyword :symbol :one-of-many :one-of-many :one-of-many
          :sequential-thing :sequential-thing :sequential-thing :map :set :default
          :droid :deeply-nested :nil :default]))

;;; ---- report -----------------------------------------------------


;;; ---- dgemm: the first Fortran routine called from clotran, now a package --
;;
;; A = [[1 2 3] [4 5 6]], B = [[7 8] [9 10] [11 12]]; A x B is
;; [[58 64] [139 154]]. Checked against the same product computed in
;; Clojure over aget, and then against the numbers.
(alias 'fb 'fortran)
(fortran/load-package "packages/blas")
(require 'blas)
(def dgA (fb/make-array "real8" 2 3))
(def dgB (fb/make-array "real8" 3 2))
(dotimes [i 2] (dotimes [j 3] (fb/aset dgA i j (double (+ 1 j (* 3 i))))))
(dotimes [i 3] (dotimes [j 2] (fb/aset dgB i j (double (+ 7 j (* 2 i))))))
(def dgC (blas/dgemm dgA dgB))
(check "dgemm answers a real8 array" (fb/array-kind dgC) "real8")
(check "dgemm answers m x n" (fb/array-shape dgC) [2 2])
(check "dgemm C = A x B"
       (vec (for [i (range 2) j (range 2)] (fb/aget dgC i j)))
       (vec (for [i (range 2) j (range 2)]
              (reduce + (for [l (range 3)] (* (fb/aget dgA i l) (fb/aget dgB l j)))))))
(check "dgemm C = A x B, the numbers" (vec (for [i (range 2) j (range 2)] (fb/aget dgC i j))) [58.0 64.0 139.0 154.0])
;; the same Fortran from eight futures at once -- each gives up the baton
;; for the call (tasks.inc, native_begin), so the routines run in
;; parallel -- answers the same matrices as the calls one after another
(check "dgemm from futures, in parallel, answers what it answers in turn"
       (let [ms (vec (for [s (range 8)] (let [a (fortran/make-array "real8" 3 3)] (dotimes [i 3] (dotimes [j 3] (fortran/aset a i j (double (+ i (* 3 j) s))))) a)))
             flat (fn [c] (vec (for [i (range 3) j (range 3)] (fortran/aget c i j))))]
         (= (mapv #(flat (blas/dgemm % %)) ms)
            (mapv (comp flat deref) (mapv (fn [m] (future (blas/dgemm m m))) ms))))
       true)
(check "dgemm refuses mismatched shapes"
       (try (blas/dgemm dgA dgA) (catch clotran.host.throwable t :refused)) :refused)
;; NUMBERS NEVER MIX at the door (PLAN step 27; model/boundary.lisp
;; `cross`). Each of these once crossed silently: 2.0 as m went in as
;; its IEEE bits and dgemm answered zeros; 2^32+2 wrapped to 2.
(defn door-refusal [f]
  (try (f) :crossed (catch clotran.host.illegal_argument_exception e (ex-message e))))
(let [a (fb/make-array "real8" 2 2) b (fb/make-array "real8" 2 2) c (fb/make-array "real8" 2 2)]
  (check "a real is refused as an int4"
         (door-refusal #(blas.raw/dgemm "N" "N" 2.0 2 2 1.0 a 2 b 2 0.0 c 2))
         "dgemm: argument m is an int4: pass an integer, not 2.0 (clotran.host.real8)")
  (check "an integer outside int4's window is refused"
         (door-refusal #(blas.raw/dgemm "N" "N" 4294967298 2 2 1.0 a 2 b 2 0.0 c 2))
         "dgemm: argument m is an int4, -2147483648..2147483647: out of range, 4294967298 (clotran.host.int8)")
  (check "the window's edge crosses"
         (door-refusal #(blas.raw/dgemm "N" "N" 2147483647 0 0 1.0 a 2147483647 b 2 0.0 c 2147483647))
         :crossed)
  (check "an integer is refused as a real8"
         (door-refusal #(blas.raw/dgemm "N" "N" 2 2 2 1 a 2 b 2 0.0 c 2))
         "dgemm: argument alpha is a real8: pass a real, not 1 (clotran.host.int8)")
  ;; ALIASING (F2018 15.5.2.13; model `alias-ok`): c is written, so it
  ;; may not also be a or b -- it crossed, and dgemm answered [3 8 3 8]
  ;; for [3 3 3 3]. a and b are only read (bind-fortran infers :in for
  ;; an array the F77 body never writes), so A x A crosses.
  (check "an array written and bound twice is refused"
         (door-refusal #(blas.raw/dgemm "N" "N" 2 2 2 1.0 c 2 b 2 1.0 c 2))
         "dgemm: argument c may be written, and the same array is also argument a; Fortran forbids the aliasing -- pass a copy")
  (check "the same array twice, only read, crosses"
         (door-refusal #(blas.raw/dgemm "N" "N" 2 2 2 1.0 a 2 a 2 0.0 c 2))
         :crossed))

;;; ---- stack traces --------------------------------------------------
;;
;; A thrown Throwable carries the call stack it was thrown from, as
;; elements answering the four StackTraceElement questions
;; clojure.stacktrace and clojure.test ask. Host check: the frame names
;; are clotran's, so real Clojure cannot answer these.
(defn st-thrower [] (throw (ex-info "boom" {})))
(defn st-caller [] (st-thrower))
(def st-trace (try (st-caller) (catch clotran.host.throwable t (.getStackTrace t))))
;; As in clj, the top frame is ex-info's own: the exception is
;; constructed inside it.
(check "a trace has a frame per call" (>= (alength st-trace) 3) true)
(check "the top frame is ex-info" (.getClassName (aget st-trace 0)) "clojure.core/ex-info")
(check "then the thrower" (.endsWith (.getClassName (aget st-trace 1)) "st-thrower") true)
(check "then the caller" (.endsWith (.getClassName (aget st-trace 2)) "st-caller") true)
(check "a frame's method is invoke" (.getMethodName (aget st-trace 0)) "invoke")
(check "a frame names its file" (boolean (re-find #"language_test" (str (.getFileName (aget st-trace 1))))) true)
(check "a frame has a line" (pos? (.getLineNumber (aget st-trace 1))) true)

;;; ---- tasks: futures that yield ------------------------------------
;;
;; A future is a task on a thread of its own (tasks.inc), running at
;; once beside whoever made it (PLAN.md step 14f): blocked on a promise
;; it cannot finish, and once the promise is delivered it goes on by
;; itself -- when it finishes is not ours to check, as it is not on the
;; clj. The values are the oracle's.
(def tk-ping (promise)) (def tk-pong (promise))
(def tk-t1 (future (let [x 10 y @tk-ping] (deliver tk-pong (+ x y)) :t1-done)))
(check "a future runs until it blocks, then is parked" (future-done? tk-t1) false)
(deliver tk-ping 5)
(check "resumed, it has its locals" [@tk-pong @tk-t1] [15 :t1-done])
(require 'clotran.thread)
(def tk-t5 (future (clotran.thread/sleep 5) 7))
(check "a block under a native frame is pinned and runs the others there"
       @(future (mapv (fn [i] (+ i @tk-t5)) [1 2])) [8 9])
(def tk-q (promise))
(check "pinned, it cannot wait for the main context: a deadlock, not a hang"
       (try @(future (mapv (fn [i] (+ i @tk-q)) [1 2])) (catch clotran.host.throwable e (boolean (re-find #"deadlock" (str e))))) true)
(check "so is a wait nothing can satisfy"
       (try @(promise) (catch clotran.host.throwable t (boolean (re-find #"deadlock" (str t))))) true)
(def tk-p3 (promise)) (def tk-t3 (future @tk-p3))
(check "a parked future can be cancelled"
       [(future-cancel tk-t3) (future-cancelled? tk-t3) (try @tk-t3 (catch clotran.host.cancellation_exception e :cancelled))]
       [true true :cancelled])
(def tk-slow (promise)) (def tk-t7 (future (deref tk-slow 20 :gave-up)))
(clotran.thread/sleep 30)
(check "a deadline rides on the parked future" @tk-t7 :gave-up)
(check "the failure's text is in the ExecutionException"
       (try @(future (throw (ex-info "boom" {}))) (catch clotran.host.throwable e (boolean (re-find #"boom" (str e))))) true)
(check "a thousand futures give their contexts back"
       (count (doall (map deref (doall (map #(future (* % %)) (range 1000)))))) 1000)
(check "eight threads forcing one lazy seq run each thunk once (model/lazy-cell.lisp)"
       (let [runs (atom 0)]
         (dotimes [_ 50]
           (let [s (map (fn [x] (swap! runs inc) x) (range 50))]
             (run! deref (doall (for [_ (range 8)] (future (reduce + s)))))))
         @runs)
       2500)

;;; ---- clotran.rt: host members written in Clojure, loaded on use ----
(check "sequence reaches clotran.rt" (sequence (map inc) [1 2]) [2 3])
(check "which is then loaded" (some? (find-ns 'clotran.rt)) true)

;;; ---- clotran.thread: the protocol, and green as its default ---------
;;
;; One API over pluggable kinds of thread; green is a task. Host check:
;; the namespace is ours, and so is when a thread runs.
(require 'clotran.thread)
(alias 'th 'clotran.thread)
(check "the default kind is green, and it takes a closure" [(th/kind-name) (th/-takes th/green)] [:green :fn])
(def th-a (th/spawn (fn [] (+ 1 2))))
(check "spawn answers a handle: join, deref and status" [(th/join th-a) @th-a (th/status th-a) (realized? th-a)] [3 3 :done true])
;; Threads run at once (PLAN.md step 14f): a new one is not yet waiting
;; when spawn returns, so a check of "parked" gives it up to 2 s to get there
(defn th-settled [h] (loop [i 0] (let [s (th/status h)] (if (or (= s :parked) (> i 400)) s (do (clotran.thread/sleep 5) (recur (inc i)))))))
(def th-box (promise))
(def th-b (th/spawn (fn [] @th-box)))
(check "a thread blocked on a promise is parked" (th-settled th-b) :parked)
(deliver th-box 7)
(check "and joins with its value, in time" (th/join th-b 100 :late) 7)
(check "join with a timeout answers the timeout value" (th/join (th/spawn (fn [] @(promise))) 5 :late) :late)
(check "cancel! stops a thread still to finish" (let [h (th/spawn (fn [] @(promise)))] [(th/cancel! h) (th/status h) (th/cancel! h)]) [true :cancelled false])
(check "a failure is rethrown by join"
       (try (th/join (th/spawn (fn [] (throw (ex-info "bad" {}))))) (catch clotran.host.execution_exception e :failed)) :failed)
;; a worker that squares what it is sent and replies to the sender
(def th-worker (th/spawn (fn [] (loop [] (let [[from x] (th/receive)]
                                           (if (= x :stop) :stopped (do (th/send! from (* x x)) (recur))))))))
(check "a worker waiting for mail is parked" (th-settled th-worker) :parked)
(th/send! th-worker [(th/self) 4])
(check "a reply arrives in the caller's mailbox" (th/receive) 16)
(th/send! th-worker [(th/self) 5])
(check "and again, with a timeout" (th/receive 100 :none) 25)
(check "an empty mailbox times out" (th/receive 5 :nothing) :nothing)
(th/send! th-worker [(th/self) :stop])
(check "the worker stops when told" (th/join th-worker) :stopped)
(check "a thread's self is a handle to it"
       (let [p (promise)] (th/join (th/spawn (fn [] (th/send! (th/self) :note) (deliver p (th/receive)) @p)))) :note)
(check "the main thread is not joinable" (try (th/join (th/self)) (catch clotran.host.throwable e :no)) :no)

;;; ---- ::keywords resolve in the reader, against *ns* and its aliases ----
(check "::b is the current namespace's" (namespace ::b) "user")
(check "and prints so" (pr-str ::b) ":user/b")
(require '[clojure.string :as lt-s])
(check "::alias/x goes through the alias" (namespace ::lt-s/x) "clojure.string")
(check "a namespace name is not an alias" (try (read-string "::clojure.core/x") (catch clotran.host.exception e :invalid)) :invalid)
(check "an alias nobody made is an invalid token" (try (read-string "::nope/x") (catch clotran.host.exception e (boolean (re-find #"Invalid token" (.getMessage e))))) true)

;;; ---- an agent's error handler is handed the error itself -- an oracle
;;; case would leave clj's agent pool running and its process never exiting
(check "the handler sees the error's class"
       (let [err (atom nil) a (agent 0 :error-mode :continue :error-handler #(reset! err %&))]
         (send a /) (await-for 1000 a)
         [(instance? clotran.host.arithmetic_exception (second @err)) (= a (first @err)) @a (agent-error a)])
       [true true 0 nil])


;;; ---- a package through the door: DynLoad.f90, clotran.package --------
;; test/f/testpkg.f90 is a shared library with a manifest and one shim per
;; routine, built by the Makefile like any package. (fortran/load-package
;; path) opens it and interns its routines as fns in the namespace the
;; manifest names.
(def tp (try (fortran/load-package "build/libtestpkg.dylib")
             (catch clotran.host.exception e (fortran/load-package "build/libtestpkg.so"))))
(check "the manifest names the package" (:package tp) "testpkg")
(check "an :out scalar comes back by name" (testpkg/double-it 21.0) {:y 42.0})
(check "an array goes by pointer with its extent; a :returns value is the value"
       (let [a (make-array clotran.host.real8/TYPE 3)] (aset a 0 1.5) (aset a 1 2.5) (aset a 2 3.0) (testpkg/sum-arr a)) 7.0)
(check "an :inout array is written in place"
       (let [a (make-array clotran.host.real8/TYPE 2)] (aset a 0 1.0) (aset a 1 2.0) (testpkg/scale! a 10.0) [(aget a 0) (aget a 1)]) [10.0 20.0])
(check "a string crosses null-terminated" (testpkg/count-chars "hello") 5)
(check "two :out scalars" (testpkg/divmod 17 5) {:q 3 :r 2})
(check "a library that is not there is an error" (try (fortran/load-package "build/nope.dylib") :loaded (catch clotran.host.exception e :no)) :no)
(check "the wrong argument count is an ArityException" (try (testpkg/double-it) (catch clotran.host.arity_exception e :arity)) :arity)
(check "a scalar where an array is wanted is an error" (try (testpkg/sum-arr 1.0) (catch clotran.host.exception e :not-array)) :not-array)
(check "the fns carry arglists" (:arglists (meta #'testpkg/divmod)) '([a b]))

;;; ---- a library bound by the generator: scripts/bind-fortran -----------
;; test/f/samplelib.f90 has no shims and no manifest; the Makefile runs
;; the generator over it and builds build/libsamplelib from the two.
(def sl (try (fortran/load-package "build/libsamplelib.dylib")
             (catch clotran.host.exception e (fortran/load-package "build/libsamplelib.so"))))
(check "the generator named the package" (:package sl) "samplelib.raw")
(check "a generated :out scalar" (samplelib.raw/double-it 21.0) {:y 42.0})
(check "a generated function over an array and its length"
       (let [a (fortran/make-array "real8" 3)] (fortran/aset a 0 1.5) (fortran/aset a 1 2.5) (fortran/aset a 2 3.0) (samplelib.raw/sum-arr a 3)) 7.0)
(check "a generated character(len=*) argument" (samplelib.raw/count-chars "hello") 5)
(check "a generated :inout int8 array, in place" (let [a (fortran/make-array "int8" 2)] (fortran/aset a 0 3) (fortran/aset a 1 -4) (samplelib.raw/bump8 a 2) [(fortran/aget a 0) (fortran/aget a 1)]) [7 -7])
(check "generated intents from the source" (samplelib.raw/divmod 17 5) {:q 3 :r 2})
(check "a generated rank-2 argument" (let [m (fortran/make-array "real8" 2 2)] (fortran/aset m 0 0 1.0) (fortran/aset m 1 1 5.0) (samplelib.raw/trace m 2)) {:t 6.0})
(check "a generated :inout array, in place" (let [a (fortran/make-array "real8" 2)] (fortran/aset a 0 1.0) (fortran/aset a 1 2.0) (samplelib.raw/scale a 2 10.0) [(fortran/aget a 0) (fortran/aget a 1)]) [10.0 20.0])
;; Every scalar kind crosses unchanged (scripts/fuzz-door checks the
;; same routine against the ACL2 model; these are its edges, kept in
;; the gate, which has no ACL2). A logical crosses through a temporary
;; of the routine's own kind -- the shim passed a one-byte C logical to
;; a four-byte dummy, which the compiler refused.
(check "each scalar kind crosses unchanged"
       (samplelib.raw/echo-kinds -2147483648 9223372036854775807 -0.0 true)
       {:oi4 -2147483648 :oi8 9223372036854775807 :or8 -0.0 :ol true})
(check "a BigInt is an integer: inside the window it crosses"
       (samplelib.raw/echo-kinds 5N -9223372036854775808N 2.5 false)
       {:oi4 5 :oi8 -9223372036854775808 :or8 2.5 :ol false})
(check "a BigInt past int8's window is refused"
       (door-refusal #(samplelib.raw/echo-kinds 0 9223372036854775808N 0.0 false))
       "echo-kinds: argument i8 is an int8, -9223372036854775808..9223372036854775807: out of range, 9223372036854775808N (clotran.host.bigint)")
(check "nil is not a logical"
       (door-refusal #(samplelib.raw/echo-kinds 0 0 0.0 nil))
       "echo-kinds: argument l is a logical: pass true or false, not nil")

;; The decimal's working precision. The oracle compares with-precision
;; against real Clojure form by form; what it cannot check is the part
;; where clotran deliberately answers where Clojure raises, because
;; there is no Clojure answer to compare with (DEVIATIONS 43).
(check "a decimal division answers rather than raising"
       (/ 1M 3) 0.3333333333333333333333333333333333M)
(check "at decimal128's 34 digits" (count (str (/ 1M 3))) 36)
(check "the default context is visible, not hidden"
       *math-context* {:precision 34 :rounding :HALF_EVEN})
(check "rounding is half to even" (/ 2M 3) 0.6666666666666666666666666666666667M)
(check "an exact quotient is still exact" (/ 1M 8) 0.125M)
(check "with-precision narrows it" (with-precision 10 (/ 1M 3)) 0.3333333333M)
(check "and nil asks for Clojure's own arithmetic back"
       (binding [*math-context* nil]
         (try (/ 1M 3) (catch clotran.host.arithmetic_exception e :exact-or-throw)))
       :exact-or-throw)
(check "a literal keeps every digit it was written with"
       (str 1.2345678901234567890123456789012345678901M)
       "1.2345678901234567890123456789012345678901")

;; The compiler's front door: the resolved tree as data (PLAN step 10).
;; Nothing in Clojure answers this, so it cannot go in the oracle. What
;; matters is that the tree a generator reads is the SAME one the
;; executor runs -- one analysis, not two front ends that can disagree.
(check "a form analyses to a top node" (:op (clotran-ast '(if true 1 2))) :top)
(check "with the form under it" (:op (:p1 (clotran-ast '(if true 1 2)))) :if)
(check "an if has its three children"
       (mapv :op (:children (:p1 (clotran-ast '(if true 1 2)))))
       [:const :const :const])
(check "a constant carries its value, not a rebuilt copy"
       (mapv :p1 (:children (:p1 (clotran-ast '(if true 1 2)))))
       [true 1 2])
(check "a literal collection is handed over whole"
       (:p1 (:p1 (clotran-ast '[1 {:a 2}])))
       nil)
;; A fn keeps its arity bodies inside a plain template vector, so the
;; exporter has to walk collections or a function shows up with no body.
(check "a fn's body is reachable through the template"
       (some? (first (filter map? (tree-seq coll? seq (clotran-ast '(fn [x] x))))))
       true)
(check "a local knows its frame slot"
       (->> (clotran-ast '(fn [x] (let [y 1] y)))
            (tree-seq coll? seq)
            (filter #(and (map? %) (= :local (:op %))))
            (map :i2)
            set)
       #{1})
(check "and its name, for the debugger"
       (->> (clotran-ast '(fn [x] (let [y 1] y)))
            (tree-seq coll? seq)
            (filter #(and (map? %) (= :local (:op %))))
            (map (comp str :p1))
            set)
       #{"y"})
(check "a call's head is a node like any other"
       (:op (first (:children (->> (clotran-ast '(fn [x] (inc x)))
                                   (tree-seq coll? seq)
                                   (filter #(and (map? %) (= :call (:op %))))
                                   first))))
       :const)
(check "every node kind that reaches the exporter has a name"
       (->> (clotran-ast '(fn [x] (loop [i 0] (if (< i x) (recur (inc i)) i))))
            (tree-seq coll? seq)
            (filter map?)
            (map :op)
            (filter #(= :unknown %))
            count)
       0)
;; A folded builtin in a call head names itself. The object is fresh on
;; every analysis, so a code generator cannot recognise + by identity,
;; and without the name it compiled every addition as a generic call.
(check "a folded call head says which builtin it is"
       (->> (clotran-ast '(fn [x] (+ x 1)))
            (tree-seq coll? seq)
            (filter #(and (map? %) (= :call (:op %))))
            first :children first :builtin str)
       "+")

;;; ---- tiers: what compiles to pure Fortran ------------------------
;;
;; clotran.tiers (PLAN.md step 13) sorts each function into A (pure
;; Fortran), B (needs the collector) or C (needs the interpreter), and
;; says why at every call site. Host check: the tiers are clotran's.
(require 'clotran.tiers)
(def tier-result (clotran.tiers/classify "test/clj/tiers_sample.cljf"))
(check "tiers, per function"
       (into (sorted-map) (for [[k v] tier-result] [(name k) (:tier v)]))
       (sorted-map "count-big" :A "describe" :B "many" :B "mean" :A "parse" :B
                   "run-it" :C "scaled" :C "show" :A "shout" :A "spread" :B
                   "squares" :B "sum-squares" :A "total" :A "uses-describe" :B))
(check "tiers, the reason codes"
       (into (sorted-map) (for [[k v] tier-result :when (not= :A (:tier v))]
                            [(name k) (vec (sort (distinct (map :code (:findings v)))))]))
       (sorted-map "describe" ["B010"] "many" ["B060" "N001"] "parse" ["B003"]
                   "run-it" ["B003" "C001"] "scaled" ["C002"] "spread" ["B003"]
                   "squares" ["B001"] "uses-describe" ["B002" "B011"]))
(check "a note says what a tier-A verdict assumes"
       (vec (sort (distinct (map :code (:findings (tier-result 'tiers-sample/sum-squares))))))
       ["N001"])
(check "every code the classifier emits is explained"
       (let [emitted (set (map second (re-seq #"\"([BCN][0-9]{3})\"" (clotran-slurp "src/clj/clotran/tiers.cljf"))))]
         [(sort (remove (set (keys clotran.tiers/codes)) emitted))
          (every? #(and (:title %) (:tier %) (:explain %)) (vals clotran.tiers/codes))
          ;; and the scan saw them at all, or the first answer is vacuous
          (>= (count emitted) 20)])
       [[] true true])
(check "a warning carries its line and its fix"
       (let [f (first (:findings (tier-result 'tiers-sample/squares)))]
         [(second (clotran-position (:pos f))) (boolean (re-find #"reduce" (:help f)))])
       [17 true])

;;; ---- the call stack is balanced: a call leaves nothing on it. A
;;; protocol fn dispatching to a reify method lost its own entry (the
;;; method took over its body frame), so every spec conform -- and every
;;; macro spec check -- left frames that showed in later traces.
(defprotocol LeakP (leak-m [x]))
(deftype LeakT [] LeakP (leak-m [this] 1))
(defn stack-depth [] (count (.getStackTrace (clotran.host.exception.))))
(check "a protocol call to an inline method leaves no frame"
       (let [d (stack-depth)] (dotimes [_ 5] (leak-m (LeakT.)) (leak-m (reify LeakP (leak-m [_] 2)))) (- (stack-depth) d))
       0)
(check "a caught throw leaves no frame"
       (let [d (stack-depth)] (dotimes [_ 5] (try (leak-m 1) (catch clotran.host.exception e nil))) (- (stack-depth) d))
       0)

;;; core's one-line wrappers run as their builtin but keep their entry,
;;; as clojure.core$first is in clj's trace -- whichever way called
(defn wr-direct [x] (first x))
(defn wr-local [x] (let [f first] (f x)))
(defn wr-apply [x] (apply first [x]))
(defn wr-trace [g] (try (g 5) (catch clotran.host.exception e (boolean (some #(clojure.string/includes? (str %) "clojure.core/first") (.getStackTrace e))))))
(check "an elided core wrapper is on the trace" (mapv wr-trace [wr-direct wr-local wr-apply]) [true true true])
(check "an elided core wrapper leaves no frame"
       (let [d (stack-depth)] (dotimes [_ 5] (first [1]) (wr-local [1]) (wr-apply [1]) (try (wr-direct 5) (catch clotran.host.exception e nil))) (- (stack-depth) d))
       0)

;;; ---- sockets and the socket REPL (PLAN step 21): loopback only, a
;;; port the OS picks, so two gate halves at once cannot collide
(require '[clotran.net :as net] '[clotran.server :as srv])
(check "a server on port 0 is given one" (let [s (net/listen 0 {:host "127.0.0.1"})] (try (pos? (:port s)) (finally (net/close s)))) true)
(check "accept answers nil when nobody comes" (let [s (net/listen 0 {:host "127.0.0.1"})] (try (net/accept s 50) (finally (net/close s)))) nil)
(check "text both ways, UTF-8 intact, one form read off the stream"
       (let [s (net/listen 0 {:host "127.0.0.1"})
             served (future (let [c (net/accept s 5000)]
                              (binding [*in* (net/reader c) *out* (net/writer c)]
                                (let [f (read)] (println (pr-str (eval f)) "λ") (flush)))
                              (net/close c) :done))
             c (net/connect "127.0.0.1" (:port s))]
         (try (let [w (net/writer c)] (.write w "(+ 1 2 (* 3 4)) rest\n") (.flush w))
              [(.readLine (net/reader c)) (deref served 5000 :timeout)]
              (finally (net/close c) (net/close s))))
       ["15 λ" :done])
(check "connecting to nothing is an IOException"
       (let [s (net/listen 0 {:host "127.0.0.1"}) p (:port s)] (net/close s)
         (try (net/connect "127.0.0.1" p) :connected (catch clotran.host.io_exception e :refused)))
       :refused)
(defn repl-says [lines]
  (let [s (srv/start-server {:name "lt" :port 0})
        c (net/connect "127.0.0.1" (:port s)) w (net/writer c) r (net/reader c)]
    (try (.write w (apply str (map #(str % "\n") lines))) (.flush w)
         (loop [acc []] (if-let [l (.readLine r)] (recur (conj acc l)) acc))
         (finally (net/close c) (srv/stop-server "lt")))))
(check "the socket REPL: values, *1, errors, a bad read, the namespace, quit"
       (repl-says ["(+ 1 2)" "(inc *1)" "(/ 1 0)" "(oops ]" "(ns lt-other)" "(str (ns-name *ns*))" ":repl/quit" "(never)"])
       ["user=> 3" "user=> 4" "user=> Execution error (arithmetic_exception)." "Divide by zero"
        "user=> Syntax error reading source (runtime_exception)." "Unmatched delimiter: ]"
        "user=> nil" "lt-other=> \"lt-other\"" "lt-other=> "])
(check "stopping a server that is not there" (srv/stop-server "nope") false)
(check "text to UTF-8 bytes and back"
       (let [b (clotran.io/utf8-bytes "aλ€𝄞")] [(vec b) (clotran.io/utf8-string b) (clotran.io/utf8-string b 1 2)])
       [[97 -50 -69 -30 -126 -84 -16 -99 -124 -98] "aλ€𝄞" "λ"])
(check "bytes both ways over a socket, counted as bytes"
       (let [s (net/listen 0 {:host "127.0.0.1"})
             served (future (let [c (net/accept s 5000) buf (byte-array 16)
                                  n (net/read-bytes c buf 0 16 5000)]
                              (net/write-bytes c buf 0 n)
                              (net/close c) n))
             c (net/connect "127.0.0.1" (:port s))]
         (try (net/write-bytes c (clotran.io/utf8-bytes "5:λλ"))
              (let [buf (byte-array 16) n (net/read-bytes c buf 0 16 5000)]
                [(deref served 5000 :timeout) n (clotran.io/utf8-string buf 0 n) (net/read-bytes c buf 0 16 5000)])
              (finally (net/close c) (net/close s))))
       [6 6 "5:λλ" -1])
(check "an array is not text: String. refuses it rather than printing the object"
       (mapv #(try (clotran.host.string. %) (catch clotran.host.illegal_argument_exception e :refused)) [(byte-array [97]) (char-array "ab")])
       [:refused :refused])
(check "a read-bytes past the array is refused"
       (try (clotran-socket-read-bytes 0 (byte-array 2) 1 5 0) (catch clotran.host.index_out_of_bounds_exception e :refused))
       :refused)
(defn prepl-says [lines]
  (let [s (srv/start-server {:name "lt-prepl" :port 0 :accept 'clotran.server/io-prepl})
        c (net/connect "127.0.0.1" (:port s)) w (net/writer c) r (net/reader c)]
    (try (.write w (apply str (map #(str % "\n") lines))) (.flush w)
         (loop [acc []] (if-let [m (read {:eof nil} r)] (recur (conj acc (dissoc m :ms))) acc))
         (finally (net/close c) (srv/stop-server "lt-prepl")))))
;; the messages clj's own clojure.core.server/io-prepl sends for the same
;; input, :ms and an exception's clj frames aside (checked 2026-09-29)
(check "the prepl: a value, printed output, a failure, the namespace, a tap"
       (let [ms (prepl-says ["(+ 1 2)" "(println \"hi\")" "(/ 1 0)" "(ns lt-p)" "(tap> :t)" "(clotran.host.thread/sleep 200)" ":repl/quit"])]
         ;; a tap may arrive before or after its :ret, in clj as here -- and
         ;; is lost if the prepl ends first, so it is given a moment
         (let [ms (mapv #(cond-> % (:exception %) (update :val (comp :cause read-string))) ms)]
           (conj (vec (remove #(= :tap (:tag %)) ms)) (first (filter #(= :tap (:tag %)) ms)))))
       [{:tag :ret :val "3" :ns "user" :form "(+ 1 2)"}
        {:tag :out :val "hi\n"}
        {:tag :ret :val "nil" :ns "user" :form "(println \"hi\")"}
        {:tag :ret :val "Divide by zero" :ns "user" :form "(/ 1 0)" :exception true}
        {:tag :ret :val "nil" :ns "lt-p" :form "(ns lt-p)"}
        {:tag :ret :val "true" :ns "lt-p" :form "(tap> :t)"}
        {:tag :ret :val "nil" :ns "lt-p" :form "(clotran.host.thread/sleep 200)"}
        {:tag :tap :val ":t"}])

;;; ---- the verdict: LAST, so every check above counts. It once sat
;;; 140 lines early, and the package and tier checks after it could fail
;;; without the gate hearing of it.
(println "")
(if (zero? @*failures*)
  (println "LANGUAGE TESTS PASSED")
  (println "LANGUAGE TESTS FAILED:" @*failures*))
