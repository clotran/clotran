;; clotran.clj -- populates the small, fixed set of `clojure.lang.*`
;; interop surface real core.clj's own bootstrap calls directly
;; (clojure.lang.RT, clojure.lang.PersistentList, clojure.lang.Util,
;; instance?'s pseudo-classes), so core.clj's own unmodified
;; definitions (list, cons, first, next, rest, conj, seq, let, loop,
;; fn, instance?, ...) evaluate correctly as literally written --
;; nothing in clojure.core itself gets overridden by this file
;; anymore. Loaded FIRST, before core.clj (see Eval.f90's
;; eval_core_bootstrap): core.clj's own bootstrap-era definitions
;; (cons, list, fn, ...) call straight into clojure.lang.RT etc.
;; starting from its first few forms, long before reaching the end of
;; the file, so this surface has to already exist by the time core.clj
;; starts loading, not after.
;;
;; This only works now because two more foundational pieces are real:
;; eval_dot resolves (. Class (method args)) / (. Class member) /
;; (Class/method args) generically against whatever real namespace
;; Class names (see Eval.f90), and macro calls always receive &form/
;; &env as their first two args (confirmed against the real `clojure`
;; CLI), matching what core.clj's own fn/let/loop/defmacro actually
;; expect. Before both of those, this file used to *replace*
;; clojure.core's own list/cons/first/.../let/loop/fn with clotran-
;; native reimplementations; now it only has to supply the handful of
;; pseudo-classes/namespaces those same unmodified definitions call
;; into, which is a much smaller, more honest surface. Grows one
;; entry at a time as walking further into core.clj turns up the
;; next thing it needs -- see NOTES.md.

;; clojure.lang.RT: core.clj's own first/next/rest/cons/conj/seq all
;; call straight into this (mostly via (. clojure.lang.RT (method
;; args)), conj via the RT/conj slash form) -- these are exactly
;; RT.f90's own generic dispatchers (already reachable under
;; clotran.native, since every builtin is registered under both
;; namespaces).
(in-ns 'clojure.lang.RT)
(def first clotran.native/first)
(def next clotran.native/next)
(def more clotran.native/rest) ; core.clj's own `rest` calls (. clojure.lang.RT (more x)), not "rest"
(def cons clotran.native/cons)
(def conj clotran.native/conj)
(def seq clotran.native/seq)
(def count clotran.native/count)
(def nth clotran.native/nth)
(def get clotran.native/get)
(def assoc clotran.native/assoc)
(def contains clotran.native/contains?)
(def dissoc clotran.native/dissoc)
(def readString clotran.native/read-string)
(def keys clotran.native/keys)
(def vals clotran.native/vals)
(def nextID clotran.native/next-id)
(def uncheckedLongCast (fn* [x] x)) ; one canonical int kind here -- a cast is a no-op; fn*
                                     ; (the real special form), not fn (real core.clj's own
                                     ; macro, which doesn't exist yet -- clotran.clj loads
                                     ; before core.clj -- and needs even?/uncheckedLongCast
                                     ; itself once it does, a chicken-and-egg loop)
(in-ns 'clojure.core)

;; clojure.lang.Numbers: core.clj's own +/-/*//< etc. all call
;; straight into this (mostly via (. clojure.lang.Numbers (op x y))
;; or the Numbers/op slash form). No arbitrary-precision/overflow-
;; checked distinction here, so the plain and "P"/"unchecked_"-suffixed
;; variants real Clojure keeps apart all map to the same native op.
(in-ns 'clojure.lang.Numbers)
(def add clotran.native/+)
(def addP clotran.native/+)
(def unchecked_add clotran.native/+)
(def minus clotran.native/-) ; variadic already -- covers both 1-arg negation and 2-arg subtraction
(def minusP clotran.native/-)
(def unchecked_minus clotran.native/-)
(def multiply clotran.native/*)
(def multiplyP clotran.native/*)
(def unchecked_multiply clotran.native/*)
(def divide clotran.native//)
(def lt clotran.native/<)
(def lte clotran.native/<=)
(def gt clotran.native/>)
(def gte clotran.native/>=)
(def inc (fn* [x] (clotran.native/+ x 1))) ; fn*, not fn -- see uncheckedLongCast's own comment
(def incP (fn* [x] (clotran.native/+ x 1)))
(def unchecked_inc (fn* [x] (clotran.native/+ x 1)))
(def dec (fn* [x] (clotran.native/- x 1)))
(def decP (fn* [x] (clotran.native/- x 1)))
(def unchecked_dec (fn* [x] (clotran.native/- x 1)))
(def isZero (fn* [x] (clotran.native/= x 0)))
(def and clotran.native/bit-and) ; bit-and/bit-or/bit-xor/bit-and-not's real 2-arg definitions
(def or clotran.native/bit-or)
(def xor clotran.native/bit-xor)
(def not clotran.native/bit-not)
(def andNot clotran.native/bit-and-not)
(def quotient clotran.native/quot)
(def remainder clotran.native/rem)
(def shiftLeft clotran.native/bit-shift-left)
(def shiftRight clotran.native/bit-shift-right)
(def unsignedShiftRight clotran.native/unsigned-bit-shift-right)
(def equiv clotran.native/=)
(def isPos (fn* [x] (clotran.native/> x 0)))
(def isNeg (fn* [x] (clotran.native/< x 0)))
(def num (fn* [x] x)) ; no boxed-number tower here, so nothing to convert
(def rationalize (fn* [x] x)) ; no ratio type either
(def abs (fn* [x] (if (clotran.native/< x 0) (clotran.native/- x) x)))
(def max (fn* [x y] (if (clotran.native/> x y) x y)))
(def min (fn* [x y] (if (clotran.native/< x y) x y)))
(def testBit (fn* [x n] (clotran.native/= 1 (clotran.native/bit-and (clotran.native/bit-shift-right x n) 1))))
(def setBit (fn* [x n] (clotran.native/bit-or x (clotran.native/bit-shift-left 1 n))))
(def clearBit (fn* [x n] (clotran.native/bit-and-not x (clotran.native/bit-shift-left 1 n))))
(def flipBit (fn* [x n] (clotran.native/bit-xor x (clotran.native/bit-shift-left 1 n))))
;; The unchecked_int_* family: one integer kind here, so each is just
;; its ordinary counterpart (same simplification as unchecked_add etc).
(def unchecked_int_add clotran.native/+)
(def unchecked_int_subtract clotran.native/-)
(def unchecked_int_multiply clotran.native/*)
(def unchecked_int_divide clotran.native/quot)
(def unchecked_int_remainder clotran.native/rem)
(def unchecked_int_negate (fn* [x] (clotran.native/- x)))
(def unchecked_int_inc (fn* [x] (clotran.native/+ x 1)))
(def unchecked_int_dec (fn* [x] (clotran.native/- x 1)))
(def unchecked_divide clotran.native/quot)
(def unchecked_remainder clotran.native/rem)
(def unchecked_negate (fn* [x] (clotran.native/- x)))
(in-ns 'clojure.core)

;; clojure.lang.PersistentHashMap/create and friends: these take ONE
;; seq of alternating keys/vals (real Clojure's create(Object...) via
;; hash-map's own (. clojure.lang.PersistentHashMap (create keyvals))),
;; not varargs -- pointing them straight at the variadic native made
;; the whole seq a single KEY, so (hash-map "a" 1) built {("a" 1) nil}.
(in-ns 'clojure.lang.PersistentHashMap)
(def create (fn* [keyvals]
              (if keyvals
                (clotran.native/apply clotran.native/hash-map keyvals)
                (clotran.native/hash-map))))
(in-ns 'clojure.core)

(in-ns 'clojure.lang.PersistentArrayMap)
(def createAsIfByAssoc (fn* [keyvals]
                         (if keyvals
                           (clotran.native/apply clotran.native/hash-map keyvals)
                           (clotran.native/hash-map))))
(def EMPTY (clotran.native/hash-map))
(in-ns 'clojure.core)

(in-ns 'clojure.lang.PersistentHashSet)
(def create (fn* [items]
              (if items
                (clotran.native/apply clotran.native/hash-set items)
                (clotran.native/hash-set))))
(in-ns 'clojure.core)

;; clojure.lang.Compiler/macroexpand1: real macroexpand's own engine.
;; clotran's native macroexpand already expands to a fixed point, which
;; macroexpand's own loop then simply confirms.
(in-ns 'clojure.lang.Compiler)
(def macroexpand1 clotran.native/macroexpand)
(in-ns 'clojure.core)

;; clojure.lang.Keyword/intern: keyword's own real definition.
(in-ns 'clojure.lang.Keyword)
(def intern clotran.native/keyword)
(in-ns 'clojure.core)

;; clojure.lang.PersistentList: core.clj's own `list` is (. clojure.
;; lang.PersistentList creator) -- a static field holding an IFn,
;; called with however many items. clotran.native/list already is
;; exactly that (variadic).
(in-ns 'clojure.lang.PersistentList)
(def creator clotran.native/list)
(in-ns 'clojure.core)

;; clojure.lang.Util/equiv and /equals: core.clj calls these directly
;; via real Clojure's own Class/staticMethod syntax (e.g. inside
;; defn's and sigs' own bootstrap bodies) -- that syntax already
;; resolves generically through *ns*, same as any other qualified
;; symbol, as long as a real clojure.lang.Util namespace exists with
;; these defined in it. Both map to the same underlying value
;; equality clotran already has; real Clojure's own equiv/equals
;; differ (numeric tower vs. Object.equals), a distinction clotran
;; doesn't make yet.
(in-ns 'clojure.lang.Util)
(def equiv clotran.native/=)
(def equals clotran.native/=)
(def identical clotran.native/=) ; nil?/true?/false?/identical? all only ever compare against the nil/true/false singletons here, where = already agrees with real identity
(in-ns 'clojure.core)

;; instance?/isInstance: real core.clj's own instance? is (fn [c x]
;; (. c (isInstance x))) -- real reflection on a real Class object,
;; neither of which exists here. Left UNOVERRIDDEN: eval_instance_call
;; (Eval.f90) handles "isInstance" as a direct passthrough to the
;; native instance? builtin, so core.clj's own definition works as
;; literally written, as long as c evaluates to *something*
;; recognizable rather than a real Class -- these defs give every
;; pseudo-class core.clj's own (unmodified) source refers to by bare
;; name a value to evaluate to: a keyword matching its own name, which
;; the native instance?/isInstance pattern-matches against. Grows one
;; entry at a time as core.clj's walk turns up the next one it needs.
(in-ns 'clojure.lang.Symbol)
(def intern clotran.native/symbol) ; (Symbol/intern "name") -- clotran's symbol builtin already does exactly this
(in-ns 'clojure.core)
(def clojure.lang.Symbol :clojure.lang.Symbol)
(def clojure.lang.Keyword :clojure.lang.Keyword)
(def clojure.lang.IPersistentVector :clojure.lang.IPersistentVector)
(def clojure.lang.IPersistentMap :clojure.lang.IPersistentMap)
(def clojure.lang.ISeq :clojure.lang.ISeq)
(def clojure.lang.IMeta :clojure.lang.IMeta)
(def clojure.lang.Counted :clojure.lang.Counted)
(def clojure.lang.IPersistentList :clojure.lang.IPersistentList)
(def clojure.lang.IDeref :clojure.lang.IDeref)
(def clojure.lang.Var :clojure.lang.Var)
(def Number :Number)
(def Character :Character)
(def Integer :Integer)
(def Long :Long)
(def Short :Short)
(def Byte :Byte)
(def clojure.lang.BigInt :clojure.lang.BigInt)
(def BigInteger :BigInteger)
(def Double :Double)
(def Float :Float)
(def clojure.lang.BigDecimal :clojure.lang.BigDecimal)
(def BigDecimal :BigDecimal)
(def String :String)
(def Boolean :Boolean)
