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
(def inc (fn [x] (clotran.native/+ x 1)))
(def incP (fn [x] (clotran.native/+ x 1)))
(def unchecked_inc (fn [x] (clotran.native/+ x 1)))
(def dec (fn [x] (clotran.native/- x 1)))
(def decP (fn [x] (clotran.native/- x 1)))
(def unchecked_dec (fn [x] (clotran.native/- x 1)))
(def isZero (fn [x] (clotran.native/= x 0)))
(in-ns 'clojure.core)

;; clojure.lang.PersistentHashMap/create: hash-map's own real
;; definition is (. clojure.lang.PersistentHashMap (create keyvals)).
(in-ns 'clojure.lang.PersistentHashMap)
(def create clotran.native/hash-map)
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
