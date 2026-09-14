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
;; java.lang.Integer/Long's static fields, as case's int-range check
;; reads them. One integer kind here (see uncheckedLongCast), so both
;; report the same bounds.
(in-ns 'Integer)
(def MIN_VALUE -2147483648)
(def MAX_VALUE 2147483647)
(in-ns 'clojure.core)
(in-ns 'Long)
(def MIN_VALUE -2147483648)
(def MAX_VALUE 2147483647)
(in-ns 'clojure.core)

;; java.lang.Double's static fields, as core_print.clj's own Double
;; method compares against them. Real IEEE values (see the infinity
;; builtin), so a computed infinity really does match.
(in-ns 'Double)
(def POSITIVE_INFINITY (clotran.native/infinity 1))
(def NEGATIVE_INFINITY (clotran.native/infinity -1))
(in-ns 'clojure.core)

;; java.lang.reflect.Array, as core.clj's aget/aset/make-array reach
;; for it. There is no reflection here and no Java array -- these are
;; real Fortran arrays (see NativeArray.f90), so `type` is a kind name
;; ("real8", "int4", ...) rather than a Class.
(in-ns 'Array)
(def get clotran.native/aget)
(def set clotran.native/aset)
(def newInstance clotran.native/make-array)
(def getLength clotran.native/alength)
(in-ns 'clojure.core)

(in-ns 'clojure.lang.LazilyPersistentVector)
(def create clotran.native/vec) ; core.clj's own `vec` and variadic `vector` both route through this
(in-ns 'clojure.lang.RT)
;; (load "core_print") from clojure.core reaches here as
;; (clojure.lang.RT/load "clojure/core_print"): core.clj's own `load`
;; builds that classpath-relative path and strips the leading slash.
;; There's no classpath here, so the path names a file under src/clj
;; directly. load-file is a special form, hence a wrapper, not an alias.
(def load
  (fn* [path]
    ;; *ns* must not leak: a loaded file starts with its own (ns ...)
    ;; or (in-ns ...), and core.clj carries on in clojure.core right
    ;; after the (load "core/protocols") that switched it. Real
    ;; RT.load pushes a thread binding of *ns* for exactly this.
    (let* [prev *ns*
           result (load-file (clotran.native/resource-path path))]
      (in-ns prev)
      result)))
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
(def subvec clotran.native/subvec)
(def pop clotran.native/pop)
(def peek clotran.native/peek)
(def alength clotran.native/alength)
(def seqToTypedArray clotran.native/into-array)
(def find clotran.native/find-entry)
(def toArray clotran.native/vec) ; no array type here -- a vector is what an Object[] becomes
(def keys clotran.native/keys)
(def vals clotran.native/vals)
(def nextID clotran.native/next-id)
(def isReduced clotran.native/reduced?)
(def booleanCast (fn* [x] (if x true false))) ; nil and false are the only falsey values
(def longCast (fn* [x] x)) ; one canonical int kind here, so every cast is a no-op
(def intCast (fn* [x] x))
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

;; clojure.lang.Namespace's statics. A namespace is represented by its
;; own name symbol here -- there's no first-class Namespace value (and
;; *ns* is a symbol for the same reason), so ns-name is just .getName
;; on that symbol, which already works.
(in-ns 'clojure.lang.Namespace)
(def find clotran.native/find-ns-sym)
(def findOrCreate clotran.native/create-ns-sym)
(def all clotran.native/all-ns-syms)
(def remove (fn* [n] nil)) ; nothing here ever unloads a namespace
(in-ns 'clojure.core)

;; java.lang.System: only getProperty, and only for the handful of
;; properties core.clj reads while setting up *file*/line separators.
(in-ns 'System)
(def getProperty (fn* [k] (if (clotran.native/= k "line.separator") "\n" nil)))
;; No object identity distinct from value here, so the value hash is the
;; only answer available. core_print.clj uses it to tag an unprintable
;; object (#object[C 0x... "..."]).
(def identityHashCode clotran.native/hash)
(in-ns 'clojure.core)

;; java.lang.Thread: core.clj only reaches for the context classloader
;; and (much later) agent threads. Neither exists here.
(in-ns 'Thread)
(def currentThread (fn* [] nil))
(in-ns 'clojure.core)

;; The dynamic vars real Clojure's RUNTIME (RT.java) creates before
;; core.clj is even read -- core.clj only ever attaches docstrings to
;; them (add-doc-and-meta), so without these every one of those forms
;; failed with "Unable to resolve var". Values match RT's defaults;
;; the stream ones are placeholders, since there's no writer object
;; here yet (see *out* in NOTES.md).
(def ^:dynamic *out* nil)
(def ^:dynamic *err* nil)
(def ^:dynamic *in* nil)
(def ^:dynamic *command-line-args* nil)
(def ^:dynamic *assert* true)
(def ^:dynamic *read-eval* true)
(def ^:dynamic *print-meta* false)
(def ^:dynamic *print-dup* false)
(def ^:dynamic *print-readably* true)
(def ^:dynamic *flush-on-newline* true)
(def ^:dynamic *file* "NO_SOURCE_PATH")
(def ^:dynamic *compile-path* nil)
(def ^:dynamic *compile-files* false)
(def ^:dynamic *warn-on-reflection* false)
(def ^:dynamic *unchecked-math* false)
(def ^:dynamic *compiler-options* nil)
(def ^:dynamic *agent* nil)
(def *clojure-version* {:major 1 :minor 12 :incremental 0 :qualifier nil})
(def *data-readers* {})
;; in-ns/load-file are special forms in Eval.f90, not functions, but
;; core.clj still hangs a docstring on each via (var in-ns) -- so the
;; vars have to exist. The special-form dispatch runs first, so these
;; placeholders never actually get called.
(def in-ns nil)
(def load-file nil)
(def *default-data-reader-fn* nil)

;; clojure.lang.Var/pushThreadBindings and popThreadBindings: what
;; core.clj's own push-thread-bindings/pop-thread-bindings (and so
;; `binding`) call into. See Eval.f90 for the stack itself.
(in-ns 'clojure.lang.Var)
(def intern clotran.native/intern-var)
(def find clotran.native/find-var)
(def pushThreadBindings clotran.native/push-thread-bindings)
(def popThreadBindings clotran.native/pop-thread-bindings)
(in-ns 'clojure.core)

;; The java.lang seq "classes" real core.clj builds its infinite and
;; ranged sequences from -- range/iterate/repeat/cycle are each just a
;; call to one of these. Each is written here with the SAME lazy-seq
;; primitive core.clj itself uses, (new clojure.lang.LazySeq (fn* []
;; ...)), spelled out longhand because clotran.clj loads before
;; core.clj defines the `lazy-seq` macro. Nothing is realized until
;; something asks, so (range) and (iterate f x) are genuinely infinite
;; and (take 5 ...) of one costs 5 steps.
(in-ns 'clojure.lang.Iterate)
(def create (fn* create [f x]
              (clotran.native/cons x (new clojure.lang.LazySeq (fn* [] (create f (f x)))))))
(in-ns 'clojure.core)

(in-ns 'clojure.lang.Repeat)
(def create (fn* create
              ([x] (clotran.native/cons x (new clojure.lang.LazySeq (fn* [] (create x)))))
              ([n x] (if (clotran.native/> n 0)
                       (clotran.native/cons
                        x
                        (new clojure.lang.LazySeq (fn* [] (create (clotran.native/- n 1) x))))
                       nil))))
(in-ns 'clojure.core)

(in-ns 'clojure.lang.Cycle)
(def create (fn* [coll]
              ((fn* step [remaining]
                 (if (clotran.native/seq remaining)
                   (clotran.native/cons
                    (clotran.native/first remaining)
                    (new clojure.lang.LazySeq (fn* [] (step (clotran.native/rest remaining)))))
                   (if (clotran.native/seq coll)
                     (step coll)
                     nil)))
               coll)))
(in-ns 'clojure.core)

(in-ns 'clojure.lang.LongRange)
(def create (fn* create
              ([end] (create 0 end 1))
              ([start end] (create start end 1))
              ([start end step]
               (if (if (clotran.native/> step 0)
                     (clotran.native/< start end)
                     (clotran.native/> start end))
                 (clotran.native/cons
                  start
                  (new clojure.lang.LazySeq
                       (fn* [] (create (clotran.native/+ start step) end step))))
                 nil))))
(in-ns 'clojure.core)

(in-ns 'clojure.lang.Range)
(def create clojure.lang.LongRange/create)
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

;; PersistentTreeMap: same story as PersistentTreeSet below --
;; sorted-map is an ordinary hash map here, so lookups are right but
;; ORDER IS NOT SORTED. clojure.test's report counters go through it.
(in-ns 'clojure.lang.PersistentTreeMap)
(def create (fn* [keyvals]
              (if keyvals
                (clotran.native/apply clotran.native/hash-map keyvals)
                (clotran.native/hash-map))))
(def EMPTY (clotran.native/hash-map))
(in-ns 'clojure.core)

;; PersistentTreeSet: clotran has no sorted collections, so sorted-set
;; is an ordinary hash set -- correct membership, NOT sorted order.
(in-ns 'clojure.lang.PersistentTreeSet)
(def create (fn* [items]
              (if items
                (clotran.native/apply clotran.native/hash-set items)
                (clotran.native/hash-set))))
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
;; gen-interface: on the JVM defprotocol emits a real interface for
;; each protocol, which a deftype can then implement directly. There
;; are no host interfaces here, so nothing is emitted -- a protocol's
;; :on-interface never matches anything, and find-protocol-impl falls
;; through to the :impls table, which is the only place an
;; implementation can live anyway. genclass.clj (where this really
;; lives) is JVM bytecode generation and is not ported.
;; A macro, as genclass.clj's own is -- its :methods argument is a
;; literal vector of munged method names, which would fail to
;; resolve if it were evaluated.
(defmacro gen-interface [& opts] nil)

;; clojure.lang.LockingTransaction: dosync/sync. There is no STM here
;; and nothing to coordinate with -- a Ref is an Atom (see eval_new) --
;; so a transaction is just "run the body". This has to come back for
;; real when the concurrency model does; see NOTES.md.
(in-ns 'clojure.lang.LockingTransaction)
(def runInTransaction (fn* [f] (f)))
(def isRunning (fn* [] false))
(in-ns 'clojure.core)

;; clojure.lang.Compiler$HostExpr: how defn's own resolve-tag asks
;; whether a ^Type hint names a primitive or a real class. There are no
;; classes here, so both answer nil, and defn leaves the tag exactly as
;; written -- which is what we want, since a type hint is advisory.
;; (Reached only once the reader started normalising ^Type into
;; {:tag Type}, as real Clojure's reader does.)
(in-ns 'clojure.lang.Compiler$HostExpr)
(def maybeSpecialTag (fn* [tag] nil))
(def maybeClass (fn* [tag string-ok] nil))
(in-ns 'clojure.core)

;; clojure.lang.Compiler: only the name munging defprotocol needs.
(in-ns 'clojure.lang.Compiler)
(def munge clotran.native/munge)
(def maybeResolveIn clotran.native/resolve-var-in) ; what ns-resolve/resolve bottom out in
(in-ns 'clojure.core)

(in-ns 'clojure.lang.Util)
(def equiv clotran.native/=)
(def equals clotran.native/=)
(def identical clotran.native/=) ; nil?/true?/false?/identical? all only ever compare against the nil/true/false singletons here, where = already agrees with real identity
(def hasheq clotran.native/hash)
(def classOf clotran.native/class)
(def hash clotran.native/hash)
(in-ns 'clojure.core)

;; java.lang.String's statics. format covers only the conversions
;; core.clj and core_print.clj actually use (%s %d %x %n %%) -- the
;; full java.util.Formatter grammar (widths, flags, argument indexes)
;; is not here.
(in-ns 'String)
(def format clotran.native/format)
(def valueOf clotran.native/str)
(in-ns 'clojure.core)

;; instance?/isInstance: real core.clj's own instance? is (fn [c x]
;; (. c (isInstance x))) -- real reflection on a real Class object,
;; neither of which exists here. Left UNOVERRIDDEN: eval_instance_call
;; (Eval.f90) handles "isInstance" as a direct passthrough to the
;; native instance? builtin, so core.clj's own definition works as
;; literally written, as long as c evaluates to *something*
;; recognizable rather than a real Class. A bare class name now
;; evaluates to the keyword of the same name on its own (eval_symbol),
;; so the long hand-written list of (def clojure.lang.ISeq
;; :clojure.lang.ISeq) forms that used to live here is gone.
(in-ns 'clojure.lang.Symbol)
(def intern clotran.native/symbol) ; (Symbol/intern "name") -- clotran's symbol builtin already does exactly this
(in-ns 'clojure.core)
