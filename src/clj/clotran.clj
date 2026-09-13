;; clotran.clj -- clotran's own replacements for the handful of
;; clojure.core vars whose real definitions (in core.clj, loaded
;; first, completely unmodified -- see src/clj/clojure/core.clj) call
;; real JVM interop clotran doesn't have. Loaded immediately after
;; core.clj, still inside the clojure.core namespace (no (ns ...) of
;; its own -- these really are overrides of clojure.core's own vars,
;; landing in the same namespace core.clj just populated, not a
;; separate one), so each def below simply replaces core.clj's own
;; binding of the same name.
;;
;; Mirrors real ClojureScript's own relationship to JVM Clojure:
;; cljs.core is a separate, independently-implemented file, not a
;; conditionalized fork of core.clj (JVM core.clj has no reader
;; conditionals at all -- #?(...) is for later, cross-host *libraries*
;; like clojure.spec.alpha, not for the two cores themselves). This
;; file is the same idea, scoped down: clotran's evaluator already
;; runs ordinary, portable Clojure logic unmodified (unlike a JS
;; runtime, which needs literally everything reimplemented), so only
;; the forms below -- the ones that actually hit real interop -- need
;; a replacement. Grows one entry at a time as walking further into
;; core.clj turns up the next thing that needs one (see NOTES.md).
;;
;; Docstrings/arglists mirror core.clj's own corresponding def as
;; closely as possible, so a diff against the matching core.clj
;; section stays easy to read side by side -- only the body changes,
;; swapping the interop call for the equivalent clotran.native one
;; (RT.f90's generic dispatchers, reachable under this name even once
;; clojure.core/first etc. point elsewhere -- see NOTES.md).

(def
 ^{:arglists '([& items])
   :doc "Creates a new list containing the items."
   :added "1.0"}
  list clotran.native/list)

(def
 ^{:arglists '([x seq])
   :doc "Returns a new seq where x is the first element and seq is
   the rest."
   :added "1.0"
   :static true}
 cons (fn* ^:static cons [x seq] (clotran.native/cons x seq)))

;; let/loop/fn: same bootstrap shape as core.clj's own (a macro built
;; directly from fn*, before destructuring exists to write a nicer
;; one) -- params drop &form/&env, which clotran's macro calls never
;; supply (no separate compile step to supply them from); fn also
;; drops the (.withMeta ... (.meta &form)) copy-through this project
;; doesn't have a Var/metadata plumbing story for yet (a real,
;; documented scope decision, not an oversight -- see NOTES.md).
(def
  ^{:macro true
    :added "1.0"}
  let (fn* let [& decl] (cons 'let* decl)))

(def
 ^{:macro true
   :added "1.0"}
 loop (fn* loop [& decl] (cons 'loop* decl)))

(def
 ^{:macro true
   :added "1.0"}
 fn (fn* fn [& decl] (cons 'fn* decl)))

(def
 ^{:arglists '([coll])
   :doc "Returns the first item in the collection. Calls seq on its
    argument. If coll is nil, returns nil."
   :added "1.0"
   :static true}
 first (fn ^:static first [coll] (clotran.native/first coll)))

(def
 ^{:arglists '([coll])
   :tag clojure.lang.ISeq
   :doc "Returns a seq of the items after the first. Calls seq on its
  argument.  If there are no more items, returns nil."
   :added "1.0"
   :static true}
 next (fn ^:static next [x] (clotran.native/next x)))

(def
 ^{:arglists '([coll])
   :tag clojure.lang.ISeq
   :doc "Returns a possibly empty seq of the items after the first. Calls seq on its
  argument."
   :added "1.0"
   :static true}
 rest (fn ^:static rest [x] (clotran.native/rest x)))

(def
 ^{:arglists '([] [coll] [coll x] [coll x & xs])
   :doc "conj[oin]. Returns a new collection with the xs
    'added'. (conj nil item) returns (item).
    (conj coll) returns coll. (conj) returns [].
    The 'addition' may happen at different 'places' depending
    on the concrete type."
   :added "1.0"
   :static true}
 conj (fn ^:static conj
        ([] [])
        ([coll] coll)
        ([coll x] (clotran.native/conj coll x))
        ([coll x & xs]
         (if xs
           (recur (clotran.native/conj coll x) (first xs) (next xs))
           (clotran.native/conj coll x)))))

(def
 ^{:arglists '(^clojure.lang.ISeq [coll])
   :doc "Returns a seq on the collection. If the collection is
    empty, returns nil.  (seq nil) returns nil. seq also works on
    Strings, native Java arrays (of reference types) and any objects
    that implement Iterable. Note that seqs cache values, thus seq
    should not be used on any Iterable whose iterator repeatedly
    returns the same mutable object."
   :tag clojure.lang.ISeq
   :added "1.0"
   :static true}
 seq (fn ^:static seq ^clojure.lang.ISeq [coll] (clotran.native/seq coll)))
