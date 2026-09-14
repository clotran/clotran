;; Loaded LAST, after clojure/core.clj -- everything here is written in
;; terms of core.clj's own definitions (derive, isa?, defmethod), so it
;; cannot live in clotran.clj, which loads first. See eval_core_bootstrap
;; in Eval.f90.

(in-ns 'clojure.core)

;; ---------------------------------------------------------------------
;; The host type hierarchy.
;;
;; clotran has no Class objects: (class x) answers the KEYWORD naming
;; the type, and a bare class name in source evaluates to the keyword of
;; the same name (see eval_symbol in Eval.f90). That makes the JVM's
;; class/interface graph -- which real Clojure reads out of
;; Class.isAssignableFrom -- something that has to be declared instead.
;;
;; Declaring it with `derive` means clojure.core's own isa?, ancestors,
;; parents and prefer-method all work on these keywords unchanged, and
;; multimethod dispatch over host types (core.clj's print-method being
;; the big one) resolves exactly the way it does on the JVM.
;;
;; derive's 2-arity insists on namespaced keywords; these are class
;; names, whose dots are not a namespace. The 3-arity has no such
;; assertion, and calling it through alter-var-root on global-hierarchy
;; is literally what the 2-arity does.
(defn- derive-class
  [tag parent]
  (alter-var-root (var global-hierarchy) derive tag parent)
  nil)

(defn- derive-all
  [tag parents]
  (doseq [p parents] (derive-class tag p)))

;; Interfaces, bottom up. Everything reaches Object, so a method on
;; Object is a genuine catch-all that any more specific method beats.
(derive-all :clojure.lang.Seqable            [:Object])
(derive-all :clojure.lang.IObj               [:Object])
(derive-all :clojure.lang.Named              [:Object])
(derive-all :clojure.lang.IDeref             [:Object])
(derive-all :clojure.lang.Fn                 [:clojure.lang.IFn])
(derive-all :clojure.lang.IFn                [:Object])
(derive-all :java.util.Collection            [:Object])
(derive-all :java.util.Map                   [:Object])
(derive-all :java.util.List                  [:java.util.Collection])
(derive-all :java.util.Set                   [:java.util.Collection])
(derive-all :java.util.RandomAccess          [:Object])
(derive-all :Number                          [:Object])
(derive-all :clojure.lang.IPersistentCollection [:clojure.lang.Seqable])
(derive-all :clojure.lang.ISeq               [:clojure.lang.IPersistentCollection])
(derive-all :clojure.lang.IPersistentList    [:clojure.lang.ISeq :java.util.List])
(derive-all :clojure.lang.IPersistentVector  [:clojure.lang.IPersistentCollection
                                              :java.util.List :java.util.RandomAccess])
(derive-all :clojure.lang.IPersistentMap     [:clojure.lang.IPersistentCollection :java.util.Map])
(derive-all :clojure.lang.IPersistentSet     [:clojure.lang.IPersistentCollection :java.util.Set])
(derive-all :clojure.lang.Associative        [:clojure.lang.IPersistentCollection])

;; The concrete types (class x) actually answers. java.lang is the
;; implicit package: java.lang.Double and Double are one class, and the
;; bare spelling is the canonical keyword here (see class_keyword_name).
(derive-all :Boolean          [:Object])
(derive-all :String           [:Object])
(derive-all :Character        [:Object])
(derive-all :Long             [:Number])
(derive-all :Double           [:Number])
(derive-all :clojure.lang.Symbol      [:clojure.lang.Named :clojure.lang.IObj])
(derive-all :clojure.lang.Keyword     [:clojure.lang.Named :clojure.lang.IFn])
(derive-all :clojure.lang.PersistentList    [:clojure.lang.IPersistentList])
(derive-all :clojure.lang.LazySeq           [:clojure.lang.ISeq])
(derive-all :clojure.lang.PersistentVector  [:clojure.lang.IPersistentVector
                                             :clojure.lang.Associative])
(derive-all :clojure.lang.PersistentHashMap [:clojure.lang.IPersistentMap
                                             :clojure.lang.Associative])
(derive-all :clojure.lang.PersistentHashSet [:clojure.lang.IPersistentSet])
(derive-all :clojure.lang.Var         [:clojure.lang.IDeref :clojure.lang.IFn])
(derive-all :clojure.lang.Atom        [:clojure.lang.IDeref])
(derive-all :clojure.lang.Reduced     [:clojure.lang.IDeref])
(derive-all :clojure.lang.MultiFn     [:clojure.lang.IFn])
(derive-all :clojure.lang.AFn         [:clojure.lang.Fn])
(derive-all :java.io.StringWriter     [:Object])
(derive-all :Class                    [:Object])

;; ---------------------------------------------------------------------
;; Arrays.
;;
;; A clotran array is a REAL Fortran array -- any kind, any rank, laid
;; out column-major so the buffer can go straight to a Fortran library
;; (see NativeArray.f90). That differs from the JVM in one visible way,
;; and these three definitions are where it shows:
;;
;; On the JVM a multi-dimensional array is an array OF arrays, so
;; core.clj's aget recurses: (apply aget (aget a i) idxs). A Fortran
;; array is genuinely rank-N, one contiguous block, so the indices are
;; applied together instead. (aget m 1 2) is a single indexed read
;; rather than two.
;;
;; Indices start at 0, which is what aget promises -- Fortran arrays
;; may start at any bound, so nothing is translated, the array is
;; simply allocated from 0.
(def aget clotran.native/aget)
(def aset clotran.native/aset)
(def alength clotran.native/alength)
(def make-array clotran.native/make-array)
(def into-array clotran.native/into-array)

;; Kinds are keywords in the hierarchy, so a multimethod or protocol
;; can dispatch on the element type of an array.
(derive-all :clotran.native.real8-array   [:clotran.native/array])
(derive-all :clotran.native.real4-array   [:clotran.native/array])
(derive-all :clotran.native.int4-array    [:clotran.native/array])
(derive-all :clotran.native.int8-array    [:clotran.native/array])
(derive-all :clotran.native.logical-array [:clotran.native/array])
(derive-all :clotran.native.complex8-array [:clotran.native/array])
(derive-all :clotran.native.value-array   [:clotran.native/array])
(derive-all :clotran.native/array         [:Object])

;; ---------------------------------------------------------------------
;; print-method's fallback.
;;
;; Real Clojure's print-method methods live in core_print.clj, which
;; core.clj (load "core_print")s; that file isn't ported yet, which
;; would leave the multimethod with no methods at all and every
;; pr/prn/println/pr-str failing on dispatch. This one method covers
;; every type clotran has, by delegating to the native printer.
(defmethod print-method :default
  [x w]
  (. w append (if *print-readably*
                (clotran.native/pr-str x)
                (clotran.native/str x)))
  nil)
