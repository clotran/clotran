;; Specs for clojure.core FUNCTIONS, for scripts/fuzz --fns.
;;
;; Clojure specs its macros (src/clj/clojure/core/specs/alpha.clj) and
;; none of its functions, so these are ours: each :args says what the
;; docstring says a function takes, and each :ret what it says comes back.
;; They are claims about Clojure, so they are checked against clj, not
;; trusted -- the fuzzer reports a clj answer that does not conform to its
;; :ret as a SPEC error, and a function clj throws on too often as an
;; :args spec too loose.
;;
;; The arguments are VALUES. A function argument is a FnRef: a small form
;; (inc, even?, (fn [x] ...)) the call is written with, since a function
;; value cannot be printed into a program. Every other value is quoted.
(ns fuzz.specs
  (:require [clojure.spec.alpha :as s]
            [clojure.test.check.generators :as g]))

(def ^:private before
  "What the registry held before this file: the macro specs, among others"
  (set (keys (s/registry))))

(defrecord FnRef [form])
(defn fnref? [x] (instance? FnRef x))
(defn fns [& forms] (g/elements (mapv ->FnRef forms)))

;;; ---- values ---------------------------------------------------------

(def g-small (g/choose -5 12))
(def g-idx (g/choose 0 6))
(def g-kw (g/elements [:a :b :c :d]))
(def g-scalar (g/one-of [g-small g-kw (g/elements [nil true false "s" "" \c 1.5 -0.0 2/3 'sym])]))
(def g-ints (g/vector g-small 0 7))
(def g-int-coll
  (g/one-of [g-ints
             (g/fmap #(apply list %) g-ints)
             (g/fmap set g-ints)
             (g/return nil)
             (g/fmap #(list 'range %) (g/choose 0 6))]))   ; a form, quoted away below
(def g-map (g/fmap #(into {} %) (g/vector (g/tuple g-kw g-small) 0 4)))
(def g-any (g/one-of [g-scalar g-ints g-map (g/fmap set g-ints) (g/fmap #(apply list %) g-ints)]))

(s/def ::int (s/with-gen int? (constantly g-small)))
(s/def ::idx (s/with-gen nat-int? (constantly g-idx)))
(s/def ::kw (s/with-gen keyword? (constantly g-kw)))
(s/def ::any (s/with-gen any? (constantly g-any)))
(s/def ::ints (s/with-gen (s/nilable (s/coll-of int?)) (constantly (g/one-of [g-ints (g/fmap #(apply list %) g-ints) (g/fmap set g-ints) (g/return nil)]))))
(s/def ::vec (s/with-gen (s/coll-of int? :kind vector?) (constantly g-ints)))
(s/def ::map (s/with-gen (s/map-of keyword? int?) (constantly g-map)))
(s/def ::str (s/with-gen string? (constantly (g/elements ["" "a" "abc" "hello" "a,b,c"]))))
;; functions, by what they take and give
(s/def ::f1 (s/with-gen fnref? (constantly (fns 'inc 'dec '- '(fn [x] (* x 2)) '(fn [x] (mod x 3))))))
(s/def ::pred (s/with-gen fnref? (constantly (fns 'even? 'odd? 'pos? 'neg? 'zero? '(fn [x] (> x 3))))))
(s/def ::f2 (s/with-gen fnref? (constantly (fns '+ '- '* 'max 'min '(fn [a b] (+ a (* 2 b)))))))
(s/def ::fkeep (s/with-gen fnref? (constantly (fns '(fn [x] (when (odd? x) (* x x))) '(fn [x] (when (pos? x) x))))))
(s/def ::fidx (s/with-gen fnref? (constantly (fns '+ '- '(fn [i x] (* i x)) 'vector))))

;;; ---- the functions --------------------------------------------------
;; :ret is only what the docstring promises, so a wrong one is a finding

(s/fdef clojure.core/first :args (s/cat :coll ::ints) :ret (s/nilable int?))
(s/fdef clojure.core/second :args (s/cat :coll ::ints) :ret (s/nilable int?))
(s/fdef clojure.core/last :args (s/cat :coll ::ints) :ret (s/nilable int?))
(s/fdef clojure.core/butlast :args (s/cat :coll ::ints) :ret (s/nilable seq?))
(s/fdef clojure.core/rest :args (s/cat :coll ::ints) :ret seq?)
(s/fdef clojure.core/next :args (s/cat :coll ::ints) :ret (s/nilable seq?))
(s/fdef clojure.core/nthrest :args (s/cat :coll ::ints :n ::idx))
(s/fdef clojure.core/nthnext :args (s/cat :coll ::ints :n ::idx) :ret (s/nilable seq?))
(s/fdef clojure.core/count :args (s/cat :coll ::ints) :ret nat-int?)
(s/fdef clojure.core/seq :args (s/cat :coll ::ints) :ret (s/nilable seq?))
(s/fdef clojure.core/empty? :args (s/cat :coll ::ints) :ret boolean?)
(s/fdef clojure.core/not-empty :args (s/cat :coll ::ints))
(s/fdef clojure.core/vec :args (s/cat :coll ::ints) :ret vector?)
(s/fdef clojure.core/set :args (s/cat :coll ::ints) :ret set?)
(s/fdef clojure.core/reverse :args (s/cat :coll ::ints) :ret seq?)
(s/fdef clojure.core/sort :args (s/cat :coll ::ints) :ret seq?)
(s/fdef clojure.core/sort-by :args (s/cat :f ::f1 :coll ::ints) :ret seq?)
(s/fdef clojure.core/distinct :args (s/cat :coll ::ints) :ret seq?)
(s/fdef clojure.core/dedupe :args (s/cat :coll ::ints) :ret seq?)
(s/fdef clojure.core/frequencies :args (s/cat :coll ::ints) :ret map?)
(s/fdef clojure.core/group-by :args (s/cat :f ::f1 :coll ::ints) :ret map?)
(s/fdef clojure.core/partition :args (s/cat :n (s/with-gen pos-int? (constantly (g/choose 1 4))) :coll ::ints) :ret seq?)
(s/fdef clojure.core/partition-all :args (s/cat :n (s/with-gen pos-int? (constantly (g/choose 1 4))) :coll ::ints) :ret seq?)
(s/fdef clojure.core/partition-by :args (s/cat :f ::pred :coll ::ints) :ret seq?)
(s/fdef clojure.core/split-at :args (s/cat :n ::idx :coll ::ints) :ret vector?)
(s/fdef clojure.core/split-with :args (s/cat :p ::pred :coll ::ints) :ret vector?)
(s/fdef clojure.core/take :args (s/cat :n ::int :coll ::ints) :ret seq?)
(s/fdef clojure.core/drop :args (s/cat :n ::int :coll ::ints) :ret seq?)
(s/fdef clojure.core/take-while :args (s/cat :p ::pred :coll ::ints) :ret seq?)
(s/fdef clojure.core/drop-while :args (s/cat :p ::pred :coll ::ints) :ret seq?)
(s/fdef clojure.core/take-last :args (s/cat :n ::int :coll ::ints) :ret (s/nilable seq?))
(s/fdef clojure.core/drop-last :args (s/cat :n ::idx :coll ::ints) :ret seq?)
(s/fdef clojure.core/take-nth :args (s/cat :n (s/with-gen pos-int? (constantly (g/choose 1 4))) :coll ::ints) :ret seq?)
(s/fdef clojure.core/interpose :args (s/cat :sep ::any :coll ::ints) :ret seq?)
(s/fdef clojure.core/interleave :args (s/cat :a ::ints :b ::ints) :ret seq?)
(s/fdef clojure.core/concat :args (s/cat :a ::ints :b ::ints) :ret seq?)
(s/fdef clojure.core/map :args (s/cat :f ::f1 :coll ::ints) :ret seq?)
(s/fdef clojure.core/mapv :args (s/cat :f ::f1 :coll ::ints) :ret vector?)
(s/fdef clojure.core/map-indexed :args (s/cat :f ::fidx :coll ::ints) :ret seq?)
(s/fdef clojure.core/mapcat :args (s/cat :f (s/with-gen fnref? (constantly (fns 'vector 'list '(fn [x] (range (mod x 3)))))) :coll ::ints) :ret seq?)
(s/fdef clojure.core/keep :args (s/cat :f ::fkeep :coll ::ints) :ret seq?)
(s/fdef clojure.core/keep-indexed :args (s/cat :f (s/with-gen fnref? (constantly (fns '(fn [i x] (when (even? i) x))))) :coll ::ints) :ret seq?)
(s/fdef clojure.core/filter :args (s/cat :p ::pred :coll ::ints) :ret seq?)
(s/fdef clojure.core/filterv :args (s/cat :p ::pred :coll ::ints) :ret vector?)
(s/fdef clojure.core/remove :args (s/cat :p ::pred :coll ::ints) :ret seq?)
(s/fdef clojure.core/reduce :args (s/cat :f ::f2 :init ::int :coll ::ints))
(s/fdef clojure.core/reductions :args (s/cat :f ::f2 :init ::int :coll ::ints) :ret seq?)
(s/fdef clojure.core/some :args (s/cat :p ::pred :coll ::ints))
(s/fdef clojure.core/every? :args (s/cat :p ::pred :coll ::ints) :ret boolean?)
(s/fdef clojure.core/not-any? :args (s/cat :p ::pred :coll ::ints) :ret boolean?)
(s/fdef clojure.core/not-every? :args (s/cat :p ::pred :coll ::ints) :ret boolean?)
(s/fdef clojure.core/into :args (s/cat :to (s/with-gen coll? (constantly (g/elements [[] () #{} [9] '(9)]))) :from ::ints) :ret coll?)
(s/fdef clojure.core/conj :args (s/cat :coll (s/with-gen coll? (constantly (g/one-of [g-ints (g/fmap #(apply list %) g-ints) (g/fmap set g-ints)]))) :x ::int) :ret coll?)
(s/fdef clojure.core/cons :args (s/cat :x ::any :coll ::ints) :ret seq?)
(s/fdef clojure.core/zipmap :args (s/cat :ks ::ints :vs ::ints) :ret map?)
(s/fdef clojure.core/get :args (s/cat :m ::map :k ::kw :nf ::int))
(s/fdef clojure.core/assoc :args (s/cat :m ::map :k ::kw :v ::int) :ret map?)
(s/fdef clojure.core/dissoc :args (s/cat :m ::map :k ::kw) :ret map?)
(s/fdef clojure.core/select-keys :args (s/cat :m ::map :ks (s/with-gen vector? (constantly (g/vector g-kw 0 3)))) :ret map?)
(s/fdef clojure.core/merge :args (s/cat :a ::map :b ::map) :ret map?)
(s/fdef clojure.core/merge-with :args (s/cat :f ::f2 :a ::map :b ::map) :ret map?)
(s/fdef clojure.core/update :args (s/cat :m ::map :k ::kw :f (s/with-gen fnref? (constantly (fns '(fnil inc 0) '(fnil - 0))))) :ret map?)
(s/fdef clojure.core/contains? :args (s/cat :m ::map :k ::kw) :ret boolean?)
(s/fdef clojure.core/find :args (s/cat :m ::map :k ::kw))
(s/fdef clojure.core/keys :args (s/cat :m ::map) :ret (s/nilable seq?))
(s/fdef clojure.core/vals :args (s/cat :m ::map) :ret (s/nilable seq?))
(s/fdef clojure.core/update-vals :args (s/cat :m ::map :f ::f1) :ret map?)
(s/fdef clojure.core/update-keys :args (s/cat :m ::map :f (s/with-gen fnref? (constantly (fns 'name 'str)))) :ret map?)
(s/fdef clojure.core/nth :args (s/cat :v ::vec :i ::idx :nf ::int))
(s/fdef clojure.core/peek :args (s/cat :v ::vec))
(s/fdef clojure.core/subvec :args (s/cat :v ::vec :start ::idx) :ret vector?)
(s/fdef clojure.core/assoc-in :args (s/cat :m ::map :ks (s/with-gen vector? (constantly (g/vector g-kw 1 2))) :v ::int) :ret map?)
(s/fdef clojure.core/get-in :args (s/cat :m ::map :ks (s/with-gen vector? (constantly (g/vector g-kw 0 2)))))
(s/fdef clojure.core/range :args (s/cat :start ::int :end ::int :step (s/with-gen int? (constantly (g/elements [1 2 3 -1 -2])))) :ret seq?)
(s/fdef clojure.core/repeat :args (s/cat :n ::idx :x ::any) :ret seq?)
(s/fdef clojure.core/flatten :args (s/cat :x (s/with-gen sequential? (constantly (g/elements [[1 [2 [3]] 4] '(1 (2 3)) [] [[[]]] [1 #{2} {:a 3}]])))) :ret sequential?)
(s/fdef clojure.core/max :args (s/cat :x ::int :y ::int) :ret int?)
(s/fdef clojure.core/min :args (s/cat :x ::int :y ::int) :ret int?)
(s/fdef clojure.core/quot :args (s/cat :x ::int :y ::int))
(s/fdef clojure.core/rem :args (s/cat :x ::int :y ::int))
(s/fdef clojure.core/mod :args (s/cat :x ::int :y ::int))
(s/fdef clojure.core/compare :args (s/cat :x ::int :y ::int) :ret int?)
(s/fdef clojure.core/abs :args (s/cat :x ::int))
(s/fdef clojure.core/str :args (s/cat :a ::any :b ::any) :ret string?)
;; the docstring: start inclusive, within the string
(s/fdef clojure.core/subs :args (s/and (s/cat :s ::str :start ::idx) #(<= (:start %) (count (:s %)))) :ret string?)
(s/fdef clojure.core/name :args (s/cat :x (s/with-gen (s/or :k keyword? :s string?) (constantly (g/one-of [g-kw (g/elements ["x" ""])])))) :ret string?)
(s/fdef clojure.core/= :args (s/cat :x ::any :y ::any) :ret boolean?)
(s/fdef clojure.core/nil? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/some? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/coll? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/seq? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/sequential? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/associative? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/counted? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/seqable? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/number? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/integer? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/ratio? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/string? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/keyword? :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/boolean :args (s/cat :x ::any) :ret boolean?)
(s/fdef clojure.core/empty :args (s/cat :x ::any))
(s/fdef clojure.core/not-empty :args (s/cat :x ::any))

(def fuzz-fns
  "Every function spec'd above, by name."
  (->> (s/registry) keys (remove before) (filter symbol?) (filter #(= "clojure.core" (namespace %))) sort vec))
