;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(in-ns 'clojure.core)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; printing ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(import )

(set! *warn-on-reflection* true)
(def ^:dynamic
 ^{:doc "*print-length* controls how many items of each collection the
  printer will print. If it is bound to logical false, there is no
  limit. Otherwise, it must be bound to an integer indicating the maximum
  number of items of each collection to print. If a collection contains
  more items, the printer will print items up to the limit followed by
  '...' to represent the remaining items. The root binding is nil
  indicating no limit."
   :added "1.0"}
 *print-length* nil)

(def ^:dynamic
 ^{:doc "*print-level* controls how many levels deep the printer will
  print nested objects. If it is bound to logical false, there is no
  limit. Otherwise, it must be bound to an integer indicating the maximum
  level to print. Each argument to print is at level 0; if an argument is a
  collection, its items are at level 1; and so on. If an object is a
  collection and is at a level greater than or equal to the value bound to
  *print-level*, the printer prints '#' to represent it. The root binding
  is nil indicating no limit."
   :added "1.0"}
 *print-level* nil)

(def ^:dynamic *verbose-defrecords* false)

(def ^:dynamic
 ^{:doc "*print-namespace-maps* controls whether the printer will print
  namespace map literal syntax. It defaults to false, but the REPL binds
  to true."
   :added "1.9"}
 *print-namespace-maps* false)

(defn- print-sequential [^clotran.host.string begin, print-one, ^clotran.host.string sep, ^clotran.host.string end, sequence, ^clotran.host.writer w]
  (binding [*print-level* (and (not *print-dup*) *print-level* (dec *print-level*))]
    (if (and *print-level* (neg? *print-level*))
      (.write w "#")
      (do
        (.write w begin)
        (when-let [xs (seq sequence)]
          (if (and (not *print-dup*) *print-length*)
            (loop [[x & xs] xs
                   print-length *print-length*]
              (if (zero? print-length)
                (.write w "...")
                (do
                  (print-one x w)
                  (when xs
                    (.write w sep)
                    (recur xs (dec print-length))))))
            (loop [[x & xs] xs]
              (print-one x w)
              (when xs
                (.write w sep)
                (recur xs)))))
        (.write w end)))))

(defn- print-meta [o, ^clotran.host.writer w]
  (when-let [m (meta o)]
    (when (and (pos? (count m))
               (or *print-dup*
                   (and *print-meta* *print-readably*)))
      (.write w "^")
      (if (and (= (count m) 1) (:tag m))
          (pr-on (:tag m) w)
          (pr-on m w))
      (.write w " "))))

(defn print-simple [o, ^clotran.host.writer w]
  (print-meta o w)
  (.write w (str o)))

(defmethod print-method :default [o, ^clotran.host.writer w]
  (if (instance? clotran.host.i_obj o)
    (print-method (vary-meta o #(dissoc % :type)) w)
    (print-simple o w)))

(defmethod print-method nil [o, ^clotran.host.writer w]
  (.write w "nil"))

(defmethod print-dup nil [o w] (print-method o w))

(defn print-ctor [o print-args ^clotran.host.writer w]
  (.write w "#=(")
  (.write w (.getName ^clotran.host.class (class o)))
  (.write w ". ")
  (print-args o w)
  (.write w ")"))

(defn- print-tagged-object [o rep ^clotran.host.writer w]
  (when (instance? clotran.host.i_meta o)
    (print-meta o w))
  (.write w "#object[")
  (let [c (class o)]
    (if (.isArray c)
      (print-method (.getName c) w)
      (.write w (.getName c))))
  (.write w " ")
  (.write w (format "0x%x " (clotran.host.system/identityHashCode o)))
  (print-method rep w)
  (.write w "]"))

(defn- print-object [o, ^clotran.host.writer w]
  (print-tagged-object o (str o) w))

(defmethod print-method clotran.host.value [o, ^clotran.host.writer w]
  (print-object o w))

(defmethod print-method clotran.host.keyword [o, ^clotran.host.writer w]
  (.write w (str o)))

(defmethod print-dup clotran.host.keyword [o w] (print-method o w))

(defmethod print-method clotran.host.number [o, ^clotran.host.writer w]
  (.write w (str o)))

(defmethod print-method clotran.host.real8 [o, ^clotran.host.writer w]
  (cond
    (= clotran.host.real8/POSITIVE_INFINITY o) (.write w "##Inf")
    (= clotran.host.real8/NEGATIVE_INFINITY o) (.write w "##-Inf")
    (.isNaN ^clotran.host.real8 o) (.write w "##NaN")
    :else (.write w (str o))))

(defmethod print-method clotran.host.real4 [o, ^clotran.host.writer w]
  (cond
    (= clotran.host.real4/POSITIVE_INFINITY o) (.write w "##Inf")
    (= clotran.host.real4/NEGATIVE_INFINITY o) (.write w "##-Inf")
    (.isNaN ^clotran.host.real4 o) (.write w "##NaN")
    :else (.write w (str o))))

(defmethod print-dup clotran.host.number [o, ^clotran.host.writer w]
  (print-ctor o
              (fn [o w]
                  (print-dup (str o) w))
              w))

(defmethod print-dup clotran.host.fn [o, ^clotran.host.writer w]
  (print-ctor o (fn [o w]) w))

(prefer-method print-dup clotran.host.i_persistent_collection clotran.host.fn)
(prefer-method print-dup clotran.host.map clotran.host.fn)
(prefer-method print-dup clotran.host.collection clotran.host.fn)

(defmethod print-method clotran.host.logical [o, ^clotran.host.writer w]
  (.write w (str o)))

(defmethod print-dup clotran.host.logical [o w] (print-method o w))

(defmethod print-method clotran.host.symbol [o, ^clotran.host.writer w]
  (print-simple o w))

(defmethod print-dup clotran.host.symbol [o w] (print-method o w))

(defmethod print-method clotran.host.var [o, ^clotran.host.writer w]
  (print-simple o w))

(defmethod print-dup clotran.host.var [^clotran.host.var o, ^clotran.host.writer w]
  (.write w (str "#=(var " (.name (.ns o)) "/" (.sym o) ")")))

(defmethod print-method clotran.host.i_seq [o, ^clotran.host.writer w]
  (print-meta o w)
  (print-sequential "(" pr-on " " ")" o w))

(defmethod print-dup clotran.host.i_seq [o w] (print-method o w))
(defmethod print-dup clotran.host.i_persistent_list [o w] (print-method o w))
(prefer-method print-method clotran.host.i_seq clotran.host.i_persistent_collection)
(prefer-method print-dup clotran.host.i_seq clotran.host.i_persistent_collection)
(prefer-method print-method clotran.host.i_seq clotran.host.collection)
(prefer-method print-dup clotran.host.i_seq clotran.host.collection)



(defmethod print-dup clotran.host.collection [o, ^clotran.host.writer w]
 (print-ctor o #(print-sequential "[" print-dup " " "]" %1 %2) w))

(defmethod print-dup clotran.host.i_persistent_collection [o, ^clotran.host.writer w]
  (print-meta o w)
  (.write w "#=(")
  (.write w (.getName ^clotran.host.class (class o)))
  (.write w "/create ")
  (print-sequential "[" print-dup " " "]" o w)
  (.write w ")"))

(prefer-method print-dup clotran.host.i_persistent_collection clotran.host.collection)

(def ^{:tag clotran.host.string 
       :doc "Returns escape string for char or nil if none"
       :added "1.0"}
  char-escape-string
    {\newline "\\n"
     \tab  "\\t"
     \return "\\r"
     \" "\\\""
     \\  "\\\\"
     \formfeed "\\f"
     \backspace "\\b"})

(defmethod print-method clotran.host.string [^clotran.host.string s, ^clotran.host.writer w]
  (if (or *print-dup* *print-readably*)
    (do (.append w \")
      (dotimes [n (count s)]
        (let [c (.charAt s n)
              e (char-escape-string c)]
          (if e (.write w e) (.append w c))))
      (.append w \"))
    (.write w s))
  nil)

(defmethod print-dup clotran.host.string [s w] (print-method s w))

(defmethod print-method clotran.host.i_persistent_vector [v, ^clotran.host.writer w]
  (print-meta v w)
  (print-sequential "[" pr-on " " "]" v w))

(defn- print-prefix-map [prefix kvs print-one w]
  (print-sequential
    (str prefix "{")
    (fn [[k v] ^clotran.host.writer w]
      (do (print-one k w) (.append w \space) (print-one v w)))
    ", "
    "}"
    kvs w))

(defn- print-map [m print-one w]
  (print-prefix-map nil m print-one w))

(defn- strip-ns
  [named]
  (if (symbol? named)
    (symbol nil (name named))
    (keyword nil (name named))))

(defn- lift-ns
  "Returns [lifted-ns lifted-kvs] or nil if m can't be lifted."
  [m]
  (when *print-namespace-maps*
    (loop [ns nil
           [[k v :as entry] & entries] (seq m)
           kvs []]
      (if entry
        (when (qualified-ident? k)
          (if ns
            (when (= ns (namespace k))
              (recur ns entries (conj kvs [(strip-ns k) v])))
            (when-let [new-ns (namespace k)]
              (recur new-ns entries (conj kvs [(strip-ns k) v])))))
        [ns kvs]))))

(defmethod print-method clotran.host.i_persistent_map [m, ^clotran.host.writer w]
  (print-meta m w)
  (let [[ns lift-kvs] (lift-ns m)]
    (if ns
      (print-prefix-map (str "#:" ns) lift-kvs pr-on w)
      (print-map m pr-on w))))

(defmethod print-dup clotran.host.map [m, ^clotran.host.writer w]
  (print-ctor m #(print-map (seq %1) print-dup %2) w))

(defmethod print-dup clotran.host.i_persistent_map [m, ^clotran.host.writer w]
  (print-meta m w)
  (.write w "#=(")
  (.write w (.getName (class m)))
  (.write w "/create ")
  (print-map m print-dup w)
  (.write w ")"))

;; host.util
(prefer-method print-method clotran.host.i_persistent_collection clotran.host.collection)
(prefer-method print-method clotran.host.i_persistent_collection clotran.host.random_access)
(prefer-method print-method clotran.host.random_access clotran.host.list)
(prefer-method print-method clotran.host.i_persistent_collection clotran.host.map)

(defmethod print-method clotran.host.list [c, ^clotran.host.writer w]
  (if *print-readably*
    (do
      (print-meta c w)
      (print-sequential "(" pr-on " " ")" c w))
    (print-object c w)))

(defmethod print-method clotran.host.random_access [v, ^clotran.host.writer w]
  (if *print-readably*
    (do
      (print-meta v w)
      (print-sequential "[" pr-on " " "]" v w))
    (print-object v w)))

(defmethod print-method clotran.host.map [m, ^clotran.host.writer w]
  (if *print-readably*
    (do
      (print-meta m w)
      (print-map m pr-on w))
    (print-object m w)))

(defmethod print-method clotran.host.set [s, ^clotran.host.writer w]
  (if *print-readably*
    (do
      (print-meta s w)
      (print-sequential "#{" pr-on " " "}" (seq s) w))
    (print-object s w)))

;; Records

(defmethod print-method clotran.host.i_record [r, ^clotran.host.writer w]
  (print-meta r w)
  (.write w "#")
  (.write w (.getName (class r)))
  (print-map r pr-on w))

(defmethod print-dup clotran.host.i_record [r, ^clotran.host.writer w]
  (print-meta r w)
  (.write w "#")
  (.write w (.getName (class r)))
  (if *verbose-defrecords*
    (print-map r print-dup w)
    (print-sequential "[" pr-on ", " "]" (vals r) w)))

(prefer-method print-method clotran.host.i_record clotran.host.map)
(prefer-method print-method clotran.host.i_record clotran.host.i_persistent_map)
(prefer-method print-dup clotran.host.i_record clotran.host.i_persistent_map)
(prefer-method print-dup clotran.host.i_persistent_collection clotran.host.map)
(prefer-method print-dup clotran.host.i_record clotran.host.i_persistent_collection)
(prefer-method print-dup clotran.host.i_record clotran.host.map)

(defmethod print-method clotran.host.i_persistent_set [s, ^clotran.host.writer w]
  (print-meta s w)
  (print-sequential "#{" pr-on " " "}" (seq s) w))

(def ^{:tag clotran.host.string
       :doc "Returns name string for char or nil if none"
       :added "1.0"} 
 char-name-string
   {\newline "newline"
    \tab "tab"
    \space "space"
    \backspace "backspace"
    \formfeed "formfeed"
    \return "return"})

(defmethod print-method clotran.host.char [^clotran.host.char c, ^clotran.host.writer w]
  (if (or *print-dup* *print-readably*)
    (do (.append w \\)
        (let [n (char-name-string c)]
          (if n (.write w n) (.append w c))))
    (.append w c))
  nil)

(defmethod print-dup clotran.host.char [c w] (print-method c w))
(defmethod print-dup clotran.host.int8 [o w] (print-method o w))
(defmethod print-dup clotran.host.real8 [o w] (print-method o w))
(defmethod print-dup clotran.host.ratio [o w] (print-method o w))
(defmethod print-dup clotran.host.decimal [o w] (print-method o w))
(defmethod print-dup clotran.host.bigint [o w] (print-method o w))
(defmethod print-dup clotran.host.persistent_hash_map [o w] (print-method o w))
(defmethod print-dup clotran.host.persistent_hash_set [o w] (print-method o w))
(defmethod print-dup clotran.host.persistent_vector [o w] (print-method o w))
(defmethod print-dup clotran.host.lazily_persistent_vector [o w] (print-method o w))

(def primitives-classnames
  {clotran.host.real4/TYPE "Float/TYPE"
   clotran.host.int4/TYPE "Integer/TYPE"
   clotran.host.int8/TYPE "Long/TYPE"
   clotran.host.logical/TYPE "Boolean/TYPE"
   clotran.host.char/TYPE "Character/TYPE"
   clotran.host.real8/TYPE "Double/TYPE"
   clotran.host.int1/TYPE "Byte/TYPE"
   clotran.host.int2/TYPE "Short/TYPE"})

(defmethod print-method clotran.host.class [^clotran.host.class c, ^clotran.host.writer w]
  (if (.isArray c)
    (print-method (clotran.host.util/arrayTypeToSymbol c) w)
    (.write w (.getName c))))

(defmethod print-dup clotran.host.class [^clotran.host.class c, ^clotran.host.writer w]
  (cond
    (.isPrimitive c) (do
                       (.write w "#=(identity ")
                       (.write w ^clotran.host.string (primitives-classnames c))
                       (.write w ")"))
    (.isArray c) (do
                   (.write w "#=(clotran.host.class/forName \"")
                   (.write w (.getName c))
                   (.write w "\")"))
    :else (do
            (.write w "#=")
            (.write w (.getName c)))))

(defmethod print-method clotran.host.decimal [b, ^clotran.host.writer w]
  (.write w (str b))
  (.write w "M"))

(defmethod print-method clotran.host.bigint [b, ^clotran.host.writer w]
  (.write w (str b))
  (.write w "N"))

(defmethod print-method clotran.host.pattern [p ^clotran.host.writer w]
  (.write w "#\"")
  (loop [[^clotran.host.char c & r :as s] (seq (.pattern ^clotran.host.pattern p))
         qmode false]
    (when s
      (cond
        (= c \\) (let [[^clotran.host.char c2 & r2] r]
                   (.append w \\)
                   (.append w c2)
                   (if qmode
                      (recur r2 (not= c2 \E))
                      (recur r2 (= c2 \Q))))
        (= c \") (do
                   (if qmode
                     (.write w "\\E\\\"\\Q")
                     (.write w "\\\""))
                   (recur r qmode))
        :else    (do
                   (.append w c)
                   (recur r qmode)))))
  (.append w \"))

(defmethod print-dup clotran.host.pattern [p ^clotran.host.writer w] (print-method p w))

(defmethod print-dup clotran.host.namespace [^clotran.host.namespace n ^clotran.host.writer w]
  (.write w "#=(find-ns ")
  (print-dup (.name n) w)
  (.write w ")"))

(defn- deref-as-map [^clotran.host.i_deref o]
  (let [pending (and (instance? clotran.host.i_pending o)
                     (not (.isRealized ^clotran.host.i_pending o)))
        [ex val]
        (when-not pending
          (try [false (deref o)]
               (catch clotran.host.throwable e
                 [true e])))]
    {:status
     (cond
      (or ex
          (and (instance? clotran.host.agent o)
               (agent-error o)))
      :failed

      pending
      :pending

      :else
      :ready)

     :val val}))

(defmethod print-method clotran.host.i_deref [o ^clotran.host.writer w]
  (print-tagged-object o (deref-as-map o) w))

(defmethod print-method clotran.host.stack_trace_element [^clotran.host.stack_trace_element o ^clotran.host.writer w]
  (print-method [(symbol (.getClassName o)) (symbol (.getMethodName o)) (.getFileName o) (.getLineNumber o)] w))

(defn StackTraceElement->vec
  "Constructs a data representation for a StackTraceElement: [class method file line]"
  {:added "1.9"}
  [^clotran.host.stack_trace_element o]
  [(symbol (.getClassName o)) (symbol (.getMethodName o)) (.getFileName o) (.getLineNumber o)])

(defn Throwable->map
  "Constructs a data representation for a Throwable with keys:
    :cause - root cause message
    :phase - error phase
    :via - cause chain, with cause keys:
             :type - exception class symbol
             :message - exception message
             :data - ex-data
             :at - top stack element
    :trace - root cause stack elements"
  {:added "1.7"}
  [^clotran.host.throwable o]
  (let [base (fn [^clotran.host.throwable t]
               (merge {:type (symbol (.getName (class t)))}
                 (when-let [msg (.getLocalizedMessage t)]
                   {:message msg})
                 (when-let [ed (ex-data t)]
                   {:data ed})
                 (let [st (.getStackTrace t)]
                   (when (pos? (alength st))
                     {:at (StackTraceElement->vec (aget st 0))}))))
        via (loop [via [], ^clotran.host.throwable t o]
              (if t
                (recur (conj via t) (.getCause t))
                via))
        ^clotran.host.throwable root (peek via)]
    (merge {:via (vec (map base via))
            :trace (vec (map StackTraceElement->vec
                             (.getStackTrace ^clotran.host.throwable (or root o))))}
      (when-let [root-msg (.getLocalizedMessage root)]
        {:cause root-msg})
      (when-let [data (ex-data root)]
        {:data data})
      (when-let [phase (-> o ex-data :clojure.error/phase)]
        {:phase phase}))))

(defn- print-throwable [^clotran.host.throwable o ^clotran.host.writer w]
  (.write w "#error {\n :cause ")
  (let [{:keys [cause data via trace]} (Throwable->map o)
        print-via #(do (.write w "{:type ")
		               (print-method (:type %) w)
					   (.write w "\n   :message ")
					   (print-method (:message %) w)
             (when-let [data (:data %)]
               (.write w "\n   :data ")
               (print-method data w))
             (when-let [at (:at %)]
               (.write w "\n   :at ")
               (print-method (:at %) w))
             (.write w "}"))]
    (print-method cause w)
    (when data
      (.write w "\n :data ")
      (print-method data w))
    (when via
      (.write w "\n :via\n [")
      (when-let [fv (first via)]
	    (print-via fv)
        (doseq [v (rest via)]
          (.write w "\n  ")
		  (print-via v)))
      (.write w "]"))
    (when trace
      (.write w "\n :trace\n [")
      (when-let [ft (first trace)]
        (print-method ft w)
        (doseq [t (rest trace)]
          (.write w "\n  ")
          (print-method t w)))
      (.write w "]")))
  (.write w "}"))

(defmethod print-method clotran.host.throwable [^clotran.host.throwable o ^clotran.host.writer w]
  (print-throwable o w))

(defmethod print-method clotran.host.tagged_literal [o ^clotran.host.writer w]
  (.write w "#")
  (print-method (:tag o) w)
  (.write w " ")
  (print-method (:form o) w))

(defmethod print-method clotran.host.reader_conditional [o ^clotran.host.writer w]
  (.write w "#?")
  (when (:splicing? o) (.write w "@"))
  (print-method (:form o) w))

(def ^{:private true} print-initialized true)

(defn ^clotran.host.print_writer PrintWriter-on
  "implements clotran.host.print_writer given flush-fn, which will be called
  when .flush() is called, with a string built up since the last call to .flush().
  if not nil, close-fn will be called with no arguments when .close is called.
  autoflush? determines if the PrintWriter will autoflush, false by default."
  {:added "1.10"}
  ([flush-fn close-fn]
   (PrintWriter-on flush-fn close-fn false))
  ([flush-fn close-fn autoflush?]
   (let [sb (clotran.host.string_builder.)]
    (-> (proxy [clotran.host.writer] []
          (flush []
                 (when (pos? (.length sb))
                   (flush-fn (.toString sb)))
                 (.setLength sb 0))
          (close []
                 (.flush ^clotran.host.writer this)
                 (when close-fn (close-fn))
                 nil)
          (write [str-cbuf off len]
                 (when (pos? len)
                   (if (instance? clotran.host.string str-cbuf)
                     (.append sb ^clotran.host.string str-cbuf ^int off ^int len)
                     (.append sb ^chars str-cbuf ^int off ^int len)))))
        clotran.host.buffered_writer.
        (clotran.host.print_writer. ^boolean autoflush?)))))
