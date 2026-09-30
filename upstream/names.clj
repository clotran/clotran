;; Renaming upstream Clojure source into clotran's names, by
;; upstream/class-names.edn. Loaded by upstream/derive and scripts/oracle.
;;
;; A file is lexed -- strings, regexes, comments and character literals
;; apart from code -- so that a class is renamed where it is code by the
;; file's own imports, and a qualified name in a string or a comment is
;; renamed as text.
(ns names
  (:require [clojure.string :as str]
            [clojure.edn :as edn]
            [clojure.java.io :as io]))

(def table (edn/read-string (slurp (io/file (.getParentFile (io/file *file*)) "class-names.edn"))))
(def implicit (set (:implicit table)))
(def host-prefix #"^(?:java|javax|clojure\.lang)\.")

(defn snake [simple]
  (-> simple
      (str/replace "$" "_")
      (str/replace #"([a-z0-9])([A-Z])" "$1_$2")
      (str/replace #"([A-Z])([A-Z][a-z])" "$1_$2")
      str/lower-case))

(defn class-name
  "clotran's name for a qualified upstream class."
  [q]
  (or (get (:classes table) q)
      (str "clotran.host." (snake (last (str/split q #"\."))))))

(defn host-class? [q] (boolean (re-find host-prefix q)))

(defn words [s]
  (reduce (fn [s [a b]] (str/replace s a b)) s (:words table)))

(defn rename-namespace [n]
  (or (some (fn [[from to]]
              (cond (= n from) to
                    (str/starts-with? n (str from ".")) (str to (subs n (count from)))))
            (:namespaces table))
      n))

;; --- text: strings, comments, docstrings ----------------------------------

(def qualified-in-text #"(?:(?<![\w.$])|(?<=\[L))(?:java|javax|clojure\.lang)(?:\.[a-z_][a-z0-9_]*)*\.[A-Z][A-Za-z0-9_$]*")

(def host-doc-link #"https?://(?:docs\.oracle\.com|java\.sun\.com)[^\s\"]*")

(defn rename-text [s]
  (-> s
      ;; links into the host's documentation: a See: line goes, and so
      ;; does a paragraph that only points there
      (str/replace (re-pattern (str "\n\\s*See: " host-doc-link)) "")
      (str/replace (re-pattern (str "\n\n\\s*For more complete information, see:\\s*" host-doc-link)) "")
      (str/replace host-doc-link "the host's documentation")
      (str/replace qualified-in-text #(class-name %))
      (str/replace #"clojure\.java\.[a-z]+" rename-namespace)
      (str/replace #"\b(?:clojure\.lang|java\.lang)\b" "clotran.host")
      words))

;; --- lexing ----------------------------------------------------------------

(def delim-start (set "()[]{}'`~^@#"))
(def token-end (set " \t\n\r,()[]{}\"`;~^@"))

(defn lex
  "[kind text] pairs: :ws :comment :string :regex :char :delim :token."
  [^String s]
  (let [n (count s)]
    (loop [i 0 out (transient [])]
      (if (>= i n)
        (persistent! out)
        (let [c (.charAt s i)
              string-end (fn [j] (loop [j j] (let [d (.charAt s j)]
                                               (cond (= d \\) (recur (+ j 2))
                                                     (= d \") (inc j)
                                                     :else (recur (inc j))))))]
          (cond
            (or (Character/isWhitespace c) (= c \,))
            (let [j (loop [j i] (if (and (< j n) (let [d (.charAt s j)] (or (Character/isWhitespace d) (= d \,)))) (recur (inc j)) j))]
              (recur j (conj! out [:ws (subs s i j)])))
            (= c \;)
            (let [j (or (str/index-of s "\n" i) n)]
              (recur j (conj! out [:comment (subs s i j)])))
            (= c \")
            (let [j (string-end (inc i))] (recur j (conj! out [:string (subs s i j)])))
            (and (= c \#) (< (inc i) n) (= (.charAt s (inc i)) \"))
            (let [j (string-end (+ i 2))] (recur j (conj! out [:regex (subs s i j)])))
            (= c \\)
            (let [j (loop [j (+ i 2)] (if (and (< j n) (Character/isLetterOrDigit (.charAt s j))) (recur (inc j)) j))
                  j (if (Character/isLetterOrDigit (.charAt s (inc i))) j (+ i 2))]
              (recur j (conj! out [:char (subs s i j)])))
            (delim-start c)
            (recur (inc i) (conj! out [:delim (str c)]))
            :else
            (let [j (loop [j i] (if (and (< j n) (not (token-end (.charAt s j)))) (recur (inc j)) j))]
              (recur j (conj! out [:token (subs s i j)])))))))))

;; --- a file's classes ------------------------------------------------------

(defn- forms-in [toks]
  ;; each list/vector as [start end] indexes into toks, with its head token
  (let [opens {"(" ")" "[" "]" "{" "}"}]
    (loop [i 0 stack [] out []]
      (if (>= i (count toks))
        out
        (let [[k t] (toks i)]
          (cond (and (= k :delim) (opens t)) (recur (inc i) (conj stack i) out)
                (and (= k :delim) (#{")" "]" "}"} t) (seq stack))
                (recur (inc i) (pop stack) (conj out [(peek stack) i]))
                :else (recur (inc i) stack out)))))))

(defn- significant [toks from to]
  (filter (fn [j] (not (#{:ws :comment} (first (toks j))))) (range from to)))

(defn import-specs
  "Each import spec in the file: {:span [from to] :classes [qualified...]},
  the span covering a preceding quote. From (:import ...) and (import ...)."
  [toks]
  (let [forms (forms-in toks)
        by-start (into {} forms)]
    (for [[s e] forms
          :when (= "(" (second (toks s)))
          :let [sig (significant toks (inc s) e)]
          :when (seq sig)
          :let [head (second (toks (first sig)))]
          :when (#{":import" "import"} head)
          :let [items (loop [js (rest sig) acc []]
                        (if (empty? js) acc
                          (let [j (first js) [k t] (toks j)]
                            (cond
                              (and (= k :delim) (= t "'"))
                              (let [j2 (second js)]
                                (if (by-start j2)
                                  (recur (drop 2 js) (conj acc [j (by-start j2) j2]))
                                  (recur (drop 2 js) (conj acc [j j2 j2]))))
                              (by-start j) (recur (drop-while #(<= % (by-start j)) js) (conj acc [j (by-start j) j]))
                              (= k :token) (recur (rest js) (conj acc [j j j]))
                              :else (recur (rest js) acc)))))]
          [from to inner] items
          :let [classes (if (= inner to)
                          (let [t (second (toks inner))] (when (str/includes? t ".") [t]))
                          (let [ts (map #(second (toks %)) (filter #(= :token (first (toks %))) (range (inc inner) to)))]
                            (map #(str (first ts) "." %) (rest ts))))]
          :when (seq classes)
          :when (every? host-class? classes)]
      {:span [from to] :classes (vec classes)})))

(defn defined-types
  "Names the file itself defines as types: a bare one of these is not a
  host class."
  [toks]
  (set (for [[i [k t]] (map-indexed vector toks)
             :when (and (= k :token) (#{"deftype" "defrecord" "defprotocol" "definterface" "gen-interface"} t))
             :let [nxt (first (significant toks (inc i) (count toks)))]
             :when nxt]
         (second (toks nxt)))))

;; --- renaming code ---------------------------------------------------------

(defn resolver
  "The upstream class a name in this file means, qualified; nil if none."
  [imports defined]
  (fn resolve [nm]
    (cond (host-class? nm) nm
          ;; Outer$Inner, the outer imported or implicit
          (and (str/includes? nm "$") (not (str/includes? nm ".")))
          (let [[outer inner] (str/split nm #"\$" 2)
                o (cond (defined outer) nil
                        (imports outer) (imports outer)
                        (implicit outer) (str "java.lang." outer))]
            (when o (str o "$" inner)))
          (str/includes? nm ".") nil
          (defined nm) nil
          (imports nm) (imports nm)
          (implicit nm) (str "java.lang." nm))))

(defn rename-token [resolve t]
  (cond
    (or (str/starts-with? t ":") (str/starts-with? t ".")) (words t)
    :else
    (let [[_ body dot] (re-matches #"(.*?)(\.?)" t)
          slash (str/last-index-of body "/")
          [cls member] (if (and slash (pos? slash)) [(subs body 0 slash) (subs body slash)] [body ""])]
      (if-let [q (resolve cls)]
        ;; (StringReader. s) is clotran's factory where the type's own
        ;; constructor takes its fields, not the host's arguments
        (if-let [f (and (= dot ".") (= member "") (get (:constructors table) q))]
          f
          (str (class-name q) member dot))
        (let [ns-renamed (if (and slash (pos? slash))
                           (str (rename-namespace cls) member)
                           (rename-namespace body))]
          (words (str ns-renamed dot)))))))

(defn rename-source
  "The file's text in clotran's names."
  [text]
  (let [toks (lex text)
        specs (import-specs toks)
        imports (into {} (for [{:keys [classes]} specs, q classes]
                           [(last (str/split q #"\.")) q]))
        resolve (resolver imports (defined-types toks))
        drop-at (into {} (map (fn [{[f t] :span}] [f t]) specs))]
    (loop [i 0 out (StringBuilder.)]
      (if (>= i (count toks))
        (str out)
        (if-let [to (drop-at i)]
          ;; the spec goes: every use of its classes is written in full
          (recur (inc to) out)
          (let [[k t] (toks i)
                ;; (new StringReader s): the factory stands for `new` and the class
                nxt (when (and (= k :token) (= t "new")) (first (significant toks (inc i) (count toks))))
                ctor (when nxt (some->> (second (toks nxt)) resolve (get (:constructors table))))]
            (if ctor
              (recur (inc nxt) (.append out ctor))
            (recur (inc i)
                   (.append out (case k
                                  :token (rename-token resolve t)
                                  (:string :regex :comment) (rename-text t)
                                  t))))))))))

(defn rename-path [p] (words p))

;; --- the other direction, for clj ------------------------------------------

(def back
  "clotran's name -> the upstream name clj knows it by: the first listed
  wins where several upstream classes are one clotran class."
  (reduce (fn [m [q c]] (if (m c) m (assoc m c q))) {} (sort-by key (:classes table))))

(defn to-upstream
  "A form's text written in clotran's names, as clj must read it."
  [text]
  (let [back-ns (into {} (map (fn [[a b]] [b a]) (:namespaces table)))
        back-ctor (into {} (map (fn [[a b]] [(str "(" b) (str "(" a ".")]) (:constructors table)))]
    (-> text
        (str/replace #"\(clotran\.[a-z]+/[a-z-]+" #(get back-ctor % %))
        (str/replace #"clotran\.host\.[a-z0-9_]+|clotran\.[a-z]+\.[A-Z][A-Za-z0-9]*"
                     #(get back % %))
        (str/replace #"clotran\.[a-z-]+" #(get back-ns % %)))))

(def simple-back
  "A simple name clj prints -- \"Long\", as .getSimpleName gives it -- to
  the last part of clotran's name, where only one class has it."
  (into {} (for [[s qs] (group-by #(last (str/split % #"\.")) (concat (keys (:classes table))
                                                                          (map #(str "java.lang." %) implicit)))
                 :let [cs (distinct (map class-name qs))] :when (= 1 (count cs))]
             [s (last (str/split (first cs) #"\."))])))

(defn from-clj
  "A line clj printed, its classes in clotran's names."
  [line]
  (-> line
      (str/replace qualified-in-text class-name)
      (str/replace #"\\\"([A-Z][A-Za-z]*)\\\"|\"([A-Z][A-Za-z]*)\""
                   (fn [[m esc plain]]
                     (let [t (simple-back (or esc plain))]
                       (cond (nil? t) m esc (str "\\\"" t "\\\"") :else (str "\"" t "\"")))))))
