;; index_check.clj: the index against the live Vars (PLAN step 36). Every
;; definition clotran.index reads out of core.clj must be where (meta #'var)
;; says the Var was defined once core.clj loaded, line and column both, and
;; every public Var core.clj defines must be in the index. The same for
;; clotran's own namespaces that are loaded here. Run by make check-index:
;;   ./clotran-bin src/clj/clojure/core.clj test/clj/index_check.clj
(require '[clotran.index :as ix] '[clojure.string :as str])
(def failures (atom 0))
(defn bad [& xs] (swap! failures inc) (apply println "FAIL -" xs))

(defn compare-file
  "The index of file against the Vars of ns: each def/defn/defmacro/defmulti
  entry at its Var's line and column, each Var in the index."
  [file ns-sym]
  (let [defs (ix/index-file file)
        errors (filter #(= :error (:kind %)) defs)
        ;; the kinds that intern a Var: not a defmethod, a type's name, an ns
        named (filter #(and (= ns-sym (:ns %)) (#{:def :defn :defmacro :defmulti :defprotocol :protocol-fn :declare} (:kind %))) defs)
        the-ns (the-ns ns-sym)
        by-name (group-by :name named)]
    (doseq [e errors] (bad file "did not read:" (:error e)))
    ;; the index's positions are the Vars'
    (doseq [e named
            :let [v (ns-resolve the-ns (:name e)) m (meta v)]]
      (cond (nil? v) (bad file (:name e) "is in the index but not a Var")
            ;; defined again by a later file -- print-initialized by core_print,
            ;; gen-class by genclass -- the Var says that file, as clj's does
            (and (:file m) (not (str/ends-with? file (:file m))) (clotran-file-exists? (str "src/clj/" (:file m)))) nil
            ;; a protocol's method Var has no position, in clj either
            (and (= :protocol-fn (:kind e)) (nil? (:line m))) nil
            ;; a name defined twice (declare and defn; a def in a reader conditional) has one Var: its last position
            (and (= (:line m) (:line e)) (= (:column m) (:column e))) nil
            (some #(and (= (:line m) (:line %)) (= (:column m) (:column %))) (by-name (:name e))) nil
            :else (bad file (:name e) "index says" (:line e) (:column e) "Var says" (:line m) (:column m))))
    ;; every Var the file defines is in the index
    (doseq [[s v] (ns-interns the-ns)
            :let [m (meta v)]
            :when (and (:file m) (str/ends-with? file (:file m)) (:line m))
            :when (not (by-name s))
            ;; a definition a macro of the file's own makes is not seen: core's
            ;; private def-aset (clotran.index's docstring says so)
            :when (not (and (= ns-sym 'clojure.core) (str/starts-with? (str s) "aset-")))]
      (bad file s "is a Var at" (:line m) "but not in the index"))
    (println (str "index-check: " file ": " (count named) " definitions, " (count (ns-interns the-ns)) " Vars, agree"))))

(compare-file "src/clj/clojure/core.clj" 'clojure.core)
(doseq [[f ns-sym] [["src/clj/clotran/bind.cljf" 'clotran.bind] ["src/clj/clotran/cache.cljf" 'clotran.cache]
                    ["src/clj/clotran/index.cljf" 'clotran.index] ["src/clj/clotran/loader.cljf" 'clotran.loader]]]
  (require ns-sym)
  (compare-file f ns-sym))

;; Fortran: the package examples/mylib declares, read by the same parser that
;; binds it, against the Vars its load interns
(let [defs (ix/fortran-defs "examples/mylib")
      _ (fortran/load-package "examples/mylib")]
  (doseq [e defs :when (:bound e)
          :let [m (meta (ns-resolve 'mylib.raw (:name e)))]]
    (when-not (and (= (:line m) (:line e)) (str/ends-with? (:file m) (:file e)))
      (bad "examples/mylib" (:name e) "index says" (:file e) (:line e) "Var says" (:file m) (:line m))))
  (println (str "index-check: examples/mylib: " (count defs) " routines, agree")))

(if (zero? @failures) (println "INDEX CHECK PASSED") (do (println "INDEX CHECK FAILED:" @failures) (clotran.host.system/exit 1)))
