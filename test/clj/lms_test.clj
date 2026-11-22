;; lms_test.clj: a Lemmis file (.lms) as a namespace source (DEVIATIONS 96,
;; 97), against the stub reader of test/lms/lemmis/reader.cljf -- Lemmis's own
;; reader is lane 2's. Run by make check-lms, with the stub and the fixtures
;; on the path:
;;   CLOTRAN_PATH=test/lms:test/lms/proj:build/lms ./clotran-bin src/clj/clojure/core.clj test/clj/lms_test.clj
(require '[clojure.string :as str] '[clotran.index :as ix])
(def failures (atom 0))
(defn bad [& xs] (swap! failures inc) (apply println "FAIL -" xs))
(defn msg "f's exception message, nil if it returns" [f]
  (try (f) nil (catch clotran.host.throwable e (str (.getMessage e)))))
(defmacro check [what expr want]
  `(let [g# (try ~expr (catch clotran.host.throwable e# [:threw (.getMessage e#)]))
         w# ~want]
     (if (= g# w#) (println "ok   -" ~what) (bad ~what "got" (pr-str g#) "want" (pr-str w#)))))
(defmacro check-msg [what expr & parts]
  `(let [m# (msg (fn [] ~expr))]
     (if (and m# (every? #(str/includes? m# %) [~@parts])) (println "ok   -" ~what) (bad ~what "message" (pr-str m#) "should name" (pr-str [~@parts])))))

;; ---- both directions: a .cljf requires a .lms that requires a .cljf ------
(require 'mix.core)
(check "a .cljf calls a .lms lib, which calls and closes over a .cljf one" (mix.core/go) [20 3 40 4])
(check "a .lms closure passed to a .cljf fn" (mix.util/twice (mix.solver/scale 3) 1) 9)
(check "a .cljf closure passed to a .lms fn" (mix.solver/run (mix.util/adder 5) 0) 10)
(check "the .lms lib's Vars are interned in its namespace" (set (keys (ns-publics 'mix.solver))) '#{scale run plus3 boom})
(check "a .lms :refer brings in the .cljf names" (= #'mix.util/twice (ns-resolve 'mix.solver 'twice)) true)

;; ---- positions: a Var's and a stack frame's are the .lms file's ----------
(let [m (meta #'mix.solver/scale)]
  (check "a .lms Var's :line and :column" [(:line m) (:column m)] [6 1])
  (check "a .lms Var's :file" (str/ends-with? (str (:file m)) "mix/solver.lms") true))
(check "a stack frame names the .lms line"
       (try (mix.solver/boom 1) nil
            (catch clotran.host.throwable e
              (some (fn [fr] (let [s (str fr)] (when (str/includes? s "solver.lms") (:line fr)))) (.getStackTrace e))))
       13)

;; ---- resolution order: .cljf .cljc .clj, then .lms (DEVIATIONS 96) -------
(require 'prec.a 'prec.b 'prec.c)
(check "a.cljf beside a.lms loads the .cljf" prec.a/which :cljf)
(check "b.clj beside b.lms loads the .clj" prec.b/which :clj)
(check "c.lms alone loads" prec.c/which :lms)
(check "load-file of a .lms path goes through the hook too" (do (load-file "test/lms/proj/prec/c.lms") @(resolve 'prec.c/which)) :lms)

;; ---- refusals -------------------------------------------------------------
(check-msg "a .lms whose ns is not its lib's is refused" (require 'bad.mismatch) "bad.elsewhere" "bad/mismatch.lms")
(check "and the wrong namespace was not made" (find-ns 'bad.elsewhere) nil)
(check-msg "a .lms whose first form is not (ns ...) is refused" (require 'bad.notns) "bad/notns.lms" "(ns <lib>")
(check-msg "a read error names the .lms file" (require 'bad.readerr) "bad/readerr.lms")
(check-msg "an analysis error in a .lms file is the analyzer's" (require 'bad.analyze) "Unable to resolve symbol: nope")
(check-msg "a missing lib names .lms among the extensions" (require 'no.such.lib) "no/such/lib.lms")

;; ---- reload -----------------------------------------------------------------
(clotran-spit "build/lms/rl/x.lms" "(ns rl.x)\n(def v 1)\n")
(require 'rl.x)
(check "a .lms lib loads from a fresh file" @(ns-resolve 'rl.x 'v) 1)
(clotran-spit "build/lms/rl/x.lms" "(ns rl.x)\n\n(def v 2)\n(defn f [] v)\n")
(require 'rl.x :reload)
(check "and :reload reads it again" [@(ns-resolve 'rl.x 'v) ((ns-resolve 'rl.x 'f))] [2 2])
(check "at its new lines" (:line (meta (ns-resolve 'rl.x 'v))) 3)

;; ---- the index: a mixed project, every definition where its Var is -------
(let [defs (ix/index-paths ["test/lms/proj/mix"])
      named (filter #(#{:def :defn} (:kind %)) defs)]
  (check "the index reads the .lms file of a mixed project" (set (map :file (filter #(= 'mix.solver (:ns %)) defs))) #{"test/lms/proj/mix/solver.lms"})
  (check "no errors" (filter #(= :error (:kind %)) defs) ())
  (check "every definition of the mixed project indexed" (set (map (juxt :ns :name) named))
         '#{[mix.core go] [mix.util twice] [mix.util adder] [mix.solver scale] [mix.solver run] [mix.solver plus3] [mix.solver boom]})
  (doseq [e named :let [m (meta (ns-resolve (:ns e) (:name e)))]]
    (check (str "index position of " (:ns e) "/" (:name e)) [(:line e) (:column e)] [(:line m) (:column m)])))
(check "an index of a .lms the reader refuses is one error entry" (map :kind (ix/index-file "test/lms/proj/bad/readerr.lms")) [:error])

(if (zero? @failures) (println "LMS TESTS PASSED") (do (println "LMS TESTS FAILED:" @failures) (clotran.host.system/exit 1)))
