;; lms_noreader_test.clj: the .lms hook with no lemmis.reader on the path
;; (DEVIATIONS 97). Run by make check-lms with only the fixtures on the path:
;;   CLOTRAN_PATH=test/lms/proj ./clotran-bin src/clj/clojure/core.clj test/clj/lms_noreader_test.clj
(require '[clojure.string :as str])
(def m (try (require 'prec.c) nil (catch clotran.host.throwable e (str (.getMessage e)))))
(def ok? (and m (every? #(str/includes? m %) ["prec/c.lms" "lemmis.reader" "CLOTRAN_PATH"])))
(println (if ok? "ok   -" "FAIL -") "a .lms lib with no reader on the path says what to add:" (pr-str m))
(require 'prec.a)
(def ok2? (= :cljf @(resolve 'prec.a/which)))
(println (if ok2? "ok   -" "FAIL -") "and a .cljf lib still loads")
(if (and ok? ok2?) (println "LMS NOREADER PASSED") (do (println "LMS NOREADER FAILED") (clotran.host.system/exit 1)))
