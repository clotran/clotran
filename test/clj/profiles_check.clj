;; profiles_check.clj (make check-profiles): the cases of test/clj/pure_sample.cljf,
;; interpreted, or through the library PROFILE_LIB names, compiled under one
;; profile. The Makefile runs it once a profile and once interpreted and diffs
;; the outputs: a profile may change speed, never an answer.
(require (quote clojure.string))
(load-file "test/clj/pure_sample.cljf")
(let [lib (clotran.host.system/getenv "PROFILE_LIB")]
  (when-not (clojure.string/blank? lib)
    (require 'clotran.loader)
    (println "installed" (boolean ((resolve 'clotran.loader/install) lib "test/clj/pure_sample.cljf")))))
(doseq [c '[(pure-sample/total (double-array [1.5 2.5 3.0]))
            (pure-sample/total (long-array [1 2 3]))
            (pure-sample/total (double-array []))
            (pure-sample/mean (double-array [1.0 2.0 4.0]))
            (pure-sample/sum-to 100000)
            (pure-sample/fact 20)
            (pure-sample/hyp 3.0 4.0)
            (pure-sample/clamp 5 1 3)
            (pure-sample/sign-of -2)
            (pure-sample/ratio 7 2)
            (pure-sample/floor-mod -7 3)
            (pure-sample/trunc-rem -7 3)
            (pure-sample/nth-or (double-array [1.0 2.0 3.0]) 1)
            (pure-sample/nth-or (double-array [1.0]) 5)
            (pure-sample/fact 21)]]
  (println (pr-str c) "=>" (try (pr-str (eval c)) (catch clotran.host.throwable e (str "!" (.getName (class e)) " " (.getMessage e))))))
(println "PROFILES CHECK DONE")
