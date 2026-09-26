;; Compiling what is loaded (clotran.loader): run by `make test` twice,
;; with CLOTRAN_AUTOCOMPILE=use and a fresh CLOTRAN_CACHE. The first run
;; builds the namespace (compile-now) and installs it over the loaded
;; source; the second finds it in the cache and installs it as it loads.
;; The answers must not change either way.

(load-file "test/clj/autocompile_demo.cljf")
(def expect [(autocompile-demo/sumsq 1000) (autocompile-demo/words "a bc d")])
(def src "test/clj/autocompile_demo.cljf")

(let [st (if (= "build" (System/getenv "AUTOCOMPILE_STEP"))
           (clotran.loader/compile-now src)
           (get (clotran.loader/compile-status) src))
      got [(autocompile-demo/sumsq 1000) (autocompile-demo/words "a bc d")]]
  (if (and (= :installed st) (= expect got [332833500 3]))
    (println "AUTOCOMPILE PASSED")
    (println "AUTOCOMPILE FAILED:" st expect got)))
