;; Compiling what is loaded (clotran.loader): run by `make test` twice,
;; with CLOTRAN_AUTOCOMPILE=use and a fresh CLOTRAN_CACHE. The first run
;; builds the namespace (compile-now) and installs it over the loaded
;; source; the second finds it in the cache and installs it as it loads.
;; The answers must not change either way, and the protocol extension's
;; methods must be the compiled fns afterwards (clotran.loader/install-extends).

(require (quote [clojure.string :as str]))
(def src (or (clotran.host.system/getenv "AUTOCOMPILE_SRC") "test/clj/autocompile_demo.cljf"))
(load-file src)
(defn answers []
  [(autocompile-demo/sumsq 1000) (autocompile-demo/words "a bc d")
   (autocompile-demo/size-of ["ab" nil ["cde"]])])
(def expect (answers))

(let [st (if (= "build" (clotran.host.system/getenv "AUTOCOMPILE_STEP"))
           (clotran.loader/compile-now src)
           (get (clotran.loader/compile-status) (clotran-real-path src)))
      got (answers)
      methods (for [[_ m] (:impls autocompile-demo/Sized)] (str (:size-of m)))]
  (if (and (= :installed st) (= expect got [332833500 3 5])
           (= 3 (count methods)) (every? #(str/starts-with? % "#<compiled") methods))
    (println "AUTOCOMPILE PASSED")
    (println "AUTOCOMPILE FAILED:" st expect got methods)))
