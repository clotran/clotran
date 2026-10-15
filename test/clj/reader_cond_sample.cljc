;; language_test loads this file: a .cljc, so its reader conditionals are
;; read, and the feature is :cljf. A branch nobody selects is read and
;; dropped, so the :cljs one may hold #js.
(def rc-pick #?(:clj :clj-side :cljs #js {} :cljf :fortran))
(def rc-splice [1 #?@(:cljf [2 3]) 4])
#?(:cljs (this-form-is-never-read))
