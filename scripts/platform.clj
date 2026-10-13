;; platform.clj -- what the scripts need to know of the system they run on,
;; in one place: (load-file (str repo "/scripts/platform.clj")).
(ns platform
  (:require [clojure.string :as str]
            [babashka.fs :as fs]
            [babashka.process :as p]))

(def windows? (fs/windows?))
(def mac? (and (not windows?) (= "Darwin" (str/trim (:out (p/shell {:out :string} "uname" "-s"))))))

;; a shared library's extension: what clotran compile writes and loads
(def soext (cond windows? "dll" mac? "dylib" :else "so"))

(defn compiled-link
  "What a compiled namespace's library links with after its object, to
  reach clotran_* in the running binary: macOS is told they resolve at
  load time, Windows links clotran-bin.exe's import library (scanned where
  it stands, so after the object), Linux needs nothing."
  [repo]
  (cond mac? ["-Wl,-undefined,dynamic_lookup"]
        windows? [(str repo "/build/libclotran-bin.dll.a")]
        :else []))

(defn slashes
  "A path with / between its parts, as it goes into a Clojure string: a
  Windows \\ there would read as an escape."
  [p]
  (str/replace (str p) "\\" "/"))

