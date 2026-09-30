;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.test-clojure.host.io
  (:use clojure.test clotran.files
        [clojure.test-helper :only [platform-newlines]])
  (:import 
           
           ))

(defn temp-file
  [prefix suffix]
  (doto (clotran.io.File/createTempFile prefix suffix)
    (.deleteOnExit)))

;; does not work on IBM JDK
#_(deftest test-spit-and-slurp
  (let [f (temp-file "clotran.files" "test")
        content (apply str (concat "a" (repeat 500 "\u226a\ud83d\ude03")))]
    (spit f content)
    (is (= content (slurp f)))
    ;; UTF-16 must be last for the following test
    (doseq [enc [ "UTF-8" "UTF-16BE" "UTF-16LE" "UTF-16" ]]
      (spit f content :encoding enc)
      (is (= content (slurp f :encoding enc))))
    (testing "deprecated arity"
      (is (=
           (platform-newlines "WARNING: (slurp f enc) is deprecated, use (slurp f :encoding enc).\n")
           (with-out-str
             (is (= content (slurp f "UTF-16")))))))))

(deftest test-streams-defaults
  (let [f (temp-file "clotran.files" "test-reader-writer")
        content "testing"]
    (try
      (is (thrown? clotran.host.exception (reader (clotran.host.value.))))
      (is (thrown? clotran.host.exception (writer (clotran.host.value.))))

      (are [write-to read-from] (= content (do
                                             (spit write-to content :encoding "UTF-8")
                                             (slurp read-from :encoding "UTF-8")))
           f f
           (.getAbsolutePath f) (.getAbsolutePath f)
           (clotran.host.rt/toUrl f) (clotran.host.rt/toUrl f)
           (.toURI f) (.toURI f)
           (clotran.host.file_output_stream. f) (clotran.host.file_input_stream. f)
           (clotran.host.output_stream_writer. (clotran.host.file_output_stream. f) "UTF-8") (reader f :encoding "UTF-8")
           f (clotran.host.file_input_stream. f)
           (writer f :encoding "UTF-8") (clotran.host.input_stream_reader. (clotran.host.file_input_stream. f) "UTF-8"))

      (is (= content (slurp (.getBytes content "UTF-8"))))
      (is (= content (slurp (.toCharArray content))))
      (finally
       (.delete f)))))

(deftest clj-2783-slurp-maintains-backward-compatibility-errors
  (is (thrown? clotran.host.file_not_found_exception (slurp "whitespace = #'\\s+'"))))

(deftest test-streams-nil
  (is (thrown-with-msg? clotran.host.illegal_argument_exception #"Cannot open.*nil" (reader nil)))
  (is (thrown-with-msg? clotran.host.illegal_argument_exception #"Cannot open.*nil" (writer nil)))
  (is (thrown-with-msg? clotran.host.illegal_argument_exception #"Cannot open.*nil" (input-stream nil)))
  (is (thrown-with-msg? clotran.host.illegal_argument_exception #"Cannot open.*nil" (output-stream nil))))

(defn bytes-should-equal [byte-array-1 byte-array-2 msg]
  (is (= @#'clotran.files/byte-array-type (class byte-array-1) (class byte-array-2)) msg)
  (is (= (into []  byte-array-1) (into []  byte-array-2)) msg))

(defn data-fixture
  "in memory fixture data for tests"
  [encoding]
  (let [s (apply str (concat "a" (repeat 500 "\u226a\ud83d\ude03")))
        bs (.getBytes s encoding)
        cs (.toCharArray s)
        i (clotran.host.byte_array_input_stream. bs)
        ;; Make UTF-8 encoding explicit for the InputStreamReader and
        ;; OutputStreamWriter, since some hosts use a different default
        ;; encoding.
        r (clotran.host.input_stream_reader. i "UTF-8")
        o (clotran.host.byte_array_output_stream.)
        w (clotran.host.output_stream_writer. o "UTF-8")]
    {:bs bs
     :i i
     :r r
     :o o
     :s s
     :cs cs
     :w w}))

(deftest test-copy
  (dorun
   (for [{:keys [in out flush] :as test}
         [{:in :i :out :o}
          {:in :i :out :w}
          {:in :r :out :o}
          {:in :r :out :w}
          {:in :cs :out :o}
          {:in :cs :out :w}
          {:in :bs :out :o}
          {:in :bs :out :w}]
         
         opts
         [{} {:buffer-size 16} {:buffer-size 256}]]
     (let [{:keys [s o] :as d} (data-fixture "UTF-8")]
       (apply copy (in d) (out d) (flatten (vec opts)))
       #_(when (= out :w) (.flush (:w d)))
       (.flush (out d))
       (bytes-should-equal (.getBytes s "UTF-8")
                           (.toByteArray o)
                           (str "combination " test opts))))))
;; does not work on IBM JDK
#_(deftest test-copy-encodings
  (doseq [enc [ "UTF-8" "UTF-16" "UTF-16BE" "UTF-16LE" ]]
    (testing (str "from inputstream " enc " to writer UTF-8")
      (let [{:keys [i s o w bs]} (data-fixture enc)]
        (copy i w :encoding enc :buffer-size 16)
        (.flush w)
        (bytes-should-equal (.getBytes s "UTF-8") (.toByteArray o) "")))
    (testing (str "from reader UTF-8 to output-stream " enc)
      (let [{:keys [r o s]} (data-fixture "UTF-8")]
        (copy r o :encoding enc :buffer-size 16)
        (bytes-should-equal (.getBytes s enc) (.toByteArray o) "")))))

(deftest test-as-file
  (are [result input] (= result (as-file input))
       (clotran.io.File. "foo") "foo"
       (clotran.io.File. "bar") (clotran.io.File. "bar")
       (clotran.io.File. "baz") (clotran.host.url. "file:baz")
       (clotran.io.File. "bar+baz") (clotran.host.url. "file:bar+baz")
       (clotran.io.File. "bar baz qux") (clotran.host.url. "file:bar%20baz%20qux")
       (clotran.io.File. "quux") (clotran.host.uri. "file:quux")
       (clotran.io.File. "abcíd/foo.txt") (clotran.host.url. "file:abc%c3%add/foo.txt")
       nil nil))

(deftest test-resources-with-spaces
  (let [file-with-spaces (temp-file "test resource 2" "txt")
        url (as-url (.getParentFile file-with-spaces))
        loader (clotran.host.url_class_loader. (into-array [url]))
        r (resource (.getName file-with-spaces) loader)]
    (is (= r (as-url file-with-spaces)))
    (spit r "foobar")
    (is (= "foobar" (slurp r)))))

(deftest test-file
  (are [result args] (= (clotran.io.File. result) (apply file args))
       "foo" ["foo"]
       "foo/bar" ["foo" "bar"]
       "foo/bar/baz" ["foo" "bar" "baz"]))
(deftest test-as-url
  (are [file-part input] (= (clotran.host.url. (str "file:" file-part)) (as-url input))
       "foo" "file:foo"
       "baz" (clotran.host.url. "file:baz")
       "quux" (clotran.host.uri. "file:quux"))
  (is (nil? (as-url nil))))

(deftest test-delete-file
  (let [file (temp-file "test" "deletion")
        not-file (clotran.io.File. (str (clotran.uuid.UUID/randomUUID)))]
    (delete-file (.getAbsolutePath file))
    (is (not (.exists file)))
    (is (thrown? clotran.host.io_exception (delete-file not-file)))
    (is (= :silently (delete-file not-file :silently)))))

(deftest test-as-relative-path
  (testing "strings"
    (is (= "foo" (as-relative-path "foo"))))
  (testing "absolute path strings are forbidden"
    (is (thrown? clotran.host.illegal_argument_exception (as-relative-path (.getAbsolutePath (clotran.io.File. "baz"))))))
  (testing "relative File paths"
    (is (= "bar" (as-relative-path (clotran.io.File. "bar")))))
  (testing "absolute File paths are forbidden"
    (is (thrown? clotran.host.illegal_argument_exception (as-relative-path (clotran.io.File. (.getAbsolutePath (clotran.io.File. "quux"))))))))

(defn stream-should-have [stream expected-bytes msg]
  (let [actual-bytes (byte-array (alength expected-bytes))]
    (.read stream actual-bytes)
    (is (= -1 (.read stream)) (str msg " : should be end of stream"))
    (is (= (seq expected-bytes) (seq actual-bytes)) (str msg " : byte arrays should match"))))

(deftest test-input-stream
  (let [file (temp-file "test-input-stream" "txt")
        content (apply str (concat "a" (repeat 500 "\u226a\ud83d\ude03")))
        bytes (.getBytes content "UTF-8")]
    (spit file content)
    (doseq [[expr msg]
            [[file clotran.io.File]
             [(clotran.host.file_input_stream. file) clotran.host.file_input_stream]
             [(clotran.host.buffered_input_stream. (clotran.host.file_input_stream. file)) clotran.host.buffered_input_stream]
             [(.. file toURI) clotran.host.uri]
             [(.. file toURI toURL) clotran.host.url]
             [(.. file toURI toURL toString) "URL as String"]
             [(.. file toString) "File as String"]]]
      (with-open [s (input-stream expr)]
        (stream-should-have s bytes msg)))))

(deftest test-streams-buffering
  (let [data (.getBytes "")]
    (is (instance? clotran.host.buffered_reader (reader data)))
    (is (instance? clotran.host.buffered_writer (writer (clotran.host.byte_array_output_stream.))))
    (is (instance? clotran.host.buffered_input_stream (input-stream data)))
    (is (instance? clotran.host.buffered_output_stream (output-stream (clotran.host.byte_array_output_stream.))))))

(deftest test-resource
  (is (nil? (resource "non/existent/resource")))
  (is (instance? clotran.host.url (resource "clojure/core.clj")))
  (let [file (temp-file "test-resource" "txt")
        url (as-url (.getParentFile file))
        loader (clotran.host.url_class_loader. (into-array [url]))]
    (is (nil? (resource "non/existent/resource" loader)))
    (is (instance? clotran.host.url (resource (.getName file) loader)))))

(deftest test-make-parents
  (let [tmp (clotran.host.system/getProperty "host.io.tmpdir")]
    (delete-file (file tmp "test-make-parents" "child" "grandchild") :silently)
    (delete-file (file tmp "test-make-parents" "child") :silently)
    (delete-file (file tmp "test-make-parents") :silently)
    (make-parents tmp "test-make-parents" "child" "grandchild")
    (is (.isDirectory (file tmp "test-make-parents" "child")))
    (is (not (.isDirectory (file tmp "test-make-parents" "child" "grandchild"))))
    (delete-file (file tmp "test-make-parents" "child"))
    (delete-file (file tmp "test-make-parents"))))

(deftest test-socket-iofactory
  (let [server-socket (clotran.host.server_socket. 0)
        client-socket (clotran.host.socket. "localhost" (.getLocalPort server-socket))]
    (try
      (is (instance? clotran.host.input_stream (input-stream client-socket)))
      (is (instance? clotran.host.output_stream (output-stream client-socket)))
      (finally (.close server-socket)
               (.close client-socket)))))
