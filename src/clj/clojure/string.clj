;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Clojure String utilities

It is poor form to (:use clojure.string). Instead, use require
with :as to specify a prefix, e.g.

(ns your.namespace.here
  (:require [clojure.string :as str]))

Design notes for clojure.string:

1. Strings are objects (as opposed to sequences). As such, the
   string being manipulated is the first argument to a function;
   passing nil will result in a NullPointerException unless
   documented otherwise. If you want sequence-y behavior instead,
   use a sequence.

2. Functions are generally not lazy, and call straight to host
   methods where those are available and efficient.

3. Functions take advantage of String implementation details to
   write high-performing loop/recurs instead of using higher-order
   functions. (This is not idiomatic in general-purpose application
   code.)

4. When a function is documented to accept a string argument, it
   will take any implementation of the correct *interface* on the
   host platform. In host, this is CharSequence, which is more
   general than String. In ordinary usage you will almost always
   pass concrete strings. If you are doing something unusual,
   e.g. passing a mutable implementation of CharSequence, then
   thread-safety is your responsibility."
      :author "Stuart Sierra, Stuart Halloway, David Liebke"}
  clojure.string
  (:refer-clojure :exclude (replace reverse))
  (:import 
           ))

(set! *warn-on-reflection* true)

(defn ^clotran.host.string reverse
  "Returns s with its characters reversed."
  {:added "1.2"}
  [^clotran.host.char_sequence s]
  (.toString (.reverse (clotran.host.string_builder. s))))

(defn ^clotran.host.string re-quote-replacement
  "Given a replacement string that you wish to be a literal
   replacement for a pattern match in replace or replace-first, do the
   necessary escaping of special characters in the replacement."
  {:added "1.5"}
  [^clotran.host.char_sequence replacement]
  (clotran.host.matcher/quoteReplacement (.toString ^clotran.host.char_sequence replacement)))

(defn- replace-by
  [^clotran.host.char_sequence s re f]
  (let [m (re-matcher re s)]
    (if (.find m)
      (let [buffer (clotran.host.string_buffer. (.length s))]
        (loop [found true]
          (if found
            (do (.appendReplacement m buffer (clotran.host.matcher/quoteReplacement (f (re-groups m))))
                (recur (.find m)))
            (do (.appendTail m buffer)
                (.toString buffer)))))
      s)))

(defn ^clotran.host.string replace
  "Replaces all instance of match with replacement in s.

   match/replacement can be:

   string / string
   char / char
   pattern / (string or function of match).

   See also replace-first.

   The replacement is literal (i.e. none of its characters are treated
   specially) for all cases above except pattern / string.

   For pattern / string, $1, $2, etc. in the replacement string are
   substituted with the string that matched the corresponding
   parenthesized group in the pattern.  If you wish your replacement
   string r to be used literally, use (re-quote-replacement r) as the
   replacement argument.  See also documentation for
   clotran.host.matcher's appendReplacement method.

   Example:
   (clojure.string/replace \"Almost Pig Latin\" #\"\\b(\\w)(\\w+)\\b\" \"$2$1ay\")
   -> \"lmostAay igPay atinLay\""
  {:added "1.2"}
  [^clotran.host.char_sequence s match replacement]
  (let [s (.toString s)]
    (cond 
     (instance? clotran.host.char match) (.replace s ^clotran.host.char match ^clotran.host.char replacement)
     (instance? clotran.host.char_sequence match) (.replace s ^clotran.host.char_sequence match ^clotran.host.char_sequence replacement)
     (instance? clotran.host.pattern match) (if (instance? clotran.host.char_sequence replacement)
                                 (.replaceAll (re-matcher ^clotran.host.pattern match s)
                                              (.toString ^clotran.host.char_sequence replacement))
                                 (replace-by s match replacement))
     :else (throw (clotran.host.illegal_argument_exception. (str "Invalid match arg: " match))))))

(defn- replace-first-by
  [^clotran.host.char_sequence s ^clotran.host.pattern re f]
  (let [m (re-matcher re s)]
    (if (.find m)
      (let [buffer (clotran.host.string_buffer. (.length s))
            rep (clotran.host.matcher/quoteReplacement (f (re-groups m)))]
        (.appendReplacement m buffer rep)
        (.appendTail m buffer)
        (str buffer))
      s)))

(defn- replace-first-char
  [^clotran.host.char_sequence s ^clotran.host.char match replace]
  (let [s (.toString s)
        i (.indexOf s (int match))]
    (if (= -1 i)
      s
      (str (subs s 0 i) replace (subs s (inc i))))))

(defn- replace-first-str
  [^clotran.host.char_sequence s ^clotran.host.string match ^clotran.host.string replace]
  (let [^clotran.host.string s (.toString s)
        i (.indexOf s match)]
    (if (= -1 i)
      s
      (str (subs s 0 i) replace (subs s (+ i (.length match)))))))

(defn ^clotran.host.string replace-first
  "Replaces the first instance of match with replacement in s.

   match/replacement can be:

   char / char
   string / string
   pattern / (string or function of match).

   See also replace.

   The replacement is literal (i.e. none of its characters are treated
   specially) for all cases above except pattern / string.

   For pattern / string, $1, $2, etc. in the replacement string are
   substituted with the string that matched the corresponding
   parenthesized group in the pattern.  If you wish your replacement
   string r to be used literally, use (re-quote-replacement r) as the
   replacement argument.  See also documentation for
   clotran.host.matcher's appendReplacement method.

   Example:
   (clojure.string/replace-first \"swap first two words\"
                                 #\"(\\w+)(\\s+)(\\w+)\" \"$3$2$1\")
   -> \"first swap two words\""
  {:added "1.2"}
  [^clotran.host.char_sequence s match replacement]
  (let [s (.toString s)]
    (cond
     (instance? clotran.host.char match)
     (replace-first-char s match replacement)
     (instance? clotran.host.char_sequence match)
     (replace-first-str s (.toString ^clotran.host.char_sequence match)
                        (.toString ^clotran.host.char_sequence replacement))
     (instance? clotran.host.pattern match)
     (if (instance? clotran.host.char_sequence replacement)
       (.replaceFirst (re-matcher ^clotran.host.pattern match s)
                      (.toString ^clotran.host.char_sequence replacement))
       (replace-first-by s match replacement))
     :else (throw (clotran.host.illegal_argument_exception. (str "Invalid match arg: " match))))))


(defn ^clotran.host.string join
  "Returns a string of all elements in coll, as returned by (seq coll),
   separated by an optional separator."
  {:added "1.2"}
  ([coll]
     (apply str coll))
  ([separator coll]
     (loop [sb (clotran.host.string_builder. (str (first coll)))
            more (next coll)
            sep (str separator)]
       (if more
         (recur (-> sb (.append sep) (.append (str (first more))))
                (next more)
                sep)
         (str sb)))))

(defn ^clotran.host.string capitalize
  "Converts first character of the string to upper-case, all other
  characters to lower-case."
  {:added "1.2"}
  [^clotran.host.char_sequence s]
  (let [s (.toString s)]
    (if (< (count s) 2)
      (.toUpperCase s)
      (str (.toUpperCase (subs s 0 1))
           (.toLowerCase (subs s 1))))))

(defn ^clotran.host.string upper-case
  "Converts string to all upper-case."
  {:added "1.2"}
  [^clotran.host.char_sequence s]
  (.. s toString toUpperCase))

(defn ^clotran.host.string lower-case
  "Converts string to all lower-case."
  {:added "1.2"}
  [^clotran.host.char_sequence s]
  (.. s toString toLowerCase))

(defn split
  "Splits string on a regular expression.  Optional argument limit is
  the maximum number of parts. Not lazy. Returns vector of the parts.
  Trailing empty strings are not returned - pass limit of -1 to return all."
  {:added "1.2"}
  ([^clotran.host.char_sequence s ^clotran.host.pattern re]
     (clotran.host.lazily_persistent_vector/createOwning (.split re s)))
  ([ ^clotran.host.char_sequence s ^clotran.host.pattern re limit]
     (clotran.host.lazily_persistent_vector/createOwning (.split re s limit))))

(defn split-lines
  "Splits s on \\n or \\r\\n. Trailing empty lines are not returned."
  {:added "1.2"}
  [^clotran.host.char_sequence s]
  (split s #"\r?\n"))

(defn ^clotran.host.string trim
  "Removes whitespace from both ends of string."
  {:added "1.2"}
  [^clotran.host.char_sequence s]
  (let [len (.length s)]
    (loop [rindex len]
      (if (zero? rindex)
        ""
        (if (clotran.host.char/isWhitespace (.charAt s (dec rindex)))
          (recur (dec rindex))
          ;; there is at least one non-whitespace char in the string,
          ;; so no need to check for lindex reaching len.
          (loop [lindex 0]
            (if (clotran.host.char/isWhitespace (.charAt s lindex))
              (recur (inc lindex))
              (.. s (subSequence lindex rindex) toString))))))))

(defn ^clotran.host.string triml
  "Removes whitespace from the left side of string."
  {:added "1.2"}
  [^clotran.host.char_sequence s]
  (let [len (.length s)]
    (loop [index 0]
      (if (= len index)
        ""
        (if (clotran.host.char/isWhitespace (.charAt s index))
          (recur (unchecked-inc index))
          (.. s (subSequence index len) toString))))))

(defn ^clotran.host.string trimr
  "Removes whitespace from the right side of string."
  {:added "1.2"}
  [^clotran.host.char_sequence s]
  (loop [index (.length s)]
    (if (zero? index)
      ""
      (if (clotran.host.char/isWhitespace (.charAt s (unchecked-dec index)))
        (recur (unchecked-dec index))
        (.. s (subSequence 0 index) toString)))))

(defn ^clotran.host.string trim-newline
  "Removes all trailing newline \\n or return \\r characters from
  string.  Similar to Perl's chomp."
  {:added "1.2"}
  [^clotran.host.char_sequence s]
  (loop [index (.length s)]
    (if (zero? index)
      ""
      (let [ch (.charAt s (dec index))]
        (if (or (= ch \newline) (= ch \return))
          (recur (dec index))
          (.. s (subSequence 0 index) toString))))))

(defn blank?
  "True if s is nil, empty, or contains only whitespace."
  {:added "1.2"}
  [^clotran.host.char_sequence s]
  (if s
    (loop [index (int 0)]
      (if (= (.length s) index)
        true
        (if (clotran.host.char/isWhitespace (.charAt s index))
          (recur (inc index))
          false)))
    true))

(defn ^clotran.host.string escape
  "Return a new string, using cmap to escape each character ch
   from s as follows:
   
   If (cmap ch) is nil, append ch to the new string.
   If (cmap ch) is non-nil, append (str (cmap ch)) instead."
  {:added "1.2"}
  [^clotran.host.char_sequence s cmap]
  (loop [index (int 0)
         buffer (clotran.host.string_builder. (.length s))]
    (if (= (.length s) index)
      (.toString buffer)
      (let [ch (.charAt s index)]
        (if-let [replacement (cmap ch)]
          (.append buffer replacement)
          (.append buffer ch))
        (recur (inc index) buffer)))))

(defn index-of
  "Return index of value (string or char) in s, optionally searching
  forward from from-index. Return nil if value not found."
  {:added "1.8"}
  ([^clotran.host.char_sequence s value]
  (let [result ^long
        (if (instance? clotran.host.char value)
          (.indexOf (.toString s) ^int (.charValue ^clotran.host.char value))
          (.indexOf (.toString s) ^clotran.host.string value))]
    (if (= result -1)
      nil
      result)))
  ([^clotran.host.char_sequence s value ^long from-index]
  (let [result ^long
        (if (instance? clotran.host.char value)
          (.indexOf (.toString s) ^int (.charValue ^clotran.host.char value) (unchecked-int from-index))
          (.indexOf (.toString s) ^clotran.host.string value (unchecked-int from-index)))]
    (if (= result -1)
      nil
      result))))

(defn last-index-of
  "Return last index of value (string or char) in s, optionally
  searching backward from from-index. Return nil if value not found."
  {:added "1.8"}
  ([^clotran.host.char_sequence s value]
  (let [result ^long
        (if (instance? clotran.host.char value)
          (.lastIndexOf (.toString s) ^int (.charValue ^clotran.host.char value))
          (.lastIndexOf (.toString s) ^clotran.host.string value))]
    (if (= result -1)
      nil
      result)))
  ([^clotran.host.char_sequence s value ^long from-index]
  (let [result ^long
        (if (instance? clotran.host.char value)
          (.lastIndexOf (.toString s) ^int (.charValue ^clotran.host.char value) (unchecked-int from-index))
          (.lastIndexOf (.toString s) ^clotran.host.string value (unchecked-int from-index)))]
    (if (= result -1)
      nil
      result))))

(defn starts-with?
  "True if s starts with substr."
  {:added "1.8"}
  [^clotran.host.char_sequence s ^clotran.host.string substr]
  (.startsWith (.toString s) substr))

(defn ends-with?
  "True if s ends with substr."
  {:added "1.8"}
  [^clotran.host.char_sequence s ^clotran.host.string substr]
  (.endsWith (.toString s) substr))

(defn includes?
  "True if s includes substr."
  {:added "1.8"}
  [^clotran.host.char_sequence s ^clotran.host.char_sequence substr]
  (.contains (.toString s) substr))
