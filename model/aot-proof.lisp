; WHAT THE ELIGIBILITY SCAN MEANS (model/aot.lisp's aot-sc and aot-fr), over
; the runs of a node anpass-runs.lisp's tr models -- exec.inc's, a recur an
; event (:recur . to-the-fn?) -- and what it costs.
;
;   aot-tc-indep      a node with no recur under it (aot-fr) passes the tail
;                     check in every position or in none: tail position
;                     changes nothing under it
;   aot-handed-norec  so a node with no recur under it, its tail check
;                     passed in its position, makes no recur in any run:
;                     the interpreter runs it whole and hands back a value,
;                     never the recur marker
;   aot-sc-sound      when the scan passes, every node it reaches (aot-in)
;                     of a kind the compiler does not emit has no recur under it
;   aot-scan-norec    the two together: when the scan passes, every node the
;                     compiler hands to the interpreter makes no recur in any run
;   aot-sc-steps-bound  the scan makes at most s(s + 1) calls, s the nodes
;                     and sequence steps of its walk (aot-sz) -- a node's own
;                     recur search again at each node not emitted, as
;                     compiler.cljf's tree-seq did
;
; Assumed, not proved here: the analyzer's tail check passed at each node in
; its own position (anp-tc 0 y 0 0 tt is 0 for the tt its parent gives it):
; analyze.inc checks each fn body at its top (tail_ok), and the positions
; under it are anp-tc's; that the top's passing gives each node's is not
; derived here.

(in-package "ACL2")

(include-book "aot")
(include-book "anpass-sound")

; ---- TAIL POSITION CHANGES NOTHING UNDER A NODE WITH NO RECUR ------------------------------

(defthm aot-reads-nonast
  (implies (not (ast-p x)) (and (equal (ast-kid x i) nil) (equal (ast-alt x i) nil) (equal (ast-s3 x) nil) (equal (aot-bod x i) nil)))
  :hints (("Goal" :in-theory (enable ast-kid ast-alt ast-s3 aot-bod))))

(defthm aot-fr-nonast (implies (not (ast-p x)) (not (aot-fr fl x j m))) :hints (("Goal" :expand ((aot-fr fl x j m)))))

(defthm aot-kid-nonnat (implies (not (natp i)) (equal (ast-kid x i) nil)) :hints (("Goal" :in-theory (enable ast-kid))))

(defthm aot-fr-nil (equal (aot-fr 0 nil 0 0) nil) :hints (("Goal" :in-theory (enable ast-kind ast-p))))
(defthm aot-ch-nonast (implies (not (ast-p x)) (equal (aot-ch fl x i) nil))
  :hints (("Goal" :in-theory (enable ast-kid ast-alt aot-bod))))

(defthm aot-fr-seq-elem
  (implies (and (not (aot-fr fl x j m)) (not (equal fl 0)) (natp j) (natp i) (<= j i) (integerp m) (< i m))
           (not (aot-fr 0 (aot-ch fl x i) 0 0)))
  :hints (("Goal" :induct (aot-fr fl x j m) :in-theory (disable aot-ch))))

(defthm aot-fr-kid
  (implies (and (not (aot-fr 1 x 0 (ast-nkids x))) (natp i))
           (not (aot-fr 0 (ast-kid x i) 0 0)))
  :hints (("Goal" :cases ((< i (ast-nkids x)))
           :use ((:instance aot-fr-seq-elem (fl 1) (j 0) (m (ast-nkids x))))
           :in-theory (enable ast-kid ast-nkids))))

(defthm aot-fr-alt
  (implies (and (not (aot-fr 3 x 0 (ast-nalts x))) (natp i))
           (not (aot-fr 0 (ast-alt x i) 0 0)))
  :hints (("Goal" :cases ((< i (ast-nalts x)))
           :use ((:instance aot-fr-seq-elem (fl 3) (j 0) (m (ast-nalts x))))
           :in-theory (enable ast-alt ast-nalts))))

(defthm aot-fr-0-kid
  (implies (and (not (aot-fr 0 x j m))
                (not (member (ast-kind x) '(12 14 15 20)))
                (or (not (equal (ast-kind x) 18)) (equal i 0) (equal i 1)))
           (not (aot-fr 0 (ast-kid x i) 0 0)))
  :hints (("Goal" :cases ((natp i)) :expand ((aot-fr 0 x j m)) :in-theory (disable aot-fr))))

(defthm aot-fr-0-alt
  (implies (and (not (aot-fr 0 x j m)) (natp i) (member (ast-kind x) '(18 19)))
           (not (aot-fr 0 (ast-alt x i) 0 0)))
  :hints (("Goal" :expand ((aot-fr 0 x j m)) :in-theory (disable aot-fr))))

(defthm aot-fr-0-s3
  (implies (and (not (aot-fr 0 x j m)) (equal (ast-kind x) 10))
           (not (aot-fr 0 (ast-s3 x) 0 0)))
  :hints (("Goal" :expand ((aot-fr 0 x j m)) :in-theory (disable aot-fr))))

(defthm aot-fr-0-recur (implies (equal (ast-kind x) 16) (aot-fr 0 x j m)))

(defthm aot-fr-0-seqs
  (implies (not (aot-fr 0 x j m))
           (and (implies (member (ast-kind x) '(18 19)) (not (aot-fr 3 x 0 (ast-nalts x))))
                (implies (not (member (ast-kind x) '(12 14 15 18 20))) (not (aot-fr 1 x 0 (ast-nkids x))))))
  :hints (("Goal" :expand ((aot-fr 0 x j m)) :in-theory (disable aot-fr))))

(defthm aot-tc-indep
  (implies (and (not (aot-fr fl x j m)) (or (equal fl 0) (equal fl 1) (equal fl 3)))
           (equal (anp-tc fl x j m tt) (anp-tc fl x j m 0)))
  :hints (("Goal" :induct (anp-tc fl x j m tt) :do-not '(generalize eliminate-destructors))))

(defthm aot-handed-norec
  (implies (and (not (aot-fr 0 x 0 0)) (equal (anp-tc 0 x 0 0 tt) 0))
           (no-rec (tr 0 x 0 0 L os n)))
  :hints (("Goal" :use ((:instance tr-tail (fl 0) (j 0) (m 0)) (:instance aot-tc-indep (fl 0) (j 0) (m 0)))
           :in-theory (e/d (tail-all) (tr-tail aot-tc-indep anp-tc tr)))))

; ---- WHAT THE SCAN REACHES ----------------------------------------------------------------

(defun aot-in (y fl x j m)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (and (not (equal k 0))
             (or (equal y x)
                 (aot-in y 1 x 0 (ast-nkids x))
                 (and (equal k *n-def*) (aot-in y 0 (ast-s3 x) 0 0))
                 (and (or (equal k *n-try*) (equal k *n-case*) (equal k *n-deftype*)) (aot-in y 3 x 0 (ast-nalts x)))
                 (and (or (equal k *n-fn*) (equal k *n-lazy*)) (aot-in y 5 x 0 (aot-nbods x))))))
    (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m)
         (or (aot-in y 0 (aot-ch fl x j) 0 0) (aot-in y fl x (+ 1 j) m)))))

(defthm aot-sc-sound
  (implies (and (not (aot-sc fl x j m)) (aot-in y fl x j m) (not (aot-cop (ast-kind y))))
           (not (aot-fr 0 y 0 0)))
  :hints (("Goal" :induct (aot-in y fl x j m) :in-theory (disable aot-ch aot-cop aot-fr))))

(defthm aot-scan-norec
  (implies (and (not (aot-sc 0 x 0 0)) (aot-in y 0 x 0 0) (not (aot-cop (ast-kind y)))
                (equal (anp-tc 0 y 0 0 tt) 0))
           (no-rec (tr 0 y 0 0 L os n)))
  :hints (("Goal" :use ((:instance aot-sc-sound (fl 0) (j 0) (m 0)) (:instance aot-handed-norec (x y)))
           :in-theory (disable aot-sc-sound aot-handed-norec aot-sc aot-in aot-cop aot-fr tr anp-tc))))

; ---- WHAT IT COSTS ------------------------------------------------------------------------
;
; a call each: aot-fr-steps and aot-sc-steps count the calls each makes;
; aot-sz the calls of the scan's walk with every branch taken

(defun aot-fr-steps (fl x j m)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (cond ((equal k *n-recur*) 1)
              ((or (equal k 0) (equal k *n-loop*) (equal k *n-fn*) (equal k *n-lazy*) (equal k *n-deftype*)) 1)
              ((equal k *n-try*)
               (+ 1 (aot-fr-steps 0 (ast-kid x 0) 0 0) (aot-fr-steps 3 x 0 (ast-nalts x)) (aot-fr-steps 0 (ast-kid x 1) 0 0)))
              ((equal k *n-case*) (+ 1 (aot-fr-steps 3 x 0 (ast-nalts x)) (aot-fr-steps 1 x 0 (ast-nkids x))))
              ((equal k *n-def*) (+ 1 (aot-fr-steps 0 (ast-s3 x) 0 0) (aot-fr-steps 1 x 0 (ast-nkids x))))
              (t (+ 1 (aot-fr-steps 1 x 0 (ast-nkids x))))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (aot-fr-steps 0 (aot-ch fl x j) 0 0) (aot-fr-steps fl x (+ 1 j) m))
      1)))

(defun aot-sc-steps (fl x j m)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (if (equal k 0) 1
          (+ 1 (if (aot-cop k) 0 (aot-fr-steps 0 x 0 0))
             (aot-sc-steps 1 x 0 (ast-nkids x))
             (if (equal k *n-def*) (aot-sc-steps 0 (ast-s3 x) 0 0) 0)
             (if (or (equal k *n-try*) (equal k *n-case*) (equal k *n-deftype*)) (aot-sc-steps 3 x 0 (ast-nalts x)) 0)
             (if (or (equal k *n-fn*) (equal k *n-lazy*)) (aot-sc-steps 5 x 0 (aot-nbods x)) 0))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (aot-sc-steps 0 (aot-ch fl x j) 0 0) (aot-sc-steps fl x (+ 1 j) m))
      1)))

(defun aot-sz (fl x j m)
  (declare (xargs :measure (anp-meas fl x j m nil)))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (if (equal k 0) 1
          (+ 1 (aot-sz 1 x 0 (ast-nkids x))
             (aot-sz 0 (ast-s3 x) 0 0) (aot-sz 3 x 0 (ast-nalts x)) (aot-sz 5 x 0 (aot-nbods x))
             (aot-sz 0 (ast-kid x 0) 0 0) (aot-sz 0 (ast-kid x 1) 0 0))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (+ 1 (aot-sz 0 (aot-ch fl x j) 0 0) (aot-sz fl x (+ 1 j) m))
      1)))

(defthm aot-sz-pos (<= 1 (aot-sz fl x j m)) :rule-classes :linear)

; the recur search walks part of what the scan's walk does
(defthm aot-fr-steps-sz
  (implies (or (equal fl 0) (equal fl 1) (equal fl 3))
           (<= (aot-fr-steps fl x j m) (aot-sz fl x j m)))
  :hints (("Goal" :induct (aot-fr-steps fl x j m) :expand ((aot-sz 0 x j m)) :in-theory (disable aot-ch)))
  :rule-classes :linear)

(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm sq-sum
         (implies (and (natp a) (natp b) (natp p) (natp q) (<= a (* p (+ 1 p))) (<= b (* q (+ 1 q))))
                  (<= (+ a b) (* (+ p q) (+ 1 p q))))
         :hints (("Goal" :nonlinearp t))))

(defthm aot-sc-steps-bound
  (<= (aot-sc-steps fl x j m) (* (aot-sz fl x j m) (+ 1 (aot-sz fl x j m))))
  :hints (("Goal" :induct (aot-sc-steps fl x j m) :expand ((aot-sz 0 x j m)) :in-theory (disable aot-ch aot-cop)
           :do-not '(generalize eliminate-destructors))
          (and stable-under-simplificationp '(:nonlinearp t)))
  :rule-classes :linear)
