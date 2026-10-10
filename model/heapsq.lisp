; clotran's heap under the model (PLAN step 33, stage 2): THE SEQ
; OPERATIONS on what is already there -- first, next, rest and seq of nil,
; of a list and of a lazy cell already realised -- as reads of the heap,
; at the level the Fortran is generated from (src/f/gen/heap_gen.inc),
; guard-verified. Both the flat executor (flat_seq_op) and the VM's prim
; (rt_prim1) answer through it; what it does not answer -- a cell not yet
; realised, a vector's seq view, a chunk -- goes the runtime's full way.
;
; The object's fields, as GC.f90 lays them out:
;   h-okind  its kind: 1 a list cell (OBJ_CONS), 6 a lazy cell (OBJ_LAZY)
;   h-oi1    a list's count; a lazy cell's state, 0 pending, 1 a cons
;            (head in slot 1, tail in slot 2), 2 empty, 3 delegating (the
;            seq in slot 1), 4 being realised
;   word 5o+k (h-otag, h-oref)  object o's slot k, 0-based
;
; THE ANSWER IS A PLACE, not a value: 0 not answered, 1 nil, 2 the
; argument itself, else the word 5o+k whose slot holds it (o >= 1, so
; >= 5). A slot's value is more than its tag and ref -- an integer's ival
; -- so the runtime copies the slot the model names; nothing is built,
; and nothing allocates.
;
; The operation is named by the runtime's builtin id (Eval.f90): 9 first,
; 39 next, 10 rest, 27 seq -- so a caller holding the builtin passes its id.
;
; Theorems (this book):
;   hpg-seq-op-place     a place answered is a slot inside the pool
;   hpg-seq-op-realised  a lazy cell is read only when realised, the
;                        argument's and, for next, its tail's: what
;                        lazy-cell.lisp's done-reads-realised and
;                        realised-stays make safe without a lock
;   hpg-seq-op-nonempty  seq answers a list or a cell itself only when it
;                        is not empty, as Clojure's seq does
;   hpg-seq-op-reads     at most 7 reads of the heap: O(1); hpg-seq-op-time
;                        the time they take at any weight per read

(in-package "ACL2")

(include-book "heaprn")

(hsb64-elems h-oi1p) (hpg-elem oi1)

; ---- READS ------------------------------------------------------------------------------

(defun hpg-ot (j hpg)
  (declare (xargs :stobjs hpg :guard (sb64p j)))
  (if (and (<= 0 j) (< j (h-otag-length hpg))) (h-otagi j hpg) -1))

(defun hpg-or (j hpg)
  (declare (xargs :stobjs hpg :guard (sb64p j)))
  (if (and (<= 0 j) (< j (h-oref-length hpg))) (h-orefi j hpg) -1))

(defun hpg-okd (o hpg)
  (declare (xargs :stobjs hpg :guard (sb64p o)))
  (if (and (<= 0 o) (< o (h-okind-length hpg))) (h-okindi o hpg) -1))

(defun hpg-oi (o hpg)
  (declare (xargs :stobjs hpg :guard (sb64p o)))
  (if (and (<= 0 o) (< o (h-oi1-length hpg))) (h-oi1i o hpg) -1))

(defthm hpg-reads-sb64
  (implies (and (hpgp hpg) (integerp j))
           (and (sb64p (hpg-ot j hpg)) (sb64p (hpg-or j hpg)) (sb64p (hpg-okd j hpg)) (sb64p (hpg-oi j hpg))))
  :hints (("Goal" :in-theory (disable nth))))
(defthm hpg-ot-int (implies (and (hpgp hpg) (integerp j)) (integerp (hpg-ot j hpg))) :rule-classes :type-prescription)
(defthm hpg-or-int (implies (and (hpgp hpg) (integerp j)) (integerp (hpg-or j hpg))) :rule-classes :type-prescription)
(defthm hpg-okd-int (implies (and (hpgp hpg) (integerp j)) (integerp (hpg-okd j hpg))) :rule-classes :type-prescription)
(defthm hpg-oi-int (implies (and (hpgp hpg) (integerp j)) (integerp (hpg-oi j hpg))) :rule-classes :type-prescription)
(in-theory (disable hpg-ot hpg-or hpg-okd hpg-oi))

; an object, all five of its slots inside the pool
(defun hpg-obj-at (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (and (equal tag 8) (< 0 ref) (< ref *hb40*)
       (< (+ 4 (* 5 ref)) (h-otag-length hpg)) (< (+ 4 (* 5 ref)) (h-oref-length hpg))))

; ---- THE OPERATIONS --------------------------------------------------------------------

; next of a realised cons cell o: the seq of its tail, word 5o+2, when that
; needs nothing done -- nil, a list (itself while not empty), a lazy cell
; realised (itself, nil, or what it delegates to)
(defun hpg-next-tail (o hpg)
  (declare (xargs :stobjs hpg :guard (and (natp o) (< o *hb40*))))
  (let* ((w (+ 2 (* 5 o)))
         (tg (hpg-ot w hpg))
         (tr (hpg-or w hpg)))
    (cond ((equal tg 0) 1)
          ((not (hpg-obj-at tg tr hpg)) 0)
          ((equal (hpg-okd tr hpg) 1) (if (< 0 (hpg-oi tr hpg)) w 1))
          ((equal (hpg-okd tr hpg) 6)
           (case (hpg-oi tr hpg)
             (1 w)
             (2 1)
             (3 (+ 1 (* 5 tr)))
             (otherwise 0)))
          (t 0))))

; op on the value (tag, ref)
(defun hpg-seq-op (op tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p op) (sb64p tag) (sb64p ref))))
  (cond ((not (or (equal op 9) (equal op 39) (equal op 27) (equal op 10))) 0)
        ((equal tag 0) (if (equal op 10) 0 1))
        ((not (hpg-obj-at tag ref hpg)) 0)
        (t (let ((kd (hpg-okd ref hpg))
                 (n (hpg-oi ref hpg))
                 (b (* 5 ref)))
             (cond ((equal kd 6)
                    (cond ((equal op 27) (case n (1 2) (2 1) (3 (+ 1 b)) (otherwise 0)))
                          ((equal op 9) (case n (1 (+ 1 b)) (2 1) (otherwise 0)))
                          ((equal op 10) (if (equal n 1) (+ 2 b) 0))
                          ((equal op 39) (case n (1 (hpg-next-tail ref hpg)) (2 1) (otherwise 0)))
                          (t 0)))
                   ((equal kd 1)
                    (cond ((equal op 9) (if (< 0 n) b 1))
                          ((equal op 27) (if (< 0 n) 2 1))
                          (t 0)))
                   (t 0))))))

; ---- WHAT IT ANSWERS --------------------------------------------------------------------

(defthm hpg-seq-op-place
  (implies (and (hpgp hpg) (integerp ref) (< 2 (hpg-seq-op op tag ref hpg)))
           (and (natp (hpg-seq-op op tag ref hpg))
                (<= 5 (hpg-seq-op op tag ref hpg))
                (< (hpg-seq-op op tag ref hpg) (len (nth *h-otagi* hpg)))
                (< (hpg-seq-op op tag ref hpg) (len (nth *h-orefi* hpg))))))

; a lazy cell, read only realised
(defun hpg-realised (o hpg)
  (declare (xargs :stobjs hpg :guard (sb64p o)))
  (member (hpg-oi o hpg) '(1 2 3)))

(defthm hpg-seq-op-realised
  (implies (and (not (equal (hpg-seq-op op tag ref hpg) 0))
                (equal tag 8) (equal (hpg-okd ref hpg) 6))
           (and (hpg-realised ref hpg)
                (implies (and (equal op 39) (equal (hpg-oi ref hpg) 1)
                              (equal (hpg-ot (+ 2 (* 5 ref)) hpg) 8)
                              (equal (hpg-okd (hpg-or (+ 2 (* 5 ref)) hpg) hpg) 6))
                         (hpg-realised (hpg-or (+ 2 (* 5 ref)) hpg) hpg)))))

; seq answers the argument itself only when it is not empty
(defun hpg-nonempty (tag ref hpg)
  (declare (xargs :stobjs hpg :guard (and (sb64p tag) (sb64p ref))))
  (and (equal tag 8)
       (or (and (equal (hpg-okd ref hpg) 1) (< 0 (hpg-oi ref hpg)))
           (and (equal (hpg-okd ref hpg) 6) (equal (hpg-oi ref hpg) 1)))))

(defthm hpg-seq-op-nonempty
  (implies (and (integerp ref) (equal (hpg-seq-op 27 tag ref hpg) 2))
           (hpg-nonempty tag ref hpg)))

; a word 5a+1 is never a word 5b+2
(defthm hpg-words-apart
  (implies (and (integerp a) (integerp b)) (not (equal (+ 1 (* 5 a)) (+ 2 (* 5 b)))))
  :hints (("Goal" :cases ((<= a b)))))

; and next answers its tail, word 5ref+2, only when that is not empty
(defthm hpg-next-tail-nonempty
  (implies (and (hpgp hpg) (natp o) (equal (hpg-next-tail o hpg) (+ 2 (* 5 o))))
           (hpg-nonempty (hpg-ot (+ 2 (* 5 o)) hpg) (hpg-or (+ 2 (* 5 o)) hpg) hpg)))

; ---- COST -------------------------------------------------------------------------------

; the heap reads hpg-seq-op makes on the path it takes (each hpg-ot,
; hpg-or, hpg-okd, hpg-oi one array read; hpg-obj-at reads only lengths)
(defun-nx hpg-next-tail-reads (o hpg)
  (let* ((w (+ 2 (* 5 o))) (tg (hpg-ot w hpg)) (tr (hpg-or w hpg)))
    (cond ((equal tg 0) 2)
          ((not (hpg-obj-at tg tr hpg)) 2)
          ((equal (hpg-okd tr hpg) 1) 4)
          (t 5))))

(defun-nx hpg-seq-op-reads (op tag ref hpg)
  (cond ((not (or (equal op 9) (equal op 39) (equal op 27) (equal op 10))) 0)
        ((equal tag 0) 0)
        ((not (hpg-obj-at tag ref hpg)) 0)
        ((and (equal (hpg-okd ref hpg) 6) (equal op 39) (equal (hpg-oi ref hpg) 1))
         (+ 2 (hpg-next-tail-reads ref hpg)))
        (t 2)))

(defthm hpg-seq-op-reads-bound
  (<= (hpg-seq-op-reads op tag ref hpg) 7)
  :rule-classes (:rewrite :linear))

; its TIME, for any weight wr a heap read takes (scripts/calibrate's): at
; most seven of them, whatever the heap
(defthm hpg-seq-op-time
  (implies (natp wr) (<= (* wr (hpg-seq-op-reads op tag ref hpg)) (* 7 wr)))
  :hints (("Goal" :in-theory (disable hpg-seq-op-reads) :nonlinearp t)))
