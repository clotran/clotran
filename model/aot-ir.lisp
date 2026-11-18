; SLICE 4 of the ahead-of-time compiler (model/aot-PLAN.md): EMISSION, as an IR with a meaning.
;
; compiler.cljf's gen answers, per node, [code slot state]: the statements that compute the node,
; the temporary its value lands in, and the next free temporary. The statements are this IR, as
; data (compiler.cljf builds the same vectors; ir-lines prints each one as its Fortran template),
; for the kinds modelled so far -- the rest are still Fortran text there, (:owed e) here.
;
; THE IR. A program is a list of instructions over (fr bt): fr the frame of locals (exec's, ex-ev's
; fr: sv(b+1)), bt the procedure's slots sv(b+d) -- the pool's entries from b+2, then the temporaries.
;   (:const d v)   bt[d] := v                 clotran_set_nil/int/real/bool (emit-const)
;   (:get d s)     bt[d] := fr[s]             clotran_frame_get
;   (:clr s)       fr[s] := nil               clotran_frame_clear (a local's last read, ex-mark)
;   (:put s d)     fr[s] := bt[d]             clotran_frame_put
;   (:copy d s)    bt[d] := bt[s]             clotran_copy
;   (:deref d s)   bt[d] := the Var's value   clotran_deref (aot-deref: a Var is (:var v))
;   (:if s th el)  th when bt[s] is truthy, else el   if (clotran_bool(b + s) /= 0) then ... end if
; aot-ir-run: the meaning, (fr bt ok), ok nil at an instruction it does not know (it stops there).
; COST: aot-ir-steps, the instructions run, at most aot-ir-size (every instruction, both branches).
;
; THE COMPILE, (aot-cc fl e i n pool) = (code slot next), gen's case per kind (fl 1, gen-op), gen's
; copy of a pool slot that came with code (fl 0), gen-seq of a do from its i-th child (fl 2) and
; bind-slots then the body of a let from its i-th binding (fl 3). n is the next free temporary
; (fresh); pool is the host's pool (Eval.f90 compiled_pool, fn-procedure's pslots) as an alist
; ((kind c) slot linked): a Var (kind 3) and a constant no Fortran spells (kind 1), its slot, and
; whether the Var is direct-linked (dereffed once at entry). 4a: const local var if do let, every
; binding and test boxed. COST: aot-cc-cnt, the calls, at most 2 + 6 acl2-count(e) (aot-cc-cost, aot-ir-proof).

(in-package "ACL2")
(include-book "exec")

; ---- THE MEANING ---------------------------------------------------------------------------

(defun aot-deref (x) (if (and (consp x) (eq (car x) :var)) (cadr x) nil))

; one instruction but :if: (fr bt), nil when it is none the IR has
(defun aot-ir-step (x fr bt)
  (let ((a (nfix (cadr x))) (b (caddr x)))
    (case (car x)
      (:const (list fr (update-nth a b bt)))
      (:get (list fr (update-nth a (nth (nfix b) fr) bt)))
      (:clr (list (update-nth a nil fr) bt))
      (:put (list (update-nth a (nth (nfix b) bt) fr) bt))
      (:copy (list fr (update-nth a (nth (nfix b) bt) bt)))
      (:deref (list fr (update-nth a (aot-deref (nth (nfix b) bt)) bt)))
      (otherwise nil))))

(defun aot-ir-run (code fr bt)
  (declare (xargs :measure (acl2-count code)))
  (if (atom code)
      (list fr bt t)
    (let ((x (car code)))
      (if (and (consp x) (eq (car x) :if))
          (let ((r (aot-ir-run (if (truthy (nth (nfix (cadr x)) bt)) (caddr x) (cadddr x)) fr bt)))
            (if (caddr r) (aot-ir-run (cdr code) (car r) (cadr r)) r))
        (let ((s (aot-ir-step x fr bt)))
          (if s (aot-ir-run (cdr code) (car s) (cadr s)) (list fr bt nil)))))))

; COST: the instructions a run takes (an :if one, and its branch's)
(defun aot-ir-steps (code fr bt)
  (declare (xargs :measure (acl2-count code)))
  (if (atom code)
      0
    (let ((x (car code)))
      (if (and (consp x) (eq (car x) :if))
          (let* ((br (if (truthy (nth (nfix (cadr x)) bt)) (caddr x) (cadddr x))) (r (aot-ir-run br fr bt)))
            (+ 1 (aot-ir-steps br fr bt) (if (caddr r) (aot-ir-steps (cdr code) (car r) (cadr r)) 0)))
        (let ((s (aot-ir-step x fr bt)))
          (+ 1 (if s (aot-ir-steps (cdr code) (car s) (cadr s)) 0)))))))

(defun aot-ir-size (code)
  (declare (xargs :measure (acl2-count code)))
  (if (atom code)
      0
    (let ((x (car code)))
      (+ 1 (if (and (consp x) (eq (car x) :if)) (+ (aot-ir-size (caddr x)) (aot-ir-size (cadddr x))) 0)
         (aot-ir-size (cdr code))))))

(defthm aot-ir-cost (<= (aot-ir-steps code fr bt) (aot-ir-size code)) :rule-classes :linear)

; ---- THE COMPILE ---------------------------------------------------------------------------

(defun aot-pent (e pool)
  (and (or (equal (ex-kind e) 1) (equal (ex-kind e) 3)) (assoc-equal (list (ex-kind e) (ex-c e)) pool)))
(defun aot-inpool (s pool)
  (cond ((atom pool) nil) ((and (consp (car pool)) (equal (cadr (car pool)) s)) t) (t (aot-inpool s (cdr pool)))))

(defun aot-ccrank (fl) (case fl (0 3) (1 2) (otherwise 1)))
(defun aot-ccleft (fl e i) (nfix (- (if (member fl (quote (0 1 2))) (ex-nk e) (ex-i2 e)) (nfix i))))

(defun aot-cc (fl e i n pool)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (aot-ccrank fl)) (aot-ccleft fl e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n (nfix n)) (i (nfix i)))
    (case fl
      (0 (let* ((r (aot-cc 1 e 0 n pool)) (m (caddr r)))
           (if (and (consp (car r)) (aot-inpool (cadr r) pool))
               (list (append (car r) (list (list :copy m (cadr r)))) m (+ 1 m))
             r)))
      (1 (let ((p (aot-pent e pool)))
           (cond ((not (consp e)) (list (list (list :owed e)) n (+ 1 n)))
                 (p (if (and (equal k 3) (not (caddr p)))
                        (list (list (list :deref n (cadr p))) n (+ 1 n))
                      (list nil (cadr p) n)))
                 ((equal k 1) (list (list (list :const n (ex-c e))) n (+ 1 n)))
                 ((equal k 2) (list (if (ex-mark e)
                                        (list (list :get n (ex-i2 e)) (list :clr (ex-i2 e)))
                                      (list (list :get n (ex-i2 e))))
                                    n (+ 1 n)))
                 ((equal k 5) (if (zp nk) (list (list (list :const n nil)) n (+ 1 n)) (aot-cc 2 e 0 n pool)))
                 ((equal k 4)
                  (let* ((tr (aot-cc 0 (ex-kid-of e 0) 0 n pool)) (tc (car tr)) (ts (cadr tr)) (r (caddr tr))
                         (lg (if (consp tc) (list (list :const ts nil)) nil))
                         (th (aot-cc 0 (ex-kid-of e 1) 0 (+ 1 r) pool)) (m (caddr th))
                         (el (if (< 2 nk)
                                 (aot-cc 0 (ex-kid-of e 2) 0 m pool)
                               (list (list (list :const m nil)) m (+ 1 m))))
                         (cpt (if (equal (ex-kind (ex-kid-of e 1)) 16) nil (list (list :copy r (cadr th)))))
                         (cpe (if (and (< 2 nk) (equal (ex-kind (ex-kid-of e 2)) 16)) nil (list (list :copy r (cadr el))))))
                    (list (append tc (list (list :if ts (append lg (car th) cpt) (append lg (car el) cpe))))
                          r (caddr el))))
                 ((equal k 11) (aot-cc 3 e 0 n pool))
                 (t (list (list (list :owed e)) n (+ 1 n))))))
      ; a do from its i-th child: the last child's slot
      (2 (if (and (consp e) (< (+ 1 i) nk))
             (let* ((r (aot-cc 0 (ex-kid-of e i) 0 n pool)) (r2 (aot-cc 2 e (+ 1 i) (caddr r) pool)))
               (list (append (car r) (car r2)) (cadr r2) (caddr r2)))
           (if (consp e) (aot-cc 0 (ex-kid-of e (nfix (- nk 1))) 0 n pool) (list (list (list :owed e)) n (+ 1 n)))))
      ; a let from its i-th binding: the init into the local's slot (its temporary let go), then the body
      (otherwise
       (if (and (consp e) (< i (ex-i2 e)))
           (let* ((r (aot-cc 0 (ex-kid-of e i) 0 n pool))
                  (r2 (aot-cc 3 e (+ 1 i) (caddr r) pool)))
             (list (append (car r) (list (list :put (+ (ex-s2 e) i) (cadr r)))
                           (if (consp (car r)) (list (list :const (cadr r) nil)) nil)
                           (car r2))
                   (cadr r2) (caddr r2)))
         (if (consp e) (aot-cc 0 (ex-kid-of e (ex-i2 e)) 0 n pool) (list (list (list :owed e)) n (+ 1 n))))))))

; COST of the compile: its calls, by the same recursion
(defun aot-cc-cnt (fl e i)
  (declare (xargs :ruler-extenders :all :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (aot-ccrank fl)) (aot-ccleft fl e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (i (nfix i)))
    (case fl
      (0 (+ 1 (aot-cc-cnt 1 e 0)))
      (1 (+ 1 (cond ((not (consp e)) 0)
                    ((or (equal k 1) (equal k 2) (equal k 3)) 0)
                    ((equal k 5) (if (zp nk) 0 (aot-cc-cnt 2 e 0)))
                    ((equal k 4) (+ (aot-cc-cnt 0 (ex-kid-of e 0) 0) (aot-cc-cnt 0 (ex-kid-of e 1) 0)
                                    (if (< 2 nk) (aot-cc-cnt 0 (ex-kid-of e 2) 0) 0)))
                    ((equal k 11) (aot-cc-cnt 3 e 0))
                    (t 0))))
      (2 (+ 1 (if (and (consp e) (< (+ 1 i) nk))
                  (+ (aot-cc-cnt 0 (ex-kid-of e i) 0) (aot-cc-cnt 2 e (+ 1 i)))
                (if (consp e) (aot-cc-cnt 0 (ex-kid-of e (nfix (- nk 1))) 0) 0))))
      (otherwise (+ 1 (if (and (consp e) (< i (ex-i2 e)))
                          (+ (aot-cc-cnt 0 (ex-kid-of e i) 0) (aot-cc-cnt 3 e (+ 1 i)))
                        (if (consp e) (aot-cc-cnt 0 (ex-kid-of e (ex-i2 e)) 0) 0)))))))
