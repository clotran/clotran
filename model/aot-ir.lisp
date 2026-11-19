; SLICE 4 of the ahead-of-time compiler (model/aot-PLAN.md): EMISSION, as an IR with a meaning.
;
; compiler.cljf's gen answers, per node, [code slot state]: the statements that compute the node,
; the temporary its value lands in, and the next free temporary. The statements are this IR, as
; data (compiler.cljf builds the same vectors; ir-lines prints each one as its Fortran template),
; for the kinds modelled so far -- the rest are still Fortran text there, (:owed e) here.
;
; THE IR. A program is a list of instructions over (fr bt rp): fr the frame of locals (exec's,
; ex-ev's fr: sv(b+1)), bt the procedure's slots sv(b+d) -- the pool's entries from b+2, then the
; temporaries -- and rp the innermost running loop's recur flag.
;   (:const d v)   bt[d] := v                 clotran_set_nil/int/real/bool (emit-const)
;   (:get d s)     bt[d] := fr[s]             clotran_frame_get
;   (:clr s)       fr[s] := nil               clotran_frame_clear (a local's last read, ex-mark)
;   (:put s d)     fr[s] := bt[d]             clotran_frame_put
;   (:copy d s)    bt[d] := bt[s]             clotran_copy
;   (:deref d s)   bt[d] := the Var's value   clotran_deref (aot-deref: a Var is (:var v))
;   (:if s th el)  th when bt[s] is truthy, else el   if (clotran_bool(b + s) /= 0) then ... end if
;   (:loop body)   rounds of body, each with the flag lowered, while a round raises it
;                  do / recurN = 0 / clotran_poll / body / if (recurN == 0) exit / end do
;   (:recur)       rp := t                    recurN = 1 (N the innermost loop's: gen's (:loop st))
; aot-ir-run: the meaning, (fr bt ok rp), ok nil at an instruction it does not know (it stops
; there) or when a loop's rounds outrun the fuel (ex-ev's :iter's). The flag's NAME is the
; printer's: the IR as ACL2 reads it has none, and ir-check checks each recur names its innermost
; loop's. COST: aot-ir-steps, the instructions run, at most aot-ir-size with k = fuel + 1 rounds a loop.
;
; THE COMPILE, (aot-cc fl e i n pool) = (code slot next), gen's case per kind (fl 1, gen-op), gen's
; copy of a pool slot that came with code (fl 0), gen-seq of a do from its i-th child (fl 2),
; bind-slots then the body of a let or loop from its i-th binding (fl 3) and a recur's arguments
; from its i-th (fl 4, with the writes apart: (code slot next writes)). n is the next free temporary
; (fresh); pool is the host's pool (Eval.f90 compiled_pool, fn-procedure's pslots) as an alist
; ((kind c) slot linked): a Var (kind 3) and a constant no Fortran spells (kind 1), its slot, and
; whether the Var is direct-linked (dereffed once at entry). 4a: const local var if do let; 4b: loop
; recur, boxed. COST: aot-cc-cnt, the calls (aot-cc-cost, aot-ir-proof).
;
; 4c (first part): TYPED TEMPORARIES AND SLOTS, no prims yet. The types are gen's, carried on the
; exported tree (aot-at: a node's infer at gen's env; aot-bt: a loop's settled slot types, a recur's
; targets'); a typed slot's Fortran variable l<s>/d<s>/q<s> is modelled as the frame slot s it
; stands for, a typed temporary ti<d>/td<d>/tl<d> as the slot d it reserves, so a value is itself
; typed or boxed and the theorem holds for any types but A-NONE's (aot-ir-proof). Instructions:
;   (:tput s t x)  fr[s] := x                 l<s> = x (a typed let or loop binding, a typed recur's write)
;   (:tset d t x)  bt[d] := x                 ti<d> = x
;   (:box d t x)   bt[d] := x                 clotran_set_int/real/bool(b + d, x)
;   (:tif x th el) th when x is truthy        if (x) then ... end if (the test a Fortran logical)
; over the operands of aot-xrun. The compile: gp (fl 5, i the type wanted) answers (code operand
; next) -- a typed constant into a temporary (a bool one in place), a typed local its variable, a node
; typed none its code and a literal never read, else gen's value unboxed; fl 6 puts gp's operand in
; a typed temporary (a typed recur argument). A typed call (a prim) is still (:owed e): 4c-ii.

(in-package "ACL2")
(include-book "exec")

; ---- THE MEANING ---------------------------------------------------------------------------

(defun aot-deref (x) (if (and (consp x) (eq (car x) :var)) (cadr x) nil))

; a TYPED OPERAND (4c): (value . frame after), the frame changed only by a local's last read
;   (:lit v t)     v                          a literal, (lit v t)
;   (:sv s t m)    fr[s], cleared when m      a typed local's variable l<s>/d<s>/q<s> (the clear: none in
;                                             Fortran -- a marked read is its slot's last)
;   (:tv d t)      bt[d]                      a typed temporary ti<d>/td<d>/tl<d>, named by the slot it reserves
;   (:unbox d t)   bt[d]                      clotran_int/real/bool(b + d)
; the type t is the printer's: a value is itself, typed or boxed
(defun aot-xrun (x fr bt)
  (case (car x)
    (:lit (cons (cadr x) fr))
    (:sv (cons (nth (nfix (cadr x)) fr) (if (cadddr x) (update-nth (nfix (cadr x)) nil fr) fr)))
    ((:tv :unbox) (cons (nth (nfix (cadr x)) bt) fr))
    (otherwise (cons nil fr))))

; one instruction but :if :loop :recur: (fr bt), nil when it is none the IR has
(defun aot-ir-step (x fr bt)
  (let ((a (nfix (cadr x))) (b (caddr x)))
    (case (car x)
      (:const (list fr (update-nth a b bt)))
      (:get (list fr (update-nth a (nth (nfix b) fr) bt)))
      (:clr (list (update-nth a nil fr) bt))
      (:put (list (update-nth a (nth (nfix b) bt) fr) bt))
      (:copy (list fr (update-nth a (nth (nfix b) bt) bt)))
      (:deref (list fr (update-nth a (aot-deref (nth (nfix b) bt)) bt)))
      ; 4c, x an operand: (:tput s t x) l<s> = x; (:tset d t x) ti<d> = x; (:box d t x) x boxed into d
      (:tput (let ((xr (aot-xrun (cadddr x) fr bt))) (list (update-nth a (car xr) (cdr xr)) bt)))
      ((:tset :box) (let ((xr (aot-xrun (cadddr x) fr bt))) (list (cdr xr) (update-nth a (car xr) bt))))
      (otherwise nil))))

(defun aot-isop (x op) (and (consp x) (eq (car x) op)))

; (fr bt ok rp): rp the recur flag of the innermost loop running (raised by :recur, read and
; lowered by the :loop round it, the outer loop's restored after it, as each Fortran loop has its
; own); a :loop's rounds take fuel, as ex-ev's :iter's do, and ok nil when it runs out
(defun aot-ir-run (code fr bt rp fuel)
  (declare (xargs :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count code))
                  :well-founded-relation o<))
  (if (atom code)
      (list fr bt t rp)
    (let ((x (car code)))
      (cond ((aot-isop x :if)
             (let ((r (aot-ir-run (if (truthy (nth (nfix (cadr x)) bt)) (caddr x) (cadddr x)) fr bt rp fuel)))
               (if (caddr r) (aot-ir-run (cdr code) (car r) (cadr r) (cadddr r) fuel) r)))
            ((aot-isop x :tif)
             (let* ((xr (aot-xrun (cadr x) fr bt))
                    (r (aot-ir-run (if (truthy (car xr)) (caddr x) (cadddr x)) (cdr xr) bt rp fuel)))
               (if (caddr r) (aot-ir-run (cdr code) (car r) (cadr r) (cadddr r) fuel) r)))
            ((aot-isop x :loop)
             (let ((r (aot-ir-run (cadr x) fr bt nil fuel)))
               (cond ((not (caddr r)) r)
                     ((not (cadddr r)) (aot-ir-run (cdr code) (car r) (cadr r) rp fuel))
                     ((zp fuel) (list (car r) (cadr r) nil nil))
                     (t (let ((r2 (aot-ir-run (list x) (car r) (cadr r) nil (1- fuel))))
                          (if (caddr r2) (aot-ir-run (cdr code) (car r2) (cadr r2) rp fuel) r2))))))
            ((aot-isop x :recur) (aot-ir-run (cdr code) fr bt t fuel))
            (t (let ((s (aot-ir-step x fr bt)))
                 (if s (aot-ir-run (cdr code) (car s) (cadr s) rp fuel) (list fr bt nil rp))))))))

; COST: the instructions a run takes, a :loop one a round
(defun aot-ir-steps (code fr bt rp fuel)
  (declare (xargs :ruler-extenders :all :measure (make-ord 1 (1+ (nfix fuel)) (acl2-count code))
                  :well-founded-relation o<))
  (if (atom code)
      0
    (let ((x (car code)))
      (cond ((aot-isop x :if)
             (let* ((br (if (truthy (nth (nfix (cadr x)) bt)) (caddr x) (cadddr x))) (r (aot-ir-run br fr bt rp fuel)))
               (+ 1 (aot-ir-steps br fr bt rp fuel) (if (caddr r) (aot-ir-steps (cdr code) (car r) (cadr r) (cadddr r) fuel) 0))))
            ((aot-isop x :tif)
             (let* ((xr (aot-xrun (cadr x) fr bt)) (br (if (truthy (car xr)) (caddr x) (cadddr x)))
                    (r (aot-ir-run br (cdr xr) bt rp fuel)))
               (+ 1 (aot-ir-steps br (cdr xr) bt rp fuel) (if (caddr r) (aot-ir-steps (cdr code) (car r) (cadr r) (cadddr r) fuel) 0))))
            ((aot-isop x :loop)
             (let ((r (aot-ir-run (cadr x) fr bt nil fuel)))
               (+ 1 (aot-ir-steps (cadr x) fr bt nil fuel)
                  (cond ((not (caddr r)) 0)
                        ((not (cadddr r)) (aot-ir-steps (cdr code) (car r) (cadr r) rp fuel))
                        ((zp fuel) 0)
                        (t (let ((r2 (aot-ir-run (list x) (car r) (cadr r) nil (1- fuel))))
                             (+ (aot-ir-steps (list x) (car r) (cadr r) nil (1- fuel))
                                (if (caddr r2) (aot-ir-steps (cdr code) (car r2) (cadr r2) rp fuel) 0))))))))
            ((aot-isop x :recur) (+ 1 (aot-ir-steps (cdr code) fr bt t fuel)))
            (t (let ((s (aot-ir-step x fr bt)))
                 (+ 1 (if s (aot-ir-steps (cdr code) (car s) (cadr s) rp fuel) 0))))))))

; the bound: every instruction once, a loop's body once a round, at most k rounds
(defun aot-lmul (k b) (* (nfix k) (+ 1 (nfix b))))
(defun aot-ir-size (code k)
  (declare (xargs :measure (acl2-count code)))
  (if (atom code)
      0
    (let ((x (car code)))
      (+ (cond ((or (aot-isop x :if) (aot-isop x :tif)) (+ 1 (aot-ir-size (caddr x) k) (aot-ir-size (cadddr x) k)))
               ((aot-isop x :loop) (aot-lmul k (aot-ir-size (cadr x) k)))
               (t 1))
         (aot-ir-size (cdr code) k)))))

; ---- THE COMPILE ---------------------------------------------------------------------------

(defun aot-pent (e pool)
  (and (or (equal (ex-kind e) 1) (equal (ex-kind e) 3)) (assoc-equal (list (ex-kind e) (ex-c e)) pool)))
(defun aot-inpool (s pool)
  (cond ((atom pool) nil) ((and (consp (car pool)) (equal (cadr (car pool)) s)) t) (t (aot-inpool s (cdr pool)))))

(defun aot-ccrank (fl) (case fl (0 3) (1 2) (5 4) (6 5) (otherwise 1)))
; 4c: gen's types, as the exported tree carries them: a node's (infer, at gen's env), and a loop's
; settled slot types or a recur's target slots' types
(defun aot-at (e) (nth 12 e))
(defun aot-bt (e) (nth 13 e))
(defun aot-typ (ty) (or (equal ty 2) (equal ty 3) (equal ty 4)))
; a let's or loop's i-th binding's type: the loop's settled one, or the init's own
(defun aot-bty (e i) (if (equal (ex-kind e) 12) (nth i (aot-bt e)) (aot-at (ex-kid-of e i))))
(defun aot-ccleft (fl e i) (nfix (- (if (member fl (quote (0 1 2 4))) (ex-nk e) (ex-i2 e)) (nfix i))))

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
                 ((and (equal k 2) (aot-typ (aot-at e)))
                  (list (list (list :box n (aot-at e) (list :sv (ex-i2 e) (aot-at e) (ex-mark e)))) n (+ 1 n)))
                 ((equal k 2) (list (if (ex-mark e)
                                        (list (list :get n (ex-i2 e)) (list :clr (ex-i2 e)))
                                      (list (list :get n (ex-i2 e))))
                                    n (+ 1 n)))
                 ((equal k 5) (if (zp nk) (list (list (list :const n nil)) n (+ 1 n)) (aot-cc 2 e 0 n pool)))
                 ((equal k 4)
                  (let* ((typ (equal (aot-at (ex-kid-of e 0)) 4))
                         (tr (if typ (aot-cc 5 (ex-kid-of e 0) 4 n pool) (aot-cc 0 (ex-kid-of e 0) 0 n pool)))
                         (tc (car tr)) (ts (cadr tr)) (r (caddr tr))
                         (lg (if (and (not typ) (consp tc)) (list (list :const ts nil)) nil))
                         (th (aot-cc 0 (ex-kid-of e 1) 0 (+ 1 r) pool)) (m (caddr th))
                         (el (if (< 2 nk)
                                 (aot-cc 0 (ex-kid-of e 2) 0 m pool)
                               (list (list (list :const m nil)) m (+ 1 m))))
                         (cpt (if (equal (ex-kind (ex-kid-of e 1)) 16) nil (list (list :copy r (cadr th)))))
                         (cpe (if (and (< 2 nk) (equal (ex-kind (ex-kid-of e 2)) 16)) nil (list (list :copy r (cadr el))))))
                    (list (append tc (list (list (if typ :tif :if) ts (append lg (car th) cpt) (append lg (car el) cpe))))
                          r (caddr el))))
                 ((or (equal k 11) (equal k 12)) (aot-cc 3 e 0 n pool))
                 ; every argument computed, then the slots written, then the loop's flag raised
                 ((equal k 16) (let ((r (aot-cc 4 e 0 n pool)))
                                 (list (append (car r) (cadddr r) (list (list :recur))) (cadr r) (caddr r))))
                 (t (list (list (list :owed e)) n (+ 1 n))))))
      ; a do from its i-th child: the last child's slot
      (2 (if (and (consp e) (< (+ 1 i) nk))
             (let* ((r (aot-cc 0 (ex-kid-of e i) 0 n pool)) (r2 (aot-cc 2 e (+ 1 i) (caddr r) pool)))
               (list (append (car r) (car r2)) (cadr r2) (caddr r2)))
           (if (consp e) (aot-cc 0 (ex-kid-of e (nfix (- nk 1))) 0 n pool) (list (list (list :owed e)) n (+ 1 n)))))
      ; a recur from its i-th argument: (code slot next writes), the writes (each slot's put, its
      ; temporary let go) kept apart to follow every argument's code; the slot gen's fresh r
      (4 (if (and (consp e) (< i nk))
             (let* ((ty (nth i (aot-bt e))) (typ (aot-typ ty))
                    (r (if typ (aot-cc 6 (ex-kid-of e i) ty n pool) (aot-cc 0 (ex-kid-of e i) 0 n pool)))
                    (r2 (aot-cc 4 e (+ 1 i) (caddr r) pool)))
               (list (append (car r) (car r2)) (cadr r2) (caddr r2)
                     (append (if typ
                                 (list (list :tput (+ (ex-rstart e) i) ty (list :tv (cadr r) ty)))
                               (append (list (list :put (+ (ex-rstart e) i) (cadr r)))
                                       (if (consp (car r)) (list (list :const (cadr r) nil)) nil)))
                             (cadddr r2))))
           (if (consp e) (list nil n (+ 1 n) nil) (list (list (list :owed e)) n (+ 1 n) nil))))
      ; GP (4c): e as a typed operand, i the type wanted -- (code operand next)
      (5 (let ((ty (aot-at e)))
           (cond ((not (consp e)) (list (list (list :owed e)) (list :lit nil i) (+ 1 n)))
                 ((and (equal k 1) (or (equal ty 2) (equal ty 3)))
                  (list (list (list :tset n ty (list :lit (ex-c e) ty))) (list :tv n ty) (+ 1 n)))
                 ((and (equal k 1) (equal ty 4)) (list nil (list :lit (ex-c e) 4) n))
                 ((and (equal k 2) (aot-typ ty)) (list nil (list :sv (ex-i2 e) ty (ex-mark e)) n))
                 ((and (equal k 6) (aot-typ ty)) (list (list (list :owed e)) (list :lit nil ty) (+ 1 n)))
                 ; a node that never answers (typed none): its code, then a literal no one reads
                 ((equal ty 0) (let ((r (aot-cc 0 e 0 n pool))) (list (car r) (list :lit (if (equal i 4) :false 0) i) (caddr r))))
                 (t (let ((r (aot-cc 0 e 0 n pool))) (list (car r) (list :unbox (cadr r) ty) (caddr r)))))))
      ; a typed value into a typed temporary, the slot it reserves (a typed recur argument)
      (6 (let* ((r (aot-cc 5 e i n pool)) (m (max n (nfix (caddr r)))))
           (list (append (car r) (list (list :tset m i (cadr r)))) m (+ 1 m))))
      ; a let or loop from its i-th binding: the init into the local's slot (its temporary let go),
      ; then the body -- a loop's as a :loop
      (otherwise
       (if (and (consp e) (< i (ex-i2 e)))
           (let ((ty (aot-bty e i)))
             (if (aot-typ ty)
                 (let* ((r (aot-cc 5 (ex-kid-of e i) ty n pool))
                        (r2 (aot-cc 3 e (+ 1 i) (caddr r) pool)))
                   (list (append (car r) (list (list :tput (+ (ex-s2 e) i) ty (cadr r))) (car r2))
                         (cadr r2) (caddr r2)))
               (let* ((r (aot-cc 0 (ex-kid-of e i) 0 n pool))
                      (r2 (aot-cc 3 e (+ 1 i) (caddr r) pool)))
                 (list (append (car r) (list (list :put (+ (ex-s2 e) i) (cadr r)))
                               (if (consp (car r)) (list (list :const (cadr r) nil)) nil)
                               (car r2))
                       (cadr r2) (caddr r2)))))
         (if (consp e)
             (let ((rb (aot-cc 0 (ex-kid-of e (ex-i2 e)) 0 n pool)))
               (if (equal k 12) (list (list (list :loop (car rb))) (cadr rb) (caddr rb)) rb))
           (list (list (list :owed e)) n (+ 1 n))))))))

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
                    ((equal k 4) (+ (if (equal (aot-at (ex-kid-of e 0)) 4) (aot-cc-cnt 5 (ex-kid-of e 0) 4) (aot-cc-cnt 0 (ex-kid-of e 0) 0))
                                    (aot-cc-cnt 0 (ex-kid-of e 1) 0)
                                    (if (< 2 nk) (aot-cc-cnt 0 (ex-kid-of e 2) 0) 0)))
                    ((or (equal k 11) (equal k 12)) (aot-cc-cnt 3 e 0))
                    ((equal k 16) (aot-cc-cnt 4 e 0))
                    (t 0))))
      (2 (+ 1 (if (and (consp e) (< (+ 1 i) nk))
                  (+ (aot-cc-cnt 0 (ex-kid-of e i) 0) (aot-cc-cnt 2 e (+ 1 i)))
                (if (consp e) (aot-cc-cnt 0 (ex-kid-of e (nfix (- nk 1))) 0) 0))))
      (4 (+ 1 (if (and (consp e) (< i nk))
                  (+ (if (aot-typ (nth i (aot-bt e))) (aot-cc-cnt 6 (ex-kid-of e i) (nth i (aot-bt e))) (aot-cc-cnt 0 (ex-kid-of e i) 0))
                     (aot-cc-cnt 4 e (+ 1 i)))
                0)))
      (5 (+ 1 (let ((ty (aot-at e)))
                (cond ((not (consp e)) 0)
                      ((and (equal k 1) (aot-typ ty)) 0)
                      ((and (equal k 2) (aot-typ ty)) 0)
                      ((and (equal k 6) (aot-typ ty)) 0)
                      (t (aot-cc-cnt 0 e 0))))))
      (6 (+ 1 (aot-cc-cnt 5 e i)))
      (otherwise (+ 1 (if (and (consp e) (< i (ex-i2 e)))
                          (+ (let ((ty (aot-bty e i)))
                               (if (aot-typ ty) (aot-cc-cnt 5 (ex-kid-of e i) ty) (aot-cc-cnt 0 (ex-kid-of e i) 0)))
                             (aot-cc-cnt 3 e (+ 1 i)))
                        (if (consp e) (aot-cc-cnt 0 (ex-kid-of e (ex-i2 e)) 0) 0)))))))
