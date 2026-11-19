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
; a typed temporary (a typed recur argument). 4c-ii: a typed call is gp-call (fl 7), the prims below.
; 4c-iii: gp-call reads its operands in the order the tree runs them -- with two, the first is read
; into a typed temporary (a slot kept for it) before the second's code when there is any, since that
; code may clear a local the first reads (a marked read: (+ x (inc x)) clears x in inc) -- and the
; meaning the code is compared with is aot-ev, exec's ex-ev with the host's apply of a builtin.

(in-package "ACL2")
(include-book "exec")

; ---- THE MEANING ---------------------------------------------------------------------------

(defun aot-deref (x) (if (and (consp x) (eq (car x) :var)) (cadr x) nil))
(defun aot-wblk (blk vals bt)
  (if (atom vals) bt (aot-wblk (+ 1 (nfix blk)) (cdr vals) (update-nth (nfix blk) (car vals) bt))))

; ---- 4c-ii: THE PRIMS -------------------------------------------------------------------------
; An op by its code p, compiler.cljf's prim-syms: 1 + 2 - 3 * 4 / 5 inc 6 dec 7 < 8 > 9 <= 10 >=
; 11 == 12 = 13 zero? 14 pos? 15 neg? 16 aget 17 aset 18 alength 19 int 20 long 21 double, 22-34 a
; Math/ member of one operand, 35 pow 36 atan2; w the type its operands are read at (2 long, 3 double).
(defconst *aot-h* (- (expt 2 63) 1))
(defun aot-i64p (x) (and (integerp x) (<= (- (- *aot-h*) 1) x) (<= x *aot-h*)))
(defun aot-bool (b) (if b t :false))
(defstub aot-dop (* *) => *)      ; a double op: Fortran's IEEE arithmetic and libm on the operands
(defstub aot-l2d (*) => *)        ; a long widened, real(x, c_double)
(defstub aot-fbig (* *) => *)     ; abs(real(a, c_double) * real(b, c_double)) > 9.0e18, in doubles
(defstub aot-dcast (* *) => *)    ; a double cast's range test (int: within int's; long: abs < 9.2e18)
; the op's value as the Fortran computes it (prim-fast): on longs exact -- in range, where the guard
; lets it run -- on doubles the IEEE op
(defun aot-opx (p w vals)
  (let ((a (car vals)) (b (cadr vals)))
    (cond
     ((equal p 21) a)    ; (double x): x as read, a long already widened by (:real)
     ((and (equal w 2) (integerp a) (or (member p '(5 6 13 14 15 19 20)) (integerp b)))
        (case p (1 (+ a b)) (2 (- a b)) (3 (* a b)) (5 (+ a 1)) (6 (- a 1))
          (7 (aot-bool (< a b))) (8 (aot-bool (> a b))) (9 (aot-bool (<= a b))) (10 (aot-bool (>= a b)))
          ((11 12) (aot-bool (equal a b))) (13 (aot-bool (equal a 0))) (14 (aot-bool (> a 0))) (15 (aot-bool (< a 0)))
          ((19 20) a)
          (otherwise (aot-dop p vals))))
     (t (aot-dop p vals)))))
; the guard (prim-ok): the op cannot overflow or leave its range
(defun aot-pg (p w vals)
  (let ((a (car vals)) (b (cadr vals)) (h *aot-h*))
    (if (equal w 2)
        (case p
          (1 (and (<= a (- h (max b 0))) (>= a (- (- (- h) 1) (min b 0)))))
          (2 (and (<= a (+ h (min b 0))) (>= a (+ (- (- h) 1) (max b 0)))))
          (3 (not (aot-fbig a b)))
          (5 (not (equal a h)))
          (6 (not (equal a (- (- h) 1))))
          (19 (and (<= (- (expt 2 31)) a) (<= a (- (expt 2 31) 1))))
          (otherwise t))
      (if (member p '(19 20)) (aot-dcast p a) t))))
; the escape hatch: the host's generic call of f on vals (clotran_call_slots, the interpreter's own
; path): (:val . v), or what it throws
(defstub aot-hcall (* *) => *)

; ---- 4c-iv: THE COMPARE WITH A BOXED OPERAND ---------------------------------------------------
; gp-call's :cmp when exactly one operand is a number (typed, read at nt) and the other a boxed value
; in slot s: (:cmpb d p nt bi x s hd hs blk res) -- bi the boxed operand's index among the two (the
; order the compare keeps: (< i n) is not (< n i)), x the typed operand. The boxed value's tag is read
; (aot-vtag: the same reading of a value's tag A-CONST makes, aot-tag in aot-ty-proof, not included
; here): a long (2) or a double (3) is compared unboxed -- on longs when x is long too, else both read
; as doubles, a long widened -- into d; anything else takes the escape hatch, the generic call with
; the operands boxed from blk in the order kept, as the prim's.
(defstub aot-vtag (*) => *)
; an operand value as the Fortran reads it: a long read as a double widened
(defun aot-cv (v a w) (if (and (equal a 2) (equal w 3)) (aot-l2d v) v))
(defun aot-ord (bi x v) (if (equal bi 1) (list x v) (list v x)))
(defun aot-numtag (tg) (or (equal tg 2) (equal tg 3)))
(defun aot-cmpw (nt tg) (if (and (equal nt 2) (equal tg 2)) 2 3))
; the unboxed compare's value
(defun aot-cmpval (p nt bi xv v)
  (let* ((tg (aot-vtag v)) (w (aot-cmpw nt tg)))
    (aot-opx p w (aot-ord bi (aot-cv xv nt w) (aot-cv v tg w)))))

; ---- THE MEANING THE CODE IS COMPARED WITH: exec's, with the host's apply (4c-iii) -------------
; aot-ev is exec.lisp's ex-ev on the kinds the compile covers (const local var if do call let loop
; recur), every case as ex-ev writes it, but for a call past its last argument whose callee is no
; closure: there ex-ev answers (:out) (exec does not model the host's apply of a builtin), aot-ev
; the host's generic call aot-hcall -- the escape hatch's own call -- when it answers a value.
; Whatever else aot-ev does not model -- a throw (an IFn test that fails, a host call that throws,
; a part's throw), a closure's entry (4d), any other kind -- is (:out): outside the theorems. On a
; tree with no call the two are the same case for case (by construction, not proved).
(defun aot-happ (tmp fr)
  (let ((h (aot-hcall (car tmp) (cdr tmp))))
    (if (and (not (ex-clo-shape (car tmp))) (consp h) (eq (car h) :val)) (list h fr 1) (list (list :out) fr 0))))
(defun aot-ev (flg e i tmp fr fuel)
  (declare (xargs :measure (make-ord 3 (1+ (nfix fuel))
                                     (make-ord 2 (1+ (acl2-count e))
                                               (make-ord 1 (1+ (ex-rank flg)) (ex-left flg e i))))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of ex-linked ex-write truthy valp val take update-nth aot-happ)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (case flg
      (:iter (if (not (consp e))
                 (list (list :out) fr 0)
               (let* ((r (aot-ev :m e 0 nil fr fuel)) (res (car r)))
                 (cond ((not (eq (car res) :recur)) r)
                       ((zp fuel) (list (list :out) fr 0))
                       (t (let ((r2 (aot-ev :iter e 0 nil (cadr r) (1- fuel))))
                            (list (car r2) (cadr r2) (c+ (caddr r) (caddr r2)))))))))
      (:do (cond ((not (consp e)) (list (list :out) fr 0))
                 ((zp nk) (list (cons :val nil) fr 1))
                 ((< i (- nk 1))
                  (let ((r (aot-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                    (if (not (valp (car r)))
                        (list (list :out) fr 0)
                      (let ((r2 (aot-ev :do e (1+ i) tmp (cadr r) fuel)))
                        (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (caddr r2))))))))
                 (t (let ((r (aot-ev :m (ex-kid-of e (- nk 1)) 0 nil fr fuel)))
                      (list (car r) (cadr r) (c+ 1 (caddr r)))))))
      (:let (cond ((not (consp e)) (list (list :out) fr 0))
                  ((< i n2)
                   (let ((r (aot-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                     (if (not (valp (car r)))
                         (list (list :out) fr 0)
                       (let ((r2 (aot-ev :let e (1+ i) tmp (update-nth (+ (ex-s2 e) i) (val (car r)) (cadr r)) fuel)))
                         (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))))
                  ((equal k 12)
                   (let ((r (aot-ev :iter (ex-kid-of e n2) 0 nil fr fuel)))
                     (list (car r) (cadr r) (c+ 1 (caddr r)))))
                  ((equal k 11)
                   (let ((r (aot-ev :m (ex-kid-of e n2) 0 nil fr fuel)))
                     (list (car r) (cadr r) (c+ 1 (caddr r)))))
                  (t (list (list :out) fr 0))))
      (:rec (cond ((not (consp e)) (list (list :out) fr 0))
                  ((< i nk)
                   (let ((r (aot-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                     (if (not (valp (car r)))
                         (list (list :out) fr 0)
                       (let ((r2 (aot-ev :rec e (1+ i) (append tmp (list (val (car r)))) (cadr r) fuel)))
                         (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))))
                  (t (list (list :recur) (ex-write (ex-rstart e) (take (min (ex-rn e) nk) tmp) fr) 1))))
      (:call (cond ((not (consp e)) (list (list :out) fr 0))
                   ((< i nk)
                    (let ((r (aot-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                      (if (not (valp (car r)))
                          (list (list :out) fr 0)
                        (let ((r2 (aot-ev :call e (1+ i) (append tmp (list (val (car r)))) (cadr r) fuel)))
                          (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))))
                   (t (aot-happ tmp fr))))
      ((:coll :fin) (list (list :out) fr 0))     ; not modelled here
      (otherwise
       (cond ((not (consp e)) (list (list :out) fr 0))
             ((equal k 1) (list (cons :val (ex-c e)) fr 1))
             ((equal k 2) (list (cons :val (nth n2 fr)) (if (ex-mark e) (update-nth n2 nil fr) fr) 1))
             ((equal k 4)
              (let ((r (aot-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                (cond ((not (valp (car r))) (list (list :out) fr 0))
                      ((truthy (val (car r)))
                       (let ((r2 (aot-ev :m (ex-kid-of e 1) 0 nil (cadr r) fuel)))
                         (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))
                      ((< 2 nk)
                       (let ((r2 (aot-ev :m (ex-kid-of e 2) 0 nil (cadr r) fuel)))
                         (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))
                      (t (list (cons :val nil) (cadr r) (c+ 1 (c+ (caddr r) 1)))))))
             ((equal k 5) (aot-ev :do e 0 nil fr fuel))
             ((or (equal k 11) (equal k 12)) (aot-ev :let e 0 nil fr fuel))
             ((equal k 16) (let ((r (aot-ev :rec e 0 nil fr fuel)))
                             (list (car r) (cadr r) (c+ 1 (caddr r)))))
             ((equal k 3) (list (cons :val (ex-c e)) fr 1))
             ((equal k 6)
              (if (ex-linked (ex-kid-of e 0))
                  (if (not (ex-ifn (ex-c (ex-kid-of e 0))))
                      (list (list :out) fr 0)
                    (let ((r2 (aot-ev :call e 1 (list (ex-c (ex-kid-of e 0))) fr fuel)))
                      (list (car r2) (cadr r2) (c+ 1 (c+ 1 (caddr r2))))))
                (let ((r (aot-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                  (cond ((not (valp (car r))) (list (list :out) fr 0))
                        ((not (ex-ifn (val (car r)))) (list (list :out) fr 0))
                        (t (let ((r2 (aot-ev :call e 1 (list (val (car r))) (cadr r) fuel)))
                             (list (car r2) (cadr r2) (c+ 1 (c+ (caddr r) (c+ 1 (caddr r2)))))))))))
             (t (list (list :out) fr 0)))))))


; a TYPED OPERAND (4c): (value . frame after), the frame changed only by a local's last read
;   (:lit v t)     v                          a literal, (lit v t)
;   (:sv s t m)    fr[s], cleared when m      a typed local's variable l<s>/d<s>/q<s> (the clear: none in
;                                             Fortran -- a marked read is its slot's last)
;   (:tv d t)      bt[d]                      a typed temporary ti<d>/td<d>/tl<d>, named by the slot it reserves
;   (:unbox d t)   bt[d]                      clotran_int/real/bool(b + d)
;   (:real x)      x widened                  real(x, c_double)             (4c-ii)
;   (:op p w xs)   the op on xs (aot-opx)     prim-fast: a + b, sqrt(a) ... (4c-ii, an unguarded op)
; the type t is the printer's: a value is itself, typed or boxed
(mutual-recursion
 (defun aot-xrun (x fr bt)
   (declare (xargs :measure (acl2-count x)))
   (case (car x)
     (:lit (cons (cadr x) fr))
     (:sv (cons (nth (nfix (cadr x)) fr) (if (cadddr x) (update-nth (nfix (cadr x)) nil fr) fr)))
     ((:tv :unbox) (cons (nth (nfix (cadr x)) bt) fr))
     (:real (if (consp (cdr x)) (let ((r (aot-xrun (cadr x) fr bt))) (cons (aot-l2d (car r)) (cdr r))) (cons nil fr)))
     (:op (if (consp (cdddr x)) (let ((r (aot-xsrun (cadddr x) fr bt))) (cons (aot-opx (cadr x) (caddr x) (car r)) (cdr r))) (cons nil fr)))
     (otherwise (cons nil fr))))
 ; operands left to right: (values . frame after)
 (defun aot-xsrun (xs fr bt)
   (declare (xargs :measure (acl2-count xs)))
   (if (atom xs)
       (cons nil fr)
     (let* ((r (aot-xrun (car xs) fr bt)) (rs (aot-xsrun (cdr xs) (cdr r) bt)))
       (cons (cons (car r) (car rs)) (cdr rs))))))

(defun aot-cmpb-step (x fr bt)
  (let* ((xr (aot-xrun (nth 5 x) fr bt)) (xv (car xr)) (d (nfix (nth 1 x))) (p (nth 2 x)) (nt (nth 3 x)) (bi (nth 4 x))
         (v (nth (nfix (nth 6 x)) bt)))
    (if (aot-numtag (aot-vtag v))
        (list (cdr xr) (update-nth d (aot-cmpval p nt bi xv v) bt))
      (let* ((vals (aot-ord bi xv v))
             (bt1 (aot-wblk (nth 9 x) vals bt))
             (bt2 (if (nth 7 x) (update-nth (nfix (nth 8 x)) (aot-deref (nth (nfix (nth 7 x)) bt1)) bt1) bt1))
             (h (aot-hcall (nth (nfix (nth 8 x)) bt2) vals)))
        (if (and (consp h) (equal (car h) :val))
            (list (cdr xr) (update-nth d (cdr h) (update-nth (nfix (nth 10 x)) (cdr h) bt2)))
          nil)))))

; (:prim d t p w xs hd hs blk res), its own function so a proof opens it only when it asks
(defun aot-prim-step (x fr bt)
  (let* ((xr (aot-xsrun (nth 5 x) fr bt)) (vals (car xr)) (p (nth 3 x)) (w (nth 4 x)) (a (nfix (nth 1 x))))
    (if (aot-pg p w vals)
        (list (cdr xr) (update-nth a (aot-opx p w vals) bt))
      (let* ((bt1 (aot-wblk (nth 8 x) vals bt))
             (bt2 (if (nth 6 x) (update-nth (nfix (nth 7 x)) (aot-deref (nth (nfix (nth 6 x)) bt1)) bt1) bt1))
             (h (aot-hcall (nth (nfix (nth 7 x)) bt2) vals)))
        (if (and (consp h) (equal (car h) :val))
            (list (cdr xr) (update-nth a (cdr h) (update-nth (nfix (nth 9 x)) (cdr h) bt2)))
          nil)))))

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
      ; 4c-ii, (:prim d t p w xs hd hs blk res): the op into d when its guard passes, else the escape
      ; hatch -- the operands boxed from blk, a Var head dereffed from hd into hs, the generic call
      ; of the fn in hs into res and d; nil when it throws (the procedure returns its status)
      (:prim (aot-prim-step x fr bt))
      ; 4c-iv, (:cmpb d p nt bi x s hd hs blk res): the compare with a boxed operand, above
      (:cmpb (aot-cmpb-step x fr bt))
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

(defun aot-ccrank (fl) (case fl (0 3) (1 2) (5 4) (6 5) (7 0) (otherwise 1)))
; 4c: gen's types, as the exported tree carries them: a node's (infer, at gen's env), and a loop's
; settled slot types or a recur's target slots' types
(defun aot-at (e) (nth 12 e))
(defun aot-bt (e) (nth 13 e))
(defun aot-typ (ty) (or (equal ty 2) (equal ty 3) (equal ty 4)))
; 4c-ii: a call's op as gen's head-op reads it (prim-code, 0 for none); a long operand read as a double
(defun aot-pop (e) (nth 14 e))
(defun aot-coerce (x from to) (if (and (equal from 2) (equal to 3)) (list :real x) x))
(defun aot-unprim (p a0 a1)   ; an op gen still prints as text: the arrays, a compare with a boxed operand
  (or (member p '(16 17 18)) (zp p) (< 36 p) (and (member p '(7 8 9 10 11)) (not (and (member a0 (quote (2 3))) (member a1 (quote (2 3))))))))
; a let's or loop's i-th binding's type: the loop's settled one, or the init's own
(defun aot-bty (e i) (if (equal (ex-kind e) 12) (nth i (aot-bt e)) (aot-at (ex-kid-of e i))))
; the type a typed op's operands are read at (gp-call's w)
(defun aot-pw (p ty a0 a1)
  (cond ((member p '(1 2 3 5 6)) ty)
        ((or (equal p 4) (< 21 p)) 3)
        ((member p '(7 8 9 10 11)) (if (or (equal a0 3) (equal a1 3)) 3 2))
        (t a0)))
; a compare with exactly one boxed operand (type any, 1): gp-call's boxed path
(defun aot-numty (a) (or (equal a 2) (equal a 3)))
(defun aot-cmpb-p (p a0 a1)
  (and (member p '(7 8 9 10 11)) (or (and (aot-numty a0) (equal a1 1)) (and (equal a0 1) (aot-numty a1)))))
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
                 ; a typed op (4c-ii): primitive, then boxed once
                 ((and (equal k 6) (aot-typ (aot-at e)) (not (equal (aot-pop e) 0)))
                  (let* ((r (aot-cc 7 e 0 n pool)) (m (caddr r)))
                    (list (append (car r) (list (list :box m (aot-at e) (cadr r)))) m (+ 1 m))))
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
                 ((and (equal k 6) (aot-typ ty) (not (equal (aot-pop e) 0))) (aot-cc 7 e 0 n pool))
                 ((and (equal k 6) (aot-typ ty)) (list (list (list :owed e)) (list :lit nil ty) (+ 1 n)))
                 ; a node that never answers (typed none): its code, then a literal no one reads
                 ((equal ty 0) (let ((r (aot-cc 0 e 0 n pool))) (list (car r) (list :lit (if (equal i 4) :false 0) i) (caddr r))))
                 (t (let ((r (aot-cc 0 e 0 n pool))) (list (car r) (list :unbox (cadr r) ty) (caddr r)))))))
      ; GP-CALL (4c-ii): a typed op e, (code operand next) -- its operands read at w (the second of =
      ; at its own type), then an unguarded op as the operand (:op p w xs) or set into a temporary, a
      ; guarded one (long + - * inc dec, the int and long casts) the instruction (:prim ...) with its
      ; hatch's slots allocated as slow-call does: the head's read (a Var dereffed), the operands' boxes,
      ; the answer
      (7 (let ((p (aot-pop e)) (ty (aot-at e)) (k1 (ex-kid-of e 1)) (k2 (ex-kid-of e 2)))
          (if (and (consp e) (aot-cmpb-p p (aot-at k1) (aot-at k2)))
              ; 4c-iv: the compare with a boxed operand, its operands in the tree's order: the typed one
              ; first is read into a kept slot before the boxed one's code when there is any
              (let* ((a0 (aot-at k1)) (a1 (aot-at k2)) (bi (if (aot-numty a0) 1 0)) (nt (if (equal bi 1) a0 a1))
                     ; k1 is read first whichever it is: typed (bi 1) through gp, boxed (bi 0) through gen
                     (ra (aot-cc (if (equal bi 1) 5 0) k1 (if (equal bi 1) nt 0) n pool)) (n1 (caddr ra))
                     (rb (aot-cc (if (equal bi 1) 0 5) k2 (if (equal bi 1) 0 nt) (if (equal bi 1) (+ 1 n1) n1) pool))
                     (snap (and (equal bi 1) (consp (car rb))))
                     (x (if (equal bi 1) (if snap (list :tv n1 nt) (cadr ra)) (cadr rb)))
                     (s (if (equal bi 1) (cadr rb) (cadr ra)))
                     (c (append (car ra) (if snap (list (list :tset n1 nt (cadr ra))) nil) (car rb)))
                     (m (caddr rb)) (h (aot-cc 1 (ex-kid-of e 0) 0 (+ 1 m) pool)) (blk (caddr h)))
                (list (append c (list (list :cmpb m p nt bi x s (if (consp (car h)) (caddr (car (car h))) nil) (cadr h) blk (+ blk 2))))
                      (list :tv m 4) (+ 3 blk)))
          (if (or (not (consp e)) (aot-unprim p (aot-at k1) (aot-at k2)))
              (list (list (list :owed e)) (list :lit nil ty) (+ 1 n))
          (let* ((a0 (aot-at k1)) (a1 (aot-at k2)) (two (< 2 nk))
                (w (aot-pw p ty a0 a1))
                (w2 (if (equal p 12) a1 w))
                (r1 (aot-cc 5 k1 w n pool)) (n1 (caddr r1))
                ; two operands: a slot n1 kept for the first, which is read into it before the second's
                ; code when there is any (the order ex-ev reads them in: that code may clear its local)
                (r2 (if two (aot-cc 5 k2 w2 (+ 1 n1) pool) (list nil nil n1)))
                (snap (and two (consp (car r2))))
                (x1 (aot-coerce (cadr r1) a0 w))
                (xs (if two (list (if snap (list :tv n1 w) x1) (aot-coerce (cadr r2) a1 w2)) (list x1)))
                (c (append (car r1) (if snap (list (list :tset n1 w x1)) nil) (car r2))) (m (caddr r2)))
           (cond ((equal p 21) (list (car r1) (aot-coerce (cadr r1) a0 3) (caddr r1)))
                 ((and (equal p 20) (equal a0 2)) (list (car r1) (cadr r1) (caddr r1)))
                 ((< 21 p) (list c (list :op p 3 xs) m))
                 ((or (equal p 19) (equal p 20) (and (equal ty 2) (member p '(1 2 3 5 6))))
                  (let* ((h (aot-cc 1 (ex-kid-of e 0) 0 (+ 1 m) pool)) (blk (caddr h)))
                    (list (append c (list (list :prim m ty p w xs (if (consp (car h)) (caddr (car (car h))) nil) (cadr h) blk (+ blk (len xs)))))
                          (list :tv m ty) (+ 1 blk (len xs)))))
                 (t (list (append c (list (list :tset m ty (list :op p w xs)))) (list :tv m ty) (+ 1 m)))))))))
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
                    ((and (equal k 6) (aot-typ (aot-at e)) (not (equal (aot-pop e) 0))) (aot-cc-cnt 7 e 0))
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
                      ((and (equal k 6) (aot-typ ty) (not (equal (aot-pop e) 0))) (aot-cc-cnt 7 e 0))
                      ((and (equal k 6) (aot-typ ty)) 0)
                      (t (aot-cc-cnt 0 e 0))))))
      (6 (+ 1 (aot-cc-cnt 5 e i)))
      ; gp-call: at most its two operands and the hatch's head read (counted whether or not it is made)
      (7 (+ 1 (if (consp e)
                  (+ (aot-cc-cnt 5 (ex-kid-of e 1) 0) (aot-cc-cnt 5 (ex-kid-of e 2) 0) (aot-cc-cnt 1 (ex-kid-of e 0) 0))
                0)))
      (otherwise (+ 1 (if (and (consp e) (< i (ex-i2 e)))
                          (+ (let ((ty (aot-bty e i)))
                               (if (aot-typ ty) (aot-cc-cnt 5 (ex-kid-of e i) ty) (aot-cc-cnt 0 (ex-kid-of e i) 0)))
                             (aot-cc-cnt 3 e (+ 1 i)))
                        (if (consp e) (aot-cc-cnt 0 (ex-kid-of e (ex-i2 e)) 0) 0)))))))
