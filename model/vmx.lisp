; clotran's VM, formally (PLAN step 30): the stack machine EXTENDED toward
; what the Fortran stack VM must run. model/vm-closure.lisp's language and
; one-stack machine, and first
;
;   (:loop (i1 .. ik) body)   k new locals, bound to i1 .. ik, and body
;                             run until it gives a value
;   (:recur e1 .. ek)         in a loop body's tail position: round again
;                             with the locals bound to e1 .. ek
;
; THE MACHINE is vm-closure.lisp's vcs-step, unchanged -- every old
; instruction is handed to it -- and one instruction more:
;
;   (:recur k b L)   the top k values into local slots b .. b+k-1, the
;                    stack top back to the frame's base + b + k, and on
;                    to L, the loop's head
;
; so a recur moves k values and jumps: a loop runs in constant stack
; whatever its iterations, and its head is reached at one depth, b + k,
; which stage 2a's depth check (model/jit2.lisp) asks of every pc.
;
; The books on vcs-step -- the stack proof, its cost, rooting, every
; JIT stage -- stay as they are; this book and the ones after it prove
; the extended machine against the extended meaning.

(in-package "ACL2")

(include-book "vm-closure")

; ---- THE MEANING ----------------------------------------------------------
;
; An answer is (:val . v), (:recur . vs) -- a loop body asking to go round
; with vs -- (:out) when fuel ran out, (:err) for a bad call. A loop's
; iterations take fuel, as calls do, so every meaning is total.

(mutual-recursion
 (defun mx (e env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 1))
                   :well-founded-relation o< :verify-guards nil))
   (case (car e)
     (:const (cons :val (cadr e)))
     (:local (cons :val (nth (nfix (cadr e)) env)))
     (:capt (cons :val (nth (nfix (cadr e)) caps)))
     (:if (let ((rc (mx (cadr e) env caps defs fuel)))
            (cond ((not (valp rc)) rc)
                  ((truthy (val rc)) (mx (caddr e) env caps defs fuel))
                  (t (mx (cadddr e) env caps defs fuel)))))
     (:let (let ((ri (mx (cadr e) env caps defs fuel)))
             (if (valp ri) (mx (caddr e) (append env (list (val ri))) caps defs fuel) ri)))
     ((:add :lt)
      (let ((ra (mx (cadr e) env caps defs fuel)))
        (if (not (valp ra))
            ra
          (let ((rb (mx (caddr e) env caps defs fuel)))
            (cond ((not (valp rb)) rb)
                  ((eq (car e) :add) (cons :val (+ (fix (val ra)) (fix (val rb)))))
                  (t (cons :val (bool (< (rfix (val ra)) (rfix (val rb)))))))))))
     (:mkclo (let ((rs (mx-args (cddr e) env caps defs fuel)))
               (if (valp rs) (cons :val (clo (cadr e) (val rs))) rs)))
     (:callv (let ((rs (mx-args (cddr e) env caps defs fuel)))
               (if (not (valp rs))
                   rs
                 (let ((rf (mx (cadr e) env caps defs fuel)))
                   (cond ((not (valp rf)) rf)
                         ((not (clop (val rf))) (list :err))
                         (t (let ((def (cdr (assoc-eq (clo-f (val rf)) defs))))
                              (cond ((not (consp def)) (list :err))
                                    ((not (equal (len (val rs)) (nfix (car def)))) (list :err))
                                    ((zp fuel) (list :out))
                                    (t (mx (cadr def) (val rs) (clo-caps (val rf)) defs (1- fuel)))))))))))
     (:loop (let ((ri (mx-args (cadr e) env caps defs fuel)))
              (if (valp ri) (mx-loop e env (val ri) caps defs fuel) ri)))
     (:recur (let ((rs (mx-args (cdr e) env caps defs fuel)))
               (if (valp rs) (cons :recur (val rs)) rs)))
     (otherwise (cons :val nil))))
 (defun mx-args (es env caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count es)) 1))))
   (if (atom es)
       (cons :val nil)
     (let ((r (mx (car es) env caps defs fuel)))
       (if (not (valp r))
           r
         (let ((rs (mx-args (cdr es) env caps defs fuel)))
           (if (valp rs) (cons :val (cons (val r) (val rs))) rs))))))
 ; loop e's body with its locals bound to vs, round again on a recur
 (defun mx-loop (e base vs caps defs fuel)
   (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) 0))))
   (if (not (consp e))
       (cons :val nil)
     (let ((r (mx (caddr e) (append base vs) caps defs fuel)))
       (cond ((not (eq (car r) :recur)) r)
             ((zp fuel) (list :out))
             (t (mx-loop e base (cdr r) caps defs (1- fuel))))))))

; ---- WELL FORMED ------------------------------------------------------------
;
; n locals in scope; k the arity of the loop whose body this is in tail
; position of, nil where a recur may not stand. A recur stands only in a
; loop body's tail, with as many values as the loop binds; a function's
; body is in no loop.

(mutual-recursion
 (defun xwf (e n k)
   (declare (xargs :measure (acl2-count e)))
   (case (car e)
     (:local (and (natp (cadr e)) (< (cadr e) (nfix n))))
     (:if (and (xwf (cadr e) n nil) (xwf (caddr e) n k) (xwf (cadddr e) n k)))
     (:let (and (xwf (cadr e) n nil) (xwf (caddr e) (1+ (nfix n)) k)))
     ((:add :lt) (and (xwf (cadr e) n nil) (xwf (caddr e) n nil)))
     (:mkclo (xwf-args (cddr e) n))
     (:callv (and (xwf (cadr e) n nil) (xwf-args (cddr e) n)))
     (:loop (and (true-listp (cadr e)) (consp (cadr e)) (xwf-args (cadr e) n)
                 (xwf (caddr e) (+ (nfix n) (len (cadr e))) (len (cadr e)))))
     (:recur (and (natp k) (true-listp (cdr e)) (equal (len (cdr e)) k) (xwf-args (cdr e) n)))
     (otherwise t)))
 (defun xwf-args (es n)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) t (and (xwf (car es) n nil) (xwf-args (cdr es) n)))))

(defun xdefs-ok (ds)
  (if (atom ds)
      t
    (and (consp (car ds)) (consp (cdar ds)) (natp (car (cdar ds)))
         (xwf (cadr (cdar ds)) (car (cdar ds)) nil)
         (xdefs-ok (cdr ds)))))

; ---- THE MACHINE ----------------------------------------------------------

; k values from src down to dst, lowest first: dst below src, so a slot
; is read before anything is written over it
(defun copy-down (src dst k stk)
  (declare (xargs :measure (nfix k)))
  (if (zp k) stk (copy-down (1+ (nfix src)) (1+ (nfix dst)) (1- k) (update-nth (nfix dst) (nth (nfix src) stk) stk))))

(defun vcsx-step (prog s)
  (let ((ins (nth (car s) (car prog))))
    (if (and (natp (car s)) (eq (car ins) :recur))
        (let ((k (nfix (cadr ins))) (b (nfix (caddr ins))) (fb (nfix (cadr s))) (sp (nfix (caddr s))))
          (if (< sp (+ fb b k))
              s
            (list (nfix (cadddr ins)) fb (+ fb b k)
                  (copy-down (- sp k) (+ fb b) k (cadddr s)) (car (cddddr s)))))
      (vcs-step prog s))))

(defun vcsx-run (prog s n)
  (if (zp n) s (vcsx-run prog (vcsx-step prog s) (1- n))))

; ---- THE COMPILER -----------------------------------------------------------
;
; vm-closure.lisp's vcs-compile, and lc, the loop a recur goes round:
; (L b k) -- its head's pc, its first local's slot, how many -- or nil.
; A loop's inits push its locals; the body runs at depth + k; a value
; leaves by k slides, which drop the locals below it.

(defun slides (k) (if (zp k) nil (cons (list :slide) (slides (1- k)))))

(mutual-recursion
 (defun vcsx-compile (e depth cenv self pc lc)
   (declare (xargs :measure (acl2-count e) :verify-guards nil))
   (case (car e)
     (:const (list (list :push (cadr e))))
     (:local (list (list :load (nth (nfix (cadr e)) cenv))))
     (:capt (if (natp self) (list (list :capt self (cadr e))) (list (list :push nil))))
     (:if (let* ((cc (vcsx-compile (cadr e) depth cenv self pc nil))
                 (pc1 (+ pc (len cc) 1))
                 (tc (vcsx-compile (caddr e) depth cenv self pc1 lc))
                 (pc2 (+ pc1 (len tc) 1))
                 (ec (vcsx-compile (cadddr e) depth cenv self pc2 lc)))
            (append cc (list (list :jmpf pc2)) tc (list (list :jmp (+ pc2 (len ec)))) ec)))
     (:let (let* ((ic (vcsx-compile (cadr e) depth cenv self pc nil))
                  (bc (vcsx-compile (caddr e) (1+ depth) (append cenv (list depth)) self (+ pc (len ic)) lc)))
             (append ic bc (list (list :slide)))))
     ((:add :lt)
      (let* ((ac (vcsx-compile (cadr e) depth cenv self pc nil))
             (bc (vcsx-compile (caddr e) (1+ depth) cenv self (+ pc (len ac)) nil)))
        (append ac bc (list (list (car e))))))
     (:mkclo (let ((ac (vcsx-compile-args (cddr e) depth cenv self pc)))
               (append ac (list (list :mkclo (cadr e) (len (cddr e)))))))
     (:callv (let* ((n (len (cddr e)))
                    (ac (vcsx-compile-args (cddr e) depth cenv self pc))
                    (fc (vcsx-compile (cadr e) (+ depth n) cenv self (+ pc (len ac)) nil)))
               (append ac fc (list (list :callv n)))))
     (:loop (let* ((k (len (cadr e)))
                   (ic (vcsx-compile-args (cadr e) depth cenv self pc))
                   (head (+ pc (len ic)))
                   (bc (vcsx-compile (caddr e) (+ depth k) (append cenv (count-from depth (+ depth k))) self head
                                     (list head depth k))))
              (append ic bc (slides k))))
     (:recur (let ((ac (vcsx-compile-args (cdr e) depth cenv self pc)))
               (append ac (list (list :recur (nfix (caddr lc)) (nfix (cadr lc)) (nfix (car lc)))))))
     (otherwise (list (list :push nil)))))
 (defun vcsx-compile-args (es depth cenv self pc)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es)
       nil
     (let ((c (vcsx-compile (car es) depth cenv self pc nil)))
       (append c (vcsx-compile-args (cdr es) (1+ depth) cenv self (+ pc (len c))))))))

(defun vcsx-body (def pc)
  (let ((n (nfix (car def))))
    (append (vcsx-compile (cadr def) (1+ n) (count-from 0 n) n pc nil) (list (list :ret)))))

(defun vcsx-defs (defs pc)
  (if (atom defs)
      (cons nil nil)
    (let* ((c (vcsx-body (cdar defs) pc))
           (rest (vcsx-defs (cdr defs) (+ pc (len c)))))
      (cons (append c (car rest))
            (cons (list (caar defs) pc (nfix (cadar defs))) (cdr rest))))))

(defun vcsx-program (e defs)
  (let* ((main (append (vcsx-compile e 0 nil nil 0 nil) (list (list :ret))))
         (rest (vcsx-defs defs (len main))))
    (cons (append main (car rest)) (cdr rest))))

(defun vcsx-run-program (e defs steps)
  (vcs-answer (vcsx-run (vcsx-program e defs) (list 0 0 0 nil nil) steps)))

; ---- AS A CHECK: the machine answers what the meaning does ----------------------

(defconst *x-defs*
  '(; sum 0..n-1 by a loop: (loop [i 0 acc 0] (if (< i n) (recur (+ i 1) (+ acc i)) acc))
    (sum 1 (:loop ((:const 0) (:const 0))
                  (:if (:lt (:local 1) (:local 0))
                       (:recur (:add (:local 1) (:const 1)) (:add (:local 2) (:local 1)))
                       (:local 2))))
    ; a let inside the loop body: its local is under the recur's values
    (tri 1 (:loop ((:local 0) (:const 0))
                  (:let (:add (:local 2) (:local 1))
                        (:if (:lt (:const 0) (:local 1))
                             (:recur (:add (:local 1) (:const -1)) (:local 3))
                             (:local 3)))))
    ; a call inside a loop, and a loop inside the callee
    (sumsums 1 (:loop ((:const 0) (:const 0))
                      (:if (:lt (:local 1) (:local 0))
                           (:recur (:add (:local 1) (:const 1))
                                   (:add (:local 2) (:callv (:mkclo sum) (:local 1))))
                           (:local 2))))
    ; a closure made in a loop, capturing the loop's local
    (adders 1 (:loop ((:const 0) (:const 0))
                     (:if (:lt (:local 1) (:local 0))
                          (:recur (:add (:local 1) (:const 1))
                                  (:callv (:mkclo addc (:local 1)) (:local 2)))
                          (:local 2))))
    (addc 1 (:add (:local 0) (:capt 0)))))

(defmacro check-x (e)
  `(assert-event (equal (vcsx-run-program ',e *x-defs* 100000)
                        (mx ',e nil nil *x-defs* 1000))))

(check-x (:callv (:mkclo sum) (:const 10)))
(check-x (:callv (:mkclo tri) (:const 6)))
(check-x (:callv (:mkclo sumsums) (:const 7)))
(check-x (:callv (:mkclo adders) (:const 5)))
(check-x (:loop ((:const 3)) (:if (:lt (:const 0) (:local 0)) (:recur (:add (:local 0) (:const -1))) (:const 42))))
(check-x (:let (:const 5) (:loop ((:const 0) (:local 0))
                               (:if (:lt (:local 1) (:local 2)) (:recur (:add (:local 1) (:const 1)) (:local 2)) (:local 1)))))
; the answers themselves, not only agreement
(assert-event (equal (mx '(:callv (:mkclo sum) (:const 10)) nil nil *x-defs* 1000) '(:val . 45)))
(assert-event (equal (mx '(:callv (:mkclo tri) (:const 6)) nil nil *x-defs* 1000) '(:val . 21)))
(assert-event (equal (mx '(:callv (:mkclo adders) (:const 5)) nil nil *x-defs* 1000) '(:val . 10)))
; well formed, and a recur out of a tail position not
(assert-event (xdefs-ok *x-defs*))
(assert-event (not (xwf '(:loop ((:const 0)) (:add (:recur (:const 1)) (:const 2))) 0 nil)))
(assert-event (not (xwf '(:recur (:const 1)) 0 nil)))
(assert-event (not (xwf '(:loop ((:const 0)) (:recur (:const 1) (:const 2))) 0 nil)))
