; clotran's VM, formally (PLAN step 28). The register machine's second
; compiler, for the register-or-stack comparison: the SAME machine as
; model/vm-call.lisp (no new instruction), compiled so an operator or a
; test reads a local IN ITS REGISTER rather than first moving it into a
; temporary -- where a register machine's published advantage over a
; stack one comes from (a stack machine must load it every time).
;
; Checked against the meaning here, and measured against the plain
; register compiler and the stack machine on the same programs.

(in-package "ACL2")

(include-book "vm-stack")

; the register an operand is already in: a local's own, or none
(defun in-place (e cenv)
  (if (and (eq (car e) :local) (natp (cadr e)) (< (cadr e) (len cenv)))
      (nfix (nth (cadr e) cenv))
    nil))

(mutual-recursion
 (defun vm-compile-o (e d f cenv pc fnpcs)
   (declare (xargs :measure (acl2-count e) :verify-guards nil))
   (case (car e)
     (:const (list (list :loadk d (cadr e))))
     (:local (list (list :move d (nth (nfix (cadr e)) cenv))))
     (:if (let* ((r (in-place (cadr e) cenv))
                 (cc (if r nil (vm-compile-o (cadr e) f (1+ f) cenv pc fnpcs)))
                 (tr (or r f))
                 (pc1 (+ pc (len cc) 1))
                 (tc (vm-compile-o (caddr e) d f cenv pc1 fnpcs))
                 (pc2 (+ pc1 (len tc) 1))
                 (ec (vm-compile-o (cadddr e) d f cenv pc2 fnpcs)))
            (append cc (list (list :jmpf tr pc2)) tc
                    (list (list :jmp (+ pc2 (len ec)))) ec)))
     (:let (let* ((ic (vm-compile-o (cadr e) f (1+ f) cenv pc fnpcs))
                  (bc (vm-compile-o (caddr e) d (1+ f) (append cenv (list f)) (+ pc (len ic)) fnpcs)))
             (append ic bc)))
     ((:add :lt)
      (let* ((ra (in-place (cadr e) cenv))
             (ac (if ra nil (vm-compile-o (cadr e) f (1+ f) cenv pc fnpcs)))
             (rb (in-place (caddr e) cenv))
             (bc (if rb nil (vm-compile-o (caddr e) (1+ f) (+ 2 f) cenv (+ pc (len ac)) fnpcs))))
        (append ac bc (list (list (car e) d (or ra f) (or rb (1+ f)))))))
     (:call (let* ((n (len (cddr e)))
                   (ac (vm-compile-args-o (cddr e) f cenv pc fnpcs)))
              (append ac (list (list :call d (cdr (assoc-eq (cadr e) fnpcs)) f n (+ f n))))))
     (otherwise (list (list :loadk d nil)))))
 (defun vm-compile-args-o (es f cenv pc fnpcs)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es)
       nil
     (let ((c (vm-compile-o (car es) f (1+ f) cenv pc fnpcs)))
       (append c (vm-compile-args-o (cdr es) (1+ f) cenv (+ pc (len c)) fnpcs))))))

(defun body-code-o (def entry fnpcs)
  (let ((n (nfix (car def))))
    (append (vm-compile-o (cadr def) n (1+ n) (count-from 0 n) entry fnpcs)
            (list (list :ret n)))))

(defun lay-out-o (defs pc fnpcs)
  (if (atom defs)
      nil
    (cons (cons (caar defs) pc)
          (lay-out-o (cdr defs) (+ pc (len (body-code-o (cdar defs) pc fnpcs))) fnpcs))))

(defun compile-defs-o (defs fnpcs pc)
  (if (atom defs)
      nil
    (let ((c (body-code-o (cdar defs) pc fnpcs)))
      (append c (compile-defs-o (cdr defs) fnpcs (+ pc (len c)))))))

(defun compile-program-o (e defs)
  (let* ((main0 (append (vm-compile-o e 0 1 nil 0 nil) (list (list :ret 0))))
         (dummy (lay-out-o defs (len main0) nil))
         (fnpcs (lay-out-o defs (len main0) dummy))
         (main (append (vm-compile-o e 0 1 nil 0 fnpcs) (list (list :ret 0)))))
    (append main (compile-defs-o defs fnpcs (len main)))))

; ---- the machine against the meaning ------------------------------------------

; vm-call's functions and the doubly recursive fib, a benchmark with
; calls on both sides of an add
(defconst *bench-defs*
  (append *defs*
          '((fib 1 (:if (:lt (:local 0) (:const 2))
                        (:local 0)
                        (:add (:call fib (:add (:local 0) (:const -1)))
                              (:call fib (:add (:local 0) (:const -2)))))))))

(defconst *bench-exprs*
  (append *all-exprs*
          '((:call fib (:const 10)) (:call tri (:const 50)) (:call fib (:const 15)))))

(defun o-check-all (es)
  (if (atom es) t
    (and (equal (answer (vm-run (compile-program-o (car es) *bench-defs*) (list 0 0 nil nil) 100000))
                (val (m (car es) nil *bench-defs* 1000)))
         (o-check-all (cdr es)))))

(assert-event (o-check-all *bench-exprs*))

; ---- THE THREE MACHINES ON THE SAME PROGRAMS ----------------------------------
;
; for each program: instructions, then steps to the answer -- the
; register machine compiled plainly, the same machine compiled with
; operands in place, the stack machine

(defun halt-steps (kind prog s n acc)
  (declare (xargs :mode :program))
  (if (zp n) nil
    (let ((s2 (if (eq kind :stack) (s-step prog s) (vm-step prog s))))
      (if (equal s2 s) acc (halt-steps kind prog s2 (1- n) (1+ acc))))))

(defun compare-three (es)
  (declare (xargs :mode :program))
  (if (atom es) nil
    (let ((rp (compile-program (car es) *bench-defs*))
          (op (compile-program-o (car es) *bench-defs*))
          (sp (s-compile-program (car es) *bench-defs*)))
      (cons (list :code (len rp) (len op) (len sp)
                  :steps (halt-steps :reg rp (list 0 0 nil nil) 1000000 0)
                  (halt-steps :reg op (list 0 0 nil nil) 1000000 0)
                  (halt-steps :stack sp (list 0 nil nil nil) 1000000 0))
            (compare-three (cdr es))))))
