; clotran's VM, formally (PLAN step 30): THE COMPILER AT THE
; IMPLEMENTATION LEVEL, the one the Fortran is generated from. vmx2's
; vcs2-compile builds lists of instruction lists; this one writes the
; code words straight into vmi's arrays at a cursor and answers the
; cursor after them:
;
;   the expression      read through rt- operations on values (car,
;                       cdr, consp, a keyword test, a small natural), so
;                       the generated Fortran walks clotran's own lists
;   the locals' slots   the compile environment, an array (stobj vce)
;                       grown and cut back with each scope -- cenv's
;                       first n entries
;   the loop            three integers, its head pc -1 for none
;   a jump's target     written when it is known: the condition's jump
;                       after the branches, the try's handler after its
;                       body -- one pass, no instruction lists built
;   a constant          into the pool slot of its push, as the encoder
;                       puts it
;
; vmic-program sizes the arrays by a first pass (vmic-size, vmx2's
; s2code-len over values), compiles main and every function's clauses,
; and fills the function table. vmic-proof.lisp proves that the arrays
; it fills read back as vcs2-program; until then the checks below run
; it against vcs2-program on vmx2's programs.
;
; A program vmx2 compiles to something the arrays cannot hold -- a
; constant operand that is not a small natural, a local past the
; environment, a function named other than by its id -- sets ce-err and
; is not run.

(in-package "ACL2")

(include-book "vmi")

(defstobj vce
  (ce-env :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (ce-err :type (signed-byte 64) :initially 0))

; ---- THE RUNTIME'S OPERATIONS ON THE EXPRESSION ---------------------------------------

(defun rt-car (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun rt-cdr (x) (declare (xargs :guard t)) (if (consp x) (cdr x) nil))
(defun rt-consp (x) (declare (xargs :guard t)) (consp x))
(defun rt-is (x k) (declare (xargs :guard t)) (equal x k))
; a small natural, or -1
(defun rt-nat (x) (declare (xargs :guard t)) (if (and (natp x) (< x 2147483648)) x -1))
(defun rt-len (x) (declare (xargs :guard t)) (len x))

(defmacro rcadr (x) `(rt-car (rt-cdr ,x)))
(defmacro rcaddr (x) `(rt-car (rt-cdr (rt-cdr ,x))))
(defmacro rcadddr (x) `(rt-car (rt-cdr (rt-cdr (rt-cdr ,x)))))
(defmacro rcddr (x) `(rt-cdr (rt-cdr ,x)))

; ---- EMITTING ------------------------------------------------------------------------------

; an instruction's four words at pc, and its pool slot
(defun vmic-put (pc op a b c k vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((i (* 4 (nfix pc))))
    (if (and (< (+ i 3) (v-code-length vmi)) (< (nfix pc) (v-pool-length vmi)))
        (let* ((vmi (update-v-codei i op vmi))
               (vmi (update-v-codei (+ i 1) a vmi))
               (vmi (update-v-codei (+ i 2) b vmi))
               (vmi (update-v-codei (+ i 3) c vmi)))
          (update-v-pooli (nfix pc) k vmi))
      (update-v-status 2 vmi))))

(defun vce-fail (vce) (declare (xargs :stobjs vce :verify-guards nil)) (update-ce-err 1 vce))

; the environment's slot n
(defun vce-set (n x vce)
  (declare (xargs :stobjs vce :verify-guards nil))
  (if (< (nfix n) (ce-env-length vce)) (update-ce-envi (nfix n) x vce) (vce-fail vce)))

(defun vce-get (i vce)
  (declare (xargs :stobjs vce :verify-guards nil))
  (if (< (nfix i) (ce-env-length vce)) (ce-envi (nfix i) vce) 0))

; slots n.. hold d, d+1, ..., d+k-1: a loop's locals, a clause's arguments
(defun vce-count (n d k vce)
  (declare (xargs :stobjs vce :measure (nfix k) :verify-guards nil))
  (if (zp k) vce (let ((vce (vce-set n d vce))) (vce-count (1+ (nfix n)) (1+ (nfix d)) (1- k) vce))))

; ---- THE SIZE: vmx2's s2code-len, over values ---------------------------------------------

(mutual-recursion
 (defun vmic-size (e)
   (declare (xargs :measure (acl2-count e) :verify-guards nil))
   (let ((op (rt-car e)))
     (cond ((rt-is op :if) (+ (vmic-size (rcadr e)) 1 (vmic-size (rcaddr e)) 1 (vmic-size (rcadddr e))))
           ((rt-is op :let) (+ (vmic-size (rcadr e)) (vmic-size (rcaddr e)) 1))
           ((or (rt-is op :add) (rt-is op :lt)) (+ (vmic-size (rcadr e)) (vmic-size (rcaddr e)) 1))
           ((rt-is op :mkclo) (+ (vmic-size-args (rcddr e)) 1))
           ((rt-is op :callv) (+ (vmic-size-args (rcddr e)) (vmic-size (rcadr e)) 1))
           ((rt-is op :loop) (+ (vmic-size-args (rcadr e)) (vmic-size (rcaddr e)) (rt-len (rcadr e))))
           ((rt-is op :recur) (+ (vmic-size-args (rt-cdr e)) 1))
           ((rt-is op :prim) (+ (vmic-size-args (rcddr e)) 1))
           ((rt-is op :throw) (+ (vmic-size (rcadr e)) 1))
           ((rt-is op :try) (+ 1 (vmic-size (rcadr e)) 2 (vmic-size (rcaddr e)) 1))
           (t 1))))
 (defun vmic-size-args (es)
   (declare (xargs :measure (acl2-count es)))
   (if (rt-consp es) (+ (vmic-size (rt-car es)) (vmic-size-args (rt-cdr es))) 0)))

; ---- THE COMPILER --------------------------------------------------------------------------
;
; (vmic-compile e depth n self pc lch lcb lck vmi vce) => (mv pc' vmi vce):
; e's code from pc to pc', cenv the environment's first n slots, self -1
; for none, the loop (lch lcb lck) or lch -1 for none

(mutual-recursion
 (defun vmic-compile (e depth n self pc lch lcb lck vmi vce)
   (declare (xargs :stobjs (vmi vce) :measure (acl2-count e) :verify-guards nil))
   (let ((op (rt-car e)) (pc (nfix pc)) (depth (nfix depth)) (n (nfix n)))
     (cond
      ((rt-is op :const) (let ((vmi (vmic-put pc 1 pc 0 0 (rcadr e) vmi))) (mv (1+ pc) vmi vce)))
      ((rt-is op :local)
       (let ((i (rt-nat (rcadr e))))
         (if (or (< i 0) (<= n i))
             (let ((vce (vce-fail vce))) (mv (1+ pc) vmi vce))
           (let ((vmi (vmic-put pc 2 (vce-get i vce) 0 0 nil vmi))) (mv (1+ pc) vmi vce)))))
      ((rt-is op :capt)
       (if (<= 0 self)
           (let ((i (rt-nat (rcadr e))))
             (if (< i 0)
                 (let ((vce (vce-fail vce))) (mv (1+ pc) vmi vce))
               (let ((vmi (vmic-put pc 9 self i 0 nil vmi))) (mv (1+ pc) vmi vce))))
         (let ((vmi (vmic-put pc 1 pc 0 0 nil vmi))) (mv (1+ pc) vmi vce))))
      ((rt-is op :if)
       (mv-let (pa vmi vce) (vmic-compile (rcadr e) depth n self pc -1 0 0 vmi vce)
         (mv-let (pb vmi vce) (vmic-compile (rcaddr e) depth n self (1+ pa) lch lcb lck vmi vce)
           (mv-let (pc2 vmi vce) (vmic-compile (rcadddr e) depth n self (1+ pb) lch lcb lck vmi vce)
             (let* ((vmi (vmic-put pa 6 (1+ pb) 0 0 nil vmi))
                    (vmi (vmic-put pb 7 pc2 0 0 nil vmi)))
               (mv pc2 vmi vce))))))
      ((rt-is op :let)
       (mv-let (pa vmi vce) (vmic-compile (rcadr e) depth n self pc -1 0 0 vmi vce)
         (let ((vce (vce-set n depth vce)))
           (mv-let (pb vmi vce) (vmic-compile (rcaddr e) (1+ depth) (1+ n) self pa lch lcb lck vmi vce)
             (let ((vmi (vmic-put pb 5 0 0 0 nil vmi))) (mv (1+ pb) vmi vce))))))
      ((or (rt-is op :add) (rt-is op :lt))
       (mv-let (pa vmi vce) (vmic-compile (rcadr e) depth n self pc -1 0 0 vmi vce)
         (mv-let (pb vmi vce) (vmic-compile (rcaddr e) (1+ depth) n self pa -1 0 0 vmi vce)
           (let ((vmi (vmic-put pb (if (rt-is op :add) 3 4) 0 0 0 nil vmi))) (mv (1+ pb) vmi vce)))))
      ((rt-is op :mkclo)
       (mv-let (pa vmi vce) (vmic-compile-args (rcddr e) depth n self pc vmi vce)
         (let ((f (rt-nat (rcadr e))))
           (if (< f 0)
               (let ((vce (vce-fail vce))) (mv (1+ pa) vmi vce))
             (let ((vmi (vmic-put pa 8 f (rt-len (rcddr e)) 0 nil vmi))) (mv (1+ pa) vmi vce))))))
      ((rt-is op :callv)
       (let ((k (rt-len (rcddr e))))
         (mv-let (pa vmi vce) (vmic-compile-args (rcddr e) depth n self pc vmi vce)
           (mv-let (pb vmi vce) (vmic-compile (rcadr e) (+ depth k) n self pa -1 0 0 vmi vce)
             (let ((vmi (vmic-put pb 10 k 0 0 nil vmi))) (mv (1+ pb) vmi vce))))))
      ((rt-is op :loop)
       (let ((k (rt-len (rcadr e))))
         (mv-let (head vmi vce) (vmic-compile-args (rcadr e) depth n self pc vmi vce)
           (let ((vce (vce-count n depth k vce)))
             (mv-let (pb vmi vce) (vmic-compile (rcaddr e) (+ depth k) (+ n k) self head head depth k vmi vce)
               (let ((vmi (vmic-slides pb k vmi))) (mv (+ pb k) vmi vce)))))))
      ((rt-is op :recur)
       (mv-let (pa vmi vce) (vmic-compile-args (rt-cdr e) depth n self pc vmi vce)
         (let ((vmi (if (< lch 0) (vmic-put pa 12 0 0 0 nil vmi) (vmic-put pa 12 (nfix lck) (nfix lcb) (nfix lch) nil vmi))))
           (mv (1+ pa) vmi vce))))
      ((rt-is op :prim)
       (mv-let (pa vmi vce) (vmic-compile-args (rcddr e) depth n self pc vmi vce)
         (let ((vmi (vmic-put pa 13 pa (rt-len (rcddr e)) 0 (rcadr e) vmi))) (mv (1+ pa) vmi vce))))
      ((rt-is op :throw)
       (mv-let (pa vmi vce) (vmic-compile (rcadr e) depth n self pc -1 0 0 vmi vce)
         (let ((vmi (vmic-put pa 14 0 0 0 nil vmi))) (mv (1+ pa) vmi vce))))
      ((rt-is op :try)
       (mv-let (pb vmi vce) (vmic-compile (rcadr e) depth n self (1+ pc) -1 0 0 vmi vce)
         (let ((vce (vce-set n depth vce)))
           (mv-let (ph vmi vce) (vmic-compile (rcaddr e) (1+ depth) (1+ n) self (+ pb 2) -1 0 0 vmi vce)
             (let* ((vmi (vmic-put pc 15 (+ pb 2) depth 0 nil vmi))
                    (vmi (vmic-put pb 16 0 0 0 nil vmi))
                    (vmi (vmic-put (1+ pb) 7 (1+ ph) 0 0 nil vmi))
                    (vmi (vmic-put ph 5 0 0 0 nil vmi)))
               (mv (1+ ph) vmi vce))))))
      (t (let ((vmi (vmic-put pc 1 pc 0 0 nil vmi))) (mv (1+ pc) vmi vce))))))
 (defun vmic-compile-args (es depth n self pc vmi vce)
   (declare (xargs :stobjs (vmi vce) :measure (acl2-count es)))
   (if (rt-consp es)
       (mv-let (pa vmi vce) (vmic-compile (rt-car es) depth n self pc -1 0 0 vmi vce)
         (vmic-compile-args (rt-cdr es) (1+ (nfix depth)) n self pa vmi vce))
     (mv (nfix pc) vmi vce)))
 (defun vmic-slides (pc k vmi)
   (declare (xargs :stobjs vmi :measure (nfix k)))
   (if (zp k) vmi (let ((vmi (vmic-put pc 5 0 0 0 nil vmi))) (vmic-slides (1+ (nfix pc)) (1- k) vmi)))))

; ---- CLAUSES, FUNCTIONS, THE PROGRAM -------------------------------------------------------

; a clause's body: its locals the arguments (and the rest), its closure above them
(defun vmic-body (cl pc vmi vce)
  (declare (xargs :stobjs (vmi vce) :verify-guards nil))
  (let* ((n (rt-nat (rt-car cl))) (rest (rt-is (rcaddr cl) :rest)))
    (if (< n 0)
        (let ((vce (vce-fail vce))) (mv (nfix pc) vmi vce))
      (let* ((nl (if rest (1+ n) n)) (vce (vce-count 0 0 nl vce)))
        (mv-let (pa vmi vce) (vmic-compile (rcadr cl) (1+ nl) nl nl pc -1 0 0 vmi vce)
          (let ((vmi (vmic-put pa 11 0 0 0 nil vmi))) (mv (1+ pa) vmi vce)))))))

; clause ci's arity n, entry pc and rest flag; function f's first clause and count
(defun vmic-clause-entry (ci n pc rest vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (and (< (nfix ci) (v-cln-length vmi)) (< (nfix ci) (v-clent-length vmi)) (< (nfix ci) (v-clrest-length vmi)))
      (let* ((vmi (update-v-clni (nfix ci) n vmi))
             (vmi (update-v-clenti (nfix ci) pc vmi)))
        (update-v-clresti (nfix ci) rest vmi))
    (update-v-status 2 vmi)))

(defun vmic-fn-entry (f ci count vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (and (< (nfix f) (v-fnfirst-length vmi)) (< (nfix f) (v-fncount-length vmi)))
      (let ((vmi (update-v-fnfirsti (nfix f) ci vmi)))
        (update-v-fncounti (nfix f) count vmi))
    (update-v-status 2 vmi)))

(defun vmic-clauses (cls ci pc vmi vce)
  (declare (xargs :stobjs (vmi vce) :measure (acl2-count cls) :verify-guards nil))
  (if (rt-consp cls)
      (let* ((cl (rt-car cls)) (n (rt-nat (rt-car cl)))
             (vmi (vmic-clause-entry ci (nfix n) (nfix pc) (if (rt-is (rcaddr cl) :rest) 1 0) vmi)))
        (mv-let (pa vmi vce) (vmic-body cl pc vmi vce)
          (vmic-clauses (rt-cdr cls) (1+ (nfix ci)) pa vmi vce)))
    (mv (nfix pc) vmi vce)))

(defun vmic-defs (defs f ci pc vmi vce)
  (declare (xargs :stobjs (vmi vce) :measure (acl2-count defs) :verify-guards nil))
  (if (rt-consp defs)
      (let* ((d (rt-car defs)) (cls (rt-cdr d))
             (vce (if (equal (rt-nat (rt-car d)) (nfix f)) vce (vce-fail vce)))
             (vmi (vmic-fn-entry f (nfix ci) (rt-len cls) vmi)))
        (mv-let (pa vmi vce) (vmic-clauses cls ci pc vmi vce)
          (vmic-defs (rt-cdr defs) (1+ (nfix f)) (+ (nfix ci) (rt-len cls)) pa vmi vce)))
    (mv (nfix pc) vmi vce)))

; the clauses' and bodies' sizes, for the arrays
(defun vmic-size-clauses (cls)
  (if (rt-consp cls) (+ (vmic-size (rcadr (rt-car cls))) 1 (vmic-size-clauses (rt-cdr cls))) 0))
(defun vmic-size-defs (defs)
  (if (rt-consp defs) (+ (vmic-size-clauses (rt-cdr (rt-car defs))) (vmic-size-defs (rt-cdr defs))) 0))
(defun vmic-nclauses (defs)
  (if (rt-consp defs) (+ (rt-len (rt-cdr (rt-car defs))) (vmic-nclauses (rt-cdr defs))) 0))

; the arrays sized as vmi-load-prog sizes them: n instructions, nf
; functions, nc clauses
(defun vmic-resize (n nf nc nstk nctl vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((vmi (resize-v-stk 0 vmi)) (vmi (resize-v-ckind 0 vmi))
         (vmi (resize-v-code (* 4 n) vmi)) (vmi (resize-v-pool n vmi)) (vmi (resize-v-stk nstk vmi))
         (vmi (resize-v-ckind nctl vmi)) (vmi (resize-v-ca nctl vmi)) (vmi (resize-v-cb nctl vmi))
         (vmi (resize-v-cc nctl vmi)) (vmi (resize-v-cprev nctl vmi))
         (vmi (resize-v-fnfirst nf vmi)) (vmi (resize-v-fncount nf vmi))
         (vmi (resize-v-cln nc vmi)) (vmi (resize-v-clent nc vmi)))
    (resize-v-clrest nc vmi)))

; THE PROGRAM: main, its return, then every function's clauses; the
; machine set up to run it, with a stack of nstk slots and a control
; stack of nctl records. At most 4096 locals are in scope at once.
(defun vmic-program (e defs nstk nctl vmi vce)
  (declare (xargs :stobjs (vmi vce) :verify-guards nil))
  (let* ((vmi (vmic-resize (+ (vmic-size e) 1 (vmic-size-defs defs)) (rt-len defs) (vmic-nclauses defs) nstk nctl vmi))
         (vmi (update-v-status 0 vmi))
         (vce (resize-ce-env 4096 vce)) (vce (update-ce-err 0 vce)))
    (mv-let (pa vmi vce) (vmic-compile e 0 0 -1 0 -1 0 0 vmi vce)
      (let ((vmi (vmic-put pa 11 0 0 0 nil vmi)))
        (mv-let (pb vmi vce) (vmic-defs defs 0 0 (1+ pa) vmi vce)
          (declare (ignore pb))
          (let* ((vmi (update-v-pc 0 vmi)) (vmi (update-v-fb 0 vmi)) (vmi (update-v-sp 0 vmi))
                 (vmi (update-v-ctop 0 vmi)) (vmi (update-v-hidx -1 vmi)))
            (mv vmi vce)))))))

; ---- AS A CHECK: the arrays read back as vcs2-program --------------------------------------

(defun vmic-check (e vmi vce)
  (declare (xargs :stobjs (vmi vce) :mode :program))
  (let* ((e (ren-e e *x2-names*)) (prog (vcs2-program e *xi-defs*)))
    (mv-let (vmi vce) (vmic-program e *xi-defs* 1024 256 vmi vce)
      (mv (cond ((not (equal (ce-err vce) 0)) :error)
                ((not (equal (v-status vmi) 0)) :overflow)
                ((not (equal (vmi-prog vmi) prog)) (list :differs (vmi-prog vmi) prog))
                (t t))
          vmi vce))))

(defun vmic-check-run (e)
  (declare (xargs :mode :program))
  (with-local-stobj vmi
    (mv-let (ok vmi)
      (with-local-stobj vce (mv-let (ok vmi vce) (vmic-check e vmi vce) (mv ok vmi)))
      ok)))

(defmacro check-vmic (e) `(assert-event (equal (vmic-check-run (quote ,e)) t)))

; vmi.lisp's checks: the compiler's arrays read back as vcs2-program
(check-vmic (:callv (:mkclo vsum) (:const 1) (:const 2) (:const 3) (:const 4)))
(check-vmic (:callv (:mkclo vsum)))
(check-vmic (:callv (:mkclo f2) (:const 5)))
(check-vmic (:callv (:mkclo f2) (:const 5) (:const 6)))
(check-vmic (:callv (:mkclo f2) (:const 5) (:const 6) (:const 7)))
(check-vmic (:callv (:mkclo f2)))
(check-vmic (:try (:callv (:mkclo f2)) (:local 0)))
(check-vmic (:callv (:const 3) (:const 1)))
(check-vmic (:try (:throw (:const 7)) (:add (:local 0) (:const 1))))
(check-vmic (:throw (:const 3)))
(check-vmic (:try (:callv (:mkclo thr) (:const 9)) (:add (:local 0) (:const 1))))
(check-vmic (:try (:callv (:mkclo to3)) (:local 0)))
(check-vmic (:try (:prim :div (:const 7) (:const 0)) (:local 0)))
(check-vmic (:prim :div (:const 7) (:const 2)))
(check-vmic (:let (:try (:const 4) (:throw (:local 0))) (:add (:local 0) (:const 0))))
