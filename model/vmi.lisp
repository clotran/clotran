; clotran's VM, formally (PLAN step 30): THE IMPLEMENTATION LEVEL, the
; model the Fortran is generated from (James, 2026-10-07: "let's write
; the generator for everything"). vmx2.lisp's machine is about lists:
; its stack a list grown by update-nth, its control stack a list of
; records, its program a list of instruction lists and an alist of
; functions. This one is about what Fortran holds: 64-bit registers and
; fixed-size arrays, in one ACL2 stobj, updated in place.
;
;   the registers  pc, the frame base, sp, a status (0 running, 1
;                  stopped by a throw nothing caught, 2 an array
;                  overflowed), the control stack's top, and the
;                  NEAREST HANDLER'S INDEX in it, or -1
;   the code       4 words an instruction: its opcode and up to three
;                  operands, all naturals
;   the pool       a value per instruction: a push's constant, a
;                  primitive's operator
;   the stack      values, unset slots nil
;   the control    records in five parallel arrays: kind (1 a call, 2 a
;                  handler), three fields, and for a handler the index
;                  of the handler below it
;   the functions  per function id, its clauses' first index and count;
;                  per clause its arity, entry pc and whether variadic
;
; A throw truncates the control stack to the nearest handler's index
; and takes that handler's own link as the next: one step, however many
; call records it passes, as vmx2-cost.lisp's bound assumes.
;
; What a value IS stays the runtime's: truthy, the arithmetic, a
; closure's parts, a rest list built from slots, and the primitives are
; vmx2's own functions here and hand-written Fortran in the build. An
; operation that may allocate writes its answer into a stack slot, so
; generated code holds no value across an allocation.
;
; vmi-proof.lisp proves that one step here, read back as vmx2's state,
; is vcs2-step on the program read back from the arrays -- unless an
; array overflowed, which vmx2's unbounded lists never do.

(in-package "ACL2")

(include-book "vmx2")

(defstobj vmi
  (v-pc :type (signed-byte 64) :initially 0)
  (v-fb :type (signed-byte 64) :initially 0)
  (v-sp :type (signed-byte 64) :initially 0)
  (v-status :type (signed-byte 64) :initially 0)
  (v-ctop :type (signed-byte 64) :initially 0)
  (v-hidx :type (signed-byte 64) :initially -1)
  (v-code :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (v-pool :type (array t (0)) :initially nil :resizable t)
  (v-stk :type (array t (0)) :initially nil :resizable t)
  (v-ckind :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (v-ca :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (v-cb :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (v-cc :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (v-cprev :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (v-fnfirst :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (v-fncount :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (v-cln :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (v-clent :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (v-clrest :type (array (signed-byte 64) (0)) :initially 0 :resizable t))

; ---- READING AND WRITING, bounded ---------------------------------------------------

; an instruction's word k, 0 past the code
(defun vmi-w (pc k vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((i (+ (* 4 (nfix pc)) (nfix k))))
    (if (< i (v-code-length vmi)) (v-codei i vmi) 0)))

(defun vmi-poolv (i vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (< (nfix i) (v-pool-length vmi)) (v-pooli (nfix i) vmi) nil))

; a slot past the stack reads nil, as nth past a list does
(defun vmi-sreg (i vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (< (nfix i) (v-stk-length vmi)) (v-stki (nfix i) vmi) nil))

; a write past the stack is an overflow
(defun vmi-sset (i v vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (< (nfix i) (v-stk-length vmi))
      (update-v-stki (nfix i) v vmi)
    (update-v-status 2 vmi)))

; the slots a..a+k-1 as a list: a rest list, a closure's captures, a
; primitive's arguments (the runtime builds it)
(defun vmi-stk-from (a k vmi)
  (declare (xargs :stobjs vmi :measure (nfix k) :verify-guards nil))
  (if (zp k) nil (cons (vmi-sreg a vmi) (vmi-stk-from (1+ (nfix a)) (1- k) vmi))))

; recur's copy of k values from src down to dst
(defun vmi-copy-down (src dst k vmi)
  (declare (xargs :stobjs vmi :measure (nfix k) :verify-guards nil))
  (if (zp k)
      vmi
    (let ((vmi (vmi-sset (nfix dst) (vmi-sreg (nfix src) vmi) vmi)))
      (vmi-copy-down (1+ (nfix src)) (1+ (nfix dst)) (1- k) vmi))))

; ---- THE CONTROL STACK -----------------------------------------------------------------

(defun vmi-push-rec (kind a b c vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((j (nfix (v-ctop vmi))))
    (if (< j (v-ckind-length vmi))
        (let* ((vmi (update-v-ckindi j kind vmi))
               (vmi (update-v-cai j a vmi))
               (vmi (update-v-cbi j b vmi))
               (vmi (update-v-cci j c vmi))
               (vmi (update-v-cprevi j (v-hidx vmi) vmi))
               (vmi (if (equal kind 2) (update-v-hidx j vmi) vmi)))
          (update-v-ctop (1+ j) vmi))
      (update-v-status 2 vmi))))

; the top record dropped; a handler's link becomes the nearest
(defun vmi-pop-rec (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((j (1- (nfix (v-ctop vmi)))))
    (if (< j 0)
        vmi
      (let ((vmi (if (equal (v-ckindi j vmi) 2) (update-v-hidx (v-cprevi j vmi) vmi) vmi)))
        (update-v-ctop j vmi)))))

; A THROW: to the nearest handler, in one step -- or stopped
(defun vmi-unwind (v vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((j (v-hidx vmi)))
    (if (or (not (integerp j)) (< j 0))
        (let* ((vmi (vmi-sset 0 v vmi))
               (vmi (if (equal (v-status vmi) 2) vmi (update-v-status 1 vmi)))
               (vmi (update-v-pc 0 vmi))
               (vmi (update-v-fb 0 vmi))
               (vmi (update-v-sp 1 vmi))
               (vmi (update-v-ctop 0 vmi)))
          (update-v-hidx -1 vmi))
      (let* ((h (nfix (v-cai j vmi))) (hfb (nfix (v-cbi j vmi))) (hd (nfix (v-cci j vmi)))
             (vmi (vmi-sset (+ hfb hd) v vmi))
             (vmi (update-v-pc h vmi))
             (vmi (update-v-fb hfb vmi))
             (vmi (update-v-sp (+ hfb hd 1) vmi))
             (vmi (update-v-ctop j vmi)))
        (update-v-hidx (v-cprevi j vmi) vmi)))))

; ---- THE FUNCTION TABLE: the clause a call takes ---------------------------------------

(defun vmi-pick-fixed (ci k m vmi)
  (declare (xargs :stobjs vmi :measure (nfix k) :verify-guards nil))
  (cond ((zp k) -1)
        ((and (not (equal (v-clresti (nfix ci) vmi) 1)) (equal (nfix (v-clni (nfix ci) vmi)) m)) (nfix ci))
        (t (vmi-pick-fixed (1+ (nfix ci)) (1- k) m vmi))))

(defun vmi-pick-rest (ci k m vmi)
  (declare (xargs :stobjs vmi :measure (nfix k) :verify-guards nil))
  (cond ((zp k) -1)
        ((and (equal (v-clresti (nfix ci) vmi) 1) (<= (nfix (v-clni (nfix ci) vmi)) m)) (nfix ci))
        (t (vmi-pick-rest (1+ (nfix ci)) (1- k) m vmi))))

; the clause index, or -1: no such function, or none for this count
(defun vmi-pick (f m vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (and (natp f) (< f (v-fnfirst-length vmi)))
      (let* ((ci (v-fnfirsti f vmi)) (k (v-fncounti f vmi)) (x (vmi-pick-fixed ci k m vmi)))
        (if (<= 0 x) x (vmi-pick-rest ci k m vmi)))
    -1))

; ---- THE INSTRUCTIONS ------------------------------------------------------------------
;
; 1 push  2 load  3 add  4 lt  5 slide  6 jmpf  7 jmp  8 mkclo  9 capt
; 10 callv  11 ret  12 recur  13 prim  14 throw  15 try  16 endtry

(defmacro vmi-next (vmi) `(update-v-pc (1+ (nfix (v-pc ,vmi))) ,vmi))

(defun vmi-push (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((sp (nfix (v-sp vmi)))
         (vmi (vmi-sset sp (vmi-poolv (vmi-w (v-pc vmi) 1 vmi) vmi) vmi))
         (vmi (update-v-sp (1+ sp) vmi)))
    (vmi-next vmi)))

(defun vmi-load (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((sp (nfix (v-sp vmi)))
         (vmi (vmi-sset sp (vmi-sreg (+ (nfix (v-fb vmi)) (nfix (vmi-w (v-pc vmi) 1 vmi))) vmi) vmi))
         (vmi (update-v-sp (1+ sp) vmi)))
    (vmi-next vmi)))

(defun vmi-add (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((sp (nfix (v-sp vmi))))
    (if (< sp 2)
        vmi
      (let* ((vmi (vmi-sset (- sp 2) (+ (fix (vmi-sreg (- sp 2) vmi)) (fix (vmi-sreg (1- sp) vmi))) vmi))
             (vmi (update-v-sp (1- sp) vmi)))
        (vmi-next vmi)))))

(defun vmi-lt (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((sp (nfix (v-sp vmi))))
    (if (< sp 2)
        vmi
      (let* ((vmi (vmi-sset (- sp 2) (bool (< (rfix (vmi-sreg (- sp 2) vmi)) (rfix (vmi-sreg (1- sp) vmi)))) vmi))
             (vmi (update-v-sp (1- sp) vmi)))
        (vmi-next vmi)))))

(defun vmi-slide (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((sp (nfix (v-sp vmi))))
    (if (< sp 2)
        vmi
      (let* ((vmi (vmi-sset (- sp 2) (vmi-sreg (1- sp) vmi) vmi))
             (vmi (update-v-sp (1- sp) vmi)))
        (vmi-next vmi)))))

(defun vmi-jmpf (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((sp (nfix (v-sp vmi))))
    (if (zp sp)
        vmi
      (let ((vmi (update-v-sp (1- sp) vmi)))
        (if (truthy (vmi-sreg (1- sp) vmi))
            (vmi-next vmi)
          (update-v-pc (nfix (vmi-w (v-pc vmi) 1 vmi)) vmi))))))

(defun vmi-jmp (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (update-v-pc (nfix (vmi-w (v-pc vmi) 1 vmi)) vmi))

(defun vmi-mkclo (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((sp (nfix (v-sp vmi))) (k (nfix (vmi-w (v-pc vmi) 2 vmi))))
    (if (< sp k)
        vmi
      (let* ((vmi (vmi-sset (- sp k) (clo (vmi-w (v-pc vmi) 1 vmi) (vmi-stk-from (- sp k) k vmi)) vmi))
             (vmi (update-v-sp (1+ (- sp k)) vmi)))
        (vmi-next vmi)))))

(defun vmi-capt (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((sp (nfix (v-sp vmi)))
         (c (vmi-sreg (+ (nfix (v-fb vmi)) (nfix (vmi-w (v-pc vmi) 1 vmi))) vmi))
         (vmi (vmi-sset sp (nth (nfix (vmi-w (v-pc vmi) 2 vmi)) (clo-caps c)) vmi))
         (vmi (update-v-sp (1+ sp) vmi)))
    (vmi-next vmi)))

; A CALL, by clause: the frame begins at the first argument; a variadic
; clause has its extra values packed into one list in place, the
; closure moved above it
(defun vmi-callv (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((sp (nfix (v-sp vmi))) (m (nfix (vmi-w (v-pc vmi) 1 vmi))))
    (if (< sp (1+ m))
        vmi
      (let ((c (vmi-sreg (1- sp) vmi)))
        (if (not (clop c))
            (vmi-unwind :not-fn vmi)
          (let ((ci (vmi-pick (clo-f c) m vmi)))
            (if (< ci 0)
                (vmi-unwind :arity vmi)
              (let* ((fb2 (- sp (1+ m))) (n (nfix (v-clni ci vmi))) (ent (nfix (v-clenti ci vmi)))
                     (vmi (vmi-push-rec 1 (1+ (nfix (v-pc vmi))) (nfix (v-fb vmi)) 0 vmi)))
                (if (equal (v-clresti ci vmi) 1)
                    (let* ((vmi (vmi-sset (+ fb2 n) (vmi-stk-from (+ fb2 n) (- m n) vmi) vmi))
                           (vmi (vmi-sset (+ fb2 n 1) c vmi))
                           (vmi (update-v-fb fb2 vmi))
                           (vmi (update-v-sp (+ fb2 n 2) vmi)))
                      (update-v-pc ent vmi))
                  (let* ((vmi (update-v-fb fb2 vmi)))
                    (update-v-pc ent vmi)))))))))))

; a return: the value to the frame's base, the caller's pc and frame back;
; a handler record on top is read as vmx2 reads it -- pc 0, frame its
; handler pc -- which compiled code never does
(defun vmi-ret (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((sp (nfix (v-sp vmi))) (fb (nfix (v-fb vmi))))
    (if (zp sp)
        vmi
      (let ((v (vmi-sreg (1- sp) vmi)))
        (if (zp (v-ctop vmi))
            (let* ((vmi (vmi-sset 0 v vmi)))
              (update-v-sp 1 vmi))
          (let* ((j (1- (v-ctop vmi)))
                 (hp (equal (v-ckindi j vmi) 2))
                 (npc (if hp 0 (nfix (v-cai j vmi))))
                 (nfb (if hp (nfix (v-cai j vmi)) (nfix (v-cbi j vmi))))
                 (vmi (vmi-sset fb v vmi))
                 (vmi (update-v-sp (1+ fb) vmi))
                 (vmi (vmi-pop-rec vmi))
                 (vmi (update-v-fb nfb vmi)))
            (update-v-pc npc vmi)))))))

(defun vmi-recur (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((pc (v-pc vmi)) (k (nfix (vmi-w pc 1 vmi))) (b (nfix (vmi-w pc 2 vmi))) (l (nfix (vmi-w pc 3 vmi)))
         (fb (nfix (v-fb vmi))) (sp (nfix (v-sp vmi))))
    (if (< sp (+ fb b k))
        vmi
      (let* ((vmi (vmi-copy-down (- sp k) (+ fb b) k vmi))
             (vmi (update-v-sp (+ fb b k) vmi)))
        (update-v-pc l vmi)))))

(defun vmi-prim (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((sp (nfix (v-sp vmi))) (n (nfix (vmi-w (v-pc vmi) 2 vmi))))
    (if (< sp n)
        vmi
      (let ((a (prim (vmi-poolv (vmi-w (v-pc vmi) 1 vmi) vmi) (vmi-stk-from (- sp n) n vmi))))
        (if (throwp a)
            (vmi-unwind (cdr a) vmi)
          (let* ((vmi (vmi-sset (- sp n) a vmi))
                 (vmi (update-v-sp (1+ (- sp n)) vmi)))
            (vmi-next vmi)))))))

(defun vmi-throw (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((sp (nfix (v-sp vmi))))
    (if (zp sp) vmi (vmi-unwind (vmi-sreg (1- sp) vmi) vmi))))

(defun vmi-try (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((pc (v-pc vmi))
         (vmi (vmi-push-rec 2 (nfix (vmi-w pc 1 vmi)) (nfix (v-fb vmi)) (nfix (vmi-w pc 2 vmi)) vmi)))
    (vmi-next vmi)))

(defun vmi-endtry (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((vmi (vmi-pop-rec vmi)))
    (vmi-next vmi)))

; ONE STEP
(defun vmi-step (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (not (equal (v-status vmi) 0))
      vmi
    (case (vmi-w (v-pc vmi) 0 vmi)
      (1 (vmi-push vmi)) (2 (vmi-load vmi)) (3 (vmi-add vmi)) (4 (vmi-lt vmi)) (5 (vmi-slide vmi))
      (6 (vmi-jmpf vmi)) (7 (vmi-jmp vmi)) (8 (vmi-mkclo vmi)) (9 (vmi-capt vmi)) (10 (vmi-callv vmi))
      (11 (vmi-ret vmi)) (12 (vmi-recur vmi)) (13 (vmi-prim vmi)) (14 (vmi-throw vmi)) (15 (vmi-try vmi))
      (16 (vmi-endtry vmi))
      (otherwise vmi))))

(defun vmi-run (n vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (zp n) vmi (let ((vmi (vmi-step vmi))) (vmi-run (1- n) vmi))))

; ---- READ BACK AS VMX2's: the state and the program ------------------------------------

(defun vmi-rec (j vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (equal (v-ckindi j vmi) 2)
      (list :h (v-cai j vmi) (v-cbi j vmi) (v-cci j vmi))
    (list (v-cai j vmi) (v-cbi j vmi))))

(defun vmi-ctl (i vmi)
  (declare (xargs :stobjs vmi :measure (nfix i) :verify-guards nil))
  (if (zp i) nil (cons (vmi-rec (1- i) vmi) (vmi-ctl (1- i) vmi))))

; the stack as a list, every slot
(defun vmi-stk-list (i k vmi)
  (declare (xargs :stobjs vmi :measure (nfix k) :verify-guards nil))
  (if (zp k) nil (cons (vmi-sreg i vmi) (vmi-stk-list (1+ (nfix i)) (1- k) vmi))))

(defun vmi-abs (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (list (if (equal (v-status vmi) 1) :thrown (v-pc vmi)) (v-fb vmi) (v-sp vmi)
        (vmi-stk-list 0 (v-stk-length vmi) vmi) (vmi-ctl (nfix (v-ctop vmi)) vmi)))

(defun vmi-ins (pc vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((a (vmi-w pc 1 vmi)) (b (vmi-w pc 2 vmi)) (c (vmi-w pc 3 vmi)))
    (case (vmi-w pc 0 vmi)
      (1 (list :push (vmi-poolv a vmi))) (2 (list :load a)) (3 (list :add)) (4 (list :lt)) (5 (list :slide))
      (6 (list :jmpf a)) (7 (list :jmp a)) (8 (list :mkclo a b)) (9 (list :capt a b)) (10 (list :callv a))
      (11 (list :ret)) (12 (list :recur a b c)) (13 (list :prim (vmi-poolv a vmi) b)) (14 (list :throw))
      (15 (list :try a b)) (16 (list :endtry))
      (otherwise nil))))

(defun vmi-code-list (pc k vmi)
  (declare (xargs :stobjs vmi :measure (nfix k) :verify-guards nil))
  (if (zp k) nil (cons (vmi-ins pc vmi) (vmi-code-list (1+ (nfix pc)) (1- k) vmi))))

(defun vmi-clauses (ci k vmi)
  (declare (xargs :stobjs vmi :measure (nfix k) :verify-guards nil))
  (if (zp k)
      nil
    (cons (if (equal (v-clresti (nfix ci) vmi) 1)
              (list (v-clni (nfix ci) vmi) (v-clenti (nfix ci) vmi) :rest)
            (list (v-clni (nfix ci) vmi) (v-clenti (nfix ci) vmi)))
          (vmi-clauses (1+ (nfix ci)) (1- k) vmi))))

(defun vmi-fntab (f k vmi)
  (declare (xargs :stobjs vmi :measure (nfix k) :verify-guards nil))
  (if (zp k)
      nil
    (cons (cons (nfix f) (vmi-clauses (v-fnfirsti (nfix f) vmi) (v-fncounti (nfix f) vmi) vmi))
          (vmi-fntab (1+ (nfix f)) (1- k) vmi))))

(defun vmi-prog (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (cons (vmi-code-list 0 (floor (v-code-length vmi) 4) vmi)
        (vmi-fntab 0 (v-fnfirst-length vmi) vmi)))

; ---- THE ENCODER: a vmx2 program into the arrays ------------------------------------------
;
; Function names are their ids 0, 1, ... in the table's order, and a
; primitive's operator and a push's constant go into the pool, one slot
; per instruction. Anything else -- a name that is not its id, an
; operand that is not a natural below 2^31 -- is not encodable.

(defun op-of (key)
  (case key (:push 1) (:load 2) (:add 3) (:lt 4) (:slide 5) (:jmpf 6) (:jmp 7) (:mkclo 8) (:capt 9)
    (:callv 10) (:ret 11) (:recur 12) (:prim 13) (:throw 14) (:try 15) (:endtry 16) (otherwise 0)))

(defun small-natp (x) (and (natp x) (< x 2147483648)))

; the instruction's 4 words; a pool slot's operand is the pc itself
(defun enc-words (ins pc)
  (let ((op (op-of (car ins))))
    (case op
      ((1 13) (list op pc (if (equal op 13) (caddr ins) 0) 0))
      (otherwise (list op (if (consp (cdr ins)) (cadr ins) 0) (if (consp (cddr ins)) (caddr ins) 0)
                       (if (consp (cdddr ins)) (cadddr ins) 0))))))

(defun enc-ok-ins (ins)
  (let ((op (op-of (car ins))))
    (and (not (equal op 0)) (true-listp ins)
         (equal (len ins) (case op ((3 4 5 11 14 16) 1) ((1 2 6 7 10) 2) ((8 9 13 15) 3) (otherwise 4)))
         (or (member op '(1 13)) (small-natp (if (consp (cdr ins)) (cadr ins) 0)))
         (small-natp (if (consp (cddr ins)) (caddr ins) 0))
         (small-natp (if (consp (cdddr ins)) (cadddr ins) 0)))))

(defun enc-ok-code (code)
  (if (atom code) (null code) (and (enc-ok-ins (car code)) (enc-ok-code (cdr code)))))

(defun enc-ok-clauses (ents)
  (if (atom ents)
      (null ents)
    (and (true-listp (car ents)) (small-natp (car (car ents))) (small-natp (cadr (car ents)))
         (or (equal (len (car ents)) 2) (and (equal (len (car ents)) 3) (eq (caddr (car ents)) :rest)))
         (enc-ok-clauses (cdr ents)))))

(defun enc-ok-fntab (tab f)
  (if (atom tab)
      (null tab)
    (and (consp (car tab)) (equal (caar tab) f) (enc-ok-clauses (cdar tab)) (enc-ok-fntab (cdr tab) (1+ f)))))

(defun enc-ok (prog) (and (consp prog) (enc-ok-code (car prog)) (enc-ok-fntab (cdr prog) 0)))

(defun nclauses (tab) (if (atom tab) 0 (+ (len (cdar tab)) (nclauses (cdr tab)))))

(defun enc-code (code pc vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (atom code)
      vmi
    (let* ((w (enc-words (car code) pc))
           (vmi (update-v-codei (* 4 pc) (nth 0 w) vmi))
           (vmi (update-v-codei (+ 1 (* 4 pc)) (nth 1 w) vmi))
           (vmi (update-v-codei (+ 2 (* 4 pc)) (nth 2 w) vmi))
           (vmi (update-v-codei (+ 3 (* 4 pc)) (nth 3 w) vmi))
           (vmi (update-v-pooli pc (case (car (car code)) (:push (cadr (car code))) (:prim (cadr (car code))) (otherwise nil))
                                vmi)))
      (enc-code (cdr code) (1+ pc) vmi))))

(defun enc-clauses (ents ci vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (atom ents)
      vmi
    (let* ((vmi (update-v-clni ci (car (car ents)) vmi))
           (vmi (update-v-clenti ci (cadr (car ents)) vmi))
           (vmi (update-v-clresti ci (if (eq (caddr (car ents)) :rest) 1 0) vmi)))
      (enc-clauses (cdr ents) (1+ ci) vmi))))

(defun enc-fntab (tab f ci vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (atom tab)
      vmi
    (let* ((vmi (update-v-fnfirsti f ci vmi))
           (vmi (update-v-fncounti f (len (cdar tab)) vmi))
           (vmi (enc-clauses (cdar tab) ci vmi)))
      (enc-fntab (cdr tab) (1+ f) (+ ci (len (cdar tab))) vmi))))

; a fresh machine: the program in, a stack of nstk slots and a control
; stack of nctl records, all registers at the start
(defun vmi-load-prog (prog nstk nctl vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((n (len (car prog))) (nf (len (cdr prog))) (nc (nclauses (cdr prog)))
         (vmi (resize-v-stk 0 vmi)) (vmi (resize-v-ckind 0 vmi))
         (vmi (resize-v-code (* 4 n) vmi)) (vmi (resize-v-pool n vmi)) (vmi (resize-v-stk nstk vmi))
         (vmi (resize-v-ckind nctl vmi)) (vmi (resize-v-ca nctl vmi)) (vmi (resize-v-cb nctl vmi))
         (vmi (resize-v-cc nctl vmi)) (vmi (resize-v-cprev nctl vmi))
         (vmi (resize-v-fnfirst nf vmi)) (vmi (resize-v-fncount nf vmi))
         (vmi (resize-v-cln nc vmi)) (vmi (resize-v-clent nc vmi)) (vmi (resize-v-clrest nc vmi))
         (vmi (enc-code (car prog) 0 vmi))
         (vmi (enc-fntab (cdr prog) 0 0 vmi))
         (vmi (update-v-pc 0 vmi)) (vmi (update-v-fb 0 vmi)) (vmi (update-v-sp 0 vmi))
         (vmi (update-v-status 0 vmi)) (vmi (update-v-ctop 0 vmi)))
    (update-v-hidx -1 vmi)))

; ---- AS A CHECK: the arrays against vmx2's lists, step by step ----------------------------
;
; *x2-defs* with each function named by its id, and the stack compared
; up to its trailing nils (vmx2's list grows; the array is all there)

(defun strip-nils (l)
  (if (atom l) nil (let ((r (strip-nils (cdr l)))) (if (and (null r) (null (car l))) nil (cons (car l) r)))))

(defun s-norm (s) (list (car s) (cadr s) (caddr s) (strip-nils (cadddr s)) (car (cddddr s))))

(defun ren-name (f names i)
  (cond ((atom names) f) ((equal f (car names)) i) (t (ren-name f (cdr names) (1+ i)))))

(mutual-recursion
 (defun ren-e (e names)
   (declare (xargs :measure (acl2-count e)))
   (cond ((atom e) e)
         ((eq (car e) :const) e)
         ((eq (car e) :mkclo) (list* :mkclo (ren-name (cadr e) names 0) (ren-list (cddr e) names)))
         ((eq (car e) :prim) (list* :prim (cadr e) (ren-list (cddr e) names)))
         ((eq (car e) :loop) (list :loop (ren-list (cadr e) names) (ren-e (caddr e) names)))
         ((member (car e) '(:local :capt)) e)
         (t (cons (car e) (ren-list (cdr e) names)))))
 (defun ren-list (es names)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) es (cons (ren-e (car es) names) (ren-list (cdr es) names)))))

(defun ren-clauses (cls names)
  (if (atom cls) cls (cons (list* (caar cls) (ren-e (cadar cls) names) (cddar cls)) (ren-clauses (cdr cls) names))))

(defun ren-defs (ds names i)
  (if (atom ds) nil (cons (cons i (ren-clauses (cdar ds) names)) (ren-defs (cdr ds) names (1+ i)))))

(defconst *x2-names* (strip-cars *x2-defs*))
(defconst *xi-defs* (ren-defs *x2-defs* *x2-names* 0))

; every step of both machines, read back and compared; t, or the step
; where they part
(defun lockstep (n prog s vmi)
  (declare (xargs :stobjs vmi :mode :program))
  (cond ((zp n) (mv t vmi))
        ((not (equal (s-norm (vmi-abs vmi)) (s-norm s))) (mv (list :differ-at n (vmi-abs vmi) s) vmi))
        (t (let ((vmi (vmi-step vmi)))
             (if (equal (v-status vmi) 2)
                 (mv :overflow vmi)
               (lockstep (1- n) prog (vcs2-step prog s) vmi))))))

(defun vmi-check (e vmi)
  (declare (xargs :stobjs vmi :mode :program))
  (let* ((e (ren-e e *x2-names*)) (prog (vcs2-program e *xi-defs*)))
    (if (not (enc-ok prog))
        (mv :not-encodable vmi)
      (let ((vmi (vmi-load-prog prog 4096 1024 vmi)))
        (if (not (equal (vmi-prog vmi) prog))
            (mv :decodes-differently vmi)
          (mv-let (ok vmi) (lockstep 5000 prog (list 0 0 0 nil nil) vmi)
            (mv (and (eq ok t)
                     (equal (vcs2-answer (vmi-abs vmi)) (mx2 e nil nil *xi-defs* 1000)))
                vmi)))))))

(defun vmi-check-run (e)
  (declare (xargs :mode :program))
  (with-local-stobj vmi (mv-let (ok vmi) (vmi-check e vmi) ok)))

(defmacro check-vmi (e) `(assert-event (equal (vmi-check-run ',e) t)))

; vmx2.lisp's checks, on the arrays, in lockstep with vcs2-step
(check-vmi (:callv (:mkclo vsum) (:const 1) (:const 2) (:const 3) (:const 4)))
(check-vmi (:callv (:mkclo vsum)))
(check-vmi (:callv (:mkclo f2) (:const 5)))
(check-vmi (:callv (:mkclo f2) (:const 5) (:const 6)))
(check-vmi (:callv (:mkclo f2) (:const 5) (:const 6) (:const 7)))
(check-vmi (:callv (:mkclo f2)))
(check-vmi (:try (:callv (:mkclo f2)) (:local 0)))
(check-vmi (:callv (:const 3) (:const 1)))
(check-vmi (:try (:throw (:const 7)) (:add (:local 0) (:const 1))))
(check-vmi (:throw (:const 3)))
(check-vmi (:try (:callv (:mkclo thr) (:const 9)) (:add (:local 0) (:const 1))))
(check-vmi (:try (:callv (:mkclo to3)) (:local 0)))
(check-vmi (:try (:prim :div (:const 7) (:const 0)) (:local 0)))
(check-vmi (:prim :div (:const 7) (:const 2)))
(check-vmi (:let (:try (:const 4) (:throw (:local 0))) (:add (:local 0) (:const 0))))
