; THE VM RUNS THE TREE (model/exec-vm.lisp with model/vmx2-proof.lisp):
; exec-vm proves a well-formed core tree's value is mx2's of its
; translation (ex-vm-agree) and the translation x2wf (ex-tr-xwf);
; vmx2-proof proves the VM's run of an x2wf program answers mx2's value
; (vcs2-correct). Together: the VM run of the translation answers the
; tree's value. A book of its own so exec-cost need not carry vmx2-proof's
; arithmetic.

(in-package "ACL2")

(include-book "exec-vm")
(include-book "vmx2-proof")

; THE VM RUN OF A WELL-FORMED TREE'S TRANSLATION ANSWERS THE TREE'S VALUE,
; the program's defs every template's the tree can call (ex-defs-ok), its
; fns of any arities, variadic ones among them, and apply's spread call
(defthm ex-vm-runs
  (implies (and (ex-vwf :m e 0 nil nil defs) (ex-defs-ok defs defs) (ex-lzok defs) (valp (car (ex-ev :m e 0 nil fr fuel))) (natp k))
           (equal (vcs2-run-program (ex-tr :m e 0 nil) defs (+ (s2clk (ex-tr :m e 0 nil) nil nil defs fuel) k))
                  (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :in-theory (disable vcs2-run-program s2clk ex-ev ex-tr ex-vwf mx2 ex-defs-ok)
                  :use ((:instance ex-vm-agree (cm nil) (env nil) (caps nil))
                        (:instance ex-tr-xwf (cm nil) (lp nil))
                        (:instance ex-defs-xdefs (ds defs))
                        (:instance vcs2-correct (e (ex-tr :m e 0 nil)))))))

; an example: (let* [y 10] ((fn [x] (if x (recur nil) y)) true)) -- a
; closure capturing y, entered, its body recurring to the fn once: the
; tree, mx2 and the VM all answer 10. The template (name arities caps
; nslots self): one arity (1 nil 0 body), the capture pair (outer 0 inner
; 1), 3 slots, the self slot 2; a node (kind i2 kids c s2 mark rstart rn)
(defconst *ex-tm*
  '(f ((1 nil 0 (4 0 ((2 0 nil nil 0 nil 0 0)
                      (16 0 ((1 0 nil nil 0 nil 0 0)) nil 0 nil 0 1)
                      (2 1 nil nil 0 nil 0 0)) nil 0 nil 0 0)))
      (0 1) 3 2))
(defconst *ex-prog*
  `(11 1 ((1 0 nil 10 0 nil 0 0)
          (6 0 ((14 0 nil ,*ex-tm* 0 nil 0 0) (1 0 nil t 0 nil 0 0)) nil 0 nil 0 0))
       nil 0 nil 0 0))
; multi-arity and variadic: (fn ([x] x) ([x & r] r)), slots 0 and 1, called
; with one argument (the fixed arity wins), three (the rest a list) and
; none (no arity: the arity error)
(defconst *ex-tmv*
  '(g ((1 nil 0 (2 0 nil nil 0 nil 0 0)) (1 t 0 (2 1 nil nil 0 nil 0 0))) nil 2 nil))
(defun ex-consts (vs) (if (atom vs) nil (cons (list 1 0 nil (car vs) 0 nil 0 0) (ex-consts (cdr vs)))))
(defun ex-callg (vs) (list 6 0 (cons (list 14 0 nil *ex-tmv* 0 nil 0 0) (ex-consts vs)) nil 0 nil 0 0))
(defconst *ex-defs* (list (cons *ex-tm* (ex-def *ex-tm*)) (cons *ex-tmv* (ex-def *ex-tmv*))))
(assert-event (ex-defs-ok *ex-defs* *ex-defs*))
(assert-event (ex-vwf :m *ex-prog* 0 nil nil *ex-defs*))
(assert-event (equal (car (ex-ev :m *ex-prog* 0 nil (make-list 1) 10)) '(:val . 10)))
(assert-event (equal (car (ex-ev :m (ex-callg (quote (5))) 0 nil nil 10)) '(:val . 5)))
(assert-event (equal (car (ex-ev :m (ex-callg (quote (5 6 7))) 0 nil nil 10)) '(:val 6 7)))
(assert-event (equal (car (ex-ev :m (ex-callg (quote (5))) 0 nil nil 10)) '(:val . 5)))
(assert-event (equal (car (ex-ev :m (ex-callg nil) 0 nil nil 10)) '(:thrown . :arity)))
(assert-event (ex-vwf :m (ex-callg (quote (5 6 7))) 0 nil nil *ex-defs*))
; mx2's lookup is assoc-equal, the VM's too: a template is its own def's
; name. vmx2's guards are not verified, so the runs on these defs are the
; logic's, evaluated by the prover
(defthm ex-example-mx (equal (mx2 (ex-tr :m *ex-prog* 0 nil) nil nil *ex-defs* 10) '(:val . 10)) :rule-classes nil)
(defthm ex-example-vm (equal (vcs2-run-program (ex-tr :m *ex-prog* 0 nil) *ex-defs* 1000) '(:val . 10)) :rule-classes nil)
(defthm ex-example-rest
  (and (equal (mx2 (ex-tr :m (ex-callg (quote (5 6 7))) 0 nil) nil nil *ex-defs* 10) '(:val 6 7))
       (equal (vcs2-run-program (ex-tr :m (ex-callg (quote (5 6 7))) 0 nil) *ex-defs* 1000) '(:val 6 7)))
  :rule-classes nil)
; the arity error: the tree, mx2 and the VM all throw :arity
(defthm ex-example-arity
  (and (equal (mx2 (ex-tr :m (ex-callg nil) 0 nil) nil nil *ex-defs* 10) '(:thrown . :arity))
       (equal (vcs2-run-program (ex-tr :m (ex-callg nil) 0 nil) *ex-defs* 1000) '(:thrown . :arity)))
  :rule-classes nil)
; apply (2c-iii): (apply g 5 '(6 7)) spreads to (g 5 6 7), the rest (6 7);
; (apply g nil) to (g), the arity error -- the tree, mx2 (:applyv) and the
; VM alike
(defun ex-applyg (vs l)
  (list 6 0 (list* (list 1 0 nil :apply 0 nil 0 0) (list 14 0 nil *ex-tmv* 0 nil 0 0) (ex-consts (append vs (list l))))
        nil 0 nil 0 0))
(assert-event (ex-vwf :m (ex-applyg '(5) '(6 7)) 0 nil nil *ex-defs*))
(assert-event (equal (car (ex-ev :m (ex-applyg '(5) '(6 7)) 0 nil nil 10)) '(:val 6 7)))
(assert-event (equal (car (ex-ev :m (ex-applyg nil nil) 0 nil nil 10)) '(:thrown . :arity)))
(defthm ex-example-apply
  (and (equal (mx2 (ex-tr :m (ex-applyg '(5) '(6 7)) 0 nil) nil nil *ex-defs* 10) '(:val 6 7))
       (equal (vcs2-run-program (ex-tr :m (ex-applyg '(5) '(6 7)) 0 nil) *ex-defs* 1000) '(:val 6 7))
       (equal (mx2 (ex-tr :m (ex-applyg nil nil) 0 nil) nil nil *ex-defs* 10) '(:thrown . :arity))
       (equal (vcs2-run-program (ex-tr :m (ex-applyg nil nil) 0 nil) *ex-defs* 1000) '(:thrown . :arity)))
  :rule-classes nil)
; over a vector (2c-iv): (apply g 5 [6 7]) spreads the vector's elements --
; the translation the same call, :applyv's spread seqk's (x2-vals) -- the
; rest (6 7) in the tree, mx2 and the VM alike
(assert-event (ex-vwf :m (ex-applyg '(5) '(:vec 6 7)) 0 nil nil *ex-defs*))
(assert-event (equal (car (ex-ev :m (ex-applyg '(5) '(:vec 6 7)) 0 nil nil 10)) '(:val 6 7)))
(defthm ex-example-apply-vector
  (and (equal (mx2 (ex-tr :m (ex-applyg '(5) '(:vec 6 7)) 0 nil) nil nil *ex-defs* 10) '(:val 6 7))
       (equal (vcs2-run-program (ex-tr :m (ex-applyg '(5) '(:vec 6 7)) 0 nil) *ex-defs* 1000) '(:val 6 7)))
  :rule-classes nil)
