; THE VM RUNS THE TREE (model/exec-vm.lisp with model/vmx-proof.lisp):
; exec-vm proves a well-formed core tree's value is mx's of its
; translation (ex-vm-agree) and the translation xwf (ex-tr-xwf);
; vmx-proof proves the VM's run of an xwf program answers mx's value
; (vcsx-correct). Together: the VM run of the translation answers the
; tree's value. A book of its own so exec-cost need not carry vmx-proof's
; arithmetic.

(in-package "ACL2")

(include-book "exec-vm")
(include-book "vmx-proof")

; THE VM RUN OF A WELL-FORMED TREE'S TRANSLATION ANSWERS THE TREE'S VALUE,
; the program's defs every template's the tree can call (ex-defs-ok)
(defthm ex-vm-runs
  (implies (and (ex-vwf :m e 0 nil nil defs) (ex-defs-ok defs defs) (valp (car (ex-ev :m e 0 nil fr fuel))) (natp k))
           (equal (vcsx-run-program (ex-tr :m e 0 nil) defs (+ (sxclk (ex-tr :m e 0 nil) nil nil defs fuel) k))
                  (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :in-theory (disable vcsx-run-program sxclk ex-ev ex-tr ex-vwf mx ex-defs-ok)
                  :use ((:instance ex-vm-agree (cm nil) (env nil) (caps nil))
                        (:instance ex-tr-xwf (cm nil) (lp nil))
                        (:instance ex-defs-xdefs (ds defs))
                        (:instance ex-defs-ok-alistp (ds defs))
                        (:instance vcsx-correct (e (ex-tr :m e 0 nil)))))))

; an example: (let* [y 10] ((fn [x] (if x (recur nil) y)) true)) -- a
; closure capturing y, entered, its body recurring to the fn once: the
; tree, mx and the VM all answer 10. The template (name arities caps
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
(defconst *ex-defs* (list (cons *ex-tm* (ex-def *ex-tm*))))
(assert-event (ex-defs-ok *ex-defs* *ex-defs*))
(assert-event (ex-vwf :m *ex-prog* 0 nil nil *ex-defs*))
(assert-event (equal (car (ex-ev :m *ex-prog* 0 nil (make-list 1) 10)) '(:val . 10)))
; mx's lookup is assoc-eq, whose guard asks a symbol name or a symbol
; alist: a template is not one, so mx's run on these defs is the logic's
; (vmx's guards are not verified), evaluated by the prover
(defthm ex-example-mx (equal (mx (ex-tr :m *ex-prog* 0 nil) nil nil *ex-defs* 10) '(:val . 10)) :rule-classes nil)
(defthm ex-example-vm (equal (vcsx-run-program (ex-tr :m *ex-prog* 0 nil) *ex-defs* 1000) '(:val . 10)) :rule-classes nil)
