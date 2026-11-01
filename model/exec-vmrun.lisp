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

; THE VM RUN OF A WELL-FORMED TREE'S TRANSLATION ANSWERS THE TREE'S VALUE
(defthm ex-vm-runs
  (implies (and (ex-vwf :m e 0 nil nil) (valp (car (ex-ev :m e 0 nil fr fuel))) (natp k))
           (equal (vcsx-run-program (ex-tr :m e 0 nil) nil (+ (sxclk (ex-tr :m e 0 nil) nil nil nil fuel) k))
                  (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :in-theory (disable vcsx-run-program sxclk ex-ev ex-tr ex-vwf mx)
                  :use ((:instance ex-vm-agree (cm nil) (env nil) (caps nil) (defs nil))
                        (:instance ex-tr-xwf (cm nil) (lp nil))
                        (:instance vcsx-correct (e (ex-tr :m e 0 nil)) (defs nil))))))
