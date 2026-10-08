; clotran's VM, formally (PLAN step 30): the definitions the Fortran is
; generated from (vmg.lisp) answer what a program means.
;
;   vmg-correct   a compiled program, encoded into the arrays and run by
;                 vmg-run -- guard-verified, every value in 64 bits --
;                 answers what its meaning does, unless an array
;                 overflowed: vmi-correct, through vmg-run = vmi-run

(in-package "ACL2")

(include-book "vmg")
(include-book "vmi-proof")

(defthm vmg-correct
  (implies (and (vmip vmi) (x2defs-ok defs) (x2wf e 0 nil) (enc-ok (vcs2-program e defs)) (natp nstk) (natp nctl)
                (or (valp (mx2 e nil nil defs fuel)) (thrownp (mx2 e nil nil defs fuel))) (natp k)
                (not (equal (v-status (vmg-run (+ (s2clk e nil nil defs fuel) k)
                                               (vmi-load-prog (vcs2-program e defs) nstk nctl vmi)))
                            2)))
           (equal (vcs2-answer (vmi-abs (vmg-run (+ (s2clk e nil nil defs fuel) k)
                                                 (vmi-load-prog (vcs2-program e defs) nstk nctl vmi))))
                  (mx2 e nil nil defs fuel)))
  :hints (("Goal" :in-theory (union-theories '(vmg-run-is) (theory 'minimal-theory))
                  :use ((:instance vmi-correct)))))
