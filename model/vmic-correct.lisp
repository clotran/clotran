; clotran's VM, formally (PLAN step 30): THE IMPLEMENTATION-LEVEL
; COMPILER'S PROGRAM RUNS AS ITS MEANING DOES. vmic-program, finishing
; with status 0 and no error, leaves the machine vmi-load-prog leaves for
; vcs2-program's lists, in everything vmi-correct reads: its shape, its
; invariant, the program it reads back, its start. So vmi-correct holds
; of it (vmic-correct).

(in-package "ACL2")

(include-book "vmic-proof")

; ---- THE PROGRAM -----------------------------------------------------------------------------

; the sizes vmic-program computes are vcs2-program's
(defthm len-vcs2-clauses-code (equal (len (car (vcs2-clauses cls pc))) (vmic-size-clauses cls)))
(defthm len-vcs2-defs-code (equal (len (car (vcs2-defs defs pc))) (vmic-size-defs defs)))
(defthm len-vcs2-defs-tab (equal (len (cdr (vcs2-defs defs pc))) (len defs)))
(defthm nclauses-vcs2-defs (equal (nclauses (cdr (vcs2-defs defs pc))) (vmic-nclauses defs)))

(defthm vmic-resize-is
  (implies (and (equal n (len (car prog))) (equal nf (len (cdr prog))) (equal nc (nclauses (cdr prog))))
           (equal (vmic-resize n nf nc nstk nctl vmi) (lp-resize prog nstk nctl vmi)))
  :hints (("Goal" :in-theory (enable lp-resize))))

; the function table reads only fields 14 to 18
(defun-nx fntab-ind (f k a b)
  (declare (xargs :measure (nfix k)))
  (if (zp k) (list f a b) (fntab-ind (1+ (nfix f)) (1- k) a b)))
(defun-nx clauses-ind (ci k a b)
  (declare (xargs :measure (nfix k)))
  (if (zp k) (list ci a b) (clauses-ind (1+ (nfix ci)) (1- k) a b)))

(defmacro same-table (a b)
  `(and (equal (nth 14 ,a) (nth 14 ,b)) (equal (nth 15 ,a) (nth 15 ,b)) (equal (nth 16 ,a) (nth 16 ,b))
        (equal (nth 17 ,a) (nth 17 ,b)) (equal (nth 18 ,a) (nth 18 ,b))))

(defthm vmi-clauses-cong
  (implies (same-table a b) (equal (vmi-clauses ci k a) (vmi-clauses ci k b)))
  :rule-classes nil
  :hints (("Goal" :induct (clauses-ind ci k a b) :in-theory (enable vmi-clauses vmi-clause))))

(defthm vmi-fntab-cong
  (implies (same-table a b) (equal (vmi-fntab f k a) (vmi-fntab f k b)))
  :rule-classes nil
  :hints (("Goal" :induct (fntab-ind f k a b) :in-theory (enable vmi-fntab))
          ("Subgoal *1/2" :use ((:instance vmi-clauses-cong (ci (nth (nfix f) (nth 14 a))) (k (nth (nfix f) (nth 15 a))))))))

(defmacro vp-p () '(vcs2-program e defs))
(defmacro vp-n () '(+ 1 (s2code-len e) (vmic-size-defs defs)))
(defmacro vp-0 () '(update-nth 3 0 (vmic-resize (vp-n) (len defs) (vmic-nclauses defs) nstk nctl vmi)))
(defmacro vp-v () '(update-nth 1 0 (update-nth 0 (resize-list (nth 0 vce) 4096 0) vce)))
(defmacro vp-c () '(vmic-compile e 0 0 -1 0 -1 0 0 (vp-0) (vp-v)))
(defmacro vp-r () '(vmic-put (s2code-len e) 11 0 0 0 nil (mv-nth 1 (vp-c))))
(defmacro vp-d () '(vmic-defs defs 0 0 (+ 1 (s2code-len e)) (vp-r) (mv-nth 2 (vp-c))))
(defmacro vp-g () '(update-nth 5 -1 (update-nth 4 0 (update-nth 2 0 (update-nth 1 0 (update-nth 0 0 (mv-nth 1 (vp-d))))))))

(defthm vmic-program-stages
  (equal (vmic-program e defs nstk nctl vmi vce) (list (vp-g) (mv-nth 2 (vp-d))))
  :hints (("Goal" :in-theory (e/d (vcs2-program) (vmic-resize lp-resize vmic-compile vmic-defs vmic-put)))))

(in-theory (disable vmic-program))

(defmacro vprog () '(car (vmic-program e defs nstk nctl vmi vce)))
(defmacro lprog2 () '(vmi-load-prog (vcs2-program e defs) nstk nctl vmi))


(defmacro lp2-r () '(lp-resize (vcs2-program e defs) nstk nctl vmi))
(defmacro vp-tab () '(cdr (vcs2-program e defs)))

(defthm vcs2-program-parts
  (and (equal (len (car (vcs2-program e defs))) (+ 1 (s2code-len e) (vmic-size-defs defs)))
       (equal (len (cdr (vcs2-program e defs))) (len defs))
       (equal (nclauses (cdr (vcs2-program e defs))) (vmic-nclauses defs))
       (equal (cdr (vcs2-program e defs)) (cdr (vcs2-defs defs (+ 1 (s2code-len e)))))
       (equal (car (vcs2-program e defs))
              (append (vcs2-compile e 0 nil nil 0 nil) (list (list :ret)) (car (vcs2-defs defs (+ 1 (s2code-len e)))))))
  :hints (("Goal" :in-theory (e/d (vcs2-program) (vcs2-compile vcs2-defs)))))

(in-theory (disable vcs2-program))

(defthm vp-resize-is (equal (vmic-resize (vp-n) (len defs) (vmic-nclauses defs) nstk nctl vmi) (lp2-r))
  :hints (("Goal" :use ((:instance vmic-resize-is (prog (vcs2-program e defs)) (n (vp-n)) (nf (len defs))
                                   (nc (vmic-nclauses defs))))
                  :in-theory (disable vmic-resize-is vmic-resize lp-resize))))

(in-theory (disable vmic-resize lp-resize))

(defmacro vp-ok ()
  '(and (equal (nth 3 (vprog)) 0) (not (failed (mv-nth 1 (vmic-program e defs nstk nctl vmi vce))))))

; the registers, and the run's state below them
(defthm vp-regs
  (implies (vp-ok)
           (and (equal (nth 0 (vprog)) 0) (equal (nth 1 (vprog)) 0) (equal (nth 2 (vprog)) 0)
                (equal (nth 4 (vprog)) 0) (equal (nth 5 (vprog)) -1)
                (not (equal (nth 3 (mv-nth 1 (vp-d))) 2)) (not (failed (mv-nth 2 (vp-d)))))))

; the fields nothing but the sizing writes
(defthm vp-other
  (implies (and (natp k) (< 7 k) (< k 14)) (equal (nth k (vprog)) (nth k (lp2-r)))))

(defthm vp-code-len (equal (len (nth 6 (vprog))) (len (nth 6 (lp2-r)))))

(defthm vp-shape (implies (and (vmip vmi) (natp nstk) (natp nctl)) (shape19 (vprog)))
  :hints (("Goal" :use ((:instance lp-resize-facts (prog (vcs2-program e defs)))) :in-theory (disable lp-resize-facts vmip))))

; the table fields
(defthm vp-table
  (implies (and (vp-ok) (member k '(14 15 16 17 18)))
           (equal (nth k (vprog)) (fn-fld k (vp-tab) 0 0 (nth k (lp2-r)))))
  :hints (("Goal" :use (vp-regs) :in-theory (disable vp-regs))))

(defthm lprog2-table
  (implies (and (natp nstk) (natp nctl) (member k '(14 15 16 17 18)))
           (equal (nth k (lprog2)) (fn-fld k (vp-tab) 0 0 (nth k (lp2-r)))))
  :hints (("Goal" :in-theory (e/d (vmi-load-prog-stages lp-regs) (vmi-load-prog enc-code enc-fntab)))))

; the code
(defthm code-at-update-low
  (implies (and (natp k) (< k 6)) (equal (code-at a c (update-nth k v vmi)) (code-at a c vmi)))
  :hints (("Goal" :induct (code-at a c vmi) :in-theory (enable ins-at ins-w))))

(defthm ins-at-defs-below
  (implies (and (natp j) (natp pc) (< j pc)) (equal (ins-at j ins (mv-nth 1 (vdf))) (ins-at j ins vmi)))
  :hints (("Goal" :use ((:instance vmic-defs-elsewhere (a j) (c (list ins)))) :in-theory (disable vmic-defs-elsewhere))))

(defthm vp-code
  (implies (vp-ok) (code-at 0 (car (vcs2-program e defs)) (vprog)))
  :hints (("Goal" :use (vp-regs) :in-theory (disable vp-regs vcs2-compile vcs2-defs))))

; ---- THE COMPILED MACHINE IS A LOADED ONE ------------------------------------------------------

(defthm vp-shape-ok
  (implies (and (vmip vmi) (natp nstk) (natp nctl) (vp-ok)) (and (vmi-shape (vprog)) (vmi-ok (vprog))))
  :hints (("Goal" :in-theory (e/d (vmi-shape vmi-ok) (vmip vmic-program-stages))
                  :use (vp-shape vp-regs (:instance lp-resize-facts (prog (vcs2-program e defs)))))))

(defthm vmi-prog-fntab
  (implies (equal (vmi-prog x) p) (equal (vmi-fntab 0 (len (nth 14 x)) x) (cdr p)))
  :rule-classes nil :hints (("Goal" :in-theory (e/d (vmi-prog) (vmi-fntab vmi-code-list)))))

(defthm lprog2-fntab-nth
  (implies (and (vmip vmi) (enc-ok (vcs2-program e defs)) (natp nstk) (natp nctl))
           (equal (vmi-fntab 0 (len (nth 14 (lprog2))) (lprog2)) (vp-tab)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use ((:instance vmi-load-prog-prog (prog (vcs2-program e defs)))
                        (:instance vmi-prog-fntab (x (lprog2)) (p (vcs2-program e defs)))))))

(defthm lprog2-fntab
  (implies (and (vmip vmi) (enc-ok (vcs2-program e defs)) (natp nstk) (natp nctl))
           (equal (vmi-fntab 0 (len (fn-fld 14 (vp-tab) 0 0 (nth 14 (lp2-r)))) (lprog2)) (vp-tab)))
  :hints (("Goal" :use (lprog2-fntab-nth (:instance lprog2-table (k 14)))
                  :in-theory (disable vmi-fntab vmi-load-prog vmip enc-ok vcs2-program-parts lprog2-table))))

(defthm vp-prog
  (implies (and (vmip vmi) (enc-ok (vcs2-program e defs)) (natp nstk) (natp nctl) (vp-ok))
           (equal (vmi-prog (vprog)) (vcs2-program e defs)))
  :hints (("Goal" :in-theory (e/d (vmi-prog enc-ok) (vmip vmic-program-stages vmi-code-list vmi-fntab vmi-load-prog vcs2-program-parts enc-ok-code enc-ok-fntab vp-code vp-code-len vmi-load-prog-prog lp-resize-facts code-at-decodes))
                  :use (vp-code vp-code-len lprog2-fntab
                        (:instance lp-resize-facts (prog (vcs2-program e defs)))
                        (:instance vmi-fntab-cong (f 0) (k (len (nth 14 (vprog)))) (a (vprog)) (b (lprog2)))
                        (:instance code-at-decodes (j 0) (code (car (vcs2-program e defs))) (vmi (vprog)))))))

(defthm vp-abs
  (implies (and (vmip vmi) (natp nstk) (natp nctl) (vp-ok))
           (equal (vmi-abs (vprog)) (list 0 0 0 (nth 8 (vprog)) nil)))
  :hints (("Goal" :in-theory (e/d (vmi-abs) (vmip vmic-program-stages))
                  :use (vp-regs (:instance lp-resize-facts (prog (vcs2-program e defs)))))))

; ---- THE THEOREM -------------------------------------------------------------------------------

; A PROGRAM THE IMPLEMENTATION-LEVEL COMPILER COMPILES, without an error or
; an overflow, run on the arrays, answers what its meaning does -- its
; value, or the value of a throw nothing caught -- unless an array
; overflowed while it ran.
(defthm vmic-correct
  (implies (and (vmip vmi) (x2defs-ok defs) (x2wf e 0 nil) (enc-ok (vcs2-program e defs)) (natp nstk) (natp nctl)
                (vp-ok)
                (or (valp (mx2 e nil nil defs fuel)) (thrownp (mx2 e nil nil defs fuel))) (natp k)
                (not (equal (v-status (vmi-run (+ (s2clk e nil nil defs fuel) k) (vprog))) 2)))
           (equal (vcs2-answer (vmi-abs (vmi-run (+ (s2clk e nil nil defs fuel) k) (vprog))))
                  (mx2 e nil nil defs fuel)))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory))
                  :use (vp-shape-ok vp-prog vp-abs
                        (:instance vmi-run-refines (n (+ (s2clk e nil nil defs fuel) k)) (vmi (vprog)))
                        (:instance vcs2-correct-stk (stk (nth 8 (vprog))))))))
