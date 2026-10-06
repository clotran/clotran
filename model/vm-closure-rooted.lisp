; clotran's VM, formally (PLAN step 30). ROOTING for the one-stack
; machine:
;
;   wiped-run-agrees  a run that never reads at or above its stack top
;                     ends where the same run does with every slot at or
;                     above the top wiped after every step -- whatever
;                     the program
;
;   vcs-rooted        and a compiled program answers what its meaning
;                     does on the wiping machine, for every clock past
;                     its own: it never reads above its top
;                     (vcs-program-reads, carried by sgood)
;
; The return records hold a pc and a frame base and no value, so the
; slots below the top are the machine's roots: a collector that scans
; them and nothing else, at any step, sees every value the computation
; will read.

(in-package "ACL2")

(include-book "vm-closure-stack-correct")

; ---- THE WIPE (vm-closure.lisp's swipe, wstep, vcs-run-wiping) ---------------

(defthm nth-swipe
  (equal (nth i (swipe h stk))
         (if (< (nfix i) (nfix h)) (nth i stk) (if (< (nfix i) (len stk)) nil (nth i stk))))
  :hints (("Goal" :induct (list (swipe h stk) (nth i stk)))))

(defthm cagree-swipe
  (cagree (swipe h stk) stk h)
  :hints (("Goal" :expand ((cagree (swipe h stk) stk h)))))

; reads-ok and run-reads-ok, what a step and a run read, are in
; vm-closure-stack-proof.lisp, where sgood carries them.

; two states alike in everything but their dead slots
(defun srel (s u)
  (and (equal (car s) (car u)) (equal (cadr s) (cadr u)) (equal (caddr s) (caddr u))
       (equal (s-ctl s) (s-ctl u)) (cagree (cadddr s) (cadddr u) (nfix (caddr s)))))

; ---- A STEP CANNOT TELL THEM APART ---------------------------------------------

(defthm cagree-write-below
  (implies (and (cagree a b h) (natp h) (natp j) (<= j h) (<= (nfix h2) (max h (1+ j))))
           (cagree (update-nth j v a) (update-nth j v b) h2))
  :hints (("Goal" :cases ((<= (nfix h2) (nfix h))) :in-theory (disable cagree-write-at cagree-smaller)
                  :use ((:instance cagree-write-at (n j) (x v))
                        (:instance cagree-smaller (a (update-nth j v a)) (b (update-nth j v b)) (h (1+ j)) (g h2))
                        (:instance cagree-smaller (a (update-nth j v a)) (b (update-nth j v b)) (g h2))))))

(defthm stk-from-agree
  (implies (and (cagree a b h) (<= (+ (nfix i) (nfix k)) (nfix h)))
           (equal (stk-from i k a) (stk-from i k b)))
  :hints (("Goal" :induct (stk-from i k a))))

; the state's shape: five fields, a natural frame base and top
(defun sshape (s)
  (and (true-listp s) (equal (len s) 5) (natp (cadr s)) (natp (caddr s))))

(defthm sshape-step (implies (sshape s) (sshape (vcs-step prog s)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))
(defthm sshape-wstep (implies (sshape s) (sshape (wstep prog s)))
  :hints (("Goal" :in-theory (disable vcs-step sshape-step) :use sshape-step)))

(defthm step-agrees-push
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s)
                (equal (car (nth (car s) (car prog))) :push))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))
(defthm step-agrees-load
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s)
                (equal (car (nth (car s) (car prog))) :load))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))
(defthm step-agrees-add
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s)
                (equal (car (nth (car s) (car prog))) :add))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))
(defthm step-agrees-lt
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s)
                (equal (car (nth (car s) (car prog))) :lt))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))
(defthm step-agrees-slide
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s)
                (equal (car (nth (car s) (car prog))) :slide))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))
(defthm step-agrees-jmpf
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s)
                (equal (car (nth (car s) (car prog))) :jmpf))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))
(defthm step-agrees-jmp
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s)
                (equal (car (nth (car s) (car prog))) :jmp))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))
(defthm step-agrees-mkclo
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s)
                (equal (car (nth (car s) (car prog))) :mkclo))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))
(defthm step-agrees-capt
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s)
                (equal (car (nth (car s) (car prog))) :capt))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))
(defthm step-agrees-callv
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s)
                (equal (car (nth (car s) (car prog))) :callv))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))
(defthm step-agrees-ret
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s)
                (equal (car (nth (car s) (car prog))) :ret))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (e/d (vcs-step reads-ok) (update-nth)))))
(defthm step-agrees-other
  (implies (and (srel s u) (sshape s) (sshape u)
                (not (member-equal (car (nth (car s) (car prog))) '(:push :load :add :lt :slide :jmpf :jmp :mkclo :capt :callv :ret))))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (enable vcs-step reads-ok))))

(in-theory (disable srel sshape))

(defthm step-agrees
  (implies (and (srel s u) (sshape s) (sshape u) (reads-ok prog s))
           (srel (vcs-step prog s) (vcs-step prog u)))
  :hints (("Goal" :in-theory (disable reads-ok)
                  :cases ((member-equal (car (nth (car s) (car prog))) '(:push :load :add :lt :slide :jmpf :jmp :mkclo :capt :callv :ret))))))

(defthm srel-wstep
  (implies (srel s (vcs-step prog u)) (srel s (wstep prog u)))
  :hints (("Goal" :in-theory (e/d (srel) (cagree-trans cagree-sym cagree-swipe))
                  :use ((:instance cagree-trans (a (cadddr s)) (b (cadddr (vcs-step prog u)))
                                   (c (swipe (nfix (caddr (vcs-step prog u))) (cadddr (vcs-step prog u))))
                                   (h (nfix (caddr s))))
                        (:instance cagree-sym (b (cadddr (vcs-step prog u)))
                                   (a (swipe (nfix (caddr (vcs-step prog u))) (cadddr (vcs-step prog u))))
                                   (h (nfix (caddr s))))
                        (:instance cagree-swipe (h (nfix (caddr (vcs-step prog u)))) (stk (cadddr (vcs-step prog u))))))))

(defun wr-ind (prog s u n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) (list s u) (wr-ind prog (vcs-step prog s) (wstep prog u) (1- n))))

; THE WIPE CHANGES NOTHING: a run that never reads above its top, and the
; same run wiped after every step, stay alike in everything but the
; dead slots
(defthm wiped-run-agrees
  (implies (and (srel s u) (sshape s) (sshape u) (run-reads-ok prog s n))
           (srel (vcs-run prog s n) (vcs-run-wiping prog u n)))
  :hints (("Goal" :in-theory (e/d (vcs-run run-reads-ok) (srel wstep vcs-step reads-ok))
                  :induct (wr-ind prog s u n))))

; ---- A COMPILED PROGRAM NEVER READS ABOVE ITS TOP --------------------------------

; a halted machine repeats its :ret, which reads its one value
(defthm shalted-reads
  (implies (and (sstatep s) (equal (cadr s) 0) (equal (caddr s) 1) (not (consp (s-ctl s)))
                (ccode-at (car prog) (car s) (list (list :ret))))
           (run-reads-ok prog s k))
  :hints (("Goal" :induct (vcs-run prog s k)
                  :in-theory (enable vcs-run run-reads-ok reads-ok)
                  :expand ((run-reads-ok prog s k)))))

(defthm vcs-program-reads
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k))
           (run-reads-ok (vcs-program e defs) (list 0 0 0 nil nil) (+ (sclk e nil nil defs fuel) k)))
  :hints (("Goal" :in-theory (disable sgood vcs-good shalted-stays shalted-reads vcs-program vcs-program-fns-ok
                                      run-reads-ok-plus)
                  :use ((:instance vcs-program-fns-ok)
                        (:instance run-reads-ok-plus (prog (vcs-program e defs)) (s (list 0 0 0 nil nil))
                                   (a (sclk e nil nil defs fuel)) (b k))
                        (:instance vcs-good (depth 0) (cenv nil) (self nil) (caps nil) (s (list 0 0 0 nil nil)) (env nil)
                                   (prog (vcs-program e defs)))
                        (:instance (:definition sgood) (depth 0) (cenv nil) (self nil) (caps nil)
                                   (s (list 0 0 0 nil nil)) (env nil) (prog (vcs-program e defs)))
                        (:instance shalted-reads (prog (vcs-program e defs))
                                   (s (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) (sclk e nil nil defs fuel))))
                        (:instance ccode-at-shift (pc 0)
                                   (a (vcs-compile e 0 nil nil 0))
                                   (b (cons '(:ret) (car (vcs-defs defs (len (sv-main))))))
                                   (c '((:ret))))))
          ("Goal'" :in-theory (enable vcs-program))))

; ---- ROOTED ------------------------------------------------------------------------

(defthm srel-refl
  (implies (sshape s) (srel s s))
  :hints (("Goal" :in-theory (enable srel))))

(defthm srel-answer
  (implies (and (srel s u) (<= 1 (nfix (caddr s))))
           (equal (vcs-answer u) (vcs-answer s)))
  :hints (("Goal" :in-theory (enable srel)
                  :use ((:instance cagree-nth (a (cadddr s)) (b (cadddr u)) (r 0) (h (nfix (caddr s))))))))

(defthm vcs-run-sshape
  (implies (sshape s) (sshape (vcs-run prog s n)))
  :hints (("Goal" :induct (vcs-run prog s n) :in-theory (enable vcs-run))))

; the machine stops with one value on its stack
(defthm vcs-final-top
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k))
           (equal (caddr (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) (+ (sclk e nil nil defs fuel) k))) 1))
  :hints (("Goal" :in-theory (disable sgood vcs-good shalted-stays vcs-program vcs-program-fns-ok vcs-run-plus)
                  :use ((:instance vcs-program-fns-ok)
                        (:instance vcs-run-plus (prog (vcs-program e defs)) (s (list 0 0 0 nil nil))
                                   (a (sclk e nil nil defs fuel)) (b k))
                        (:instance vcs-good (depth 0) (cenv nil) (self nil) (caps nil) (s (list 0 0 0 nil nil)) (env nil)
                                   (prog (vcs-program e defs)))
                        (:instance (:definition sgood) (depth 0) (cenv nil) (self nil) (caps nil)
                                   (s (list 0 0 0 nil nil)) (env nil) (prog (vcs-program e defs)))
                        (:instance shalted-stays (prog (vcs-program e defs))
                                   (s (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) (sclk e nil nil defs fuel))))
                        (:instance cagree-nth (r 0) (h 1)
                                   (a (cadddr (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) (sclk e nil nil defs fuel))))
                                   (b (update-nth 0 (cdr (mc e nil nil defs fuel)) nil)))
                        (:instance ccode-at-shift (pc 0)
                                   (a (vcs-compile e 0 nil nil 0))
                                   (b (cons '(:ret) (car (vcs-defs defs (len (sv-main))))))
                                   (c '((:ret))))))
          ("Goal'" :in-theory (enable vcs-program))))

; A COMPILED PROGRAM ON THE WIPING MACHINE answers what its meaning does:
; every slot at or above the stack top is dead at every step
(defthm vcs-rooted
  (implies (and (alistp defs) (cdefs-ok defs) (cwf e 0)
                (valp (mc e nil nil defs fuel)) (natp k))
           (equal (vcs-answer (vcs-run-wiping (vcs-program e defs) (list 0 0 0 nil nil)
                                              (+ (sclk e nil nil defs fuel) k)))
                  (mc e nil nil defs fuel)))
  :hints (("Goal" :in-theory (e/d (sshape vcs-run-program) (vcs-correct vcs-final-top vcs-program-reads wiped-run-agrees
                                                            srel-answer vcs-program vcs-run-wiping vcs-answer))
                  :use ((:instance vcs-correct) (:instance vcs-final-top)
                        (:instance vcs-program-reads)
                        (:instance wiped-run-agrees (prog (vcs-program e defs)) (s (list 0 0 0 nil nil))
                                   (u (list 0 0 0 nil nil)) (n (+ (sclk e nil nil defs fuel) k)))
                        (:instance srel-answer
                                   (s (vcs-run (vcs-program e defs) (list 0 0 0 nil nil) (+ (sclk e nil nil defs fuel) k)))
                                   (u (vcs-run-wiping (vcs-program e defs) (list 0 0 0 nil nil)
                                                      (+ (sclk e nil nil defs fuel) k))))))))
