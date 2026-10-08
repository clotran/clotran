; clotran's VM, formally (PLAN step 30): THE ARRAYS ARE THE LISTS. One
; step of vmi.lisp's machine -- 64-bit registers, fixed-size arrays, the
; nearest handler's index -- read back as vmx2's state, is vcs2-step on
; the program read back from the arrays, unless an array overflowed:
;
;   vmi-step-refines   (vmi-abs (vmi-step vmi)) = vcs2-step (vmi-prog vmi)
;                      (vmi-abs vmi), for a machine in vmi-ok whose step
;                      did not overflow
;   vmi-step-ok        a step keeps vmi-ok, and the program
;
; vmi-ok is what the arrays must keep: the registers natural, the
; control stack's top inside its arrays, the code whole instructions,
; and THE HANDLER CHAIN -- the nearest-handler register is the topmost
; handler record's index, and each handler record links to the next one
; below. That chain is what lets a throw truncate the control stack in
; one step where vmx2's unwind walks it.

(in-package "ACL2")

(include-book "vmi")
(include-book "vmx2-proof")

; ---- THE SHAPE the refinement needs: 19 fields, the stack a list, no
; control record's first field the handler tag. A well-typed stobj has it
; (vmip-shape); keeping vmip itself -- every value 64-bit -- is a separate
; theorem, about overflow, not about meaning.

(defun no-h (l) (if (atom l) t (and (not (equal (car l) :h)) (no-h (cdr l)))))

(defun vmi-shape (vmi)
  (and (true-listp vmi) (equal (len vmi) 19) (true-listp (nth 8 vmi)) (no-h (nth 10 vmi))))

(defthm v-cap-no-h (implies (v-cap x) (no-h x)))

(defthm v-stkp-tl (implies (v-stkp x) (true-listp x)))

(defthm vmip-shape (implies (vmip vmi) (vmi-shape vmi)))

; ---- THE INVARIANT --------------------------------------------------------------------------

; the topmost handler record below i, or -1
(defun hidx-of (i vmi)
  (declare (xargs :stobjs vmi :measure (nfix i) :verify-guards nil))
  (cond ((zp i) -1)
        ((equal (v-ckindi (1- i) vmi) 2) (1- i))
        (t (hidx-of (1- i) vmi))))

; every handler record below i links to the one below it
(defun prevs-ok (i vmi)
  (declare (xargs :stobjs vmi :measure (nfix i) :verify-guards nil))
  (if (zp i)
      t
    (and (implies (equal (v-ckindi (1- i) vmi) 2) (equal (v-cprevi (1- i) vmi) (hidx-of (1- i) vmi)))
         (prevs-ok (1- i) vmi))))

(defun vmi-ok (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (and (natp (v-pc vmi)) (natp (v-fb vmi)) (natp (v-sp vmi)) (natp (v-ctop vmi))
       (member (v-status vmi) (quote (0 1 2)))
       (<= (v-ctop vmi) (v-ckind-length vmi))
       (<= (v-ckind-length vmi) (v-ca-length vmi)) (<= (v-ckind-length vmi) (v-cb-length vmi))
       (<= (v-ckind-length vmi) (v-cc-length vmi)) (<= (v-ckind-length vmi) (v-cprev-length vmi))
       (equal (v-code-length vmi) (* 4 (floor (v-code-length vmi) 4)))
       (equal (v-hidx vmi) (hidx-of (v-ctop vmi) vmi))
       (prevs-ok (v-ctop vmi) vmi)))

; ---- THE STACK: the array's field is the list ---------------------------------------------

(defthm nthcdr-open-nth
  (implies (and (natp i) (< i (len l)))
           (equal (nthcdr i l) (cons (nth i l) (nthcdr (1+ i) l)))))

(defthm nthcdr-past-true-list
  (implies (and (true-listp l) (<= (len l) (nfix i))) (equal (nthcdr i l) nil)))

(defthm vmi-stk-list-is
  (implies (and (true-listp (nth 8 vmi)) (natp i) (equal (+ i k) (len (nth 8 vmi))))
           (equal (vmi-stk-list i k vmi) (nthcdr i (nth 8 vmi))))
  :hints (("Goal" :induct (vmi-stk-list i k vmi))))

(defthm v-stkp-true-listp (implies (v-stkp x) (true-listp x)) :rule-classes :forward-chaining)

(defthm vmi-abs-is
  (implies (true-listp (nth 8 vmi))
           (equal (vmi-abs vmi)
                  (list (if (equal (v-status vmi) 1) :thrown (v-pc vmi)) (v-fb vmi) (v-sp vmi)
                        (nth 8 vmi) (vmi-ctl (nfix (v-ctop vmi)) vmi))))
  :hints (("Goal" :use ((:instance vmi-stk-list-is (i 0) (k (len (nth 8 vmi))))))))

(defthm nth-past-true-list
  (implies (and (true-listp l) (<= (len l) (nfix i))) (equal (nth i l) nil)))

(defthm vmi-sreg-is
  (implies (true-listp (nth 8 vmi)) (equal (vmi-sreg i vmi) (nth (nfix i) (nth 8 vmi)))))

(defthm vmi-stk-from-is
  (implies (true-listp (nth 8 vmi)) (equal (vmi-stk-from a k vmi) (stk-from a k (nth 8 vmi)))))

(in-theory (disable vmi-abs vmi-sreg vmi-stk-from))

(in-theory (disable nthcdr-open-nth))

; ---- WHAT EACH READ-BACK LOOKS AT ----------------------------------------------------------
;
; fields: 0 pc 1 fb 2 sp 3 status 4 ctop 5 hidx 6 code 7 pool 8 stk
; 9 ckind 10 ca 11 cb 12 cc 13 cprev 14 fnfirst 15 fncount 16 cln
; 17 clent 18 clrest

(defthm vmi-ctl-frame
  (implies (not (member k '(9 10 11 12)))
           (equal (vmi-ctl i (update-nth k v vmi)) (vmi-ctl i vmi))))

(defthm hidx-of-frame
  (implies (not (equal k 9)) (equal (hidx-of i (update-nth k v vmi)) (hidx-of i vmi))))

(defthm prevs-ok-frame
  (implies (not (member k '(9 13))) (equal (prevs-ok i (update-nth k v vmi)) (prevs-ok i vmi))))

; the control stack's read-backs as functions of the field lists, so a
; record written at or above i is a fact about lists
(defun ctl-of (i kinds as bs cs)
  (if (zp i)
      nil
    (cons (if (equal (nth (1- i) kinds) 2)
              (list :h (nth (1- i) as) (nth (1- i) bs) (nth (1- i) cs))
            (list (nth (1- i) as) (nth (1- i) bs)))
          (ctl-of (1- i) kinds as bs cs))))

(defun hof (i kinds) (cond ((zp i) -1) ((equal (nth (1- i) kinds) 2) (1- i)) (t (hof (1- i) kinds))))

(defun pok (i kinds prevs)
  (if (zp i)
      t
    (and (implies (equal (nth (1- i) kinds) 2) (equal (nth (1- i) prevs) (hof (1- i) kinds)))
         (pok (1- i) kinds prevs))))

(defthm vmi-ctl-is
  (equal (vmi-ctl i vmi) (ctl-of i (nth 9 vmi) (nth 10 vmi) (nth 11 vmi) (nth 12 vmi))))
(defthm hidx-of-is (equal (hidx-of i vmi) (hof i (nth 9 vmi))))
(defthm prevs-ok-is (equal (prevs-ok i vmi) (pok i (nth 9 vmi) (nth 13 vmi))))
(in-theory (disable vmi-ctl hidx-of prevs-ok))

; a record written at or above i changes nothing below it
(defthm ctl-of-above
  (implies (and (natp j) (<= (nfix i) j))
           (and (equal (ctl-of i (update-nth j x kinds) as bs cs) (ctl-of i kinds as bs cs))
                (equal (ctl-of i kinds (update-nth j x as) bs cs) (ctl-of i kinds as bs cs))
                (equal (ctl-of i kinds as (update-nth j x bs) cs) (ctl-of i kinds as bs cs))
                (equal (ctl-of i kinds as bs (update-nth j x cs)) (ctl-of i kinds as bs cs)))))

(defthm hof-above
  (implies (and (natp j) (<= (nfix i) j)) (equal (hof i (update-nth j x kinds)) (hof i kinds))))

(defthm pok-above
  (implies (and (natp j) (<= (nfix i) j))
           (and (equal (pok i (update-nth j x kinds) prevs) (pok i kinds prevs))
                (equal (pok i kinds (update-nth j x prevs)) (pok i kinds prevs)))))

(defthm vmi-w-frame
  (implies (not (equal k 6)) (equal (vmi-w pc n (update-nth k v vmi)) (vmi-w pc n vmi))))
(defthm vmi-poolv-frame
  (implies (not (equal k 7)) (equal (vmi-poolv i (update-nth k v vmi)) (vmi-poolv i vmi))))
(defthm vmi-ins-frame
  (implies (not (member k '(6 7))) (equal (vmi-ins pc (update-nth k v vmi)) (vmi-ins pc vmi)))
  :hints (("Goal" :in-theory (disable vmi-w vmi-poolv))))
(defthm vmi-code-list-frame
  (implies (not (member k '(6 7))) (equal (vmi-code-list pc n (update-nth k v vmi)) (vmi-code-list pc n vmi)))
  :hints (("Goal" :in-theory (disable vmi-ins))))
(defthm vmi-clauses-frame
  (implies (not (member k '(16 17 18))) (equal (vmi-clauses ci n (update-nth k v vmi)) (vmi-clauses ci n vmi))))
(defthm vmi-fntab-frame
  (implies (not (member k '(14 15 16 17 18))) (equal (vmi-fntab f n (update-nth k v vmi)) (vmi-fntab f n vmi))))
(defthm vmi-prog-frame
  (implies (not (member k '(6 7 14 15 16 17 18))) (equal (vmi-prog (update-nth k v vmi)) (vmi-prog vmi)))
  :hints (("Goal" :in-theory (disable vmi-code-list vmi-fntab))))
(in-theory (disable vmi-w vmi-poolv vmi-ins vmi-code-list vmi-clauses vmi-fntab vmi-prog))

; ---- THE CONTROL STACK: the handler chain is vmx2's hfind ----------------------------------

(defthm v-cap-not-h
  (implies (v-cap x) (not (equal (nth j x) :h))))

(defthm hof-range
  (and (integerp (hof i kinds)) (<= -1 (hof i kinds)) (< (hof i kinds) (nfix i))
       (implies (<= 0 (hof i kinds)) (equal (nth (hof i kinds) kinds) 2)))
  :rule-classes ((:rewrite) (:linear :corollary (and (<= -1 (hof i kinds)) (< (hof i kinds) (nfix i))))))

; the nearest handler record, found by vmx2's walk, is the chain's head
(defthm no-h-nth (implies (no-h l) (not (equal (nth j l) :h))))

(defthm hfind-ctl-of
  (implies (no-h as)
           (equal (hfind (ctl-of i kinds as bs cs))
                  (if (< (hof i kinds) 0) nil (ctl-of (1+ (hof i kinds)) kinds as bs cs)))))

(defthm pok-link
  (implies (and (pok i kinds prevs) (natp j) (< j (nfix i)) (equal (nth j kinds) 2))
           (equal (nth j prevs) (hof j kinds)))
  :hints (("Goal" :induct (pok i kinds prevs) :in-theory (disable hof))))

; ---- THE PROGRAM, read back -----------------------------------------------------------------

(defthm vmi-ins-past-code
  (implies (and (natp pc) (<= (v-code-length vmi) (* 4 pc))) (equal (vmi-ins pc vmi) nil))
  :hints (("Goal" :in-theory (enable vmi-ins vmi-w))))

(defun ncl-ind (pc i k)
  (if (or (zp k) (zp pc)) (list pc i k) (ncl-ind (1- pc) (1+ i) (1- k))))

(defthm nth-vmi-code-list
  (implies (and (natp pc) (natp i))
           (equal (nth pc (vmi-code-list i k vmi)) (if (< pc (nfix k)) (vmi-ins (+ i pc) vmi) nil)))
  :hints (("Goal" :in-theory (enable vmi-code-list) :induct (ncl-ind pc i k)
                  :expand ((vmi-code-list i k vmi)))))

; THE INSTRUCTION AT pc, in vmx2's program, is the one the words decode to
(defthm vmi-prog-ins
  (implies (and (natp pc) (equal (v-code-length vmi) (* 4 (floor (v-code-length vmi) 4))))
           (equal (nth pc (car (vmi-prog vmi))) (vmi-ins pc vmi)))
  :hints (("Goal" :in-theory (enable vmi-prog) :cases ((< pc (floor (v-code-length vmi) 4))))))

(defun vmi-clause (x vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (equal (v-clresti x vmi) 1)
      (list (v-clni x vmi) (v-clenti x vmi) :rest)
    (list (v-clni x vmi) (v-clenti x vmi))))

(defthm vmi-clause-parts
  (and (consp (vmi-clause x vmi))
       (equal (car (vmi-clause x vmi)) (nth x (nth 16 vmi)))
       (equal (cadr (vmi-clause x vmi)) (nth x (nth 17 vmi)))
       (equal (caddr (vmi-clause x vmi)) (if (equal (nth x (nth 18 vmi)) 1) :rest nil))
       (equal (restp (vmi-clause x vmi)) (equal (nth x (nth 18 vmi)) 1))))
(in-theory (disable vmi-clause))

(defthm vmi-clauses-open
  (equal (vmi-clauses ci k vmi)
         (if (zp k) nil (cons (vmi-clause (nfix ci) vmi) (vmi-clauses (1+ (nfix ci)) (1- k) vmi))))
  :rule-classes ((:definition :controller-alist ((vmi-clauses nil t nil))))
  :hints (("Goal" :in-theory (enable vmi-clause) :expand ((vmi-clauses ci k vmi)))))

(defthm assoc-vmi-fntab
  (implies (natp f0)
           (equal (cdr (assoc-equal g (vmi-fntab f0 k vmi)))
                  (if (and (natp g) (<= f0 g) (< g (+ f0 (nfix k))))
                      (vmi-clauses (nth g (nth 14 vmi)) (nth g (nth 15 vmi)) vmi)
                    nil)))
  :hints (("Goal" :in-theory (enable vmi-fntab) :induct (vmi-fntab f0 k vmi))))

; a function's clauses, by id: none for anything not an id
(defthm vmi-prog-clauses
  (equal (cdr (assoc-equal g (cdr (vmi-prog vmi))))
         (if (and (natp g) (< g (v-fnfirst-length vmi)))
             (vmi-clauses (nth g (nth 14 vmi)) (nth g (nth 15 vmi)) vmi)
           nil))
  :hints (("Goal" :in-theory (enable vmi-prog))))

(defthm pick-fixed-vmi
  (implies (natp m)
           (equal (pick-fixed (vmi-clauses ci k vmi) m)
                  (if (< (vmi-pick-fixed ci k m vmi) 0) nil (vmi-clause (vmi-pick-fixed ci k m vmi) vmi))))
  :hints (("Goal" :induct (vmi-pick-fixed ci k m vmi) :in-theory (disable restp nth)
                  :expand ((vmi-clauses ci k vmi) (vmi-pick-fixed ci k m vmi)))))

(defthm pick-rest-vmi
  (implies (natp m)
           (equal (pick-rest (vmi-clauses ci k vmi) m)
                  (if (< (vmi-pick-rest ci k m vmi) 0) nil (vmi-clause (vmi-pick-rest ci k m vmi) vmi))))
  :hints (("Goal" :induct (vmi-pick-rest ci k m vmi) :in-theory (disable restp nth)
                  :expand ((vmi-clauses ci k vmi) (vmi-pick-rest ci k m vmi)))))

(defthm vmi-pick-fixed-range
  (and (integerp (vmi-pick-fixed ci k m vmi)) (<= -1 (vmi-pick-fixed ci k m vmi)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (integerp (vmi-pick-fixed ci k m vmi))))
  :hints (("Goal" :induct (vmi-pick-fixed ci k m vmi) :in-theory (disable nth))))
(defthm vmi-pick-rest-range
  (and (integerp (vmi-pick-rest ci k m vmi)) (<= -1 (vmi-pick-rest ci k m vmi)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (integerp (vmi-pick-rest ci k m vmi))))
  :hints (("Goal" :induct (vmi-pick-rest ci k m vmi) :in-theory (disable nth))))

; THE CLAUSE A CALL TAKES is the one vmx2's pick-arity takes
(defthm pick-arity-vmi
  (implies (natp m)
           (equal (pick-arity (cdr (assoc-equal g (cdr (vmi-prog vmi)))) m)
                  (if (< (vmi-pick g m vmi) 0) nil (vmi-clause (vmi-pick g m vmi) vmi))))
  :hints (("Goal" :in-theory (e/d (pick-arity) (vmi-clause vmi-clauses-open)))))

; ---- ONE INSTRUCTION AT A TIME ---------------------------------------------------------------
;
; for each opcode: a running machine at an instruction of it, whose step
; did not overflow, steps as vcs2-step does

(defthm vmi-sset-is
  (equal (vmi-sset i v vmi)
         (if (< (nfix i) (len (nth 8 vmi)))
             (update-nth 8 (update-nth (nfix i) v (nth 8 vmi)) vmi)
           (update-nth 3 2 vmi))))
(in-theory (disable vmi-sset))

(defthm len-update-nth-in
  (implies (< (nfix i) (len l)) (equal (len (update-nth i v l)) (len l))))

(defthm true-listp-update-nth-tl
  (implies (true-listp l) (true-listp (update-nth i v l))))

(defmacro vmi-at (k)
  `(and (vmi-shape vmi) (vmi-ok vmi) (equal (v-status vmi) 0) (equal (vmi-w (v-pc vmi) 0 vmi) ,k)))

(defmacro vmi-thy ()
  '(set-difference-theories (union-theories '(vcs2-step vcsx-step vcs-step sreg ssetreg vmi-ins)
                                          (current-theory :here))
                           '(nth update-nth)))

(defmacro def-refines (name f k &rest hints)
  `(defthm ,name
     (implies (and (vmi-at ,k) (not (equal (v-status (,f vmi)) 2)))
              (equal (vmi-abs (,f vmi)) (vcs2-step (vmi-prog vmi) (vmi-abs vmi))))
     :hints (("Goal" :in-theory (union-theories '(,f) (vmi-thy)) ,@hints))))

(def-refines vmi-push-refines vmi-push 1)
(def-refines vmi-load-refines vmi-load 2)
(def-refines vmi-add-refines vmi-add 3)
(def-refines vmi-lt-refines vmi-lt 4)
(def-refines vmi-slide-refines vmi-slide 5)
(def-refines vmi-jmpf-refines vmi-jmpf 6)
(def-refines vmi-jmp-refines vmi-jmp 7)
(def-refines vmi-mkclo-refines vmi-mkclo 8)
(def-refines vmi-capt-refines vmi-capt 9)

; ---- A THROW: the chain's head, in one step, is vmx2's unwind ------------------------------

(defthm vmi-unwind-refines
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (equal (v-status vmi) 0) (not (equal (v-status (vmi-unwind v vmi)) 2)))
           (equal (vmi-abs (vmi-unwind v vmi)) (unwind v (vmi-ctl (v-ctop vmi) vmi) (nth 8 vmi))))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories '(vmi-unwind unwind-is) (current-theory :here))
                                                      '(nth update-nth hof))
                  :use ((:instance hof-range (i (v-ctop vmi)) (kinds (nth 9 vmi)))))))

(in-theory (disable vmi-unwind))

; ---- THE CONTROL STACK'S PUSH AND POP -------------------------------------------------------

; a push writes the record at the top, links a handler to the one below
; it, and raises the top -- or overflows
(defthm vmi-push-rec-fields
  (let ((p (vmi-push-rec kind a b c vmi)) (j (nfix (v-ctop vmi))) (ok (< (nfix (v-ctop vmi)) (len (nth 9 vmi)))))
    (and (implies (member k '(0 1 2 6 7 8 14 15 16 17 18)) (equal (nth k p) (nth k vmi)))
         (equal (nth 3 p) (if ok (nth 3 vmi) 2))
         (equal (nth 4 p) (if ok (1+ j) (nth 4 vmi)))
         (equal (nth 5 p) (if (and ok (equal kind 2)) j (nth 5 vmi)))
         (equal (nth 9 p) (if ok (update-nth j kind (nth 9 vmi)) (nth 9 vmi)))
         (equal (nth 10 p) (if ok (update-nth j a (nth 10 vmi)) (nth 10 vmi)))
         (equal (nth 11 p) (if ok (update-nth j b (nth 11 vmi)) (nth 11 vmi)))
         (equal (nth 12 p) (if ok (update-nth j c (nth 12 vmi)) (nth 12 vmi)))
         (equal (nth 13 p) (if ok (update-nth j (nth 5 vmi) (nth 13 vmi)) (nth 13 vmi)))
         (equal (vmi-prog p) (vmi-prog vmi))
         (implies (< 18 (len vmi)) (equal (len p) (len vmi)))
         (implies (true-listp vmi) (true-listp p))))
  :hints (("Goal" :in-theory (disable nth update-nth))))

; a pop lowers the top, a handler's link becoming the nearest
(defthm vmi-pop-rec-fields
  (let ((p (vmi-pop-rec vmi)) (i (nfix (v-ctop vmi))))
    (and (implies (not (member k '(4 5))) (equal (nth k p) (nth k vmi)))
         (equal (nth 4 p) (if (zp i) (nth 4 vmi) (1- i)))
         (equal (nth 5 p) (if (and (not (zp i)) (equal (nth (1- i) (nth 9 vmi)) 2)) (nth (1- i) (nth 13 vmi)) (nth 5 vmi)))
         (equal (vmi-prog p) (vmi-prog vmi))
         (implies (< 18 (len vmi)) (equal (len p) (len vmi)))
         (implies (true-listp vmi) (true-listp p))))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm true-listp-push-pop
  (and (equal (true-listp (nth 8 (vmi-push-rec kind a b c vmi))) (true-listp (nth 8 vmi)))
       (equal (true-listp (nth 8 (vmi-pop-rec vmi))) (true-listp (nth 8 vmi)))))

(in-theory (disable vmi-push-rec vmi-pop-rec))

; ---- RECUR'S COPY -------------------------------------------------------------------------------

(defthm true-listp-copy-down
  (implies (true-listp l) (true-listp (copy-down src dst k l))))

(defthm vmi-copy-down-sticky
  (implies (equal (nth 3 vmi) 2) (equal (nth 3 (vmi-copy-down src dst k vmi)) 2))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm update-nth-nth-same
  (implies (< (nfix n) (len x)) (equal (update-nth n (nth n x) x) x)))

(defthm vmi-copy-down-is
  (implies (and (true-listp (nth 8 vmi)) (< 8 (len vmi)) (not (equal (nth 3 (vmi-copy-down src dst k vmi)) 2)))
           (equal (vmi-copy-down src dst k vmi) (update-nth 8 (copy-down src dst k (nth 8 vmi)) vmi)))
  :hints (("Goal" :induct (vmi-copy-down src dst k vmi) :in-theory (disable nth update-nth))))

(in-theory (disable vmi-copy-down))

; ---- THE REST OF THE INSTRUCTIONS -----------------------------------------------------------

; the call, one path at a time
(defmacro c-m () '(nfix (vmi-w (v-pc vmi) 1 vmi)))
(defmacro c-c () '(nth (1- (v-sp vmi)) (nth 8 vmi)))
(defmacro c-ci () '(vmi-pick (clo-f (c-c)) (c-m) vmi))

(defmacro def-refines-if (name f k cond &rest hints)
  `(defthm ,name
     (implies (and (vmi-at ,k) ,cond (not (equal (v-status (,f vmi)) 2)))
              (equal (vmi-abs (,f vmi)) (vcs2-step (vmi-prog vmi) (vmi-abs vmi))))
     :rule-classes nil
     :hints (("Goal" :in-theory (union-theories '(,f) (set-difference-theories (vmi-thy) '(restp))) ,@hints))))

(def-refines-if callv-stuck vmi-callv 10 (< (v-sp vmi) (1+ (c-m))))
(def-refines-if callv-not-fn vmi-callv 10 (and (<= (1+ (c-m)) (v-sp vmi)) (not (clop (c-c)))))
(def-refines-if callv-arity vmi-callv 10 (and (<= (1+ (c-m)) (v-sp vmi)) (clop (c-c)) (< (c-ci) 0)))
(def-refines-if callv-fixed vmi-callv 10
  (and (<= (1+ (c-m)) (v-sp vmi)) (clop (c-c)) (<= 0 (c-ci)) (not (equal (nth (c-ci) (nth 18 vmi)) 1))))
(def-refines-if callv-rest vmi-callv 10
  (and (<= (1+ (c-m)) (v-sp vmi)) (clop (c-c)) (<= 0 (c-ci)) (equal (nth (c-ci) (nth 18 vmi)) 1)))

(defthm vmi-callv-refines
  (implies (and (vmi-at 10) (not (equal (v-status (vmi-callv vmi)) 2)))
           (equal (vmi-abs (vmi-callv vmi)) (vcs2-step (vmi-prog vmi) (vmi-abs vmi))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (callv-stuck callv-not-fn callv-arity callv-fixed callv-rest))))
(def-refines vmi-ret-refines vmi-ret 11)
(def-refines vmi-recur-refines vmi-recur 12)
(def-refines vmi-prim-refines vmi-prim 13)
(def-refines vmi-throw-refines vmi-throw 14)
(def-refines vmi-try-refines vmi-try 15)
(def-refines vmi-endtry-refines vmi-endtry 16)

; ---- ONE STEP ------------------------------------------------------------------------------

; anything else -- an opcode outside 1..16, or past the code -- is stuck
; in both: vmx2 reads no instruction there
(defthm vmi-other-refines
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (equal (v-status vmi) 0)
                (not (member (vmi-w (v-pc vmi) 0 vmi) '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16))))
           (equal (vmi-abs vmi) (vcs2-step (vmi-prog vmi) (vmi-abs vmi))))
  :rule-classes nil
  :hints (("Goal" :in-theory (vmi-thy))))

; a stopped machine stays stopped in both
(defthm vmi-thrown-refines
  (implies (and (vmi-shape vmi) (equal (v-status vmi) 1))
           (equal (vmi-abs vmi) (vcs2-step (vmi-prog vmi) (vmi-abs vmi))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable vcs2-step))))

(defthm vmi-ok-status
  (implies (vmi-ok vmi) (or (equal (v-status vmi) 0) (equal (v-status vmi) 1) (equal (v-status vmi) 2)))
  :rule-classes nil)

; ONE STEP OF THE ARRAYS IS ONE STEP OF VMX2's MACHINE, unless an array
; overflowed
(defthm vmi-step-refines
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (not (equal (v-status (vmi-step vmi)) 2)))
           (equal (vmi-abs (vmi-step vmi)) (vcs2-step (vmi-prog vmi) (vmi-abs vmi))))
  :hints (("Goal" :in-theory (union-theories '(vmi-step member-equal
                                               vmi-push-refines vmi-load-refines vmi-add-refines vmi-lt-refines
                                               vmi-slide-refines vmi-jmpf-refines vmi-jmp-refines vmi-mkclo-refines
                                               vmi-capt-refines vmi-callv-refines vmi-ret-refines vmi-recur-refines
                                               vmi-prim-refines vmi-throw-refines vmi-try-refines vmi-endtry-refines)
                                             (theory 'minimal-theory))
                  :use (vmi-ok-status vmi-other-refines vmi-thrown-refines))))

; ---- A STEP KEEPS THE INVARIANT, AND THE PROGRAM -----------------------------------------------

(defthm pok-smaller
  (implies (and (pok i kinds prevs) (natp j) (<= j (nfix i))) (pok j kinds prevs))
  :hints (("Goal" :induct (pok i kinds prevs) :in-theory (disable hof))))

(defthm no-h-update-nth
  (implies (and (no-h l) (not (equal x :h))) (no-h (update-nth j x l))))

(defthm len-update-nth-same
  (implies (< (nfix j) (len l)) (equal (len (update-nth j x l)) (len l))))

(defmacro keeps (fv)
  `(and (vmi-shape ,fv) (vmi-ok ,fv) (equal (vmi-prog ,fv) (vmi-prog vmi))))

(defthm vmi-unwind-keeps
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (not (equal (v-status (vmi-unwind v vmi)) 2)))
           (keeps (vmi-unwind v vmi)))
  :hints (("Goal" :in-theory (set-difference-theories (union-theories '(vmi-unwind) (current-theory :here))
                                                      '(nth update-nth hof))
                  :use ((:instance hof-range (i (v-ctop vmi)) (kinds (nth 9 vmi)))
                        (:instance pok-link (i (v-ctop vmi)) (j (v-hidx vmi)) (kinds (nth 9 vmi)) (prevs (nth 13 vmi)))))))

(defthm vmi-push-rec-keeps
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (not (equal (v-status (vmi-push-rec kind a b c vmi)) 2))
                (member kind '(1 2)) (natp a) (natp b) (natp c))
           (keeps (vmi-push-rec kind a b c vmi)))
  :hints (("Goal" :in-theory (e/d (vmi-push-rec) (nth update-nth))
                  :expand ((hof (+ 1 (nth 4 vmi)) (update-nth (nth 4 vmi) kind (nth 9 vmi)))
                           (pok (+ 1 (nth 4 vmi)) (update-nth (nth 4 vmi) kind (nth 9 vmi))
                                (update-nth (nth 4 vmi) (nth 5 vmi) (nth 13 vmi)))))))

(defthm vmi-pop-rec-keeps
  (implies (and (vmi-shape vmi) (vmi-ok vmi)) (keeps (vmi-pop-rec vmi)))
  :hints (("Goal" :in-theory (e/d (vmi-pop-rec) (nth update-nth))
                  :expand ((hof (nth 4 vmi) (nth 9 vmi)) (pok (nth 4 vmi) (nth 9 vmi) (nth 13 vmi)))
                  :use ((:instance pok-link (i (v-ctop vmi)) (j (1- (v-ctop vmi))) (kinds (nth 9 vmi)) (prevs (nth 13 vmi)))))))

(defmacro def-keeps (name f k)
  `(defthm ,name
     (implies (and (vmi-at ,k) (not (equal (v-status (,f vmi)) 2))) (keeps (,f vmi)))
     :hints (("Goal" :in-theory (union-theories '(,f) (vmi-thy))))))

(def-keeps vmi-push-keeps vmi-push 1)
(def-keeps vmi-load-keeps vmi-load 2)
(def-keeps vmi-add-keeps vmi-add 3)
(def-keeps vmi-lt-keeps vmi-lt 4)
(def-keeps vmi-slide-keeps vmi-slide 5)
(def-keeps vmi-jmpf-keeps vmi-jmpf 6)
(def-keeps vmi-jmp-keeps vmi-jmp 7)
(def-keeps vmi-mkclo-keeps vmi-mkclo 8)
(def-keeps vmi-capt-keeps vmi-capt 9)
(def-keeps vmi-callv-keeps vmi-callv 10)
(def-keeps vmi-ret-keeps vmi-ret 11)
(def-keeps vmi-recur-keeps vmi-recur 12)
(def-keeps vmi-prim-keeps vmi-prim 13)
(def-keeps vmi-throw-keeps vmi-throw 14)
(def-keeps vmi-try-keeps vmi-try 15)
(def-keeps vmi-endtry-keeps vmi-endtry 16)

(defthm vmi-step-keeps
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (not (equal (v-status (vmi-step vmi)) 2)))
           (keeps (vmi-step vmi)))
  :hints (("Goal" :in-theory (union-theories '(vmi-step member-equal
                                               vmi-push-keeps vmi-load-keeps vmi-add-keeps vmi-lt-keeps
                                               vmi-slide-keeps vmi-jmpf-keeps vmi-jmp-keeps vmi-mkclo-keeps
                                               vmi-capt-keeps vmi-callv-keeps vmi-ret-keeps vmi-recur-keeps
                                               vmi-prim-keeps vmi-throw-keeps vmi-try-keeps vmi-endtry-keeps)
                                             (theory 'minimal-theory)))))

; ---- RUNS --------------------------------------------------------------------------------------

(defthm vmi-step-stopped (implies (not (equal (v-status vmi) 0)) (equal (vmi-step vmi) vmi)))

(defthm vmi-run-overflowed (implies (equal (v-status vmi) 2) (equal (vmi-run n vmi) vmi)))

; RUNNING THE ARRAYS IS RUNNING VMX2's MACHINE, step for step, unless an
; array overflowed on the way
(defthm vmi-run-refines
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (not (equal (v-status (vmi-run n vmi)) 2)))
           (and (equal (vmi-abs (vmi-run n vmi)) (vcs2-run (vmi-prog vmi) (vmi-abs vmi) n))
                (keeps (vmi-run n vmi))))
  :hints (("Goal" :induct (vmi-run n vmi)
                  :in-theory (disable vmi-step vmi-abs-is vmi-ok vmi-shape vmi-prog)
                  :expand ((vcs2-run (vmi-prog vmi) (vmi-abs vmi) n)))
          ("Subgoal *1/2" :cases ((equal (v-status (vmi-step vmi)) 2)))))

; ---- VMX2's THEOREM FROM A STACK OF ANYTHING -------------------------------------------------
;
; vcs2-correct starts on an empty stack; the arrays start on a stack of
; nils. Nothing below the top is ever read before it is written, so
; any starting stack will do.

(defthm vcs2-start-hyps-stk
  (implies (and (x2defs-ok defs) (x2wf e 0 nil))
           (s2-hyps e 0 nil nil nil (list 0 0 0 stk nil) nil defs (s2c-prog) nil))
  :hints (("Goal" :in-theory (disable vcs2-compile vcs2-defs)
                  :use ((:instance vcs2-program-fns-ok)
                        (:instance ccode-at-shift (pc 0) (a (vcs2-compile e 0 nil nil 0 nil))
                                   (b (cons '(:ret) (car (vcs2-defs defs (len (s2v-main))))))
                                   (c (vcs2-compile e 0 nil nil 0 nil))))
                  :expand ((vcs2-program e defs)))))

(defmacro s2c-end-stk () '(vcs2-run (vcs2-program e defs) (list 0 0 0 stk nil) (s2clk e nil nil defs fuel)))

(defthm vcs2-correct-stk
  (implies (and (x2defs-ok defs) (x2wf e 0 nil)
                (or (valp (mx2 e nil nil defs fuel)) (thrownp (mx2 e nil nil defs fuel))) (natp k))
           (equal (vcs2-answer (vcs2-run (vcs2-program e defs) (list 0 0 0 stk nil) (+ (s2clk e nil nil defs fuel) k)))
                  (mx2 e nil nil defs fuel)))
  :hints (("Goal" :in-theory (disable s2good vcs2-good s2halted-stays vcs2-program vcs2-program-fns-ok vcs2-run-plus
                                      s2-val s2-thr s2-rec s2-hyps vcs2-start-hyps-stk thrown-at)
                  :use ((:instance vcs2-start-hyps-stk)
                        (:instance vcs2-run-plus (prog (s2c-prog)) (s (list 0 0 0 stk nil)) (a (s2clk e nil nil defs fuel)) (b k))
                        (:instance vcs2-good (depth 0) (cenv nil) (self nil) (caps nil) (s (list 0 0 0 stk nil)) (env nil)
                                   (prog (s2c-prog)) (lc nil))
                        (:instance (:definition s2good) (depth 0) (cenv nil) (self nil) (caps nil)
                                   (s (list 0 0 0 stk nil)) (env nil) (prog (s2c-prog)) (lc nil))
                        (:instance (:definition s2-val) (s (list 0 0 0 stk nil)) (r (mx2 e nil nil defs fuel)) (s2 (s2c-end-stk)))
                        (:instance (:definition s2-thr) (s (list 0 0 0 stk nil)) (r (mx2 e nil nil defs fuel)) (s2 (s2c-end-stk)))
                        (:instance (:definition thrown-at) (s (list 0 0 0 stk nil)) (v (cdr (mx2 e nil nil defs fuel)))
                                   (s2 (s2c-end-stk)))
                        (:instance s2halted-stays (prog (s2c-prog)) (s (s2c-end-stk)))
                        (:instance s2thrown-stays (prog (s2c-prog)) (s (s2c-end-stk)))
                        (:instance cagree-nth (r 0) (h 1) (a (cadddr (s2c-end-stk)))
                                   (b (update-nth 0 (cdr (mx2 e nil nil defs fuel)) stk)))
                        (:instance ccode-at-shift (pc 0)
                                   (a (vcs2-compile e 0 nil nil 0 nil))
                                   (b (cons '(:ret) (car (vcs2-defs defs (len (s2v-main))))))
                                   (c '((:ret))))))
          ("Goal'" :in-theory (enable vcs2-program))))

; ---- THE ENCODER: what goes into the arrays reads back as the program --------------------------

(defthm enc-code-frame
  (implies (not (member k '(6 7))) (equal (nth k (enc-code code pc vmi)) (nth k vmi)))
  :hints (("Goal" :in-theory (disable nth update-nth enc-words))))

(defmacro enc-room (pc code)
  `(and (<= (* 4 (+ ,pc (len ,code))) (len (nth 6 vmi))) (<= (+ ,pc (len ,code)) (len (nth 7 vmi)))))

(defthm enc-code-lens
  (implies (and (natp pc) (enc-room pc code))
           (and (equal (len (nth 6 (enc-code code pc vmi))) (len (nth 6 vmi)))
                (equal (len (nth 7 (enc-code code pc vmi))) (len (nth 7 vmi)))))
  :hints (("Goal" :in-theory (disable nth update-nth enc-words))))

(defthm enc-code-below
  (implies (and (natp pc) (natp j))
           (and (implies (< j (* 4 pc)) (equal (nth j (nth 6 (enc-code code pc vmi))) (nth j (nth 6 vmi))))
                (implies (< j pc) (equal (nth j (nth 7 (enc-code code pc vmi))) (nth j (nth 7 vmi))))))
  :hints (("Goal" :in-theory (disable nth update-nth enc-words))))

; the words and the pool slot, decoded as vmi-ins decodes them
(defun dec-words (w c)
  (let ((a (nth 1 w)) (b (nth 2 w)) (d (nth 3 w)))
    (case (nth 0 w)
      (1 (list :push c)) (2 (list :load a)) (3 (list :add)) (4 (list :lt)) (5 (list :slide))
      (6 (list :jmpf a)) (7 (list :jmp a)) (8 (list :mkclo a b)) (9 (list :capt a b)) (10 (list :callv a))
      (11 (list :ret)) (12 (list :recur a b d)) (13 (list :prim c b)) (14 (list :throw))
      (15 (list :try a b)) (16 (list :endtry))
      (otherwise nil))))

(defun enc-const (ins) (case (car ins) (:push (cadr ins)) (:prim (cadr ins)) (otherwise nil)))

; an instruction's own round trip: nothing about arrays
(defthm dec-enc-words
  (implies (enc-ok-ins ins) (equal (dec-words (enc-words ins pc) (enc-const ins)) ins))
  :hints (("Goal" :in-theory (enable op-of small-natp))))

(defthm enc-words-parts
  (and (equal (nth 0 (enc-words ins pc)) (op-of (car ins)))
       (implies (member (op-of (car ins)) '(1 13)) (equal (nth 1 (enc-words ins pc)) pc))
       (equal (enc-const ins) (if (member (op-of (car ins)) '(1 13)) (cadr ins) nil))))

(defmacro v1 (ins)
  `(update-nth 7 (update-nth pc (enc-const ,ins) c7)
               (update-nth 6 (update-nth (+ 3 (* 4 pc)) (nth 3 (enc-words ,ins pc))
                                         (update-nth (+ 2 (* 4 pc)) (nth 2 (enc-words ,ins pc))
                                                     (update-nth (+ 1 (* 4 pc)) (nth 1 (enc-words ,ins pc))
                                                                 (update-nth (* 4 pc) (nth 0 (enc-words ,ins pc)) c6))))
                           vmi)))

; the arrays' four words and pool slot, read back, are the list written
(defthm vmi-ins-written
  (implies (and (natp pc) (< (+ 3 (* 4 pc)) (len c6)) (< pc (len c7)))
           (equal (vmi-ins pc (v1 ins)) (dec-words (enc-words ins pc) (enc-const ins))))
  :hints (("Goal" :in-theory (e/d (vmi-ins vmi-w vmi-poolv) (nth update-nth enc-words enc-const op-of))
                  :do-not-induct t :cases ((member (op-of (car ins)) '(1 13))))))

(defthm enc-one-ins
  (implies (and (enc-ok-ins ins) (natp pc) (< (+ 3 (* 4 pc)) (len c6)) (< pc (len c7)))
           (equal (vmi-ins pc (v1 ins)) ins))
  :hints (("Goal" :in-theory (disable vmi-ins-written dec-words enc-words enc-const nth update-nth)
                  :use (vmi-ins-written dec-enc-words))))

; the encoder's step for one instruction, named
(defun enc-one (ins pc vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((w (enc-words ins pc))
         (vmi (update-v-codei (* 4 pc) (nth 0 w) vmi))
         (vmi (update-v-codei (+ 1 (* 4 pc)) (nth 1 w) vmi))
         (vmi (update-v-codei (+ 2 (* 4 pc)) (nth 2 w) vmi))
         (vmi (update-v-codei (+ 3 (* 4 pc)) (nth 3 w) vmi)))
    (update-v-pooli pc (case (car ins) (:push (cadr ins)) (:prim (cadr ins)) (otherwise nil)) vmi)))

(defthm enc-code-open
  (equal (enc-code code pc vmi) (if (atom code) vmi (enc-code (cdr code) (1+ pc) (enc-one (car code) pc vmi))))
  :rule-classes ((:definition :controller-alist ((enc-code t nil nil))))
  :hints (("Goal" :expand ((enc-code code pc vmi)) :in-theory (disable enc-words))))

(defthm update-nth-update-nth-same
  (equal (update-nth k a (update-nth k b x)) (update-nth k a x)))

(defthm enc-one-is-v1
  (equal (enc-one ins pc vmi)
         (let ((c6 (nth 6 vmi)) (c7 (nth 7 vmi))) (v1 ins)))
  :hints (("Goal" :in-theory (disable nth enc-words enc-const))))

(defthm enc-one-decodes
  (implies (and (enc-ok-ins ins) (natp pc) (< (+ 3 (* 4 pc)) (len (nth 6 vmi))) (< pc (len (nth 7 vmi))))
           (equal (vmi-ins pc (enc-one ins pc vmi)) ins))
  :hints (("Goal" :in-theory (disable enc-one enc-words enc-const vmi-ins nth update-nth)
                  :use ((:instance enc-one-ins (c6 (nth 6 vmi)) (c7 (nth 7 vmi)))))))

(defthm enc-one-fields
  (implies (and (natp pc) (< (+ 3 (* 4 pc)) (len (nth 6 vmi))) (< pc (len (nth 7 vmi))))
           (and (implies (not (member k '(6 7))) (equal (nth k (enc-one ins pc vmi)) (nth k vmi)))
                (equal (len (nth 6 (enc-one ins pc vmi))) (len (nth 6 vmi)))
                (equal (len (nth 7 (enc-one ins pc vmi))) (len (nth 7 vmi)))))
  :hints (("Goal" :in-theory (disable enc-one nth update-nth enc-words enc-const))))

; encoding instructions from pc on leaves an earlier one as it was
(defthm enc-code-ins-below
  (implies (and (natp pc) (natp j) (< j pc) (enc-room pc code)
                (or (not (member (nth (* 4 j) (nth 6 vmi)) (quote (1 13)))) (< (nfix (nth (+ 1 (* 4 j)) (nth 6 vmi))) pc)))
           (equal (vmi-ins j (enc-code code pc vmi)) (vmi-ins j vmi)))
  :hints (("Goal" :in-theory (e/d (vmi-ins vmi-w vmi-poolv) (enc-code-open nth update-nth))
                  :do-not-induct t)))

(defthm enc-one-words
  (implies (and (natp pc) (< (+ 3 (* 4 pc)) (len (nth 6 vmi))))
           (and (equal (nth (* 4 pc) (nth 6 (enc-one ins pc vmi))) (op-of (car ins)))
                (implies (member (op-of (car ins)) '(1 13))
                         (equal (nth (+ 1 (* 4 pc)) (nth 6 (enc-one ins pc vmi))) pc))))
  :hints (("Goal" :in-theory (disable enc-one nth update-nth enc-words enc-const op-of))))

(in-theory (disable enc-one enc-code enc-one-is-v1))

(defun enc-ind (code pc vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (if (atom code) vmi (let ((vmi (enc-one (car code) pc vmi))) (enc-ind (cdr code) (1+ pc) vmi))))

(defthm enc-code-decodes
  (implies (and (enc-ok-code code) (natp pc) (enc-room pc code))
           (equal (vmi-code-list pc (len code) (enc-code code pc vmi)) code))
  :hints (("Goal" :induct (enc-ind code pc vmi)
                  :in-theory (e/d (vmi-code-list) (enc-words enc-ok-ins vmi-ins nth update-nth enc-const)))
          ("Subgoal *1/2" :use ((:instance enc-code-ins-below (code (cdr code)) (pc (1+ pc)) (j pc)
                                             (vmi (enc-one (car code) pc vmi)))))))

; the function table: clauses, then each function's first index and count

(defthm enc-clauses-fields
  (implies (not (member k '(16 17 18))) (equal (nth k (enc-clauses ents ci vmi)) (nth k vmi)))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defmacro cl-room (ci ents)
  `(and (<= (+ ,ci (len ,ents)) (len (nth 16 vmi))) (<= (+ ,ci (len ,ents)) (len (nth 17 vmi)))
        (<= (+ ,ci (len ,ents)) (len (nth 18 vmi)))))

(defthm enc-clauses-lens
  (implies (and (natp ci) (cl-room ci ents))
           (and (equal (len (nth 16 (enc-clauses ents ci vmi))) (len (nth 16 vmi)))
                (equal (len (nth 17 (enc-clauses ents ci vmi))) (len (nth 17 vmi)))
                (equal (len (nth 18 (enc-clauses ents ci vmi))) (len (nth 18 vmi)))))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm enc-clauses-below
  (implies (and (natp ci) (natp j) (< j ci) (member k '(16 17 18)))
           (equal (nth j (nth k (enc-clauses ents ci vmi))) (nth j (nth k vmi))))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm enc-clauses-decodes
  (implies (and (enc-ok-clauses ents) (natp ci) (cl-room ci ents))
           (equal (vmi-clauses ci (len ents) (enc-clauses ents ci vmi)) ents))
  :hints (("Goal" :induct (enc-clauses ents ci vmi) :in-theory (e/d (vmi-clause) (nth update-nth)))))

(defthm enc-fntab-fields
  (implies (not (member k '(14 15 16 17 18))) (equal (nth k (enc-fntab tab f ci vmi)) (nth k vmi)))
  :hints (("Goal" :in-theory (disable nth update-nth enc-clauses))))

(defmacro fn-room (f ci tab)
  `(and (<= (+ ,f (len ,tab)) (len (nth 14 vmi))) (<= (+ ,f (len ,tab)) (len (nth 15 vmi)))
        (<= (+ ,ci (nclauses ,tab)) (len (nth 16 vmi))) (<= (+ ,ci (nclauses ,tab)) (len (nth 17 vmi)))
        (<= (+ ,ci (nclauses ,tab)) (len (nth 18 vmi)))))

(defthm enc-fntab-lens
  (implies (and (natp f) (natp ci) (fn-room f ci tab))
           (and (equal (len (nth 14 (enc-fntab tab f ci vmi))) (len (nth 14 vmi)))
                (equal (len (nth 15 (enc-fntab tab f ci vmi))) (len (nth 15 vmi)))
                (equal (len (nth 16 (enc-fntab tab f ci vmi))) (len (nth 16 vmi)))
                (equal (len (nth 17 (enc-fntab tab f ci vmi))) (len (nth 17 vmi)))
                (equal (len (nth 18 (enc-fntab tab f ci vmi))) (len (nth 18 vmi)))))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm enc-fntab-below
  (implies (and (natp f) (natp ci) (natp j))
           (and (implies (and (< j f) (member k '(14 15))) (equal (nth j (nth k (enc-fntab tab f ci vmi))) (nth j (nth k vmi))))
                (implies (and (< j ci) (member k '(16 17 18))) (equal (nth j (nth k (enc-fntab tab f ci vmi))) (nth j (nth k vmi))))))
  :hints (("Goal" :in-theory (disable nth update-nth))))

; clauses read from below ci are what they were before later writes
(defthm vmi-clauses-frame-below
  (implies (and (natp ci) (natp k) (natp ci2) (natp f) (<= (+ ci k) ci2))
           (equal (vmi-clauses ci k (enc-fntab tab f ci2 vmi)) (vmi-clauses ci k vmi)))
  :hints (("Goal" :induct (vmi-clauses ci k vmi) :in-theory (e/d (vmi-clause (:induction vmi-clauses)) (nth update-nth enc-fntab)))))

(defthm enc-fntab-decodes
  (implies (and (enc-ok-fntab tab f) (natp f) (natp ci) (fn-room f ci tab))
           (equal (vmi-fntab f (len tab) (enc-fntab tab f ci vmi)) tab))
  :hints (("Goal" :induct (enc-fntab tab f ci vmi) :in-theory (e/d (vmi-fntab) (nth update-nth vmi-clauses-open)))))

; ---- LOADING A PROGRAM -------------------------------------------------------------------------

(defthm enc-clauses-code-list
  (equal (vmi-code-list pc n (enc-clauses ents ci vmi)) (vmi-code-list pc n vmi))
  :hints (("Goal" :induct (enc-clauses ents ci vmi) :in-theory (disable nth update-nth))))

(defthm enc-fntab-code-list
  (equal (vmi-code-list pc n (enc-fntab tab f ci vmi)) (vmi-code-list pc n vmi))
  :hints (("Goal" :induct (enc-fntab tab f ci vmi) :in-theory (disable nth update-nth enc-clauses))))

(defthm floor-4n (implies (integerp n) (equal (floor (* 4 n) 4) n)))

(defthm len-resize-list (equal (len (resize-list l n d)) (nfix n)))

(defthm true-listp-resize-list (implies (true-listp l) (true-listp (resize-list l n d))))

(defthm no-h-resize-list (implies (and (no-h l) (not (equal d :h))) (no-h (resize-list l n d))))

(defthm enc-clauses-shape
  (implies (and (true-listp vmi) (< 18 (len vmi)))
           (and (true-listp (enc-clauses ents ci vmi)) (equal (len (enc-clauses ents ci vmi)) (len vmi))))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(defthm enc-fntab-shape
  (implies (and (true-listp vmi) (< 18 (len vmi)))
           (and (true-listp (enc-fntab tab f ci vmi)) (equal (len (enc-fntab tab f ci vmi)) (len vmi))))
  :hints (("Goal" :in-theory (disable nth update-nth enc-clauses))))

(defthm enc-code-shape
  (implies (and (true-listp vmi) (< 18 (len vmi)))
           (and (true-listp (enc-code code pc vmi)) (equal (len (enc-code code pc vmi)) (len vmi))))
  :hints (("Goal" :induct (enc-ind code pc vmi) :in-theory (e/d (enc-one) (nth update-nth enc-words)))))

; the loader in four named stages: arrays sized, code in, table in, registers set
(defun lp-resize (prog nstk nctl vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((n (len (car prog))) (nf (len (cdr prog))) (nc (nclauses (cdr prog)))
         (vmi (resize-v-stk 0 vmi)) (vmi (resize-v-ckind 0 vmi))
         (vmi (resize-v-code (* 4 n) vmi)) (vmi (resize-v-pool n vmi)) (vmi (resize-v-stk nstk vmi))
         (vmi (resize-v-ckind nctl vmi)) (vmi (resize-v-ca nctl vmi)) (vmi (resize-v-cb nctl vmi))
         (vmi (resize-v-cc nctl vmi)) (vmi (resize-v-cprev nctl vmi))
         (vmi (resize-v-fnfirst nf vmi)) (vmi (resize-v-fncount nf vmi))
         (vmi (resize-v-cln nc vmi)) (vmi (resize-v-clent nc vmi)))
    (resize-v-clrest nc vmi)))

(defun lp-regs (vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let* ((vmi (update-v-pc 0 vmi)) (vmi (update-v-fb 0 vmi)) (vmi (update-v-sp 0 vmi))
         (vmi (update-v-status 0 vmi)) (vmi (update-v-ctop 0 vmi)))
    (update-v-hidx -1 vmi)))

(defthm vmi-load-prog-stages
  (equal (vmi-load-prog prog nstk nctl vmi)
         (lp-regs (enc-fntab (cdr prog) 0 0 (enc-code (car prog) 0 (lp-resize prog nstk nctl vmi)))))
  :hints (("Goal" :in-theory (disable enc-fntab enc-code))))

; the sized arrays
(defthm lp-resize-facts
  (implies (and (vmip vmi) (natp nstk) (natp nctl))
           (let ((r (lp-resize prog nstk nctl vmi)))
             (and (true-listp r) (equal (len r) 19)
                  (equal (len (nth 6 r)) (* 4 (len (car prog)))) (equal (len (nth 7 r)) (len (car prog)))
                  (true-listp (nth 8 r)) (equal (len (nth 8 r)) nstk)
                  (equal (len (nth 9 r)) nctl) (equal (len (nth 10 r)) nctl) (equal (len (nth 11 r)) nctl)
                  (equal (len (nth 12 r)) nctl) (equal (len (nth 13 r)) nctl)
                  (no-h (nth 10 r))
                  (equal (len (nth 14 r)) (len (cdr prog))) (equal (len (nth 15 r)) (len (cdr prog)))
                  (equal (len (nth 16 r)) (nclauses (cdr prog))) (equal (len (nth 17 r)) (nclauses (cdr prog)))
                  (equal (len (nth 18 r)) (nclauses (cdr prog))))))
  :hints (("Goal" :in-theory (disable resize-list))))

(defthm lp-regs-facts
  (implies (and (true-listp vmi) (equal (len vmi) 19))
           (let ((g (lp-regs vmi)))
             (and (true-listp g) (equal (len g) 19)
                  (equal (nth 0 g) 0) (equal (nth 1 g) 0) (equal (nth 2 g) 0) (equal (nth 3 g) 0)
                  (equal (nth 4 g) 0) (equal (nth 5 g) -1)
                  (implies (and (natp k) (not (member k '(0 1 2 3 4 5)))) (equal (nth k g) (nth k vmi)))
                  (equal (vmi-prog g) (vmi-prog vmi)))))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(in-theory (disable lp-resize lp-regs vmi-load-prog))

(defmacro lprog () '(vmi-load-prog prog nstk nctl vmi))
(defmacro lp-r () '(lp-resize prog nstk nctl vmi))
(defmacro lp-s () '(enc-code (car prog) 0 (lp-r)))
(defmacro lp-t () '(enc-fntab (cdr prog) 0 0 (lp-s)))

; the program reads back
(defthm vmi-load-prog-prog
  (implies (and (vmip vmi) (enc-ok prog) (natp nstk) (natp nctl))
           (equal (vmi-prog (lprog)) prog))
  :hints (("Goal" :in-theory (e/d (vmi-prog enc-ok) (nth update-nth enc-code enc-fntab vmi-code-list vmi-fntab))
                  :use ((:instance enc-code-decodes (code (car prog)) (pc 0) (vmi (lp-r)))
                        (:instance enc-fntab-decodes (tab (cdr prog)) (f 0) (ci 0) (vmi (lp-s)))))))

; it starts at 0 with nothing on the control stack, in vmi-ok
(defthm vmi-load-prog-state
  (implies (and (vmip vmi) (natp nstk) (natp nctl))
           (and (vmi-shape (lprog)) (vmi-ok (lprog))
                (equal (vmi-abs (lprog)) (list 0 0 0 (nth 8 (lprog)) nil))))
  :hints (("Goal" :in-theory (disable nth update-nth enc-code enc-fntab vmi-prog))))

(defthm vmi-load-prog-facts
  (implies (and (vmip vmi) (enc-ok prog) (natp nstk) (natp nctl))
           (and (vmi-shape (lprog)) (vmi-ok (lprog))
                (equal (vmi-prog (lprog)) prog)
                (equal (vmi-abs (lprog)) (list 0 0 0 (nth 8 (lprog)) nil))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (vmi-load-prog-prog vmi-load-prog-state))))

; ---- THE THEOREM -------------------------------------------------------------------------------

; A COMPILED PROGRAM, ENCODED INTO THE ARRAYS AND RUN THERE, answers what
; its meaning does -- its value, or the value of a throw nothing caught
; -- unless an array overflowed. With vcs2-correct below it, this is the
; meaning to the 64-bit machine the Fortran is generated from.
(defthm vmi-correct
  (implies (and (vmip vmi) (x2defs-ok defs) (x2wf e 0 nil) (enc-ok (vcs2-program e defs)) (natp nstk) (natp nctl)
                (or (valp (mx2 e nil nil defs fuel)) (thrownp (mx2 e nil nil defs fuel))) (natp k)
                (not (equal (v-status (vmi-run (+ (s2clk e nil nil defs fuel) k)
                                               (vmi-load-prog (vcs2-program e defs) nstk nctl vmi)))
                            2)))
           (equal (vcs2-answer (vmi-abs (vmi-run (+ (s2clk e nil nil defs fuel) k)
                                                 (vmi-load-prog (vcs2-program e defs) nstk nctl vmi))))
                  (mx2 e nil nil defs fuel)))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory))
                  :use ((:instance vmi-load-prog-facts (prog (vcs2-program e defs)))
                        (:instance vmi-run-refines (n (+ (s2clk e nil nil defs fuel) k))
                                   (vmi (vmi-load-prog (vcs2-program e defs) nstk nctl vmi)))
                        (:instance vcs2-correct-stk
                                   (stk (nth 8 (vmi-load-prog (vcs2-program e defs) nstk nctl vmi))))))))
