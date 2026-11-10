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

; ex-aplook in the form these walks were proved over (seqk.lisp ex-aplook-is)
(local (defthmd ex-aplook-old
  (equal (ex-aplook req k) (if (and (integerp req) (<= 0 req) (integerp k) (<= k (+ req 1))) 1 0))
  :hints (("Goal" :use ex-aplook-is))))

; ---- THE SHAPE the refinement needs: 20 fields, the stack and the scratch lists, no
; control record's first field the handler tag. A well-typed stobj has it
; (vmip-shape); keeping vmip itself -- every value 64-bit -- is a separate
; theorem, about overflow, not about meaning.

(defun no-h (l) (if (atom l) t (and (not (equal (car l) :h)) (no-h (cdr l)))))

(defun vmi-shape (vmi)
  (and (true-listp vmi) (equal (len vmi) 20) (true-listp (nth 8 vmi)) (no-h (nth 10 vmi)) (true-listp (nth 19 vmi))))

(defthm v-cap-no-h (implies (v-cap x) (no-h x)))

(defthm v-stkp-tl (implies (v-stkp x) (true-listp x)))
(defthm v-tmpp-tl (implies (v-tmpp x) (true-listp x)))

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
     :hints (("Goal" :in-theory (union-theories '(,f vmi-call) (set-difference-theories (vmi-thy) '(restp))) ,@hints))))

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

; ---- THE CALL, at any count: vcs2-callv on what the arrays hold ---------------------------

(defmacro call-rhs ()
  '(vcs2-callv (vmi-prog vmi) (v-pc vmi) (v-fb vmi) (- (v-sp vmi) (1+ m)) (c-c)
               (stk-from (- (v-sp vmi) (1+ m)) m (nth 8 vmi)) (nth 8 vmi) (vmi-ctl (v-ctop vmi) vmi)))
(defmacro m-ci () '(vmi-pick (clo-f (c-c)) m vmi))

(defmacro def-call-if (name cond)
  `(defthm ,name
     (implies (and (vmi-shape vmi) (vmi-ok vmi) (equal (v-status vmi) 0) (natp m) (<= (1+ m) (v-sp vmi)) ,cond
                   (not (equal (v-status (vmi-call m vmi)) 2)))
              (equal (vmi-abs (vmi-call m vmi)) (call-rhs)))
     :rule-classes nil
     :hints (("Goal" :in-theory (union-theories '(vmi-call) (set-difference-theories (vmi-thy) '(restp)))))))

(def-call-if call-not-fn (not (clop (c-c))))
(def-call-if call-arity (and (clop (c-c)) (< (m-ci) 0)))
(def-call-if call-fixed (and (clop (c-c)) (<= 0 (m-ci)) (not (equal (nth (m-ci) (nth 18 vmi)) 1))))
(def-call-if call-rest (and (clop (c-c)) (<= 0 (m-ci)) (equal (nth (m-ci) (nth 18 vmi)) 1)))

(defthm vmi-call-refines
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (equal (v-status vmi) 0) (natp m) (<= (1+ m) (v-sp vmi))
                (not (equal (v-status (vmi-call m vmi)) 2)))
           (equal (vmi-abs (vmi-call m vmi)) (call-rhs)))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (call-not-fn call-arity call-fixed call-rest))))

(in-theory (disable vmi-call))

; ---- APPLY'S SPREAD -----------------------------------------------------------------------------
;
; fields: 19 the scratch. Its writes as list writes, an overflow the status

(defthm vmi-tset-is
  (equal (vmi-tset i v vmi)
         (if (< (nfix i) (len (nth 19 vmi)))
             (update-nth 19 (update-nth (nfix i) v (nth 19 vmi)) vmi)
           (update-nth 3 2 vmi))))
(defthm vmi-treg-is
  (equal (vmi-treg i vmi) (if (< (nfix i) (len (nth 19 vmi))) (nth (nfix i) (nth 19 vmi)) nil)))
(in-theory (disable vmi-tset vmi-treg))
(defthm consp-len-pos (implies (consp x) (< 0 (len x))) :rule-classes :linear)

(defthm update-nth-update-nth-same-19
  (equal (update-nth k a (update-nth k b x)) (update-nth k a x)))
(defthm update-nth-nth-same-19
  (implies (< (nfix n) (len x)) (equal (update-nth n (nth n x) x) x)))

; the lists: x2-put writes in order, a list's tail is its writes past the head
(defthm x2-put-cons-tail
  (implies (and (natp j) (consp tl))
           (equal (x2-put (1+ j) l tl) (cons (car tl) (x2-put j l (cdr tl))))))
(defthm x2-put-append
  (equal (x2-put k (append a b) l) (x2-put (+ (nfix k) (len a)) b (x2-put k a l))))
(defthm x2-put-list1 (equal (x2-put k (list x) l) (update-nth (nfix k) x l)))
(in-theory (disable x2-put-cons-tail))
(defthm nth-x2-put-under
  (implies (and (natp k) (natp r) (< r k)) (equal (nth r (x2-put k l stk)) (nth r stk))))
(defthm stk-from-tail
  (implies (natp a) (equal (stk-from (1+ a) n l) (stk-from a n (cdr l))))
  :hints (("Goal" :in-theory (enable sreg))))
(in-theory (disable stk-from-tail))
(defthm stk-from-x2-put-prefix
  (implies (natp k) (equal (stk-from k (len a) (x2-put k (append a b) l)) (true-list-fix a)))
  :hints (("Goal" :in-theory (enable sreg) :induct (x2-put k a l))))
(defthm stk-from-x2-put-all
  (implies (natp k) (equal (stk-from k (len a) (x2-put k a l)) (true-list-fix a)))
  :hints (("Goal" :in-theory (enable sreg) :induct (x2-put k a l))))
(defthm nth-x2-put-past
  (implies (and (natp k) (true-listp a))
           (equal (nth (+ k (len a)) (x2-put k (append a (list x)) l)) x)))

; a call's arguments: the first, the last, and those between
(defthm stk-from-car
  (implies (and (natp m) (< 0 m)) (and (consp (stk-from a m stk)) (equal (car (stk-from a m stk)) (nth (nfix a) stk))))
  :hints (("Goal" :in-theory (enable sreg) :expand ((stk-from a m stk)))))
(defthm stk-from-last
  (implies (and (natp a) (natp m) (< 0 m)) (equal (car (last (stk-from a m stk))) (nth (+ a m -1) stk)))
  :hints (("Goal" :in-theory (enable sreg) :induct (stk-from a m stk))))
(defthm len-stk-from-is (equal (len (stk-from a k stk)) (nfix k)))
(defun ind-tsf (n a m) (if (zp n) (list a m) (ind-tsf (1- n) (1+ (nfix a)) (1- m))))
(defthm take-stk-from
  (implies (and (natp n) (<= n (nfix m))) (equal (take n (stk-from a m stk)) (stk-from a n stk)))
  :hints (("Goal" :in-theory (enable sreg) :induct (ind-tsf n a m) :expand ((stk-from a m stk) (stk-from a n stk)))))
(defthm stk-from-butlast
  (implies (and (natp a) (natp m) (< 0 m)) (equal (butlast (stk-from a m stk) 1) (stk-from a (1- m) stk)))
  :hints (("Goal" :in-theory (enable butlast))))
(defthm stk-from-cdr
  (implies (and (natp a) (natp m) (< 0 m)) (equal (cdr (stk-from a m stk)) (stk-from (1+ a) (1- m) stk)))
  :hints (("Goal" :in-theory (enable sreg) :expand ((stk-from a m stk)))))

; ---- THE SCRATCH'S LISTS ----------------------------------------------------------------------

(defthm vmi-treg-tl
  (implies (true-listp (nth 19 vmi)) (equal (vmi-treg i vmi) (nth (nfix i) (nth 19 vmi)))))

(defthm stk-from-snoc
  (implies (and (natp a) (natp k)) (equal (stk-from a (1+ k) l) (append (stk-from a k l) (list (nth (+ a k) l)))))
  :hints (("Goal" :in-theory (enable sreg stk-from) :induct (stk-from a k l) :expand ((stk-from a 1 l) (stk-from a (+ 1 k) l)))))
(defthm stk-from-update-outside
  (implies (and (natp a) (natp j) (or (< j a) (<= (+ a (nfix k)) j)))
           (equal (stk-from a k (update-nth j x l)) (stk-from a k l)))
  :hints (("Goal" :in-theory (enable sreg stk-from) :induct (stk-from a k l))))
(defthm stk-from-split
  (implies (and (natp a) (natp k) (natp n))
           (equal (stk-from a (+ k n) l) (append (stk-from a k l) (stk-from (+ a k) n l))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable sreg stk-from) :induct (stk-from a k l))))
(defthm stk-from-x2-put-under
  (implies (and (natp a) (natp k) (<= (+ a (nfix n)) k)) (equal (stk-from a n (x2-put k vs l)) (stk-from a n l)))
  :hints (("Goal" :in-theory (enable x2-put) :induct (x2-put k vs l))))
(defthm stk-from-x2-put-after
  (implies (and (natp k) (true-listp els))
           (equal (stk-from 0 (+ k (len els)) (x2-put k els r)) (append (stk-from 0 k r) els)))
  :hints (("Goal" :use ((:instance stk-from-split (a 0) (n (len els)) (l (x2-put k els r)))))))
(defthm nthcdr-stk-from
  (implies (and (natp n) (natp a) (<= n (nfix k))) (equal (nthcdr n (stk-from a k l)) (stk-from (+ a n) (- (nfix k) n) l)))
  :hints (("Goal" :in-theory (enable sreg stk-from) :induct (ind-tsf n a k) :expand ((stk-from a k l)))))
(defthm sk-consv-snoc
  (equal (sk-consv (append xs (list y)) s) (sk-consv xs (sk-cell y s))))
(defthm sk-consv-nil (equal (sk-consv nil s) s))

; ---- THE WALKS, on the scratch's list ---------------------------------------------------------

(defun twalk (k l i top tl)
  (declare (xargs :measure (+ (* 2 (nfix l)) (if (equal (sk-step (sk-kind (car tl) (sk-topk top)) i (sk-cnt (car tl))) 3) 1 0))))
  (let* ((v (car tl)) (d (sk-step (sk-kind v (sk-topk top)) i (sk-cnt v))))
    (cond ((equal d 0) (list 0 k tl))
          ((equal d 3) (twalk k l 0 2 (update-nth 0 (sk-nextv v 3) tl)))
          ((sk-more d)
           (if (zp l)
               (list 2 k tl)
             (twalk (1+ (nfix k)) (1- l) (if (equal d 2) (1+ (nfix i)) 0) (if (equal d 1) 0 1)
                    (update-nth 0 (sk-nextv v d) (update-nth (1+ (nfix k)) (sk-elem v d i) tl)))))
          (t (list 1 k tl)))))

(defun tawalk-d (req k i top tl)
  (if (equal (ex-aplook req k) 1) (sk-step (sk-kind (car tl) (sk-topk top)) i (sk-cnt (car tl))) 1))
(defun tawalk (req k i top tl)
  (declare (xargs :measure (+ (* 2 (nfix (- (ifix req) (nfix k)))) (if (equal (tawalk-d req k i top tl) 3) 1 0))))
  (let* ((v (car tl)) (d (tawalk-d req k i top tl)))
    (if (equal d 3)
        (tawalk req k 0 2 (update-nth 0 (sk-nextv v 3) tl))
      (let ((w (ex-apstep req k (if (sk-more d) 1 0))))
        (if (and (equal w 1) (sk-more d) (< (nfix k) req))
            (tawalk req (1+ (nfix k)) (if (equal d 2) (1+ (nfix i)) 0) (if (equal d 1) 0 1)
                    (update-nth 0 (sk-nextv v d) (update-nth (1+ (nfix k)) (sk-elem v d i) tl)))
          (list (if (equal w 2) 2 3) k i top tl))))))

(defun tconsv (j lo tl)
  (declare (xargs :measure (nfix (- (nfix j) (nfix lo)))))
  (if (<= (nfix j) (nfix lo)) tl (tconsv (1- (nfix j)) lo (update-nth 0 (sk-cell (nth j tl) (car tl)) tl))))

; the arrays' walks are them, when nothing overflowed
(defthm vmi-walk-sticky
  (implies (equal (nth 3 vmi) 2) (equal (nth 3 (mv-nth 2 (vmi-walk k l i top vmi))) 2)))
(defthm vmi-awalk-sticky
  (implies (equal (nth 3 vmi) 2) (equal (nth 3 (mv-nth 4 (vmi-awalk req k i top vmi))) 2)))
(defthm vmi-consv-sticky
  (implies (equal (nth 3 vmi) 2) (equal (nth 3 (vmi-consv j lo vmi)) 2)))

(defthm vmi-walk-twalk
  (implies (and (not (equal (nth 3 (mv-nth 2 (vmi-walk k l i top vmi))) 2)) (consp (nth 19 vmi)) (true-listp (nth 19 vmi)) (< 19 (len vmi)) (natp k) (natp i))
           (equal (vmi-walk k l i top vmi)
                  (let ((tw (twalk k l i top (nth 19 vmi))))
                    (mv (car tw) (cadr tw) (update-nth 19 (caddr tw) vmi)))))
  :hints (("Goal" :induct (vmi-walk k l i top vmi) :in-theory (disable sk-step sk-kind sk-nextv sk-elem)
                  :expand ((:free (top) (twalk k l i top (nth 19 vmi))) (:free (top) (vmi-walk k l i top vmi))))))

(defthm vmi-awalk-tawalk
  (implies (and (not (equal (nth 3 (mv-nth 4 (vmi-awalk req k i top vmi))) 2)) (consp (nth 19 vmi)) (true-listp (nth 19 vmi)) (< 19 (len vmi)) (natp k) (natp i))
           (equal (vmi-awalk req k i top vmi)
                  (let ((tw (tawalk req k i top (nth 19 vmi))))
                    (mv (nth 0 tw) (nth 1 tw) (nth 2 tw) (nth 3 tw) (update-nth 19 (nth 4 tw) vmi)))))
  :hints (("Goal" :induct (vmi-awalk req k i top vmi) :in-theory (disable sk-step sk-kind sk-nextv sk-elem ex-apstep ex-aplook)
                  :expand ((:free (top) (tawalk req k i top (nth 19 vmi))) (:free (top) (vmi-awalk req k i top vmi))))))

(defthm vmi-consv-tconsv
  (implies (and (not (equal (nth 3 (vmi-consv j lo vmi)) 2)) (true-listp (nth 19 vmi)) (< 19 (len vmi)))
           (equal (vmi-consv j lo vmi) (update-nth 19 (tconsv j lo (nth 19 vmi)) vmi)))
  :hints (("Goal" :induct (vmi-consv j lo vmi) :in-theory (disable sk-cell))))

; ---- WHAT THE WALKS ARE: seqk's sk-els and ex-apwalk ---------------------------------------------

(defun walk-code (st) (case st (:ok 0) (:none 1) (otherwise 2)))

(defthm sk-d-cursor
  (equal (sk-d (list v i tp)) (sk-step (sk-kind v tp) i (len (cdr v))))
  :hints (("Goal" :in-theory (enable sk-d))))
(defthm sk-first-cursor
  (equal (sk-first (list v i tp)) (sk-elem v (sk-step (sk-kind v tp) i (len (cdr v))) i))
  :hints (("Goal" :in-theory (enable sk-first sk-d))))
(defthm sk-next-cursor
  (equal (sk-next (list v i tp))
         (let ((d (sk-step (sk-kind v tp) i (len (cdr v)))))
           (case d (1 (list (cdr v) 0 nil)) (2 (list v (1+ (nfix i)) t)) (3 (list (sk-real (cdr v)) 0 :r))
             (5 (list (cddr v) 0 t)) (otherwise (list v i tp)))))
  :hints (("Goal" :in-theory (enable sk-next sk-d))))
(defthm sk-topk-int (and (equal (sk-topk 0) nil) (equal (sk-topk 1) t) (equal (sk-topk 2) :r)))

(defthm twalk-els
  (implies (and (natp k) (consp tl))
           (let ((tw (twalk k l i top tl)) (els (sk-els (list (car tl) i (sk-topk top)) l)))
             (and (equal (car tw) (walk-code (car els)))
                  (equal (cadr tw) (+ k (len (cdr els))))
                  (consp (caddr tw))
                  (equal (cdr (caddr tw)) (x2-put k (cdr els) (cdr tl))))))
  :hints (("Goal" :induct (twalk k l i top tl)
                  :expand ((sk-els (list (car tl) i (sk-topk top)) l)))))

(defthm stk-from-1-slot0
  (implies (natp n) (equal (stk-from 1 n (update-nth 0 x l)) (stk-from 1 n l)))
  :hints (("Goal" :in-theory (disable stk-from-update-outside) :use ((:instance stk-from-update-outside (a 1) (j 0) (k n))))))
(defthm stk-from-1-grow
  (implies (natp k)
           (equal (stk-from 1 (1+ k) (update-nth 0 x (update-nth (1+ k) e tl))) (append (stk-from 1 k tl) (list e))))
  :hints (("Goal" :in-theory (disable stk-from stk-from-snoc update-nth stk-from-1-slot0)
                  :use ((:instance stk-from-snoc (a 1) (l (update-nth 0 x (update-nth (1+ k) e tl))))))))

(defthm car-update-nth-pos (implies (not (zp n)) (and (equal (car (update-nth n v x)) (car x)) (equal (cdr (update-nth n v x)) (update-nth (1- n) v (cdr x))))))
(defthm car-update-nth-0 (and (equal (car (update-nth 0 x l)) x) (equal (cdr (update-nth 0 x l)) (cdr l))))
(defmacro tw-fx (tw) `(stk-from 1 (nth 1 ,tw) (nth 4 ,tw)))
(defmacro tw-cur (tw) `(list (car (nth 4 ,tw)) (nth 2 ,tw) (sk-topk (nth 3 ,tw))))

(defthm tawalk-apwalk
  (implies (and (natp k) (natp i))
           (let ((tw (tawalk req k i top tl)) (w (ex-apwalk req (stk-from 1 k tl) (list (car tl) i (sk-topk top)))))
             (and (equal (car w) (car tw))
                  (natp (nth 1 tw)) (natp (nth 2 tw))
                  (implies (equal (car tw) 2)
                           (and (natp req) (<= req (nth 1 tw))
                                (equal (nth 1 w) (take req (tw-fx tw)))
                                (equal (nth 2 w) (nthcdr req (tw-fx tw)))
                                (equal (nth 3 w) (tw-cur tw))))
                  (implies (not (equal (car tw) 2))
                           (and (equal (car tw) 3)
                                (equal (nth 1 w) (tw-fx tw))
                                (equal (nth 2 w) (tw-cur tw)))))))
  :hints (("Goal" :induct (tawalk req k i top tl) :in-theory (e/d (ex-apstep ex-aplook ex-aplook-old) (update-nth stk-from))
                  :expand ((ex-apwalk req (stk-from 1 k tl) (list (car tl) i (sk-topk top))) (tawalk req k i top tl)))))

(defthm stk-from-zero (implies (zp k) (equal (stk-from a k l) nil)))
(defthm tconsv-is
  (implies (and (natp j) (natp lo) (consp tl))
           (and (equal (car (tconsv j lo tl)) (sk-consv (stk-from (1+ lo) (nfix (- j lo)) tl) (car tl)))
                (equal (cdr (tconsv j lo tl)) (cdr tl))
                (consp (tconsv j lo tl))
                (implies (true-listp tl) (true-listp (tconsv j lo tl)))))
  :hints (("Goal" :induct (tconsv j lo tl) :in-theory (disable sk-cell update-nth stk-from stk-from-snoc))
          ("Subgoal *1/2" :use ((:instance stk-from-snoc (a (1+ lo)) (k (- j (1+ lo))) (l tl))))))

; ---- THE SPREAD, on the lists: sk-spread ---------------------------------------------------------

(defthm vmi-to-tmp-sticky (implies (equal (nth 3 vmi) 2) (equal (nth 3 (vmi-to-tmp a j k vmi)) 2)))
(defthm vmi-from-tmp-sticky (implies (equal (nth 3 vmi) 2) (equal (nth 3 (vmi-from-tmp j a k vmi)) 2)))
(defthm vmi-to-tmp-is
  (implies (and (not (equal (nth 3 (vmi-to-tmp a j k vmi)) 2)) (natp j) (true-listp (nth 8 vmi)) (< 19 (len vmi)))
           (equal (vmi-to-tmp a j k vmi) (update-nth 19 (x2-put j (stk-from a k (nth 8 vmi)) (nth 19 vmi)) vmi)))
  :hints (("Goal" :induct (vmi-to-tmp a j k vmi) :in-theory (enable sreg))))
(defthm vmi-from-tmp-is
  (implies (and (not (equal (nth 3 (vmi-from-tmp j a k vmi)) 2)) (natp a) (true-listp (nth 19 vmi)) (< 19 (len vmi)))
           (equal (vmi-from-tmp j a k vmi) (update-nth 8 (x2-put a (stk-from j k (nth 19 vmi)) (nth 8 vmi)) vmi)))
  :hints (("Goal" :induct (vmi-from-tmp j a k vmi) :in-theory (enable sreg))))
(defthm vmi-to-tmp-stk (equal (nth 8 (vmi-to-tmp a j k vmi)) (nth 8 vmi))
  :hints (("Goal" :induct (vmi-to-tmp a j k vmi))))
(defthm vmi-to-tmp-t0
  (implies (and (natp m) (natp fb2) (<= 2 m) (true-listp (nth 8 vmi)) (true-listp (nth 19 vmi)) (< 19 (len vmi)) (equal (nth 3 vmi) 0)
                (not (equal (nth 3 (vmi-tset 0 x (vmi-to-tmp (1+ fb2) 1 (- m 2) vmi))) 2)))
           (equal (vmi-tset 0 x (vmi-to-tmp (1+ fb2) 1 (- m 2) vmi))
                  (update-nth 19 (update-nth 0 x (x2-put 1 (stk-from (1+ fb2) (- m 2) (nth 8 vmi)) (nth 19 vmi))) vmi)))
  :hints (("Goal" :do-not-induct t :in-theory (disable vmi-to-tmp)
                  :cases ((equal (nth 3 (vmi-to-tmp (1+ fb2) 1 (- m 2) vmi)) 2)))))
(defthm true-listp-x2-put (implies (true-listp l) (true-listp (x2-put k vs l))))
(defthm true-listp-twalk (implies (true-listp tl) (true-listp (caddr (twalk k l i top tl))))
  :hints (("Goal" :induct (twalk k l i top tl) :expand ((:free (top) (twalk k l i top tl))))))
(defthm true-listp-tawalk (implies (true-listp tl) (true-listp (nth 4 (tawalk req k i top tl))))
  :hints (("Goal" :induct (tawalk req k i top tl) :expand ((:free (top) (tawalk req k i top tl))))))
(defthm consp-tawalk (implies (consp tl) (consp (nth 4 (tawalk req k i top tl))))
  :hints (("Goal" :induct (tawalk req k i top tl) :expand ((:free (top) (tawalk req k i top tl))))))
(defthm natp-tawalk (implies (and (natp k) (natp i)) (and (natp (nth 1 (tawalk req k i top tl))) (natp (nth 2 (tawalk req k i top tl)))))
  :rule-classes ((:rewrite) (:type-prescription :corollary (implies (and (natp k) (natp i)) (natp (nth 1 (tawalk req k i top tl)))))
                 (:type-prescription :corollary (implies (and (natp k) (natp i)) (natp (nth 2 (tawalk req k i top tl))))))
  :hints (("Goal" :induct (tawalk req k i top tl) :expand ((:free (top) (tawalk req k i top tl))))))

(defun vmi-spread-tl (req m vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (cond ((not (equal (v-status vmi) 0)) (mv 1 0 vmi))
        ((equal (vmi-walk-d 0 1 vmi) 4) (mv 1 0 vmi))
        (t (mv-let (w k i top vmi) (vmi-awalk req (- (nfix m) 2) 0 1 vmi)
             (if (equal w 2)
                 (let* ((vmi (vmi-tset 0 (sk-cvalv (vmi-treg 0 vmi) i top) vmi))
                        (vmi (vmi-consv k (nfix req) vmi))
                        (vmi (vmi-tset (1+ (nfix req)) (vmi-treg 0 vmi) vmi)))
                   (mv 2 (1+ (nfix req)) vmi))
               (mv-let (st k vmi) (vmi-walk k *sk-lim* i top vmi)
                 (mv (if (equal st 0) 0 1) (nfix k) vmi)))))))
(defthm vmi-spread-in-tl
  (equal (vmi-spread-in req m fb2 vmi)
         (vmi-spread-tl req m (vmi-tset 0 (vmi-sreg (+ (nfix fb2) (nfix m) -1) (vmi-to-tmp (1+ (nfix fb2)) 1 (- (nfix m) 2) vmi))
                                       (vmi-to-tmp (1+ (nfix fb2)) 1 (- (nfix m) 2) vmi))))
  :hints (("Goal" :in-theory (e/d (vmi-spread-in vmi-spread-tl) (vmi-awalk vmi-walk vmi-consv vmi-to-tmp vmi-tset-is vmi-treg-is vmi-walk-d vmi-sreg-is)))))
(defun tspread-tl (req m tl)
  (if (equal (sk-step (sk-kind (car tl) t) 0 (sk-cnt (car tl))) 4)
      (list 1 0 tl)
    (let ((tw (tawalk req (- m 2) 0 1 tl)))
      (if (equal (car tw) 2)
          (let* ((t1 (update-nth 0 (sk-cvalv (car (nth 4 tw)) (nth 2 tw) (nth 3 tw)) (nth 4 tw)))
                 (t2 (tconsv (nth 1 tw) (nfix req) t1)))
            (list 2 (1+ (nfix req)) (update-nth (1+ (nfix req)) (car t2) t2)))
        (let ((t3 (twalk (nth 1 tw) *sk-lim* (nth 2 tw) (nth 3 tw) (nth 4 tw))))
          (list (if (equal (car t3) 0) 0 1) (nfix (cadr t3)) (caddr t3)))))))
(defthm vmi-tset-status
  (equal (nth 3 (vmi-tset i x v)) (if (< (nfix i) (len (nth 19 v))) (nth 3 v) 2)))
(defthm vmi-tset-in
  (implies (< (nfix i) (len (nth 19 v))) (equal (vmi-tset i x v) (update-nth 19 (update-nth (nfix i) x (nth 19 v)) v))))
(defthm true-listp-update-nth-t (implies (true-listp l) (true-listp (update-nth i x l))))
(defthm len-tconsv (implies (consp tl) (equal (len (tconsv j lo tl)) (len tl)))
  :hints (("Goal" :induct (tconsv j lo tl) :in-theory (disable sk-cell))))
(defthm natp-plus-m2 (implies (and (integerp m) (<= 2 m)) (natp (+ -2 m))))
(defthm true-listp-cdr-t (implies (true-listp x) (true-listp (cdr x))))
(defthm tawalk-nums
  (implies (and (natp k) (natp i))
           (and (integerp (nth 1 (tawalk req k i top tl))) (<= 0 (nth 1 (tawalk req k i top tl)))
                (integerp (nth 2 (tawalk req k i top tl))) (<= 0 (nth 2 (tawalk req k i top tl)))))
  :rule-classes ((:rewrite) (:linear :corollary (implies (and (natp k) (natp i)) (<= 0 (nth 1 (tawalk req k i top tl)))))))
(defthm tawalk-way2-req
  (implies (equal (car (tawalk req k i top tl)) 2) (natp req))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (tawalk req k i top tl) :in-theory (enable ex-apstep ex-aplook ex-aplook-old) :expand ((:free (top) (tawalk req k i top tl))))))
(defmacro aw () '(vmi-awalk req (+ -2 m) 0 1 vmi))
(defthm vmi-spread-tl-is
  (implies (and (equal (nth 3 vmi) 0) (consp (nth 19 vmi)) (true-listp (nth 19 vmi)) (< 19 (len vmi)) (natp m) (<= 2 m)
                (not (equal (nth 3 (mv-nth 2 (vmi-spread-tl req m vmi))) 2)))
           (equal (vmi-spread-tl req m vmi)
                  (let ((r (tspread-tl req m (nth 19 vmi)))) (mv (car r) (cadr r) (update-nth 19 (caddr r) vmi)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (vmi-spread-tl vmi-walk-d) (vmi-tset-is vmi-treg-is tawalk twalk tconsv vmi-walk vmi-awalk vmi-consv sk-step sk-kind sk-cvalv sk-cnt))
                  :cases ((equal (nth 3 (mv-nth 4 (aw))) 2)))))
(defmacro ts-t0 ()
  '(update-nth 0 (nth (+ fb2 m -1) stk) (x2-put 1 (stk-from (1+ fb2) (- m 2) stk) tl)))
(defun tspread (req m fb2 stk tl) (tspread-tl req m (ts-t0)))
(defthm vmi-spread-tl-stopped
  (implies (not (equal (nth 3 vmi) 0)) (equal (vmi-spread-tl req m vmi) (mv 1 0 vmi))))
(defthm vmi-spread-in-is
  (implies (and (not (equal (nth 3 (mv-nth 2 (vmi-spread-in req m fb2 vmi))) 2)) (natp m) (natp fb2) (<= 2 m)
                (true-listp (nth 8 vmi)) (true-listp (nth 19 vmi)) (< 19 (len vmi)) (equal (nth 3 vmi) 0))
           (equal (vmi-spread-in req m fb2 vmi)
                  (let ((r (tspread req m fb2 (nth 8 vmi) (nth 19 vmi))))
                    (mv (car r) (cadr r) (update-nth 19 (caddr r) vmi)))))
  :hints (("Goal" :do-not-induct t :in-theory (disable vmi-spread-tl tspread-tl vmi-to-tmp vmi-tset-is vmi-treg-is vmi-tset-in vmi-tset-status)
                  :cases ((equal (nth 3 (vmi-tset 0 (nth (+ fb2 m -1) (nth 8 vmi)) (vmi-to-tmp (1+ fb2) 1 (- m 2) vmi))) 2)))))
(defthm vmi-spread-out-is
  (implies (and (equal (nth 3 (vmi-spread-out fb2 k vmi)) 0) (natp fb2) (natp k)
                (true-listp (nth 8 vmi)) (true-listp (nth 19 vmi)) (< 19 (len vmi)))
           (equal (vmi-spread-out fb2 k vmi)
                  (let ((t4 (update-nth (1+ k) (nth fb2 (nth 8 vmi)) (nth 19 vmi))))
                    (update-nth 2 (+ fb2 k 1)
                                (update-nth 8 (x2-put fb2 (stk-from 1 (1+ k) t4) (nth 8 vmi)) (update-nth 19 t4 vmi))))))
  :hints (("Goal" :in-theory (e/d (vmi-spread-out) (vmi-from-tmp)))))

(defmacro sp-of () '(sk-spread req (stk-from (1+ fb2) (- m 2) stk) (nth (+ fb2 m -1) stk)))
(defun sp-code (st) (case st (:ok 0) (:hand 2) (otherwise 1)))

(defthm true-listp-stk-from-b (true-listp (stk-from a k stk)) :hints (("Goal" :in-theory (enable stk-from))))
(defthm true-list-fix-id-b (implies (true-listp x) (equal (true-list-fix x) x)))
(defthm stk-from-1-t0
  (implies (and (natp fb2) (natp m) (<= 2 m))
           (equal (stk-from 1 (- m 2) (ts-t0)) (stk-from (1+ fb2) (- m 2) stk)))
  :hints (("Goal" :in-theory (disable stk-from-x2-put-all update-nth)
                  :use ((:instance stk-from-x2-put-all (k 1) (a (stk-from (1+ fb2) (- m 2) stk)) (l tl))))))
(defthm stk-from-shift
  (implies (natp a) (equal (stk-from (1+ a) n l) (stk-from a n (cdr l))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable sreg stk-from) :induct (stk-from a n l))))
(defthm stk-from-1-cdr-same
  (implies (equal (cdr x) (cdr y)) (equal (equal (stk-from 1 n x) (stk-from 1 n y)) t))
  :hints (("Goal" :use ((:instance stk-from-shift (a 0) (l x)) (:instance stk-from-shift (a 0) (l y))))))
(defthm stk-from-1-tconsv
  (implies (and (consp tl) (natp j) (natp lo)) (equal (stk-from 1 n (tconsv j lo tl)) (stk-from 1 n tl)))
  :hints (("Goal" :in-theory (disable tconsv stk-from)
                  :use ((:instance stk-from-shift (a 0) (l tl)) (:instance stk-from-shift (a 0) (l (tconsv j lo tl)))))))
(defthm tspread-hand-args
  (implies (and (natp req) (natp k) (<= req k) (consp tl))
           (let* ((t1 (update-nth 0 cv tl)) (t2 (tconsv k req t1)))
             (equal (stk-from 1 (1+ req) (update-nth (1+ req) (car t2) t2))
                    (append (take req (stk-from 1 k tl)) (list (sk-consv (nthcdr req (stk-from 1 k tl)) cv))))))
  :hints (("Goal" :do-not-induct t :in-theory (disable stk-from stk-from-snoc tconsv update-nth sk-consv)
                  :use ((:instance stk-from-snoc (a 1) (k req)
                                   (l (update-nth (1+ req) (car (tconsv k req (update-nth 0 cv tl))) (tconsv k req (update-nth 0 cv tl)))))
                        (:instance stk-from-1-cdr-same (n req) (x (tconsv k req (update-nth 0 cv tl))) (y tl))
                        (:instance stk-from-update-outside (a (1+ req)) (k (- k req)) (j 0) (x cv) (l tl))))))
(defthm tspread-walk-args
  (implies (and (natp k) (consp tl))
           (equal (stk-from 1 (+ k (len (cdr (sk-els (list (car tl) i (sk-topk top)) l)))) (caddr (twalk k l i top tl)))
                  (append (stk-from 1 k tl) (cdr (sk-els (list (car tl) i (sk-topk top)) l)))))
  :hints (("Goal" :do-not-induct t :in-theory (disable twalk sk-els stk-from twalk-els)
                  :use (twalk-els
                        (:instance stk-from-shift (a 0) (n (+ k (len (cdr (sk-els (list (car tl) i (sk-topk top)) l))))) (l (caddr (twalk k l i top tl))))
                        (:instance stk-from-shift (a 0) (n k) (l tl))))))
(defthm consp-tconsv (implies (consp tl) (consp (tconsv j lo tl))) :hints (("Goal" :induct (tconsv j lo tl))))
(defthm consp-twalk (implies (consp tl) (consp (caddr (twalk k l i top tl))))
  :hints (("Goal" :induct (twalk k l i top tl) :expand ((:free (top) (twalk k l i top tl))))))
(defthm true-listp-tconsv (implies (true-listp tl) (true-listp (tconsv j lo tl))) :hints (("Goal" :induct (tconsv j lo tl))))
(defthm stk-from-x2-put-stk-from
  (implies (natp k) (equal (stk-from k n (x2-put k (stk-from a n s) l)) (stk-from a n s)))
  :hints (("Goal" :in-theory (disable stk-from-x2-put-all) :use ((:instance stk-from-x2-put-all (a (stk-from a n s)))))))
(defthm sk-els-car-values
  (or (equal (car (sk-els c l)) :ok) (equal (car (sk-els c l)) :none) (equal (car (sk-els c l)) :long))
  :rule-classes ((:forward-chaining :trigger-terms ((car (sk-els c l)))))
  :hints (("Goal" :induct (sk-els c l))))
(defthm tspread-is
  (implies (and (natp m) (<= 2 m) (natp fb2) (true-listp tl))
           (let ((r (tspread req m fb2 stk tl)))
             (and (equal (car r) (sp-code (car (sp-of))))
                  (natp (cadr r))
                  (true-listp (caddr r)) (consp (caddr r))
                  (implies (not (equal (car r) 1))
                           (and (equal (cadr r) (len (cadr (sp-of))))
                                (equal (stk-from 1 (cadr r) (caddr r)) (cadr (sp-of))))))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (sk-cur) (tawalk twalk tconsv sk-els ex-apwalk sk-step sk-kind sk-consv sk-cval update-nth stk-from
                                            tawalk-apwalk twalk-els tspread-walk-args take nthcdr sk-topk))
                  :use ((:instance tawalk-apwalk (k (- m 2)) (i 0) (top 1) (tl (ts-t0)))
                        (:instance twalk-els (k (nth 1 (tawalk req (- m 2) 0 1 (ts-t0)))) (l *sk-lim*)
                                   (i (nth 2 (tawalk req (- m 2) 0 1 (ts-t0)))) (top (nth 3 (tawalk req (- m 2) 0 1 (ts-t0))))
                                   (tl (nth 4 (tawalk req (- m 2) 0 1 (ts-t0)))))
                        (:instance tspread-walk-args (k (nth 1 (tawalk req (- m 2) 0 1 (ts-t0)))) (l *sk-lim*)
                                   (i (nth 2 (tawalk req (- m 2) 0 1 (ts-t0)))) (top (nth 3 (tawalk req (- m 2) 0 1 (ts-t0))))
                                   (tl (nth 4 (tawalk req (- m 2) 0 1 (ts-t0)))))))))

; ---- THE TABLE: a function's variadic clause is x2-req's and x2-hcls's ---------------------------

(defthm vmi-rest-at-range
  (and (integerp (vmi-rest-at ci k vmi)) (<= -1 (vmi-rest-at ci k vmi)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (integerp (vmi-rest-at ci k vmi))))
  :hints (("Goal" :induct (vmi-rest-at ci k vmi) :in-theory (disable nth))))

(defthm rest-at-clauses
  (and (equal (x2-req (vmi-clauses ci k vmi))
              (if (< (vmi-rest-at ci k vmi) 0) -1 (nfix (nth (vmi-rest-at ci k vmi) (nth 16 vmi)))))
       (equal (x2-hcls (vmi-clauses ci k vmi))
              (if (< (vmi-rest-at ci k vmi) 0)
                  nil
                (list (list (1+ (nfix (nth (vmi-rest-at ci k vmi) (nth 16 vmi)))) (nth (vmi-rest-at ci k vmi) (nth 17 vmi)))))))
  :hints (("Goal" :induct (vmi-rest-at ci k vmi) :in-theory (disable restp nth)
                  :expand ((vmi-clauses ci k vmi) (vmi-rest-at ci k vmi)))))

(defmacro r-ci (f) `(vmi-rest-ci ,f vmi))
(defmacro r-req (f) `(if (< (r-ci ,f) 0) -1 (nfix (nth (r-ci ,f) (nth 16 vmi)))))

(defthm rest-ci-prog
  (and (equal (x2-req (cdr (assoc-equal f (cdr (vmi-prog vmi))))) (r-req f))
       (equal (x2-hcls (cdr (assoc-equal f (cdr (vmi-prog vmi)))))
              (if (< (r-ci f) 0) nil (list (list (1+ (nfix (nth (r-ci f) (nth 16 vmi)))) (nth (r-ci f) (nth 17 vmi)))))))
  :hints (("Goal" :in-theory (e/d (vmi-rest-ci) (vmi-clauses-open)))))
(defthm vmi-rest-ci-range
  (and (integerp (vmi-rest-ci f vmi)) (<= -1 (vmi-rest-ci f vmi)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (integerp (vmi-rest-ci f vmi))))
  :hints (("Goal" :in-theory (enable vmi-rest-ci))))
(defthm vmi-rest-at-frame
  (implies (not (member k '(18))) (equal (vmi-rest-at ci n (update-nth k v vmi)) (vmi-rest-at ci n vmi))))
(defthm vmi-rest-ci-frame
  (implies (not (member k '(14 15 18))) (equal (vmi-rest-ci f (update-nth k v vmi)) (vmi-rest-ci f vmi)))
  :hints (("Goal" :in-theory (e/d (vmi-rest-ci) (vmi-rest-at)))))
(defthm vmi-rest-ci-not-fn
  (implies (not (natp f)) (equal (vmi-rest-ci f vmi) -1))
  :hints (("Goal" :in-theory (enable vmi-rest-ci))))
(in-theory (disable vmi-rest-ci))

; a hand-over: the variadic clause's spread arguments, and there is one
(defthm ex-apwalk-way2-req
  (implies (equal (car (ex-apwalk req fx c)) 2) (natp req))
  :rule-classes nil
  :hints (("Goal" :induct (ex-apwalk req fx c) :in-theory (enable ex-apstep ex-aplook ex-aplook-old) :expand ((ex-apwalk req fx c)))))
(defthm sk-spread-hand-req
  (implies (equal (car (sk-spread req fx v)) :hand) (natp req))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable ex-apwalk) :use ((:instance ex-apwalk-way2-req (c (sk-cur v)))))))

; ---- THE INSTRUCTION'S PARTS ----------------------------------------------------------------------

(defmacro a-m () '(nfix (vmi-w (nth 0 vmi) 1 vmi)))
(defmacro a-fb2 () '(- (nth 2 vmi) (1+ (a-m))))
(defmacro a-c () '(nth (1- (nth 2 vmi)) (nth 8 vmi)))
(defmacro a-f () '(nth (a-fb2) (nth 8 vmi)))
(defmacro a-vs () '(stk-from (a-fb2) (a-m) (nth 8 vmi)))
(defmacro a-seq () '(nth (+ (a-fb2) (a-m) -1) (nth 8 vmi)))
(defmacro a-shape ()
  '(and (<= 2 (a-m)) (equal (a-c) :apply) (clop (a-f)) (not (clop (a-seq)))))
(defmacro a-ci () '(vmi-rest-ci (clo-f (a-f)) vmi))
(defmacro a-req () '(r-req (clo-f (a-f))))
(defmacro a-ts () '(tspread (a-req) (a-m) (a-fb2) (nth 8 vmi) (nth 19 vmi)))
(defmacro a-sp () '(sk-spread (a-req) (stk-from (1+ (a-fb2)) (- (a-m) 2) (nth 8 vmi)) (a-seq)))
(defmacro a-hyps ()
  '(and (true-listp (nth 8 vmi)) (true-listp (nth 19 vmi)) (equal (len vmi) 20) (natp (nth 2 vmi))
        (equal (nth 3 vmi) 0) (<= (1+ (a-m)) (nth 2 vmi)) (not (equal (nth 3 (vmi-applyv vmi)) 2))))
; the state the spread leaves, k arguments from scratch tl: the k
; arguments and the fn above them where the first argument was
(defun a-stf (fb2 k f tl vmi)
  (update-nth 2 (+ fb2 k 1)
              (update-nth 8 (x2-put fb2 (stk-from 1 (1+ k) (update-nth (1+ k) f tl)) (nth 8 vmi))
                          (update-nth 19 (update-nth (1+ k) f tl) vmi))))
(defmacro a-st (k tl) `(a-stf (a-fb2) ,k (a-f) ,tl vmi))

; vmx2's spread is the arrays' sk-spread
(defthm x2-sp-is
  (implies (and (natp (nth 2 vmi)) (<= (1+ (a-m)) (nth 2 vmi)) (<= 2 (a-m)))
           (equal (x2-sp (a-vs) (cdr (vmi-prog vmi))) (a-sp)))
  :hints (("Goal" :in-theory (e/d (x2-sp vmi-rest-ci) (sk-spread vmi-w last butlast)))))

(defthm x2-spreads-is
  (implies (and (natp (nth 2 vmi)) (<= (1+ (a-m)) (nth 2 vmi)))
           (iff (x2-spreads :applyv (a-c) (a-vs) (cdr (vmi-prog vmi)))
                (and (a-shape) (member-equal (car (a-sp)) '(:ok :hand)))))
  :hints (("Goal" :in-theory (e/d (x2-spreads vmi-rest-ci) (sk-spread x2-sp vmi-w last butlast clop x2-sp-is)) :cases ((<= 2 (a-m))) :use x2-sp-is)))

(defthm vmi-spread-in-sticky
  (implies (equal (nth 3 vmi) 2) (equal (nth 3 (mv-nth 2 (vmi-spread-in req m fb2 vmi))) 2))
  :hints (("Goal" :in-theory (e/d (vmi-spread-in) (vmi-walk vmi-awalk vmi-consv vmi-to-tmp)))))
(defthm vmi-from-tmp-status
  (implies (or (equal (nth 3 vmi) 0) (equal (nth 3 vmi) 2))
           (or (equal (nth 3 (vmi-from-tmp j a k vmi)) 0) (equal (nth 3 (vmi-from-tmp j a k vmi)) 2)))
  :rule-classes nil
  :hints (("Goal" :induct (vmi-from-tmp j a k vmi))))
(defthm vmi-spread-out-status
  (implies (equal (nth 3 vmi) 0) (member (nth 3 (vmi-spread-out fb2 k vmi)) '(0 2)))
  :hints (("Goal" :in-theory (e/d (vmi-spread-out) (vmi-from-tmp))
                  :use ((:instance vmi-from-tmp-status (j 1) (a fb2) (k (1+ (nfix k)))
                                   (vmi (vmi-tset (1+ (nfix k)) (vmi-sreg fb2 vmi) vmi)))))))
(defthm vmi-spread-out-status-2
  (implies (and (equal (nth 3 vmi) 0) (not (equal (nth 3 (vmi-spread-out fb2 k vmi)) 0)))
           (equal (nth 3 (vmi-spread-out fb2 k vmi)) 2))
  :hints (("Goal" :use vmi-spread-out-status :in-theory (disable vmi-spread-out-status))))
(in-theory (disable vmi-spread-in vmi-spread-out tspread tspread-tl vmi-spread-in-tl vmi-spread-tl))

; THE INSTRUCTION, opened: the call on m, or the spread's call
(defthm vmi-applyv-open
  (implies (a-hyps)
           (equal (vmi-applyv vmi)
                  (if (and (a-shape) (not (equal (car (a-ts)) 1)))
                      (if (and (equal (car (a-ts)) 2) (<= 0 (a-ci)))
                          (vmi-hcall (a-ci) (cadr (a-ts)) (a-st (cadr (a-ts)) (caddr (a-ts))))
                        (vmi-call (cadr (a-ts)) (a-st (cadr (a-ts)) (caddr (a-ts)))))
                    (vmi-call (a-m) (if (a-shape) (update-nth 19 (caddr (a-ts)) vmi) vmi)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (vmi-applyp) (vmi-call vmi-hcall vmi-w clop tawalk twalk tconsv nth update-nth
                                                vmi-spread-in-tl vmi-spread-tl tspread tspread-tl sk-spread stk-from sk-cval
                                                sk-kind sk-topk sk-step))
                  :expand ((vmi-applyv vmi))
                  :cases ((equal (nth 3 (mv-nth 2 (vmi-spread-in (a-req) (a-m) (a-fb2) vmi))) 2)))))

; ---- ONE (:applyv m) IS ONE STEP OF VMX2's MACHINE ---------------------------------------

; vcs2-step there, past the stuck case: :callv's dispatch on x2's spread
(defthm applyv-vcs2
  (implies (and (vmi-at 17) (<= (1+ (c-m)) (v-sp vmi)))
           (equal (vcs2-step (vmi-prog vmi) (vmi-abs vmi))
                  (vcs2-callv (x2-prog :applyv (a-c) (a-vs) (vmi-prog vmi)) (v-pc vmi) (v-fb vmi) (a-fb2)
                              (x2-fn :applyv (a-c) (a-vs) (cdr (vmi-prog vmi))) (x2-vals :applyv (a-c) (a-vs) (cdr (vmi-prog vmi)))
                              (x2-stk :applyv (a-fb2) (a-c) (a-vs) (nth 8 vmi) (cdr (vmi-prog vmi)))
                              (vmi-ctl (v-ctop vmi) vmi))))
  :rule-classes nil
  :hints (("Goal" :in-theory (set-difference-theories (vmi-thy) '(x2-fn x2-vals x2-stk x2-spreads vcs2-callv x2-prog x2-hands)))))

(def-refines-if applyv-stuck vmi-applyv 17 (< (v-sp vmi) (1+ (c-m))))

; the hand-over's call: the clause's entry, its frame the arguments
(defthm vmi-hcall-abs
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (equal (v-status vmi) 0) (natp m) (<= (1+ m) (v-sp vmi))
                (not (equal (v-status (vmi-hcall ci m vmi)) 2)))
           (equal (vmi-abs (vmi-hcall ci m vmi))
                  (list (nfix (nth (nfix ci) (nth 17 vmi))) (- (v-sp vmi) (1+ m)) (v-sp vmi) (nth 8 vmi)
                        (cons (list (1+ (v-pc vmi)) (v-fb vmi)) (vmi-ctl (v-ctop vmi) vmi)))))
  :hints (("Goal" :in-theory (union-theories '(vmi-hcall) (vmi-thy)))))
(defthm vcs2-callv-hand
  (implies (and (clop f) (natp req) (equal (len vs) (1+ req)))
           (equal (vcs2-callv (cons code (cons (cons (clo-f f) (list (list (1+ req) ent))) fns)) pc fb fb2 f vs stk ctl)
                  (list (nfix ent) fb2 (+ fb2 (len vs) 1) stk (cons (list (1+ pc) fb) ctl)))))

; the states the spread leaves keep the shape and the invariant
(defthm vmi-ok-spread-states
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (natp sp) (true-listp stk) (true-listp tmp))
           (and (vmi-shape (update-nth 2 sp (update-nth 8 stk (update-nth 19 tmp vmi))))
                (vmi-ok (update-nth 2 sp (update-nth 8 stk (update-nth 19 tmp vmi))))
                (vmi-shape (update-nth 19 tmp vmi)) (vmi-ok (update-nth 19 tmp vmi)))))

; the spread's stack: the arguments, the fn above them
(defthm stk-from-1-put-top
  (implies (natp k) (equal (stk-from 1 (1+ k) (update-nth (1+ k) f tl)) (append (stk-from 1 k tl) (list f))))
  :hints (("Goal" :in-theory (disable stk-from stk-from-snoc update-nth stk-from-update-outside)
                  :use ((:instance stk-from-snoc (a 1) (l (update-nth (1+ k) f tl)))
                        (:instance stk-from-update-outside (a 1) (j (1+ k)) (x f) (l tl))))))
(defthm applyv-no-spread
  (implies (and (natp (nth 2 vmi)) (<= (1+ (a-m)) (nth 2 vmi)) (true-listp (nth 19 vmi))
                (not (and (a-shape) (not (equal (car (a-ts)) 1)))))
           (not (x2-spreads :applyv (a-c) (a-vs) (cdr (vmi-prog vmi)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)
                  :use (x2-spreads-is (:instance tspread-is (req (a-req)) (m (a-m)) (fb2 (a-fb2)) (stk (nth 8 vmi)) (tl (nth 19 vmi)))))
          ("Goal'" :in-theory (union-theories '(sp-code natp nfix member-equal) (theory 'minimal-theory)))))
(defmacro a-rhs () '(let ((m (a-m))) (call-rhs)))
(defthm applyv-vcs2-plain
  (implies (and (vmi-at 17) (<= (1+ (c-m)) (v-sp vmi)) (not (x2-spreads :applyv (a-c) (a-vs) (cdr (vmi-prog vmi)))))
           (equal (vcs2-step (vmi-prog vmi) (vmi-abs vmi)) (a-rhs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(x2-prog x2-hands x2-fn x2-vals x2-stk v-sp v-pc) (theory 'minimal-theory))
                  :use applyv-vcs2)))
(defthm applyv-call-tmp
  (implies (and (vmi-at 17) (<= (1+ (a-m)) (nth 2 vmi)) (true-listp tl)
                (not (equal (v-status (vmi-call (a-m) (update-nth 19 tl vmi))) 2)))
           (equal (vmi-abs (vmi-call (a-m) (update-nth 19 tl vmi))) (a-rhs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable vmi-call vmi-abs-is vcs2-callv vmi-shape vmi-ok vmi-call-refines clop)
                  :use ((:instance vmi-call-refines (m (a-m)) (vmi (update-nth 19 tl vmi)))))))
(defthm applyv-plain
  (implies (and (a-hyps) (vmi-shape vmi) (vmi-ok vmi) (equal (vmi-w (v-pc vmi) 0 vmi) 17)
                (not (and (a-shape) (not (equal (car (a-ts)) 1)))))
           (equal (vmi-abs (vmi-applyv vmi)) (vcs2-step (vmi-prog vmi) (vmi-abs vmi))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
                  :in-theory (union-theories '(v-sp v-pc v-status natp nfix) (theory 'minimal-theory))
                  :use (vmi-applyv-open applyv-no-spread applyv-vcs2-plain (:instance applyv-call-tmp (tl (caddr (a-ts))))
                        (:instance vmi-call-refines (m (a-m)))
                        (:instance tspread-is (req (a-req)) (m (a-m)) (fb2 (a-fb2)) (stk (nth 8 vmi)) (tl (nth 19 vmi)))))))

; ---- THE SPREADS CALL ---------------------------------------------------------------------------
(defmacro a-st2 () '(a-st (cadr (a-ts)) (caddr (a-ts))))
(defmacro a-stk2 () '(x2-put (a-fb2) (append (cadr (a-sp)) (list (a-f))) (nth 8 vmi)))
; vmx2 spreads: the call on the spread, the variadic clause's as a fixed one on a hand-over
(defthm applyv-spreads
  (implies (and (natp (nth 2 vmi)) (<= (1+ (a-m)) (nth 2 vmi)) (true-listp (nth 19 vmi)) (a-shape) (not (equal (car (a-ts)) 1)))
           (and (x2-spreads :applyv (a-c) (a-vs) (cdr (vmi-prog vmi)))
                (equal (x2-fn :applyv (a-c) (a-vs) (cdr (vmi-prog vmi))) (a-f))
                (equal (x2-vals :applyv (a-c) (a-vs) (cdr (vmi-prog vmi))) (cadr (a-sp)))
                (equal (x2-stk :applyv (a-fb2) (a-c) (a-vs) (nth 8 vmi) (cdr (vmi-prog vmi))) (a-stk2))
                (equal (x2-prog :applyv (a-c) (a-vs) (vmi-prog vmi))
                       (if (equal (car (a-ts)) 2)
                           (cons (car (vmi-prog vmi))
                                 (cons (cons (clo-f (a-f)) (x2-hcls (cdr (assoc-equal (clo-f (a-f)) (cdr (vmi-prog vmi))))))
                                       (cdr (vmi-prog vmi))))
                         (vmi-prog vmi)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (x2-fn x2-vals x2-stk x2-prog x2-hands)
                                  (x2-spreads x2-sp sk-spread tspread clop vmi-w vmi-applyv nth update-nth tspread-is x2-spreads-is x2-sp-is rest-ci-prog vmi-prog-clauses))
                  :use (x2-spreads-is x2-sp-is
                        (:instance tspread-is (req (a-req)) (m (a-m)) (fb2 (a-fb2)) (stk (nth 8 vmi)) (tl (nth 19 vmi)))))))
(defmacro st-hyps2 ()
  '(and (vmi-shape vmi) (vmi-ok vmi) (equal (nth 3 vmi) 0) (natp (nth 2 vmi)) (<= (1+ (a-m)) (nth 2 vmi))
        (true-listp (nth 8 vmi)) (true-listp (nth 19 vmi))
        (natp k) (true-listp tl) (equal (stk-from 1 k tl) vals)))
(defthm a-st-call
  (implies (and (st-hyps2) (not (equal (v-status (vmi-call k (a-st k tl))) 2)))
           (equal (vmi-abs (vmi-call k (a-st k tl)))
                  (vcs2-callv (vmi-prog vmi) (v-pc vmi) (v-fb vmi) (a-fb2) (a-f) vals
                              (x2-put (a-fb2) (append vals (list (a-f))) (nth 8 vmi)) (vmi-ctl (v-ctop vmi) vmi))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable vmi-call vmi-abs-is vcs2-callv vmi-shape vmi-ok vmi-call-refines clop vmi-w stk-from update-nth)
                  :use ((:instance vmi-call-refines (m k) (vmi (a-st k tl)))))))
(defthm a-st-hcall
  (implies (and (st-hyps2) (not (equal (v-status (vmi-hcall ci k (a-st k tl))) 2)))
           (equal (vmi-abs (vmi-hcall ci k (a-st k tl)))
                  (list (nfix (nth (nfix ci) (nth 17 vmi))) (a-fb2) (+ (a-fb2) k 1) (x2-put (a-fb2) (append vals (list (a-f))) (nth 8 vmi))
                        (cons (list (1+ (v-pc vmi)) (v-fb vmi)) (vmi-ctl (v-ctop vmi) vmi)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable vmi-hcall vmi-abs-is vmi-shape vmi-ok vmi-hcall-abs clop vmi-w stk-from update-nth)
                  :use ((:instance vmi-hcall-abs (m k) (vmi (a-st k tl)))))))
(defthm take-len-b (equal (len (take n l)) (nfix n)))
(defthm ex-apwalk-way2-len
  (implies (equal (car (ex-apwalk req fx c)) 2) (equal (len (nth 1 (ex-apwalk req fx c))) (nfix req)))
  :hints (("Goal" :induct (ex-apwalk req fx c) :in-theory (enable ex-apstep ex-aplook ex-aplook-old) :expand ((ex-apwalk req fx c)))))
(defthm sk-spread-hand-len
  (implies (equal (car (sk-spread req fx v)) :hand) (equal (len (cadr (sk-spread req fx v))) (1+ (nfix req))))
  :hints (("Goal" :in-theory (e/d (sk-spread) (ex-apwalk)))))
(defmacro sp-thy2 ()
  '(disable a-stf x2-put vmi-applyv vmi-call vmi-hcall vcs2-step vcs2-callv x2-spreads x2-fn x2-vals x2-stk x2-prog x2-hands x2-hcls
            tspread sk-spread sk-cval vmi-shape vmi-ok nth update-nth vmi-w clop vmi-rest-ci stk-from vmi-abs-is
            vmi-applyv-open tspread-is x2-spreads-is x2-sp-is rest-ci-prog vmi-prog-clauses vmi-call-refines vmi-hcall-abs))
(defthm applyv-spread-ok
  (implies (and (a-hyps) (vmi-shape vmi) (vmi-ok vmi) (equal (vmi-w (v-pc vmi) 0 vmi) 17)
                (a-shape) (equal (car (a-ts)) 0))
           (equal (vmi-abs (vmi-applyv vmi)) (vcs2-step (vmi-prog vmi) (vmi-abs vmi))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (sp-thy2)
                  :use (vmi-applyv-open applyv-vcs2 applyv-spreads
                        (:instance tspread-is (req (a-req)) (m (a-m)) (fb2 (a-fb2)) (stk (nth 8 vmi)) (tl (nth 19 vmi)))
                        (:instance a-st-call (k (cadr (a-ts))) (tl (caddr (a-ts))) (vals (cadr (a-sp))))))))
(defthm applyv-spread-hand
  (implies (and (a-hyps) (vmi-shape vmi) (vmi-ok vmi) (equal (vmi-w (v-pc vmi) 0 vmi) 17)
                (a-shape) (equal (car (a-ts)) 2))
           (equal (vmi-abs (vmi-applyv vmi)) (vcs2-step (vmi-prog vmi) (vmi-abs vmi))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (sp-thy2)
                  :use (vmi-applyv-open applyv-vcs2 applyv-spreads (:instance rest-ci-prog (f (clo-f (a-f))))
                        (:instance tspread-is (req (a-req)) (m (a-m)) (fb2 (a-fb2)) (stk (nth 8 vmi)) (tl (nth 19 vmi)))
                        (:instance sk-spread-hand-req (req (a-req)) (fx (stk-from (1+ (a-fb2)) (- (a-m) 2) (nth 8 vmi))) (v (a-seq)))
                        (:instance sk-spread-hand-len (req (a-req)) (fx (stk-from (1+ (a-fb2)) (- (a-m) 2) (nth 8 vmi))) (v (a-seq)))
                        (:instance a-st-hcall (ci (a-ci)) (k (cadr (a-ts))) (tl (caddr (a-ts))) (vals (cadr (a-sp))))
                        (:instance vcs2-callv-hand (f (a-f)) (req (nfix (nth (a-ci) (nth 16 vmi)))) (vs (cadr (a-sp)))
                                   (code (car (vmi-prog vmi))) (ent (nth (a-ci) (nth 17 vmi))) (fns (cdr (vmi-prog vmi)))
                                   (pc (v-pc vmi)) (fb (v-fb vmi)) (fb2 (a-fb2)) (stk (a-stk2)) (ctl (vmi-ctl (v-ctop vmi) vmi)))))))

(def-refines vmi-ret-refines vmi-ret 11)
(def-refines vmi-recur-refines vmi-recur 12)
(def-refines vmi-prim-refines vmi-prim 13)
(def-refines vmi-throw-refines vmi-throw 14)
(def-refines vmi-try-refines vmi-try 15)
(def-refines vmi-endtry-refines vmi-endtry 16)

(defthm tspread-car
  (or (equal (car (tspread req m fb2 stk tl)) 0) (equal (car (tspread req m fb2 stk tl)) 1) (equal (car (tspread req m fb2 stk tl)) 2))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (tspread tspread-tl) (tawalk twalk tconsv)))))

(defthm vmi-applyv-refines
  (implies (and (vmi-at 17) (not (equal (v-status (vmi-applyv vmi)) 2)))
           (equal (vmi-abs (vmi-applyv vmi)) (vcs2-step (vmi-prog vmi) (vmi-abs vmi))))
  :hints (("Goal" :in-theory (union-theories '(vmi-shape vmi-ok v-sp v-pc v-status natp nfix) (theory 'minimal-theory))
                  :use (applyv-stuck applyv-plain applyv-spread-ok applyv-spread-hand
                        (:instance tspread-car (req (a-req)) (m (a-m)) (fb2 (a-fb2)) (stk (nth 8 vmi)) (tl (nth 19 vmi)))))))

; ---- ONE STEP ------------------------------------------------------------------------------

; anything else -- an opcode outside 1..16, or past the code -- is stuck
; in both: vmx2 reads no instruction there
(defthm vmi-other-refines
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (equal (v-status vmi) 0)
                (not (member (vmi-w (v-pc vmi) 0 vmi) '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17))))
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
                                               vmi-prim-refines vmi-throw-refines vmi-try-refines vmi-endtry-refines
                                               vmi-applyv-refines)
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

; the call, at any count, a path at a time, and the hand-over's: the frame record pushed
(defthm vmi-push-rec-tmp (equal (nth 19 (vmi-push-rec kind a b c vmi)) (nth 19 vmi))
  :hints (("Goal" :in-theory (enable vmi-push-rec))))
(defmacro def-call-keeps-if (name cond)
  `(defthm ,name
     (implies (and (vmi-shape vmi) (vmi-ok vmi) (equal (v-status vmi) 0) (natp m) ,cond (not (equal (v-status (vmi-call m vmi)) 2)))
              (keeps (vmi-call m vmi)))
     :rule-classes nil
     :hints (("Goal" :in-theory (union-theories '(vmi-call) (set-difference-theories (vmi-thy) '(restp)))))))
(def-call-keeps-if call-keeps-stuck (< (v-sp vmi) (1+ m)))
(def-call-keeps-if call-keeps-not-fn (and (<= (1+ m) (v-sp vmi)) (not (clop (c-c)))))
(def-call-keeps-if call-keeps-arity (and (<= (1+ m) (v-sp vmi)) (clop (c-c)) (< (m-ci) 0)))
(def-call-keeps-if call-keeps-fixed (and (<= (1+ m) (v-sp vmi)) (clop (c-c)) (<= 0 (m-ci)) (not (equal (nth (m-ci) (nth 18 vmi)) 1))))
(def-call-keeps-if call-keeps-rest (and (<= (1+ m) (v-sp vmi)) (clop (c-c)) (<= 0 (m-ci)) (equal (nth (m-ci) (nth 18 vmi)) 1)))
(defthm vmi-call-nfix (equal (vmi-call (nfix m) vmi) (vmi-call m vmi)) :rule-classes nil
  :hints (("Goal" :in-theory (enable vmi-call))))
(defthm vmi-call-keeps
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (equal (v-status vmi) 0) (not (equal (v-status (vmi-call m vmi)) 2)))
           (keeps (vmi-call m vmi)))
  :hints (("Goal" :in-theory (union-theories '(natp nfix) (theory 'minimal-theory))
                  :use (vmi-call-nfix (:instance call-keeps-stuck (m (nfix m))) (:instance call-keeps-not-fn (m (nfix m)))
                        (:instance call-keeps-arity (m (nfix m))) (:instance call-keeps-fixed (m (nfix m))) (:instance call-keeps-rest (m (nfix m)))))))
(defthm vmi-hcall-keeps
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (equal (v-status vmi) 0) (natp m) (<= (1+ m) (v-sp vmi)) (natp ci)
                (not (equal (v-status (vmi-hcall ci m vmi)) 2)))
           (keeps (vmi-hcall ci m vmi)))
  :hints (("Goal" :in-theory (union-theories '(vmi-hcall) (vmi-thy)))))

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

; (:applyv m) keeps them: the call on m, or the call (or hand-over's) on
; the spread
(defthm a-stf-keeps
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (natp fb2) (natp k) (true-listp tl) (true-listp (nth 8 vmi)))
           (and (vmi-shape (a-stf fb2 k f tl vmi)) (vmi-ok (a-stf fb2 k f tl vmi))
                (equal (vmi-prog (a-stf fb2 k f tl vmi)) (vmi-prog vmi)) (equal (nth 3 (a-stf fb2 k f tl vmi)) (nth 3 vmi))))
  :hints (("Goal" :in-theory (e/d (a-stf) (vmi-shape vmi-ok update-nth x2-put stk-from)))))
(defthm a-stf-sp (equal (nth 2 (a-stf fb2 k f tl vmi)) (+ fb2 k 1)))
(defthm applyv-keeps-plain
  (implies (and (a-hyps) (vmi-shape vmi) (vmi-ok vmi) (not (and (a-shape) (not (equal (car (a-ts)) 1)))))
           (keeps (vmi-applyv vmi)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (sp-thy2)
                  :use (vmi-applyv-open (:instance vmi-call-keeps (m (a-m)))
                        (:instance tspread-is (req (a-req)) (m (a-m)) (fb2 (a-fb2)) (stk (nth 8 vmi)) (tl (nth 19 vmi)))
                        (:instance vmi-call-keeps (m (a-m)) (vmi (update-nth 19 (caddr (a-ts)) vmi)))))))
(defthm applyv-keeps-spread
  (implies (and (a-hyps) (vmi-shape vmi) (vmi-ok vmi) (a-shape) (not (equal (car (a-ts)) 1)))
           (keeps (vmi-applyv vmi)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (sp-thy2)
                  :use (vmi-applyv-open
                        (:instance tspread-is (req (a-req)) (m (a-m)) (fb2 (a-fb2)) (stk (nth 8 vmi)) (tl (nth 19 vmi)))
                        (:instance a-stf-keeps (fb2 (a-fb2)) (k (cadr (a-ts))) (f (a-f)) (tl (caddr (a-ts))))
                        (:instance vmi-call-keeps (m (cadr (a-ts))) (vmi (a-st (cadr (a-ts)) (caddr (a-ts)))))
                        (:instance vmi-hcall-keeps (ci (a-ci)) (m (cadr (a-ts))) (vmi (a-st (cadr (a-ts)) (caddr (a-ts)))))))))
(defthm applyv-keeps-stuck
  (implies (and (vmi-at 17) (< (v-sp vmi) (1+ (c-m)))) (keeps (vmi-applyv vmi)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable vmi-applyv vmi-call vmi-hcall vmi-spread-in vmi-spread-out) :expand ((vmi-applyv vmi)))))
(defthm vmi-applyv-keeps
  (implies (and (vmi-at 17) (not (equal (v-status (vmi-applyv vmi)) 2))) (keeps (vmi-applyv vmi)))
  :hints (("Goal" :in-theory (union-theories '(vmi-shape vmi-ok v-sp v-pc v-status natp nfix) (theory 'minimal-theory))
                  :use (applyv-keeps-stuck applyv-keeps-plain applyv-keeps-spread))))

(defthm vmi-step-keeps
  (implies (and (vmi-shape vmi) (vmi-ok vmi) (not (equal (v-status (vmi-step vmi)) 2)))
           (keeps (vmi-step vmi)))
  :hints (("Goal" :in-theory (union-theories '(vmi-step member-equal
                                               vmi-push-keeps vmi-load-keeps vmi-add-keeps vmi-lt-keeps
                                               vmi-slide-keeps vmi-jmpf-keeps vmi-jmp-keeps vmi-mkclo-keeps
                                               vmi-capt-keeps vmi-callv-keeps vmi-ret-keeps vmi-recur-keeps
                                               vmi-prim-keeps vmi-throw-keeps vmi-try-keeps vmi-endtry-keeps
                                               vmi-applyv-keeps)
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
          ("Goal'" :in-theory (e/d (vcs2-program) (s2clk mx2)))))

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
      (15 (list :try a b)) (16 (list :endtry)) (17 (list :applyv a))
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
         (vmi (resize-v-cln nc vmi)) (vmi (resize-v-clent nc vmi)) (vmi (resize-v-clrest nc vmi)))
    (resize-v-tmp nstk vmi)))

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
             (and (true-listp r) (equal (len r) 20) (true-listp (nth 19 r))
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
  (implies (and (true-listp vmi) (equal (len vmi) 20))
           (let ((g (lp-regs vmi)))
             (and (true-listp g) (equal (len g) 20)
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
