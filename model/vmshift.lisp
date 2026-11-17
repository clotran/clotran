; DROPPING A SCOPE POSITION (gap B, the sl-0 clause): a fn's body
; translated in a scope without position np (the self slot, vm_clause's
; sl 0) is the shifted form of its translation with it, so long as the
; latter never reads np. x2-sh np shifts every (:local p) of a vmx2 term
; at or above np down by one (mx2's grammar: a :const, a template, a
; :mkgrp's shape are data and untouched); x2-rd np asks whether a term
; reads (:local np). ex-drop np cm is cm without its position np.

(in-package "ACL2")

(include-book "exec-vmtr")

(defun ex-drop (n l)
  (cond ((atom l) l) ((zp n) (cdr l)) (t (cons (car l) (ex-drop (1- n) (cdr l))))))
(defun x2-shp (np p) (if (< (nfix p) (nfix np)) (nfix p) (1- (nfix p))))

(mutual-recursion
 (defun x2-sh (np e)
   (declare (xargs :measure (acl2-count e)))
   (if (atom e)
       e
     (case (car e)
       (:local (list :local (x2-shp np (cadr e))))
       (:if (list :if (x2-sh np (cadr e)) (x2-sh np (caddr e)) (x2-sh np (cadddr e))))
       ((:let :add :lt :try) (list (car e) (x2-sh np (cadr e)) (x2-sh np (caddr e))))
       ((:mkclo :mkgrp :prim) (list* (car e) (cadr e) (x2-sh-args np (cddr e))))
       ((:callv :applyv) (list* (car e) (x2-sh np (cadr e)) (x2-sh-args np (cddr e))))
       (:loop (list :loop (x2-sh-args np (cadr e)) (x2-sh np (caddr e))))
       (:recur (cons :recur (x2-sh-args np (cdr e))))
       (:throw (list :throw (x2-sh np (cadr e))))
       (otherwise e))))
 (defun x2-sh-args (np es)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) es (cons (x2-sh np (car es)) (x2-sh-args np (cdr es))))))

(mutual-recursion
 (defun x2-rd (np e)
   (declare (xargs :measure (acl2-count e)))
   (if (atom e)
       nil
     (case (car e)
       (:local (equal (nfix (cadr e)) (nfix np)))
       (:if (or (x2-rd np (cadr e)) (x2-rd np (caddr e)) (x2-rd np (cadddr e))))
       ((:let :add :lt :try) (or (x2-rd np (cadr e)) (x2-rd np (caddr e))))
       ((:mkclo :mkgrp :prim :recur) (x2-rd-args np (if (eq (car e) :recur) (cdr e) (cddr e))))
       ((:callv :applyv) (or (x2-rd np (cadr e)) (x2-rd-args np (cddr e))))
       (:loop (or (x2-rd-args np (cadr e)) (x2-rd np (caddr e))))
       (:throw (x2-rd np (cadr e)))
       (otherwise nil))))
 (defun x2-rd-args (np es)
   (declare (xargs :measure (acl2-count es)))
   (if (atom es) nil (or (x2-rd np (car es)) (x2-rd-args np (cdr es))))))

; ---- the scope ----------------------------------------------------------
(defthm ex-pos-drop
  (implies (not (equal (ex-pos s cm) (nfix np)))
           (equal (ex-pos s (ex-drop np cm)) (x2-shp np (ex-pos s cm)))))
(defthm ex-len-drop
  (implies (< (nfix np) (len cm)) (equal (len (ex-drop np cm)) (1- (len cm)))))
(defthm ex-drop-blank (equal (ex-drop n (ex-blank ls cm)) (ex-blank ls (ex-drop n cm))))
(defthm ex-drop-append
  (implies (< (nfix n) (len a)) (equal (ex-drop n (append a b)) (append (ex-drop n a) b))))
(defun ex-nils (l) (if (atom l) l (cons nil (ex-nils (cdr l)))))
(defthm ex-blank-all (implies (subsetp-equal l ls) (equal (ex-blank ls l) (ex-nils l))))
(defthm ex-drop-nils (equal (ex-drop n (ex-nils l)) (ex-nils (ex-drop n l))))
(defthm ex-drop-sub (subsetp-equal (ex-drop n l) l))
(defthm ex-drop-blank-self
  (equal (ex-drop n (ex-blank cm cm)) (ex-blank (ex-drop n cm) (ex-drop n cm))))
(in-theory (disable ex-drop-blank-self))

; ---- the helpers ---------------------------------------------------------
(defthm x2-sh-args-append (equal (x2-sh-args np (append a b)) (append (x2-sh-args np a) (x2-sh-args np b))))
(defthm x2-rd-args-append (equal (x2-rd-args np (append a b)) (or (x2-rd-args np a) (x2-rd-args np b))))
(defthm ex-locals-drop
  (implies (not (x2-rd-args np (ex-locals ls cm)))
           (equal (x2-sh-args np (ex-locals ls cm)) (ex-locals ls (ex-drop np cm)))))
(defthm ex-lfcaps-drop
  (implies (not (x2-rd-args np (ex-lfcaps os s n cm)))
           (equal (x2-sh-args np (ex-lfcaps os s n cm)) (ex-lfcaps os s n (ex-drop np cm)))))
(defthm ex-lfargs-drop
  (implies (not (x2-rd-args np (ex-lfargs e j cm)))
           (equal (x2-sh-args np (ex-lfargs e j cm)) (ex-lfargs e j (ex-drop np cm))))
  :hints (("Goal" :induct (ex-lfargs e j cm) :in-theory (disable ex-lfos ex-lfcaps))))
(defthm ex-lfargs-end (implies (<= (ex-i2 e) (nfix j)) (equal (ex-lfargs e j cm) nil)))
(defthm ex-trlf-rd
  (equal (x2-rd np (ex-trlf e j cm x))
         (or (and (< (nfix j) (ex-i2 e)) (x2-rd-args np (ex-lfargs e 0 cm))) (x2-rd np x)))
  :hints (("Goal" :induct (ex-trlf e j cm x) :in-theory (disable ex-lfargs ex-lfshape))))
(defthm ex-trlf-sh
  (implies (not (x2-rd-args np (ex-lfargs e 0 cm)))
           (equal (x2-sh np (ex-trlf e j cm x)) (ex-trlf e j (ex-drop np cm) (x2-sh np x))))
  :hints (("Goal" :induct (ex-trlf e j cm x) :in-theory (disable ex-lfargs ex-lfshape))))
(defthm ex-trh-sh (equal (x2-sh np (ex-trh cs hs p)) (ex-trh cs (x2-sh-args np hs) (x2-shp np p))))
(defthm ex-trh-rd
  (implies (equal (len hs) (len cs))
           (equal (x2-rd np (ex-trh cs hs p)) (or (x2-rd-args np hs) (equal (nfix p) (nfix np))))))
(defthm ex-trcs-sh
  (equal (x2-sh np (ex-trcs ct ts d p)) (ex-trcs ct (x2-sh-args np ts) (x2-sh np d) (x2-shp np p)))
  :hints (("Goal" :induct (ex-trcs ct ts d p) :in-theory (e/d (ex-trcs) (x2-shp)))))
(defthm ex-trcs-rd
  (implies (equal (len ts) (len ct))
           (equal (x2-rd np (ex-trcs ct ts d p))
                  (or (x2-rd-args np ts) (x2-rd np d) (and (consp ct) (equal (nfix p) (nfix np))))))
  :hints (("Goal" :induct (ex-trcs ct ts d p) :in-theory (enable ex-trcs))))
(defun ex-csi (e i)
  (declare (xargs :measure (nfix (- (len (ex-c e)) (nfix i)))))
  (if (< (nfix i) (len (ex-c e))) (ex-csi e (1+ (nfix i))) i))
(defthm ex-tr-cs-len
  (implies (consp e) (equal (len (ex-tr :cs e i cm)) (nfix (- (len (ex-c e)) (nfix i)))))
  :hints (("Goal" :induct (ex-csi e i) :expand ((ex-tr :cs e i cm)))))
(defthm ex-tr-ct-len
  (implies (consp e) (equal (len (ex-tr :ct e i cm)) (nfix (- (len (ex-c e)) (nfix i)))))
  :hints (("Goal" :induct (ex-csi e i) :expand ((ex-tr :ct e i cm)))))

; ---- LEMMA (2): the translation without position np ---------------------
(defun ex-trlst (flg) (member-eq flg '(:lin :rec :call :coll :cs :ct)))
(defun ex-trsh (flg np x) (if (ex-trlst flg) (x2-sh-args np x) (x2-sh np x)))
(defun ex-trrd (flg np x) (if (ex-trlst flg) (x2-rd-args np x) (x2-rd np x)))

; a call whose head is read at translation (exec-vmtr ex-pcall): its items read no position
(defthm ex-pcall-sh-rd
  (implies (ex-pcall e)
           (and (equal (x2-sh np (cons (ex-pop e) (append (ex-phd e) x))) (cons (ex-pop e) (append (ex-phd e) (x2-sh-args np x))))
                (equal (x2-rd np (cons (ex-pop e) (append (ex-phd e) x))) (x2-rd-args np x))))
  :hints (("Goal" :in-theory (enable ex-pcall ex-pk ex-pop ex-phd)
                  :expand ((:free (x y) (x2-sh-args np (cons x y))) (:free (x y) (x2-rd-args np (cons x y)))
                           (:free (x) (x2-sh np (cons :callv x))) (:free (x) (x2-rd np (cons :callv x)))
                           (:free (x) (x2-sh np (cons :prim x))) (:free (x) (x2-rd np (cons :prim x)))))))
(defthm ex-tr-drop-flag
  (implies (and (natp np) (< np (len cm)) (not (ex-trrd flg np (ex-tr flg e i cm))))
           (equal (ex-trsh flg np (ex-tr flg e i cm)) (ex-tr flg e i (ex-drop np cm))))
  :rule-classes nil
  :hints (("Goal" :induct (ex-tr flg e i cm)
                  :in-theory (e/d (ex-drop-blank-self ex-trtry ex-trfin)
                                  (ex-kid-of ex-lffns ex-lfok ex-trlf ex-lfargs ex-lfshape ex-trh ex-trcs ex-clr ex-lind
                                   ex-slots ex-blank ex-locals ex-drop))
                  :expand ((:free (flg cm) (ex-tr flg e i cm))))))

(defthm ex-tr-drop
  (implies (and (natp np) (< np (len cm)) (not (x2-rd np (ex-tr :m e i cm))))
           (equal (x2-sh np (ex-tr :m e i cm)) (ex-tr :m e i (ex-drop np cm))))
  :hints (("Goal" :use ((:instance ex-tr-drop-flag (flg :m))))))

; a fn's clause: its body's scope ex-fbcm is the parameters, the captures
; and the self slot last, at position ex-fnp; without it, ex-fbcm0 (vm_clause's
; sl 0 scope), and the loop's ex-fcmb likewise
(defun ex-fnp (tm ar) (+ (ex-anp ar) (len (ex-inners (nth 2 tm)))))
(defun ex-fbcm0 (tm ar) (append (ex-fparams ar) (true-list-fix (ex-inners (nth 2 tm)))))
(defun ex-fcmb0 (tm ar) (append (ex-blank (ex-lsl (ex-flp ar)) (ex-fbcm0 tm ar)) (ex-lsl (ex-flp ar))))
(defthm ex-drop-append-past
  (implies (and (natp n) (<= (len a) n)) (equal (ex-drop n (append a b)) (append a (ex-drop (- n (len a)) b))))
  :hints (("Goal" :induct (ex-drop n a))))
(defthm ex-drop-last (equal (ex-drop (len a) (append a (list y))) (true-list-fix a)))
(defthm ex-len-fbcm-np (equal (len (ex-fbcm tm ar)) (1+ (ex-fnp tm ar))))
(defthm ex-len-fcmb-np (< (ex-fnp tm ar) (len (ex-fcmb tm ar))) :rule-classes :linear
  :hints (("Goal" :in-theory (disable ex-fnp ex-fbcm ex-lsl))))
(defthm ex-fbcm-drop (equal (ex-drop (ex-fnp tm ar) (ex-fbcm tm ar)) (ex-fbcm0 tm ar))
  :hints (("Goal" :in-theory (disable ex-drop-append))))
(defthm ex-fcmb-drop (equal (ex-drop (ex-fnp tm ar) (ex-fcmb tm ar)) (ex-fcmb0 tm ar))
  :hints (("Goal" :in-theory (disable ex-fnp ex-fbcm0 ex-fbcm ex-lsl))))

; LEMMA (2) at the clause: a body that never reads the self slot,
; translated without it, is the shifted translation with it
(defthm ex-fbody-drop
  (implies (not (x2-rd (ex-fnp tm ar) (ex-tr :m (ex-abody ar) 0 (ex-fbcm tm ar))))
           (equal (x2-sh (ex-fnp tm ar) (ex-tr :m (ex-abody ar) 0 (ex-fbcm tm ar)))
                  (ex-tr :m (ex-abody ar) 0 (ex-fbcm0 tm ar))))
  :hints (("Goal" :in-theory (disable ex-fnp ex-fbcm0 ex-fbcm ex-tr-drop)
                  :use ((:instance ex-tr-drop (np (ex-fnp tm ar)) (e (ex-abody ar)) (i 0) (cm (ex-fbcm tm ar)))))))
(defthm ex-floop-drop
  (implies (not (x2-rd (ex-fnp tm ar) (ex-tr :m (ex-abody ar) 0 (ex-fcmb tm ar))))
           (equal (x2-sh (ex-fnp tm ar) (ex-tr :m (ex-abody ar) 0 (ex-fcmb tm ar)))
                  (ex-tr :m (ex-abody ar) 0 (ex-fcmb0 tm ar))))
  :hints (("Goal" :in-theory (disable ex-fnp ex-fbcm0 ex-fbcm ex-fcmb0 ex-tr-drop ex-lsl)
                  :use ((:instance ex-tr-drop (np (ex-fnp tm ar)) (e (ex-abody ar)) (i 0) (cm (ex-fcmb tm ar)))))))

; ---- COST: x2-sh and x2-rd each visit a term's nodes once -- one step a
; node, at most 4n + 1 for a term of acl2-count n; ex-drop at most n + 1
(defun x2-walk-steps (flg e)
  (declare (xargs :measure (acl2-count e)))
  (cond ((atom e) 1)
        (flg (+ 1 (x2-walk-steps nil (car e)) (x2-walk-steps t (cdr e))))
        (t (case (car e)
             (:if (+ 1 (x2-walk-steps nil (cadr e)) (x2-walk-steps nil (caddr e)) (x2-walk-steps nil (cadddr e))))
             ((:let :add :lt :try) (+ 1 (x2-walk-steps nil (cadr e)) (x2-walk-steps nil (caddr e))))
             ((:mkclo :mkgrp :prim) (+ 1 (x2-walk-steps t (cddr e))))
             ((:callv :applyv) (+ 1 (x2-walk-steps nil (cadr e)) (x2-walk-steps t (cddr e))))
             (:loop (+ 1 (x2-walk-steps t (cadr e)) (x2-walk-steps nil (caddr e))))
             (:recur (+ 1 (x2-walk-steps t (cdr e))))
             (:throw (+ 1 (x2-walk-steps nil (cadr e))))
             (otherwise 1)))))
(defthm x2-walk-steps-bound (<= (x2-walk-steps flg e) (+ 1 (* 4 (acl2-count e)))) :rule-classes :linear)
(defun ex-drop-steps (n l) (if (or (atom l) (zp n)) 1 (1+ (ex-drop-steps (1- n) (cdr l)))))
(defthm ex-drop-steps-bound (<= (ex-drop-steps n l) (1+ (nfix n))) :rule-classes :linear)

; ---- LEMMA (1): the frame without position np ---------------------------
; mx2 answers the same of a term that never reads np under a ++ (x) ++ b
; as of its shifted form under a ++ b, np = (len a): the self slot's value
; x is never asked, and every other position moves down past it.
(local (include-book "arithmetic-5/top" :dir :system))
(defthm x2-sh-nth
  (implies (and (natp p) (not (equal p (len a))))
           (equal (nth (x2-shp (len a) p) (append a b)) (nth p (append a (cons x b))))))
(set-irrelevant-formals-ok t)
(defun x2-dp-ind (flg e a x b vs caps defs fuel)
  (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) (if (equal flg :loop) 0 1)))
                  :well-founded-relation o< :verify-guards nil))
  (let ((env (append a (cons x b))))
    (case flg
      (:args (if (atom e) nil (list (x2-dp-ind :m (car e) a x b vs caps defs fuel) (x2-dp-ind :args (cdr e) a x b vs caps defs fuel))))
      (:loop (if (not (consp e))
                 nil
               (let ((r (mx2 (caddr e) (append env vs) caps defs fuel)))
                 (if (zp fuel)
                     (x2-dp-ind :m (caddr e) a x (append b vs) nil caps defs fuel)
                   (list (x2-dp-ind :m (caddr e) a x (append b vs) nil caps defs fuel)
                         (x2-dp-ind :loop e a x b (cdr r) caps defs (1- fuel)))))))
      (otherwise
       (if (atom e)
           nil
         (case (car e)
           (:if (list (x2-dp-ind :m (cadr e) a x b vs caps defs fuel) (x2-dp-ind :m (caddr e) a x b vs caps defs fuel) (x2-dp-ind :m (cadddr e) a x b vs caps defs fuel)))
           ((:add :lt) (list (x2-dp-ind :m (cadr e) a x b vs caps defs fuel) (x2-dp-ind :m (caddr e) a x b vs caps defs fuel)))
           (:throw (x2-dp-ind :m (cadr e) a x b vs caps defs fuel))
           ((:callv :applyv) (list (x2-dp-ind :m (cadr e) a x b vs caps defs fuel) (x2-dp-ind :args (cddr e) a x b vs caps defs fuel)))
           (:recur (x2-dp-ind :args (cdr e) a x b vs caps defs fuel))
           ((:mkclo :mkgrp :prim) (x2-dp-ind :args (cddr e) a x b vs caps defs fuel))
           ((:let :try) (let ((r (mx2 (cadr e) env caps defs fuel)))
                          (list (x2-dp-ind :m (cadr e) a x b vs caps defs fuel)
                                (x2-dp-ind :m (caddr e) a x (append b (list (cdr r))) vs caps defs fuel))))
           (:loop (let ((ri (mx2-args (cadr e) env caps defs fuel)))
                    (list (x2-dp-ind :args (cadr e) a x b vs caps defs fuel)
                          (x2-dp-ind :loop e a x b (cdr ri) caps defs fuel))))
           (otherwise nil)))))))
(defun x2-dp (flg e a x b vs caps defs fuel)
  (let ((env (append a (cons x b))) (env0 (append a b)) (np (len a)))
    (case flg
      (:args (implies (not (x2-rd-args np e))
                      (equal (mx2-args (x2-sh-args np e) env0 caps defs fuel) (mx2-args e env caps defs fuel))))
      (:loop (implies (and (equal (car e) :loop) (not (x2-rd np e)))
                      (equal (mx2-loop (x2-sh np e) env0 vs caps defs fuel) (mx2-loop e env vs caps defs fuel))))
      (otherwise (implies (not (x2-rd np e))
                          (equal (mx2 (x2-sh np e) env0 caps defs fuel) (mx2 e env caps defs fuel)))))))
(defthm x2-dp-app-assoc (equal (append (append a b) c) (append a (append b c))))
(defthm x2-dp-flag
  (x2-dp flg e a x b vs caps defs fuel)
  :rule-classes nil
  :hints (("Goal" :induct (x2-dp-ind flg e a x b vs caps defs fuel)
                  :in-theory (disable mx2 mx2-args mx2-loop x2-sh x2-sh-args x2-rd x2-rd-args x2-fn x2-vals x2-cls pick-arity clop clo-caps clo-f split-rest restp x2-seal clo)
                  :expand ((:free (env) (mx2 e env caps defs fuel)) (:free (env) (mx2-args e env caps defs fuel))
                           (:free (env vs) (mx2-loop e env vs caps defs fuel))
                           (:free (k y env) (mx2 (cons k y) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (k y env vs) (mx2-loop (cons k y) env vs caps defs fuel))
                           (:free (np) (x2-sh np e)) (:free (np) (x2-sh-args np e))
                           (:free (np) (x2-rd np e)) (:free (np) (x2-rd-args np e))))))

; THE SELF SLOT DROPPED: the same answer
(defthm x2-drop-mx
  (implies (and (equal (len a) np) (not (x2-rd np e)))
           (equal (mx2 (x2-sh np e) (append a b) caps defs fuel) (mx2 e (append a (cons x b)) caps defs fuel)))
  :hints (("Goal" :use ((:instance x2-dp-flag (flg :m) (vs nil))))))

; ---- (a) EX-CS AND X2-SH COMMUTE --------------------------------------------
; ex-fbtc reads the captures in place (ex-cs np m) after the body is
; translated, which moves the self slot from position np + m to np: a term
; that never reads np + m, shifted there and then ex-cs'd, is ex-cs'd and
; then shifted at np, and the ex-cs'd term never reads np.
(defun ex-shf (flg np e) (if flg (x2-sh-args np e) (x2-sh np e)))
(defun ex-rdf (flg np e) (if flg (x2-rd-args np e) (x2-rd np e)))
(defun ex-csh-ind (flg e)
  (declare (xargs :measure (acl2-count e)))
  (cond ((atom e) e)
        (flg (list (ex-csh-ind nil (car e)) (ex-csh-ind t (cdr e))))
        (t (case (car e)
             (:if (list (ex-csh-ind nil (cadr e)) (ex-csh-ind nil (caddr e)) (ex-csh-ind nil (cadddr e))))
             ((:let :add :lt :try) (list (ex-csh-ind nil (cadr e)) (ex-csh-ind nil (caddr e))))
             ((:mkclo :mkgrp :prim) (ex-csh-ind t (cddr e)))
             ((:callv :applyv) (list (ex-csh-ind nil (cadr e)) (ex-csh-ind t (cddr e))))
             (:loop (list (ex-csh-ind t (cadr e)) (ex-csh-ind nil (caddr e))))
             (:recur (ex-csh-ind t (cdr e)))
             (:throw (ex-csh-ind nil (cadr e)))
             (otherwise e)))))
(defthm ex-cs-sh-flag
  (implies (and (natp np) (natp m) (not (ex-rdf flg (+ np m) e)))
           (and (equal (ex-cs flg (ex-shf flg (+ np m) e) np m) (ex-shf flg np (ex-cs flg e np m)))
                (not (ex-rdf flg np (ex-cs flg e np m)))))
  :rule-classes nil
  :hints (("Goal" :induct (ex-csh-ind flg e) :in-theory (enable ex-cs)
                  :expand ((:free (np m) (ex-cs flg e np m))
                           (:free (np) (x2-sh np e)) (:free (np) (x2-sh-args np e))
                           (:free (np) (x2-rd np e)) (:free (np) (x2-rd-args np e))))))
(defthm ex-cs-sh
  (implies (and (natp np) (natp m) (not (x2-rd (+ np m) e)))
           (and (equal (ex-cs nil (x2-sh (+ np m) e) np m) (x2-sh np (ex-cs nil e np m)))
                (not (x2-rd np (ex-cs nil e np m)))))
  :hints (("Goal" :use ((:instance ex-cs-sh-flag (flg nil))))))
