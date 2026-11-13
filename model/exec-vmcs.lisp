; A FN'S CAPTURES READ IN PLACE (exec-PLAN Lane 3, the entry): ex-cs
; rewrites a vmx2 expression whose environment is a ++ c ++ b -- np
; positions a, then the m captures c, each caps[j] resolved (ex-nths) --
; into one over a ++ b that reads capture j as (:capt j): a position below
; np stays, one of the captures' is (:capt j), one above them moves down m.
; ex-cs-mx: mx2 answers the same of both. ex-cs-xwf: well formed in m
; fewer positions. So a fn's body need not copy its captures into locals
; first (exec-vmtr's ex-fbtc is ex-fbtr's body, so rewritten), and
; vm.inc's capture read (:capt j) is the translation's.

(in-package "ACL2")

(include-book "vmx2")
(local (include-book "arithmetic-5/top" :dir :system))

(defun ex-nths (j m l) (if (zp m) nil (cons (x2-res (nth (nfix j) l)) (ex-nths (1+ (nfix j)) (1- m) l))))

(defun ex-cloc (p np m)
  (let ((p (nfix p)) (np (nfix np)) (m (nfix m)))
    (cond ((< p np) (list :local p)) ((< p (+ np m)) (list :capt (- p np))) (t (list :local (- p m))))))

; flg t: a list of expressions
(defun ex-cs (flg e np m)
  (declare (xargs :measure (acl2-count e)))
  (cond ((atom e) e)
        (flg (cons (ex-cs nil (car e) np m) (ex-cs t (cdr e) np m)))
        (t (case (car e)
             (:local (ex-cloc (cadr e) np m))
             ((:if :let :add :lt :throw :try :callv :applyv :recur) (cons (car e) (ex-cs t (cdr e) np m)))
             ((:mkclo :mkgrp :prim) (if (consp (cdr e)) (list* (car e) (cadr e) (ex-cs t (cddr e) np m)) e))
             (:loop (if (consp (cdr e)) (list* :loop (ex-cs t (cadr e) np m) (ex-cs t (cddr e) np m)) e))
             (otherwise e)))))

(defthm ex-cs-parts
  (and (equal (ex-cs t (cons x y) np m) (cons (ex-cs nil x np m) (ex-cs t y np m)))
       (equal (ex-cs t nil np m) nil)))

(defthm ex-len-nths (equal (len (ex-nths j m l)) (nfix m)))
(defun ex-nths-ind (i j m) (if (or (zp i) (zp m)) j (ex-nths-ind (1- i) (1+ (nfix j)) (1- m))))
(defthm ex-nth-nths (implies (< (nfix i) (nfix m)) (equal (nth i (ex-nths j m l)) (x2-res (nth (+ (nfix i) (nfix j)) l))))
  :hints (("Goal" :induct (ex-nths-ind i j m) :expand ((ex-nths j m l)))))
(defthm ex-cs-nth-app
  (implies (natp p)
           (equal (nth p (append a c)) (if (< p (len a)) (nth p a) (nth (- p (len a)) c)))))

; the induction: mx2's, b growing as the environment does
(set-irrelevant-formals-ok t)
(defun ex-cs-ind (flg e a b vs caps defs fuel np m)
  (declare (xargs :measure (make-ord 2 (1+ (nfix fuel)) (make-ord 1 (1+ (acl2-count e)) (if (equal flg :loop) 0 1)))
                  :well-founded-relation o< :verify-guards nil))
  (let ((env (append a (ex-nths 0 m caps) b)))
    (case flg
      (:args (if (atom e) nil (list (ex-cs-ind :m (car e) a b vs caps defs fuel np m) (ex-cs-ind :args (cdr e) a b vs caps defs fuel np m))))
      (:loop (if (not (consp e))
                 nil
               (let ((r (mx2 (caddr e) (append env vs) caps defs fuel)))
                 (if (zp fuel)
                     (ex-cs-ind :m (caddr e) a (append b vs) nil caps defs fuel np m)
                   (list (ex-cs-ind :m (caddr e) a (append b vs) nil caps defs fuel np m)
                         (ex-cs-ind :loop e a b (cdr r) caps defs (1- fuel) np m))))))
      (otherwise
       (if (atom e)
           nil
         (case (car e)
           (:if (list (ex-cs-ind :m (cadr e) a b vs caps defs fuel np m) (ex-cs-ind :m (caddr e) a b vs caps defs fuel np m) (ex-cs-ind :m (cadddr e) a b vs caps defs fuel np m)))
           (:add (list (ex-cs-ind :m (cadr e) a b vs caps defs fuel np m) (ex-cs-ind :m (caddr e) a b vs caps defs fuel np m)))
           (:lt (list (ex-cs-ind :m (cadr e) a b vs caps defs fuel np m) (ex-cs-ind :m (caddr e) a b vs caps defs fuel np m)))
           (:throw (ex-cs-ind :m (cadr e) a b vs caps defs fuel np m))
           (:callv (list (ex-cs-ind :m (cadr e) a b vs caps defs fuel np m) (ex-cs-ind :args (cddr e) a b vs caps defs fuel np m)))
           (:applyv (list (ex-cs-ind :m (cadr e) a b vs caps defs fuel np m) (ex-cs-ind :args (cddr e) a b vs caps defs fuel np m)))
           (:recur (ex-cs-ind :args (cdr e) a b vs caps defs fuel np m))
           (:mkclo (ex-cs-ind :args (cddr e) a b vs caps defs fuel np m))
           (:mkgrp (ex-cs-ind :args (cddr e) a b vs caps defs fuel np m))
           (:prim (ex-cs-ind :args (cddr e) a b vs caps defs fuel np m))
           (:let (let ((r (mx2 (cadr e) env caps defs fuel)))
              (list (ex-cs-ind :m (cadr e) a b vs caps defs fuel np m)
                    (ex-cs-ind :m (caddr e) a (append b (list (cdr r))) vs caps defs fuel np m))))
           (:try (let ((r (mx2 (cadr e) env caps defs fuel)))
              (list (ex-cs-ind :m (cadr e) a b vs caps defs fuel np m)
                    (ex-cs-ind :m (caddr e) a (append b (list (cdr r))) vs caps defs fuel np m))))
           (:loop (let ((ri (mx2-args (cadr e) env caps defs fuel)))
                    (list (ex-cs-ind :args (cadr e) a b vs caps defs fuel np m)
                          (ex-cs-ind :loop e a b (cdr ri) caps defs fuel np m))))
           (otherwise nil)))))))

(defun ex-cs-p (flg e a b vs caps defs fuel np m)
  (let ((env (append a (ex-nths 0 m caps) b)))
    (case flg
      (:args (equal (mx2-args (ex-cs t e np m) (append a b) caps defs fuel) (mx2-args e env caps defs fuel)))
      (:loop (implies (equal (car e) :loop)
                      (equal (mx2-loop (ex-cs nil e np m) (append a b) vs caps defs fuel) (mx2-loop e env vs caps defs fuel))))
      (otherwise (equal (mx2 (ex-cs nil e np m) (append a b) caps defs fuel) (mx2 e env caps defs fuel))))))

(defthm ex-cs-car (equal (car (ex-cs t x np m)) (if (consp x) (ex-cs nil (car x) np m) nil)))
(defthm ex-cs-cdr (equal (cdr (ex-cs t x np m)) (if (consp x) (ex-cs t (cdr x) np m) nil)))
(defthm ex-cs-atom (implies (atom e) (and (equal (ex-cs flg e np m) e) (equal (mx2 e env caps defs fuel) (quote (:val))))))
(defthm ex-cs-app-assoc (equal (append (append a b) c) (append a (append b c))))
(defthm ex-cs-mx-flag
  (implies (natp m) (ex-cs-p flg e a b vs caps defs fuel (len a) m))
  :rule-classes nil
  :hints (("Goal" :induct (ex-cs-ind flg e a b vs caps defs fuel (len a) m)
                  :in-theory (disable mx2 mx2-args mx2-loop ex-cs x2-fn x2-vals x2-cls pick-arity clop clo-caps clo-f split-rest restp x2-seal clo)
                  :expand ((:free (env) (mx2 e env caps defs fuel)) (:free (env) (mx2-args e env caps defs fuel))
                           (:free (env vs) (mx2-loop e env vs caps defs fuel))
                           (:free (k y env) (mx2 (cons k y) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (k y env vs) (mx2-loop (cons k y) env vs caps defs fuel))
                           (:free (np) (ex-cs nil e np m)) (:free (np) (ex-cs t e np m))))))

; THE CAPTURES READ IN PLACE: the same answer
(defthm ex-cs-mx
  (implies (and (equal (len a) np) (natp m) (true-listp a))
           (equal (mx2 (ex-cs nil e np m) a caps defs fuel) (mx2 e (append a (ex-nths 0 m caps)) caps defs fuel)))
  :hints (("Goal" :use ((:instance ex-cs-mx-flag (flg :m) (b nil) (vs nil))))))

; and well formed in m fewer positions
(defun ex-cs-wind (flg e n k)
  (declare (xargs :measure (acl2-count e)))
  (cond ((atom e) nil)
        (flg (list (ex-cs-wind nil (car e) n nil) (ex-cs-wind t (cdr e) n nil)))
        (t (case (car e)
             (:if (list (ex-cs-wind nil (cadr e) n nil) (ex-cs-wind nil (caddr e) n k) (ex-cs-wind nil (cadddr e) n k)))
             (:let (list (ex-cs-wind nil (cadr e) n nil) (ex-cs-wind nil (caddr e) (1+ (nfix n)) k)))
             (:try (list (ex-cs-wind nil (cadr e) n nil) (ex-cs-wind nil (caddr e) (1+ (nfix n)) nil)))
             (:add (list (ex-cs-wind nil (cadr e) n nil) (ex-cs-wind nil (caddr e) n nil)))
             (:lt (list (ex-cs-wind nil (cadr e) n nil) (ex-cs-wind nil (caddr e) n nil)))
             (:throw (ex-cs-wind nil (cadr e) n nil))
             (:callv (list (ex-cs-wind nil (cadr e) n nil) (ex-cs-wind t (cddr e) n nil)))
             (:applyv (list (ex-cs-wind nil (cadr e) n nil) (ex-cs-wind t (cddr e) n nil)))
             (:mkclo (ex-cs-wind t (cddr e) n nil))
             (:mkgrp (ex-cs-wind t (cddr e) n nil))
             (:prim (ex-cs-wind t (cddr e) n nil))
             (:recur (ex-cs-wind t (cdr e) n nil))
             (:loop (list (ex-cs-wind t (cadr e) n nil) (ex-cs-wind nil (caddr e) (+ (nfix n) (len (cadr e))) (len (cadr e)))))
             (otherwise nil)))))
(defthm ex-cs-len (equal (len (ex-cs t e np m)) (len e)))
(defthm ex-cs-true-listp (equal (true-listp (ex-cs t e np m)) (true-listp e)))
(defthm ex-cs-consp (equal (consp (ex-cs t e np m)) (consp e)))
(defthm ex-cs-xwf-flag
  (implies (and (natp np) (natp m) (<= (+ np m) (nfix n)))
           (if flg
               (implies (x2wf-args e n) (x2wf-args (ex-cs t e np m) (- n m)))
             (implies (x2wf e n k) (x2wf (ex-cs nil e np m) (- n m) k))))
  :rule-classes nil
  :hints (("Goal" :induct (ex-cs-wind flg e n k) :in-theory (disable ex-cs)
                  :expand ((ex-cs nil e np m) (ex-cs t e np m) (x2wf e n k) (x2wf-args e n)
                           (:free (x n k) (x2wf (cons :local x) n k)) (:free (x n k) (x2wf (cons :capt x) n k))
                           (:free (x y n) (x2wf-args (cons x y) n))
                           (:free (y n k) (x2wf (cons (car e) y) n k))))))
(defthm ex-cs-xwf
  (implies (and (x2wf e n k) (natp np) (natp m) (<= (+ np m) (nfix n)))
           (x2wf (ex-cs nil e np m) (- n m) k))
  :hints (("Goal" :use ((:instance ex-cs-xwf-flag (flg nil))))))
