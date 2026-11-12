; A LETFN IN THE TRANSLATION (exec-PLAN milestone 5; model/exec-vm.lisp's
; third part): what the tree and mx2 make of a letfn's n fns, for
; ex-vm-agree's case of it (ex-vgood-m-letfn, exec-vm).
;
; The tree binds the fns' closures into slots s .. s+n-1, one after
; another (ex-lfr), each capture of an outer slot read as it is made, then
; seals them (ex-seal): each capture of one of the group's slots made (:grp
; G j). Its other captures read slots outside the group, so the group G
; and the sealed closures are the fns' templates and captures read from
; the frame the letfn started with (ex-lfg, ex-lfsv; ex-gcv: a capture of
; the group (:grp g j), any other its slot's value). mx2's n lets of
; (:mkgrp (j . shape) caps..) read every fn's captures from the letfn's
; scope (ex-lfargs: a group capture the constant (:grp nil j)), so each
; let's x2-seal is the j-th of those same sealed closures (ex-trlf-mx):
; the body runs in the scope cm ++ (s .. s+n-1) on env ++ the closures,
; agreeing with the sealed frame (ex-lf-facts), the closures good values
; (their group captures a good group: exec-vmtr's ex-gcok).

(in-package "ACL2")

(include-book "exec-vmcall")

; ---- THE CAPTURES, THE GROUP, THE SEALED CLOSURES ---------------------------------------------

(defun ex-gcv (os fr s n g)
  (if (atom os)
      nil
    (cons (if (ex-ingrp (car os) s n) (list :grp g (- (car os) (nfix s))) (nth (car os) fr))
          (ex-gcv (cdr os) fr s n g))))
(defthm ex-gcaps-caps (equal (ex-gcaps capv (ex-caps capv fr) s n g) (ex-gcv (ex-outers capv) fr s n g)))
(defthm ex-gcv-upd
  (implies (and (nat-listp os) (ex-ingrp x s n)) (equal (ex-gcv os (update-nth x v fr) s n g) (ex-gcv os fr s n g))))
(defthm ex-len-gcv (equal (len (ex-gcv os fr s n g)) (len os)))
(defthm ex-tl-gcv (true-listp (ex-gcv os fr s n g)))

(defmacro ex-kj () '(ex-kid-of e (nfix j)))
(defun ex-lfr (e j fr) (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e)) (ex-lfr e (1+ (nfix j)) (update-nth (+ (ex-s2 e) (nfix j)) (ex-mkclo (ex-c (ex-kj)) fr) fr)) fr))
(defun ex-lfcl (e j fr) (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e))
      (cons (ex-mkclo (ex-c (ex-kj)) fr) (ex-lfcl e (1+ (nfix j)) (update-nth (+ (ex-s2 e) (nfix j)) (ex-mkclo (ex-c (ex-kj)) fr) fr)))
    nil))
(defun ex-lfg (e j fr g) (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e))
      (cons (list (ex-c (ex-kj)) (ex-gcv (ex-lfos e (nfix j)) fr (ex-s2 e) (ex-i2 e) g)) (ex-lfg e (1+ (nfix j)) fr g))
    nil))
(defun ex-lfsv (e j fr g) (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e))
      (cons (list :clo (ex-c (ex-kj)) (ex-gcv (ex-lfos e (nfix j)) fr (ex-s2 e) (ex-i2 e) g)) (ex-lfsv e (1+ (nfix j)) fr g))
    nil))
(defun ex-lfall (e j fr) (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e))
      (append (ex-gcv (ex-lfos e (nfix j)) fr (ex-s2 e) (ex-i2 e) nil) (ex-lfall e (1+ (nfix j)) fr))
    nil))
(defthm ex-len-lfsv (equal (len (ex-lfsv e j fr g)) (nfix (- (ex-i2 e) (nfix j)))))
(defthm ex-tl-lfg (true-listp (ex-lfg e j fr g)))

(defthm ex-lfg-upd
  (implies (and (ex-lffns e j) (ex-ingrp x (ex-s2 e) (ex-i2 e)))
           (and (equal (ex-lfg e j (update-nth x v fr) g) (ex-lfg e j fr g))
                (equal (ex-lfsv e j (update-nth x v fr) g) (ex-lfsv e j fr g))))
  :hints (("Goal" :induct (ex-lfg e j fr g) :in-theory (disable ex-lfos))))

; ---- THE TREE: the fns bound, then sealed ------------------------------------------------------

(defthm ex-ev-fn
  (implies (and (consp f) (equal (ex-kind f) 14)) (equal (ex-ev :m f 0 nil fr fuel) (list (cons :val (ex-mkclo (ex-c f) fr)) fr 1)))
  :hints (("Goal" :expand ((ex-ev :m f 0 nil fr fuel)))))
(defthm ex-ev-lf
  (implies (and (consp e) (equal (ex-kind e) 13) (ex-lffns e j))
           (and (equal (car (ex-ev :let e j nil fr fuel))
                       (car (ex-ev :m (ex-kid-of e (ex-i2 e)) 0 nil (ex-seal (ex-s2 e) (ex-i2 e) (ex-lfr e j fr)) fuel)))
                (equal (cadr (ex-ev :let e j nil fr fuel))
                       (cadr (ex-ev :m (ex-kid-of e (ex-i2 e)) 0 nil (ex-seal (ex-s2 e) (ex-i2 e) (ex-lfr e j fr)) fuel)))))
  :hints (("Goal" :induct (ex-lfr e j fr) :expand ((ex-ev :let e j nil fr fuel))
                  :in-theory (disable ex-kid-of ex-lfos ex-mkclo ex-seal))))

(defthm ex-nth-lfr
  (implies (and (natp x) (< x (+ (ex-s2 e) (nfix j)))) (equal (nth x (ex-lfr e j fr)) (nth x fr)))
  :hints (("Goal" :induct (ex-lfr e j fr) :in-theory (disable ex-kid-of ex-mkclo))))
(defthm ex-take-nthcdr-open
  (implies (and (natp s) (not (zp m))) (equal (take m (nthcdr s l)) (cons (nth s l) (take (1- m) (nthcdr (1+ s) l)))))
  :hints (("Goal" :induct (nthcdr s l) :in-theory (enable nth nthcdr))))
(defthm ex-lfcl-lfr
  (implies (and (natp j) (<= j (ex-i2 e)))
           (equal (take (- (ex-i2 e) j) (nthcdr (+ (ex-s2 e) j) (ex-lfr e j fr))) (ex-lfcl e j fr)))
  :hints (("Goal" :induct (ex-lfr e j fr) :in-theory (disable ex-kid-of ex-mkclo ex-take-nthcdr-open))
          ("Subgoal *1/1" :use ((:instance ex-take-nthcdr-open (m (- (ex-i2 e) j)) (s (+ (ex-s2 e) j))
                                           (l (ex-lfr e (+ 1 j) (update-nth (+ (ex-s2 e) j) (ex-mkclo (ex-c (ex-kid-of e j)) fr) fr))))))))
(defthm ex-grp-lfcl
  (implies (ex-lffns e j)
           (and (equal (ex-grp (ex-lfcl e j fr) (ex-s2 e) (ex-i2 e)) (ex-lfg e j fr nil))
                (equal (ex-sealvs (ex-lfcl e j fr) (ex-s2 e) (ex-i2 e) g) (ex-lfsv e j fr g))))
  :hints (("Goal" :induct (ex-lfcl e j fr) :in-theory (e/d (ex-mkclo ex-lfos) (ex-kid-of)))))
(defthm ex-seal-lfr
  (implies (ex-lffns e 0)
           (equal (ex-seal (ex-s2 e) (ex-i2 e) (ex-lfr e 0 fr))
                  (ex-write (ex-s2 e) (ex-lfsv e 0 fr (ex-lfg e 0 fr nil)) (ex-lfr e 0 fr))))
  :hints (("Goal" :in-theory (e/d (ex-seal) (ex-lfcl-lfr ex-lfr ex-lfcl ex-lfg ex-lfsv)) :use ((:instance ex-lfcl-lfr (j 0))))))
(defthm ex-nomem-mem (implies (and (ex-nomem ls cm) (member-equal x ls) x) (not (member-equal x cm))))
(defun ex-msi (s j n) (if (zp j) (list s n) (ex-msi (1+ (nfix s)) (1- j) (1- n))))
(defthm ex-mem-slots (implies (and (natp j) (< j (nfix n))) (member-equal (+ (nfix s) j) (ex-slots s n)))
  :hints (("Goal" :induct (ex-msi s j n) :expand ((ex-slots s n)))))
(defthm ex-agree-lfr
  (implies (and (ex-agree cm env fr) (ex-nomem (cons nil (ex-slots (ex-s2 e) (ex-i2 e))) cm) (natp j))
           (ex-agree cm env (ex-lfr e j fr)))
  :hints (("Goal" :induct (ex-lfr e j fr) :in-theory (disable ex-kid-of ex-mkclo ex-nomem-mem ex-mem-slots))
          ("Subgoal *1/1" :use ((:instance ex-nomem-mem (ls (cons nil (ex-slots (ex-s2 e) (ex-i2 e)))) (x (+ j (ex-s2 e))))
                                (:instance ex-mem-slots (s (ex-s2 e)) (n (ex-i2 e)))))))

; ---- MX2: the lets' captures read, each let's value a sealed closure ---------------------------

(defthm ex-nth-take (implies (< (nfix p) (nfix k)) (equal (nth p (take k l)) (nth p l)))
  :hints (("Goal" :in-theory (enable nth take))))
(defmacro ex-rdok () '(and (ex-agree cm (take (len cm) env2) fr) (<= (len cm) (len env2))))
(defthm ex-lfcaps-mx
  (implies (and (ex-rdok) (ex-lfin os s n cm))
           (equal (mx2-args (ex-lfcaps os s n cm) env2 caps d2 fuel) (cons :val (ex-gcv os fr s n nil))))
  :hints (("Goal" :induct (ex-lfcaps os s n cm) :in-theory (disable ex-agree-local)
                  :expand ((:free (x y) (mx2-args (cons x y) env2 caps d2 fuel))
                           (:free (x) (mx2 (cons :local x) env2 caps d2 fuel)) (:free (x) (mx2 (cons :const x) env2 caps d2 fuel))))
          ("Subgoal *1/2" :use ((:instance ex-agree-local (s (car os)) (env (take (len cm) env2)))))))
(defthm ex-mx-args-app
  (equal (mx2-args (append a b) env caps d2 fuel)
         (let ((ra (mx2-args a env caps d2 fuel)))
           (if (valp ra) (let ((rb (mx2-args b env caps d2 fuel))) (if (valp rb) (cons :val (append (val ra) (val rb))) rb)) ra)))
  :hints (("Goal" :induct (len a) :expand ((mx2-args a env caps d2 fuel) (:free (x y) (mx2-args (cons x y) env caps d2 fuel))))))
(defthm ex-lfargs-mx
  (implies (and (ex-rdok) (ex-lfok e j cm defs))
           (equal (mx2-args (ex-lfargs e j cm) env2 caps d2 fuel) (cons :val (ex-lfall e j fr))))
  :hints (("Goal" :induct (ex-lfargs e j cm) :in-theory (disable ex-lfos)
                  :expand ((mx2-args nil env2 caps d2 fuel)))))
(defthm ex-take-app-len (implies (and (true-listp a) (equal k (len a))) (equal (take k (append a b)) a)))
(defthm ex-nthcdr-app-len (implies (equal k (len a)) (equal (nthcdr k (append a b)) b)))
(defthm ex-split-lf (equal (x2-split (ex-lfshape e j) (ex-lfall e j fr)) (ex-lfg e j fr nil))
  :hints (("Goal" :induct (ex-lfall e j fr) :in-theory (disable ex-lfos ex-kid-of))))

; each plain capture a good value, so no group's own (:grp nil m)
(defun ex-fvok (os fr s n defs)
  (or (atom os) (and (or (ex-ingrp (car os) s n) (ex-xvs defs (list (nth (car os) fr)))) (ex-fvok (cdr os) fr s n defs))))
(defun ex-lfvok (e j fr defs) (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e)) (and (ex-fvok (ex-lfos e (nfix j)) fr (ex-s2 e) (ex-i2 e) defs) (ex-lfvok e (1+ (nfix j)) fr defs)) t))
(defthm ex-fvok-in
  (implies (and (ex-lfin os s n cm) (ex-agree cm env fr) (ex-xvs defs env)) (ex-fvok os fr s n defs)))
(defthm ex-lfvok-ok
  (implies (and (ex-lfok e j cm defs) (ex-agree cm env fr) (ex-xvs defs env)) (ex-lfvok e j fr defs))
  :hints (("Goal" :induct (ex-lfok e j cm defs) :in-theory (disable ex-lfos))))
(defthm ex-fill-gcv
  (implies (and g (ex-fvok os fr s n defs)) (equal (x2-fill (ex-gcv os fr s n nil) g) (ex-gcv os fr s n g))))

(defun ex-nli (i m) (if (zp m) i (ex-nli (1+ (nfix i)) (1- m))))
(defthm ex-nth-lfg
  (implies (and (natp i) (natp m) (< (+ i m) (ex-i2 e)))
           (equal (nth m (ex-lfg e i fr g))
                  (list (ex-c (ex-kid-of e (+ i m))) (ex-gcv (ex-lfos e (+ i m)) fr (ex-s2 e) (ex-i2 e) g))))
  :hints (("Goal" :induct (ex-nli i m) :in-theory (e/d (nth) (ex-lfos ex-kid-of)) :expand ((ex-lfg e i fr g)))))
(defthm ex-lfvok-nth
  (implies (and (ex-lfvok e i fr defs) (natp i) (natp m) (<= i m) (< m (ex-i2 e)))
           (ex-fvok (ex-lfos e m) fr (ex-s2 e) (ex-i2 e) defs))
  :hints (("Goal" :induct (ex-lfvok e i fr defs) :in-theory (disable ex-lfos))))
(defthm ex-lf-res
  (implies (and (ex-lfvok e 0 fr defs) (natp j) (< j (ex-i2 e)))
           (equal (x2-res (list :grp (ex-lfg e 0 fr nil) j))
                  (list :clo (ex-c (ex-kid-of e j)) (ex-gcv (ex-lfos e j) fr (ex-s2 e) (ex-i2 e) (ex-lfg e 0 fr nil)))))
  :hints (("Goal" :in-theory (e/d (x2-res clo) (ex-lfg ex-lfos ex-gcv ex-fill-gcv))
                  :expand ((ex-lfg e 0 fr nil))
                  :use ((:instance ex-nth-lfg (i 0) (m j) (g nil))
                        (:instance ex-fill-gcv (os (ex-lfos e j)) (s (ex-s2 e)) (n (ex-i2 e)) (g (ex-lfg e 0 fr nil)))))))

(defthm ex-mx-mkgrp
  (equal (mx2 (cons :mkgrp x) env caps defs fuel)
         (let ((rs (mx2-args (cdr x) env caps defs fuel))) (if (valp rs) (cons :val (x2-seal (car x) (val rs))) rs)))
  :hints (("Goal" :expand ((mx2 (cons :mkgrp x) env caps defs fuel)))))
(defun ex-lfind (e j env2 fr)
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (1+ (nfix j)) (ex-i2 e))
      (ex-lfind e (1+ (nfix j)) (append env2 (list (car (ex-lfsv e j fr (ex-lfg e 0 fr nil))))) fr)
    env2))
(defthm ex-take-app-long (implies (<= (nfix k) (len a)) (equal (take k (append a b)) (take k a))))
(defthm ex-trlf-mx
  (implies (and (ex-rdok) (ex-lfok e 0 cm defs) (ex-lfvok e 0 fr defs) (natp j) (< j (ex-i2 e)))
           (equal (mx2 (ex-trlf e j cm x) env2 caps d2 fuel)
                  (mx2 x (append env2 (ex-lfsv e j fr (ex-lfg e 0 fr nil))) caps d2 fuel)))
  :hints (("Goal" :induct (ex-lfind e j env2 fr)
                  :in-theory (e/d (x2-seal) (ex-lfos ex-lfshape ex-lfargs ex-lfok ex-lfvok ex-lfg ex-lfall ex-kid-of))
                  :expand ((ex-trlf e j cm x) (ex-trlf e (+ 1 j) cm x) (ex-lfsv e j fr (ex-lfg e 0 fr nil))
                           (ex-lfsv e (+ 1 j) fr (ex-lfg e 0 fr nil))
                           (:free (y env) (mx2 (cons :let y) env caps d2 fuel))))))

; ---- THE CLOSURES ARE GOOD VALUES --------------------------------------------------------------

(defthm ex-gcv-gnils
  (implies (and (ex-fvok os fr s n defs) (natp s)) (ex-gnils (ex-gcv os fr s n nil) n)))
(defthm ex-gcv-gplain
  (implies (ex-fvok os fr s n defs) (ex-xvs defs (ex-gplain (ex-gcv os fr s n nil))))
  :hints (("Goal" :in-theory (enable ex-xvs-cons1))))
(defthm ex-lfg-gents
  (implies (and (ex-lfvok e j fr defs) (ex-lfok e j cm defs))
           (and (ex-gents (ex-lfg e j fr nil) defs (ex-i2 e)) (ex-xvs defs (ex-gall (ex-lfg e j fr nil)))))
  :hints (("Goal" :induct (ex-lfg e j fr nil) :in-theory (disable ex-lfos ex-kid-of))
          (and stable-under-simplificationp '(:in-theory (e/d (ex-lfos ex-len-inners-outers) (ex-kid-of))))))
(defthm ex-gcv-good
  (implies (and (ex-fvok os fr s n defs) (consp g) (true-listp g) (equal (len g) (nfix n)) (natp s)
                (ex-gents g defs (len g)) (ex-xvs defs (ex-gall g)))
           (and (ex-gcok (ex-gcv os fr s n g) defs) (ex-xvs defs (ex-gvals (ex-gcv os fr s n g)))))
  :hints (("Goal" :in-theory (enable ex-xvs-cons1))))
(defthm ex-len-lfg (equal (len (ex-lfg e j fr g)) (nfix (- (ex-i2 e) (nfix j)))))
(defthm ex-lfsv-good
  (implies (and (ex-lfvok e j fr defs) (ex-lfok e j cm defs) (consp g) (true-listp g) (equal (len g) (ex-i2 e))
                (ex-gents g defs (len g)) (ex-xvs defs (ex-gall g)))
           (ex-xvs defs (ex-lfsv e j fr g)))
  :hints (("Goal" :induct (ex-lfsv e j fr g) :in-theory (e/d (ex-xvs-cons1 ex-len-inners-outers) (ex-kid-of)))
          (and stable-under-simplificationp '(:expand ((:free (a) (ex-xvs defs (list a))))))))

; ---- THE LETFN'S FACTS: its run, translation, scope and values, the body's -------------------

(defthm ex-agree-take (implies (ex-agree cm env fr) (ex-agree cm (take (len cm) env) fr))
  :hints (("Goal" :induct (ex-agree cm env fr))))
(defmacro ex-lfb () '(ex-kid-of e (ex-i2 e)))
(defmacro ex-lfcm () '(append cm (ex-slots (ex-s2 e) (ex-i2 e))))
(defmacro ex-lfsvs () '(ex-lfsv e 0 fr (ex-lfg e 0 fr nil)))
(defmacro ex-lffr () '(ex-write (ex-s2 e) (ex-lfsvs) (ex-lfr e 0 fr)))
(defthm ex-lf-parts
  (implies (and (consp e) (equal (ex-kind e) 13))
           (and (equal (ex-vwf :m e i cm lp defs)
                       (and (equal (ex-nk e) (1+ (ex-i2 e))) (ex-lffns e 0) (ex-lfok e 0 cm defs)
                            (ex-nomem (cons nil (ex-slots (ex-s2 e) (ex-i2 e))) cm)
                            (ex-vwf :m (ex-lfb) 0 (ex-lfcm) lp defs)))
                (equal (ex-tr :m e i cm) (ex-trlf e 0 cm (ex-tr :m (ex-lfb) 0 (ex-lfcm))))
                (equal (ex-clr :m e i) (ex-clr :let e 0))
                (equal (ex-ev :m e i tmp fr fuel) (ex-ev :let e 0 nil fr fuel))))
  :hints (("Goal" :in-theory (disable ex-kid-of ex-lffns ex-lfok ex-trlf ex-clr ex-tr ex-vwf ex-ev)
                  :expand ((ex-vwf :m e i cm lp defs) (ex-tr :m e i cm) (ex-clr :m e i) (ex-ev :m e i tmp fr fuel)))))
; THE BODY'S ENV: the lets' values after the letfn's own; an empty letfn's
; body sees env itself (its scope cm ++ nil agrees with it all the same)
(defun ex-lfenv (e env fr) (if (zp (ex-i2 e)) env (append env (ex-lfsvs))))
(defthm ex-agree-app-nil (implies (ex-agree cm env fr) (ex-agree (append cm nil) env fr)))
(defthm ex-lf-facts-0
  (implies (and (consp e) (equal (ex-kind e) 13) (equal (ex-i2 e) 0) (ex-vwf :m e i cm lp defs) (ex-agree cm env fr))
           (and (equal (car (ex-ev :m e i tmp fr fuel)) (car (ex-ev :m (ex-lfb) 0 nil (ex-lffr) fuel)))
                (equal (cadr (ex-ev :m e i tmp fr fuel)) (cadr (ex-ev :m (ex-lfb) 0 nil (ex-lffr) fuel)))
                (equal (mx2 (ex-tr :m e i cm) env caps d2 fuel) (mx2 (ex-tr :m (ex-lfb) 0 (ex-lfcm)) env caps d2 fuel))
                (ex-agree (ex-lfcm) env (ex-lffr))
                (ex-vwf :m (ex-lfb) 0 (ex-lfcm) lp defs)
                (equal (ex-clr :m e i) (ex-clr :m (ex-lfb) 0))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (ex-seal ex-lfr ex-lfsv ex-lfg ex-write ex-trlf ex-slots) (ex-kid-of ex-lffns ex-lfok ex-clr ex-tr ex-vwf ex-ev ex-agree ex-ev-lf))
                  :use ((:instance ex-ev-lf (j 0)) (:instance ex-clr-lf (j 0)) ex-lf-parts))))
(defthm ex-lf-facts
  (implies (and (consp e) (equal (ex-kind e) 13) (ex-vwf :m e i cm lp defs) (ex-agree cm env fr) (ex-xvs defs env))
           (and (equal (car (ex-ev :m e i tmp fr fuel)) (car (ex-ev :m (ex-lfb) 0 nil (ex-lffr) fuel)))
                (equal (cadr (ex-ev :m e i tmp fr fuel)) (cadr (ex-ev :m (ex-lfb) 0 nil (ex-lffr) fuel)))
                (equal (mx2 (ex-tr :m e i cm) env caps d2 fuel) (mx2 (ex-tr :m (ex-lfb) 0 (ex-lfcm)) (ex-lfenv e env fr) caps d2 fuel))
                (ex-agree (ex-lfcm) (ex-lfenv e env fr) (ex-lffr))
                (ex-xvs defs (ex-lfenv e env fr))
                (ex-vwf :m (ex-lfb) 0 (ex-lfcm) lp defs)
                (equal (ex-clr :m e i) (ex-clr :m (ex-lfb) 0))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :cases ((equal (ex-i2 e) 0)))
          ("Subgoal 1" :in-theory (disable ex-kid-of ex-clr ex-tr ex-vwf ex-ev ex-agree ex-xvs ex-lfsv ex-lfg ex-lfr ex-write ex-seal)
                       :use ex-lf-facts-0)
          ("Subgoal 2" :do-not-induct t
                  :in-theory (disable ex-kid-of ex-lffns ex-lfok ex-trlf ex-clr ex-tr ex-vwf ex-ev ex-lfsv ex-lfg ex-lfr ex-seal
                                      ex-write ex-lfvok ex-agree ex-xvs ex-ev-lf ex-trlf-mx ex-lfvok-ok ex-lfsv-good ex-lfg-gents
                                      ex-agree-write-blank ex-agree-lfr ex-agree-take)
                  :use ((:instance ex-ev-lf (j 0)) ex-seal-lfr
                        (:instance ex-trlf-mx (j 0) (env2 env) (x (ex-tr :m (ex-lfb) 0 (ex-lfcm))))
                        (:instance ex-lfvok-ok (j 0)) ex-agree-take
                        (:instance ex-lfg-gents (j 0))
                        (:instance ex-lfsv-good (j 0) (g (ex-lfg e 0 fr nil)))
                        (:instance ex-agree-lfr (j 0))
                        (:instance ex-agree-write-blank (fr (ex-lfr e 0 fr)) (s (ex-s2 e)) (n (ex-i2 e)) (vs (ex-lfsvs)))
                        (:instance ex-agree-written (fr (ex-lfr e 0 fr)) (s (ex-s2 e)) (n (ex-i2 e)) (vs (ex-lfsvs))))
                  :expand ((ex-lfg e 0 fr nil)))))

(in-theory (disable ex-lfenv ex-lf-parts ex-trlf ex-lfargs ex-lfcaps ex-lfshape ex-lfok ex-lffns ex-lfsv ex-lfg ex-lfr ex-lfall ex-gcv))
(set-irrelevant-formals-ok t)
; THE DEFS ARE THE VM'S: every clause's body x2wf at its locals (vmx2's x2defs-ok)
(defthm ex-xwf-capts (x2wf-args (ex-capts j m) n))
(defun ex-clets-ind2 (j m n) (if (zp m) n (ex-clets-ind2 (1+ (nfix j)) (1- m) (1+ n))))
(defthm ex-xwf-clets (implies (natp n) (equal (x2wf (ex-clets j m x) n k) (x2wf x (+ n (nfix m)) k)))
  :hints (("Goal" :induct (ex-clets-ind2 j m n) :expand ((:free (y n) (x2wf (cons :let y) n k))))))
(defthm ex-len-fbcm (equal (len (ex-fbcm tm ar)) (+ (ex-anp ar) (len (ex-inners (nth 2 tm))) 1))
  :hints (("Goal" :in-theory (enable ex-fbcm))))
(defthm ex-len-fcm (equal (len (ex-fcm tm ar)) (len (ex-fbcm tm ar))) :hints (("Goal" :in-theory (enable ex-fcm))))
(defthm ex-params-sub (subsetp-equal (ex-fparams ar) (ex-fbcm tm ar)) :hints (("Goal" :in-theory (enable ex-fbcm))))
(defthm ex-len-fparams (equal (len (ex-fparams ar)) (ex-anp ar)))
(defthm ex-arwf-vwf
  (implies (ex-arwf tm ar defs) (ex-vwf :m (ex-abody ar) 0 (ex-fcmb tm ar) (ex-flp ar) defs))
  :hints (("Goal" :in-theory (enable ex-arwf))))
(defthm ex-fbtr-xwf
  (implies (ex-arwf tm ar defs) (x2wf (ex-fbtr tm ar) (ex-anp ar) nil))
  :hints (("Goal" :in-theory (e/d (ex-fbtr) (ex-tr-xwf ex-fparams ex-arwf-vwf))
                  :use ((:instance ex-tr-xwf (e (ex-abody ar)) (cm (ex-fcmb tm ar)) (lp (ex-flp ar))) ex-arwf-vwf
                        (:instance ex-locals-xwf (ls (ex-fparams ar)) (cm (ex-fbcm tm ar))))
                  :expand ((:free (y n) (x2wf (cons :let y) n nil)) (:free (y n k) (x2wf (cons :loop y) n k))
                           (:free (y n) (x2wf (cons :mkclo y) n nil)) (:free (x y n) (x2wf-args (cons x y) n))))))
(defthm ex-clauses-ok (implies (ex-arswf tm ars defs) (clauses-ok (ex-clauses tm ars)))
  :hints (("Goal" :in-theory (e/d (ex-clause ex-anp ex-anf ex-avar ex-arwf) (ex-fbtr-xwf))
                  :induct (ex-clauses tm ars))
          ("Subgoal *1/2" :use ((:instance ex-fbtr-xwf (ar (car ars)))))))
(defthm ex-defs-xdefs (implies (ex-defs-ok ds defs) (x2defs-ok ds))
  :hints (("Goal" :in-theory (enable ex-def ex-tmwf))))
