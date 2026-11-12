; THE GOOD VALUES (model/exec-vm.lisp's first part, split from exec-vmtr.lisp
; for size): ex-xvs, a letfn group's captures in a closure, and what a good
; value's reads, spreads and resolutions keep good. exec-vm.lisp's header
; says what they are; nothing restated.

(in-package "ACL2")

(include-book "exec")
(include-book "vmx2")

; a template's capture pairs (outer inner): their outer and inner slots, as ex-caps and ex-bind-caps walk them
(defun ex-outers (capv) (if (or (atom capv) (atom (cdr capv))) nil (cons (car capv) (ex-outers (cddr capv)))))
(defun ex-inners (capv) (if (or (atom capv) (atom (cdr capv))) nil (cons (cadr capv) (ex-inners (cddr capv)))))

; A LETFN GROUP'S CAPTURE (milestone 5) in a closure: (:grp G m), G its
; group's entries (tm caps), m < |G|; each tm a def's, its caps as many as
; tm's pairs, each the group's own (:grp nil m'), m' < |G|, or a plain
; value. ex-gvals: the plain values a closure's captures hold, its groups'
; entries' among them -- ex-xvs asks them good.
(defun ex-gcap (x) (and (x2-grpp x) (cadr x) t))
(defun ex-gnil (x) (and (x2-grpp x) (null (cadr x))))
(defun ex-gplain (c) (cond ((atom c) nil) ((ex-gnil (car c)) (ex-gplain (cdr c))) (t (cons (car c) (ex-gplain (cdr c))))))
(defun ex-gnils (c n) (or (atom c) (and (or (not (ex-gnil (car c))) (and (natp (caddr (car c))) (< (caddr (car c)) n))) (ex-gnils (cdr c) n))))
(defun ex-gents (g defs n)
  (or (atom g)
      (and (consp (car g)) (consp (assoc-equal (car (car g)) defs)) (true-listp (cadr (car g)))
           (equal (len (cadr (car g))) (len (ex-inners (nth 2 (car (car g)))))) (ex-gnils (cadr (car g)) n)
           (ex-gents (cdr g) defs n))))
(defun ex-gcok (c defs)
  (or (atom c)
      (and (or (not (ex-gcap (car c)))
               (and (true-listp (cadr (car c))) (natp (caddr (car c))) (< (caddr (car c)) (len (cadr (car c))))
                    (ex-gents (cadr (car c)) defs (len (cadr (car c))))))
           (ex-gcok (cdr c) defs))))
(defun ex-gall (g) (if (atom g) nil (append (ex-gplain (cadr (car g))) (ex-gall (cdr g)))))
(defun ex-gvals (c)
  (cond ((atom c) nil) ((ex-gcap (car c)) (append (ex-gall (cadr (car c))) (ex-gvals (cdr c)))) (t (cons (car c) (ex-gvals (cdr c))))))
(defthm ex-count-app (implies (true-listp a) (equal (acl2-count (append a b)) (+ (acl2-count a) (acl2-count b)))))
(defthm ex-tl-gplain (true-listp (ex-gplain c)))
(defthm ex-tl-gall (true-listp (ex-gall g)))
(defthm ex-count-gplain (<= (acl2-count (ex-gplain c)) (acl2-count c)) :rule-classes :linear)
(defthm ex-count-gall (<= (acl2-count (ex-gall g)) (acl2-count g)) :rule-classes :linear
  :hints (("Goal" :induct (ex-gall g)) ("Subgoal *1/2" :use ((:instance ex-count-gplain (c (cadr (car g))))))))
(defthm ex-count-gvals (<= (acl2-count (ex-gvals c)) (acl2-count c)) :rule-classes :linear
  :hints (("Goal" :induct (ex-gvals c)) ("Subgoal *1/2" :use ((:instance ex-count-gall (g (cadr (car c))))))))

; THE VALUES (milestone 2b): every closure-shaped value one whose template
; is in defs (so mx2's :callv finds its def), its captures as many as the
; template's pairs and good themselves or a good group's (ex-gcok, its
; plain values ex-gvals good); any other value is good but the
; symbol :recur-marker (the tree's recur marker's) and
; symbols :clo and :grp themselves, so a variadic call's rest list of good
; values is never closure-shaped nor a letfn group's capture (the model's
; list is the machine's seq, and :clo and :grp no values a program holds:
; x2-res is the identity on a good value, ex-xvs-res); and a list's elements good too, so apply's
; spread of a good seq is good arguments (2c-iii: apply is a value like
; any other, its call spread by vmx2's :applyv)
(defun ex-xvs (defs l)
  (if (atom l)
      t
    (and (let ((v (car l)))
           (and (not (equal v :clo)) (not (equal v :recur-marker)) (not (equal v :grp))
                (if (clop v)
                    (and (equal v (clo (cadr v) (caddr v))) (consp (assoc-equal (cadr v) defs))
                         (true-listp (caddr v)) (equal (len (caddr v)) (len (ex-inners (nth 2 (cadr v)))))
                         (ex-gcok (caddr v) defs) (ex-xvs defs (ex-gvals (caddr v))))
                  (ex-xvs defs v))))
         (ex-xvs defs (cdr l)))))

; THE CALL A GOOD RECORD MAKES, apply's spread or itself, is a good record
(defthm ex-xvs-elem (implies (and (ex-xvs defs (list v)) (not (clop v))) (ex-xvs defs v))
  :hints (("Goal" :expand ((ex-xvs defs (list v))))))
(defthm ex-xvs-last (implies (ex-xvs defs l) (ex-xvs defs (list (car (last l))))))
(defthm ex-xvs-take (implies (ex-xvs defs l) (ex-xvs defs (take n l)))
  :hints (("Goal" :induct (take n l) :expand ((ex-xvs defs l) (:free (a b) (ex-xvs defs (cons a b)))))))
(defthm ex-xvs-append (equal (ex-xvs defs (append a b)) (and (ex-xvs defs a) (ex-xvs defs b))))
(defun-sk ex-lzok (defs) (forall c (ex-xvs defs (sk-real c))))
(defthm ex-xvs-cons1 (implies (syntaxp (not (equal b ''nil)))
                              (equal (ex-xvs defs (cons a b)) (and (ex-xvs defs (list a)) (ex-xvs defs b))))
  :hints (("Goal" :expand ((ex-xvs defs (cons a b)) (ex-xvs defs (list a))))))
(defthm ex-xvs-nth1 (implies (ex-xvs defs l) (ex-xvs defs (list (nth j l))))
  :hints (("Goal" :in-theory (enable nth) :induct (nth j l) :expand ((ex-xvs defs l)))))
(defthm ex-xvs-sk-first
  (implies (and (ex-xvs defs (car c)) (sk-more (sk-d c))) (ex-xvs defs (list (sk-first c))))
  :hints (("Goal" :in-theory (enable sk-d sk-first) :expand ((ex-xvs defs (car c)) (ex-xvs defs (cdr (car c)))))))
(defthm ex-xvs-sk-next
  (implies (and (ex-lzok defs) (ex-xvs defs (car c))) (ex-xvs defs (car (sk-next c))))
  :hints (("Goal" :in-theory (e/d (sk-d sk-next) (ex-lzok)) :expand ((ex-xvs defs (car c)) (ex-xvs defs (cdr (car c))))
                  :use ((:instance ex-lzok-necc (c (cdr (car c))))))))
(defthm ex-sk-els-good
  (implies (and (ex-lzok defs) (ex-xvs defs (car c))) (ex-xvs defs (cdr (sk-els c l))))
  :hints (("Goal" :induct (sk-els c l) :in-theory (disable ex-lzok) :expand ((sk-els c l)))))
(defthm ex-sk-elems-good
  (implies (and (ex-lzok defs) (ex-xvs defs v)) (ex-xvs defs (cdr (sk-elems v))))
  :hints (("Goal" :in-theory (e/d (sk-elems sk-cur) (ex-lzok)))))
(in-theory (disable ex-xvs-cons1 ex-xvs-sk-first ex-xvs-sk-next))

(defthm ex-xvs-noclo
  (implies (and (ex-xvs defs (list v)) (not (ex-clo-shape v))) (ex-xvs defs v))
  :hints (("Goal" :expand ((ex-xvs defs (list v))) :in-theory (enable ex-clo-shape))))
(defthm ex-xvs-atom (implies (atom l) (ex-xvs defs l)))
(defthm ex-last-cdr (implies (consp (cdr l)) (equal (last l) (last (cdr l)))))
(defthm ex-xvs-butlast(implies (ex-xvs defs l) (ex-xvs defs (butlast l n))) :hints (("Goal" :in-theory (enable butlast))))
; APPLY'S SPREAD of good arguments is good arguments (seqk's sk-spread):
; the elements the walk takes and every element it reads (sk-first of a
; good cursor); and the rest it hands over, the cursor's seq read at its
; top with the arguments past req consed on, one good value -- never the
; symbol :clo, as the walk hands over a seq that has another element, or
; arguments past req
(defthm ex-xvs-list1 (implies (and (ex-xvs defs x) (not (equal x :clo)) (not (equal x :recur-marker)) (not (equal x :grp))) (ex-xvs defs (list x)))
  :hints (("Goal" :expand ((ex-xvs defs (list x)) (ex-xvs defs x)))))
(defthm ex-xvs-nthcdr-l (implies (ex-xvs defs l) (ex-xvs defs (nthcdr n l)))
  :hints (("Goal" :induct (nthcdr n l) :expand ((ex-xvs defs l)))))
; a good value is its own resolution, and so a good list its captures read
(defthm ex-xvs-res (implies (ex-xvs defs (list v)) (equal (x2-res v) v))
  :hints (("Goal" :in-theory (enable x2-res x2-grpp) :expand ((ex-xvs defs (list v)) (ex-xvs defs v) (ex-xvs defs (cdr v))))))
(defthm ex-xvs-car1 (implies (and (ex-xvs defs l) (consp l)) (ex-xvs defs (list (car l))))
  :hints (("Goal" :expand ((ex-xvs defs l) (ex-xvs defs (list (car l)))))))
(defthm ex-xvs-resl (implies (ex-xvs defs l) (equal (ex-resl l) l))
  :hints (("Goal" :induct (ex-resl l) :in-theory (disable ex-xvs-car1 ex-xvs-res))
          ("Subgoal *1/2" :use ((:instance ex-xvs-car1) (:instance ex-xvs-res (v (car l)))
                                (:instance ex-xvs-nthcdr-l (n 1))))))
; A GROUP'S CAPTURE RESOLVED IS A GOOD CLOSURE (milestone 5): so a good
; closure's captures, resolved as a call binds them, are good values; and
; a plain good list is its own ex-gvals, no group capture among it
(defthm ex-xvs-nogrp (implies (ex-xvs defs (list x)) (not (x2-grpp x)))
  :hints (("Goal" :expand ((ex-xvs defs (list x)) (ex-xvs defs x) (ex-xvs defs (cdr x))))))
(defthm ex-xvs-plain (implies (and (ex-xvs defs l) (true-listp l)) (and (equal (ex-gvals l) l) (ex-gcok l defs)))
  :hints (("Goal" :induct (len l) :in-theory (disable ex-xvs-car1 ex-xvs-nogrp))
          ("Subgoal *1/1" :use ((:instance ex-xvs-car1) (:instance ex-xvs-nogrp (x (car l))) (:instance ex-xvs-nthcdr-l (n 1))))))
(defthm ex-gents-nth
  (implies (and (ex-gents g defs n) (natp m) (< m (len g)))
           (and (consp (assoc-equal (car (nth m g)) defs)) (true-listp (cadr (nth m g)))
                (equal (len (cadr (nth m g))) (len (ex-inners (nth 2 (car (nth m g)))))) (ex-gnils (cadr (nth m g)) n)))
  :hints (("Goal" :in-theory (enable nth) :induct (nth m g))))
(defthm ex-gall-nth
  (implies (and (ex-xvs defs (ex-gall g)) (natp m) (< m (len g))) (ex-xvs defs (ex-gplain (cadr (nth m g)))))
  :hints (("Goal" :in-theory (enable nth) :induct (nth m g))))
(defthm ex-fill-tl (equal (true-listp (x2-fill c g)) (true-listp c)))
(defthm ex-fill-len (equal (len (x2-fill c g)) (len c)))
(defthm ex-fill-good
  (implies (and (consp g) (true-listp g) (ex-gnils c (len g)) (ex-gents g defs (len g))
                (ex-xvs defs (ex-gplain c)) (ex-xvs defs (ex-gall g)))
           (and (ex-gcok (x2-fill c g) defs) (ex-xvs defs (ex-gvals (x2-fill c g)))))
  :hints (("Goal" :induct (len c) :in-theory (disable ex-xvs-car1 ex-xvs-nogrp))
          ("Subgoal *1/1" :use ((:instance ex-xvs-car1 (l (ex-gplain c))) (:instance ex-xvs-nogrp (x (car c)))
                                (:instance ex-xvs-nthcdr-l (n 1) (l (ex-gplain c)))))))
(defthm ex-xvs-gres
  (implies (and (ex-gcap x) (ex-gcok (list x) defs) (ex-xvs defs (ex-gall (cadr x))))
           (ex-xvs defs (list (x2-res x))))
  :hints (("Goal" :in-theory (e/d (x2-res clo clop) (ex-gents-nth ex-gall-nth ex-fill-good))
                  :use ((:instance ex-gents-nth (g (cadr x)) (m (caddr x)) (n (len (cadr x))))
                        (:instance ex-gall-nth (g (cadr x)) (m (caddr x)))
                        (:instance ex-fill-good (g (cadr x)) (c (cadr (nth (caddr x) (cadr x))))))
                  :expand ((:free (a) (ex-xvs defs (list a)))))))
(defthm ex-xvs-resl-caps
  (implies (and (ex-gcok c defs) (ex-xvs defs (ex-gvals c))) (ex-xvs defs (ex-resl c)))
  :hints (("Goal" :induct (len c) :in-theory (e/d (ex-xvs-cons1) (ex-xvs-gres ex-xvs-res)))
          ("Subgoal *1/1" :use ((:instance ex-xvs-gres (x (car c))) (:instance ex-xvs-res (v (car c)))))))
(defthm ex-xvs-clo-resl
  (implies (and (ex-xvs defs (list v)) (clop v)) (ex-xvs defs (ex-resl (caddr v))))
  :hints (("Goal" :expand ((ex-xvs defs (list v))))))
(defthm ex-resl-tl (equal (true-listp (ex-resl c)) (true-listp c)))
(defthm ex-resl-len (equal (len (ex-resl c)) (len c)))
; A LAZY SEQ'S ELEMENTS are what the runtime's realisations give (seqk's
; sk-real, constrained by nothing): the agreement asks they be good values
; too, as it asks it of the scope's -- ex-lzok, the runtime handing the
; machine only closures it knows. Then a good seq's elements, every kind,
; are good.
(defthm ex-xvs-sk-topv (implies (ex-xvs defs v) (ex-xvs defs (sk-topv v)))
  :hints (("Goal" :induct (sk-topv v) :expand ((ex-xvs defs v) (:free (a b) (ex-xvs defs (cons a b)))))))
(defthm ex-sk-cval-good (implies (ex-xvs defs (car c)) (ex-xvs defs (sk-cval c)))
  :hints (("Goal" :in-theory (enable sk-cval) :expand ((ex-xvs defs (car c)) (:free (b) (ex-xvs defs (cons :vec b)))))))
(defthm ex-sk-cval-noclo (implies (sk-more (sk-d c)) (and (consp (sk-cval c)) (not (equal (sk-cval c) :clo)) (not (equal (sk-cval c) :recur-marker)) (not (equal (sk-cval c) :grp))))
  :hints (("Goal" :in-theory (enable sk-cval sk-d sk-kind sk-step sk-topv))))
(defthm ex-xvs-consv (implies (and (ex-xvs defs xs) (ex-xvs defs s)) (ex-xvs defs (sk-consv xs s)))
  :hints (("Goal" :induct (sk-consv xs s) :expand ((ex-xvs defs xs) (:free (a b) (ex-xvs defs (cons a b)))))))
(defthm ex-consv-consp (implies (consp xs) (consp (sk-consv xs s))))
(defthm ex-consv-noclo (implies (consp xs) (and (not (equal (sk-consv xs s) :clo)) (not (equal (sk-consv xs s) :recur-marker)) (not (equal (sk-consv xs s) :grp)))))
(defthm ex-consv-id (implies (atom xs) (equal (sk-consv xs s) s)))
(defthm ex-nthcdr-consp (implies (and (natp n) (< n (len l))) (consp (nthcdr n l))))
(defthm ex-apwalk-good
  (implies (and (ex-lzok defs) (ex-xvs defs (car c)) (ex-xvs defs fx))
           (let ((w (ex-apwalk req fx c)))
             (and (ex-xvs defs (nth 1 w))
                  (if (equal (car w) 2)
                      (and (ex-xvs defs (nth 2 w)) (ex-xvs defs (car (nth 3 w)))
                           (or (consp (nth 2 w)) (sk-more (sk-d (nth 3 w)))))
                    (ex-xvs defs (car (nth 2 w)))))))
  :hints (("Goal" :induct (ex-apwalk req fx c) :expand ((ex-apwalk req fx c))
                  :in-theory (e/d (ex-xvs-sk-first ex-xvs-sk-next ex-apstep ex-aplook) (ex-lzok)))))
(defthm ex-sk-spread-good
  (implies (and (ex-lzok defs) (ex-xvs defs fx) (ex-xvs defs v))
           (ex-xvs defs (cadr (sk-spread req fx v))))
  :hints (("Goal" :in-theory (e/d (sk-spread sk-cur) (ex-lzok ex-apwalk-good ex-apwalk sk-cval sk-consv sk-els ex-xvs))
                  :do-not-induct t
                  :cases ((consp (nth 2 (ex-apwalk req fx (sk-cur v)))))
                  :use ((:instance ex-apwalk-good (c (sk-cur v)))))))
(in-theory (disable ex-apwalk-good))

(defthm ex-callee-nop (implies (not (equal (ex-apway tmp) 1)) (equal (ex-callee tmp) tmp))
  :hints (("Goal" :in-theory (enable ex-callee))))
(in-theory (disable ex-callee ex-apway ex-lzok))
