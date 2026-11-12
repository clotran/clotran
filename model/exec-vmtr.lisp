; THE TREE'S TRANSLATION TO VMX2 (model/exec-vm.lisp's first part): the
; translation ex-tr, the good values ex-xvs, well-formedness ex-vwf, the
; scope's agreement and the translation's x2wf. exec-vm.lisp's header
; says what they are; this book is it split for size, nothing restated.

(in-package "ACL2")

(include-book "exec")
(include-book "vmx2")

(defthm ex-i2-natp (natp (ex-i2 e)) :rule-classes :type-prescription)
(defthm ex-s2-natp (natp (ex-s2 e)) :rule-classes :type-prescription)
(defthm ex-nk-natp (natp (ex-nk e)) :rule-classes :type-prescription)
(defthm ex-rstart-natp2 (natp (ex-rstart e)) :rule-classes :type-prescription)
(defthm ex-rn-natp2 (natp (ex-rn e)) :rule-classes :type-prescription)

(defun ex-vrank (flg) (case flg ((:do :let :rec :call :coll :cs :ct :fin) 0) (otherwise 1)))
(defun ex-vleft (flg e i)
  (case flg (:let (nfix (- (ex-i2 e) (nfix i)))) ((:do :rec :call :coll) (nfix (- (ex-nk e) (nfix i))))
    ((:cs :ct) (nfix (- (len (ex-c e)) (nfix i)))) (otherwise 0)))

(defun ex-pos (s cm) (cond ((atom cm) 0) ((equal s (car cm)) 0) (t (1+ (ex-pos s (cdr cm))))))

; slots s .. s+n-1; a loop's scope list: the dummy, then its slots
(defun ex-slots (s n) (if (zp n) nil (cons (nfix s) (ex-slots (1+ (nfix s)) (1- n)))))
(defun ex-lsl (lp) (cons nil (ex-slots (car lp) (cdr lp))))
; the arity x2wf asks a recur in the tail of loop lp (nil: none may stand)
(defun ex-k (lp) (if (consp lp) (1+ (nfix (cdr lp))) nil))
; cm with every entry of ls blanked
(defun ex-blank (ls cm)
  (if (atom cm) cm (cons (if (member-equal (car cm) ls) nil (car cm)) (ex-blank ls (cdr cm)))))
; no entry of cm but nil is in ls
(defun ex-nomem (ls cm)
  (if (atom cm) t (and (or (null (car cm)) (not (member-equal (car cm) ls))) (ex-nomem ls (cdr cm)))))
(defun ex-locals (ls cm) (if (atom ls) nil (cons (list :local (ex-pos (car ls) cm)) (ex-locals (cdr ls) cm))))
; a template's capture pairs (outer inner): their outer and inner slots, as ex-caps and ex-bind-caps walk them
(defun ex-outers (capv) (if (or (atom capv) (atom (cdr capv))) nil (cons (car capv) (ex-outers (cddr capv)))))
(defun ex-inners (capv) (if (or (atom capv) (atom (cdr capv))) nil (cons (cadr capv) (ex-inners (cddr capv)))))

; a call, head first as the tree runs it: the head's value bound at
; position p, its cast to IFn asked of the runtime (prim :ifn, as the tree's
; ex-ifn), then :applyv of it on the arguments, or :not-fn thrown
(defun ex-trcall (h args p)
  (list :let h (list :if (list :prim :ifn (list :local p)) (list* :applyv (list :local p) args) '(:throw (:const :not-fn)))))

; A TRY (exec-PLAN 3b): (:try B H), H the catch walk at the thrown value's
; position p -- (:if (:prim :isa (:const c) (:local p)) Hj ..(:throw (:local
; p))), clause j's body Hj in scope cm ++ (slot j) -- and with a finally F,
; vmx2's desugaring: (:let (:try X (:if F (:throw p) (:throw p))) (:if F p
; p)), F in scope cm ++ (nil) both times (its value discarded, the try's kept)
(defun ex-trh (cs hs p)
  (if (atom cs)
      (list :throw (list :local p))
    (list :if (list :prim :isa (list :const (nth 0 (car cs))) (list :local p)) (car hs) (ex-trh (cdr cs) (cdr hs) p))))
(defun ex-trfin (x f p)
  (list :let (list :try x (list :if f (list :throw (list :local p)) (list :throw (list :local p))))
        (list :if f (list :local p) (list :local p))))
(defun ex-trtry (b hs f cs fin p)
  (let ((x (list :try b (ex-trh cs hs p)))) (if fin (ex-trfin x f p) x)))

; A CASE (exec-PLAN 3b): (:let X W), X its test, W the table's walk at the
; test's value's position p -- (:if (:prim :case (:const t) (:local p)) Tj ..D),
; entry j's then Tj and the default D in scope cm ++ (nil), in the case's tail
(defun ex-trcs (ct ts d p)
  (if (atom ct)
      d
    (list :if (list :prim :case (list :const (nth 0 (car ct))) (list :local p)) (car ts) (ex-trcs (cdr ct) (cdr ts) d p))))

; A LETFN (milestone 5): its n fns in slots s .. s+n-1, n of mx2's lets,
; the j-th (:mkgrp (j . shape) caps..) -- shape each fn's template and
; count of captures, caps every fn's captures in turn: one of the group's
; slots (:const (:grp nil o-s)), any other its outer slot's local in the
; letfn's scope cm -- then the body in scope cm ++ (s .. s+n-1)
(defun ex-lfcaps (os s n cm)
  (if (atom os)
      nil
    (cons (if (ex-ingrp (car os) s n) (list :const (list :grp nil (- (car os) (nfix s)))) (list :local (ex-pos (car os) cm)))
          (ex-lfcaps (cdr os) s n cm))))
(defun ex-lfos (e j) (ex-outers (nth 2 (ex-c (ex-kid-of e j)))))
(defun ex-lfshape (e j)
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e))
      (cons (cons (ex-c (ex-kid-of e (nfix j))) (len (ex-lfos e (nfix j)))) (ex-lfshape e (1+ (nfix j))))
    nil))
(defun ex-lfargs (e j cm)
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e))
      (append (ex-lfcaps (ex-lfos e (nfix j)) (ex-s2 e) (ex-i2 e) cm) (ex-lfargs e (1+ (nfix j)) cm))
    nil))
(defun ex-trlf (e j cm x)
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e))
      (list :let (list* :mkgrp (cons (nfix j) (ex-lfshape e 0)) (ex-lfargs e 0 cm)) (ex-trlf e (1+ (nfix j)) cm x))
    x))
; well formed: each init a fn (kind 14) of a def's template, its outer
; slots naturals, each one of the group's or in scope
(defun ex-lfin (os s n cm)
  (or (atom os) (and (natp (car os)) (or (ex-ingrp (car os) s n) (member-equal (car os) cm)) (ex-lfin (cdr os) s n cm))))
(defun ex-lffns (e j)
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e))
      (and (consp (ex-kid-of e (nfix j))) (equal (ex-kind (ex-kid-of e (nfix j))) 14) (nat-listp (ex-lfos e (nfix j)))
           (ex-lffns e (1+ (nfix j))))
    t))
(defun ex-lfok (e j cm defs)
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e))
      (and (consp (assoc-equal (ex-c (ex-kid-of e (nfix j))) defs)) (ex-lfin (ex-lfos e (nfix j)) (ex-s2 e) (ex-i2 e) cm)
           (ex-lfok e (1+ (nfix j)) cm defs))
    t))

; A COLLECTION: the runtime's build of its elements' values, (:prim op
; args..) -- a vector :vector, a map :map, a set :set, a new or a host action (:host k C)
; (ex-cop, exec.lisp)

; THE SLOTS A NODE MAY CLEAR (milestone 4): its marked reads', every one a
; run of it may make -- a branch's, a catch's -- but none of a fn's body,
; which clears its own frame. A place a run reaches after a part ran sees
; the scope with those slots blanked (ex-blank): no name reaches them.
(defun ex-clr (flg e i)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        nil
      (case flg
        (:do (cond ((zp nk) nil)
                   ((< i (- nk 1)) (append (ex-clr :m (ex-kid-of e i) 0) (ex-clr :do e (1+ i))))
                   (t (ex-clr :m (ex-kid-of e (- nk 1)) 0))))
        (:let (if (< i n2) (append (ex-clr :m (ex-kid-of e i) 0) (ex-clr :let e (1+ i))) (ex-clr :m (ex-kid-of e n2) 0)))
        ((:rec :call :coll) (if (< i nk) (append (ex-clr :m (ex-kid-of e i) 0) (ex-clr flg e (1+ i))) nil))
        (:cs (if (< i (len (ex-c e))) (append (ex-clr :m (ex-cbody e i) 0) (ex-clr :cs e (1+ i))) nil))
        (:ct (if (< i (len (ex-c e))) (append (ex-clr :m (ex-cthen e i) 0) (ex-clr :ct e (1+ i))) nil))
        (:fin (ex-clr :m (ex-kid-of e 1) 0))
        (otherwise
         (cond ((equal k 2) (if (ex-mark e) (list n2) nil))
               ((equal k 4) (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :m (ex-kid-of e 1) 0) (ex-clr :m (ex-kid-of e 2) 0)))
               ((equal k 5) (ex-clr :do e 0))
               ((or (equal k 11) (equal k 12)) (ex-clr :let e 0))
               ((equal k 16) (ex-clr :rec e 0))
               ((equal k 17) (ex-clr :m (ex-kid-of e 0) 0))
               ((equal k 18) (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0) (ex-clr :fin e 0)))
               ((member k '(7 8 9 22 23 10 20 24)) (ex-clr :coll e 0))
               ((equal k 19) (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :m (ex-kid-of e 1) 0) (ex-clr :ct e 0)))
               ((equal k 6) (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :call e 1)))
               (t nil)))))))

(defun ex-tr (flg e i cm)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        '(:const nil)
      (case flg
        (:do (cond ((zp nk) '(:const nil))
                   ((< i (- nk 1)) (let ((r (ex-tr :do e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm)))) (list :if (ex-tr :m (ex-kid-of e i) 0 cm) r r)))
                   (t (ex-tr :m (ex-kid-of e (- nk 1)) 0 cm))))
        (:let (cond ((< i n2)
                     (list :let (ex-tr :m (ex-kid-of e i) 0 cm)
                           (ex-tr :let e (1+ i) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (list (+ (ex-s2 e) i))))))
                    ((equal k 12)
                     (let ((ls (cons nil (ex-slots (ex-s2 e) n2))))
                       (list :loop (cons '(:const nil) (ex-locals (cdr ls) cm))
                             (ex-tr :m (ex-kid-of e n2) 0 (append (ex-blank ls cm) ls)))))
                    (t (ex-tr :m (ex-kid-of e n2) 0 cm))))
        ((:rec :call :coll)
         (if (< i nk) (cons (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr flg e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm))) nil))
        (:cs (if (< i (len (ex-c e)))
                 (cons (ex-tr :m (ex-cbody e i) 0 (append cm (list (ex-cslot e i)))) (ex-tr :cs e (1+ i) cm))
               nil))
        (:fin (ex-tr :m (ex-kid-of e 1) 0 (append cm (list nil))))
        (:ct (if (< i (len (ex-c e))) (cons (ex-tr :m (ex-cthen e i) 0 cm) (ex-tr :ct e (1+ i) cm)) nil))
        (otherwise
         (cond ((or (equal k 1) (equal k 3)) (list :const (ex-c e)))
               ((equal k 14) (list* :mkclo (ex-c e) (ex-locals (ex-outers (nth 2 (ex-c e))) cm)))
               ((equal k 6) (ex-trcall (ex-tr :m (ex-kid-of e 0) 0 cm)
                                    (ex-tr :call e 1 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil))) (len cm)))
               ((equal k 2) (list :local (ex-pos (ex-i2 e) cm)))
               ((equal k 4) (let ((cm1 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm)))
                              (list :if (ex-tr :m (ex-kid-of e 0) 0 cm) (ex-tr :m (ex-kid-of e 1) 0 cm1)
                                    (if (< 2 nk) (ex-tr :m (ex-kid-of e 2) 0 cm1) '(:const nil)))))
               ((equal k 5) (ex-tr :do e 0 cm))
               ((or (equal k 11) (equal k 12)) (ex-tr :let e 0 cm))
               ((equal k 13) (ex-trlf e 0 cm (ex-tr :m (ex-kid-of e n2) 0 (append cm (ex-slots (ex-s2 e) n2)))))
               ((equal k 16) (list* :recur '(:const nil) (ex-tr :rec e 0 cm)))
               ((equal k 17) (list :throw (ex-tr :m (ex-kid-of e 0) 0 cm)))
               ((equal k 18) (ex-trtry (ex-tr :m (ex-kid-of e 0) 0 cm) (ex-tr :cs e 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm))
                                       (ex-tr :fin e 0 (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm))
                                       (ex-c e) (< 1 nk) (len cm)))
               ((member k '(7 8 9 22 23 10 20 24)) (list* :prim (ex-cop e) (ex-tr :coll e 0 cm)))
               ((equal k 19) (list :let (ex-tr :m (ex-kid-of e 0) 0 cm)
                                   (ex-trcs (ex-c e) (ex-tr :ct e 0 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)))
                                            (ex-tr :m (ex-kid-of e 1) 0 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)))
                                            (len cm))))
               (t '(:const nil))))))))

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

; well-formed: the core, every local in scope -- a marked one's slot
; blanked after its read for every place a run reaches later (ex-clr),
; a loop's body clearing nothing of the scope outside it -- every let's and loop's
; slot new to the scope, a recur only in the tail of a loop lp -- (s . n),
; its first slot and count of bindings, nil outside every loop's tail --
; writing that loop's slots with as many values; a constant's and a Var's
; value good, a fn's template in defs, its outer slots in scope
(defun ex-vwf (flg e i cm lp defs)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (and (consp e)
         (case flg
           (:do (cond ((zp nk) t)
                      ((< i (- nk 1)) (and (ex-vwf :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf :do e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) lp defs)))
                      (t (ex-vwf :m (ex-kid-of e (- nk 1)) 0 cm lp defs))))
           (:let (cond ((< i n2)
                        (and (or (equal k 11) (equal k 12)) (not (member-equal (+ (ex-s2 e) i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm)))
                             (ex-vwf :m (ex-kid-of e i) 0 cm nil defs)
                             (ex-vwf :let e (1+ i) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (list (+ (ex-s2 e) i))) lp defs)))
                       ((equal k 11) (ex-vwf :m (ex-kid-of e n2) 0 cm lp defs))
                       ((equal k 12)
                        (let ((ls (cons nil (ex-slots (ex-s2 e) n2))))
                          (and (subsetp-equal (cdr ls) cm) (ex-nomem (ex-clr :m (ex-kid-of e n2) 0) (ex-blank ls cm))
                               (ex-vwf :m (ex-kid-of e n2) 0 (append (ex-blank ls cm) ls) (cons (ex-s2 e) n2) defs))))
                       (t nil)))
           (:rec (and (equal k 16) (consp lp) (equal (ex-rstart e) (car lp)) (equal (ex-rn e) (cdr lp))
                      (equal nk (cdr lp))
                      (if (< i nk)
                          (and (ex-vwf :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf :rec e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) lp defs))
                        (equal i nk))))
           (:call (and (equal k 6)
                       (if (< i nk)
                           (and (ex-vwf :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf :call e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) lp defs))
                         t)))
           (:cs (and (equal k 18)
                     (if (< i (len (ex-c e)))
                         (and (not (member-equal (ex-cslot e i) cm))
                              (ex-vwf :m (ex-cbody e i) 0 (append cm (list (ex-cslot e i))) nil defs)
                              (ex-vwf :cs e (1+ i) cm lp defs))
                       t)))
           (:fin (or (not (< 1 nk)) (ex-vwf :m (ex-kid-of e 1) 0 (append cm (list nil)) nil defs)))
           (:coll (and (member k '(7 8 9 22 23 10 20 24))
                       (if (< i nk)
                           (and (ex-vwf :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf :coll e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) lp defs))
                         t)))
           (:ct (and (equal k 19)
                     (if (< i (len (ex-c e)))
                         (and (ex-vwf :m (ex-cthen e i) 0 cm lp defs) (ex-vwf :ct e (1+ i) cm lp defs))
                       t)))
           (otherwise
            (cond ((or (equal k 1) (equal k 3)) (ex-xvs defs (list (ex-c e))))
                  ((equal k 2) (member-equal (ex-i2 e) cm))
                  ((equal k 14) (and (consp (assoc-equal (ex-c e) defs))
                                     (nat-listp (ex-outers (nth 2 (ex-c e))))
                                     (subsetp-equal (ex-outers (nth 2 (ex-c e))) cm)))
                  ((equal k 6) (and (< 0 nk) (ex-vwf :m (ex-kid-of e 0) 0 cm nil defs) (ex-vwf :call e 1 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)) lp defs)))
                  ((equal k 4) (and (or (equal nk 2) (equal nk 3))
                                    (ex-vwf :m (ex-kid-of e 0) 0 cm nil defs) (ex-vwf :m (ex-kid-of e 1) 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) lp defs)
                                    (or (equal nk 2) (ex-vwf :m (ex-kid-of e 2) 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) lp defs))))
                  ((equal k 5) (ex-vwf :do e 0 cm lp defs))
                  ((equal k 11) (and (equal nk (1+ n2)) (ex-vwf :let e 0 cm lp defs)))
                  ((equal k 12) (and (equal nk (1+ n2)) (ex-nomem (cons nil (ex-slots (ex-s2 e) n2)) cm)
                                     (ex-vwf :let e 0 cm lp defs)))
                  ((equal k 13) (and (equal nk (1+ n2)) (< 0 n2) (ex-lffns e 0) (ex-lfok e 0 cm defs)
                                     (ex-nomem (cons nil (ex-slots (ex-s2 e) n2)) cm) (ex-nomem (ex-clr :m (ex-kid-of e n2) 0) cm)
                                     (ex-vwf :m (ex-kid-of e n2) 0 (append cm (ex-slots (ex-s2 e) n2)) lp defs)))
                  ((equal k 16) (and (consp lp) (equal (ex-rstart e) (car lp)) (equal (ex-rn e) (cdr lp))
                                     (equal nk (cdr lp)) (ex-vwf :rec e 0 cm lp defs)))
                  ((equal k 17) (and (equal nk 1) (ex-vwf :m (ex-kid-of e 0) 0 cm nil defs)))
                  ((equal k 18) (and (or (equal nk 1) (equal nk 2)) (ex-vwf :m (ex-kid-of e 0) 0 cm nil defs)
                                     (ex-vwf :cs e 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) nil defs)
                                     (ex-vwf :fin e 0 (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm) nil defs)))
                  ((member k '(7 8 9 22 23 10 20 24)) (ex-vwf :coll e 0 cm nil defs))
                  ((equal k 19) (and (equal nk 2) (ex-vwf :m (ex-kid-of e 0) 0 cm nil defs)
                                     (ex-vwf :m (ex-kid-of e 1) 0 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)) lp defs)
                                     (ex-vwf :ct e 0 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)) lp defs)))
                  (t nil)))))))

; A FN'S TEMPLATE (name arities caps nslots self), each arity (nf variadic
; start body): nf fixed parameters in slots start .. start+nf-1 and, when
; variadic, the rest in slot start+nf -- np parameters in all; the capture
; pairs' inner slots and the self slot (if any) distinct from them and each
; other. Its def in mx2, keyed by the template itself, is a clause for each
; arity, (nf body) or (nf body :rest) as vmx2's are: the body lets of
; (:capt j) for the m captures and of the closure remade, (:mkclo template
; (:capt 0) ..), for the self slot -- the scope bcm, the parameters, the
; inner slots and the self slot by position (mx2's arguments, the rest
; list among them, then the lets) -- around the 1b loop of the parameters'
; copies, so a recur to the fn is that loop's (a variadic one's np values,
; the rest a list, as clj's).
(defun ex-anf (ar) (nfix (nth 0 ar)))
(defun ex-avar (ar) (truthy (nth 1 ar)))
(defun ex-anp (ar) (+ (ex-anf ar) (if (ex-avar ar) 1 0)))
(defun ex-astart (ar) (nfix (nth 2 ar)))
(defun ex-abody (ar) (nth 3 ar))
(defun ex-fself (tm) (if (natp (nth 4 tm)) (nth 4 tm) nil))
(defun ex-fparams (ar) (ex-slots (ex-astart ar) (ex-anp ar)))
(defun ex-fbcm (tm ar) (append (ex-fparams ar) (ex-inners (nth 2 tm)) (list (ex-fself tm))))
(defun ex-flp (ar) (cons (ex-astart ar) (ex-anp ar)))
(defun ex-fcm (tm ar) (ex-blank (ex-lsl (ex-flp ar)) (ex-fbcm tm ar)))
(defun ex-fcmb (tm ar) (append (ex-fcm tm ar) (ex-lsl (ex-flp ar))))
(defun ex-capts (j m) (if (zp m) nil (cons (list :capt (nfix j)) (ex-capts (1+ (nfix j)) (1- m)))))
(defun ex-clets (j m x) (if (zp m) x (list :let (list :capt (nfix j)) (ex-clets (1+ (nfix j)) (1- m) x))))
(defun ex-fbtr (tm ar)
  (let ((m (len (ex-inners (nth 2 tm)))))
    (ex-clets 0 m (list :let (list* :mkclo tm (ex-capts 0 m))
                        (list :loop (cons '(:const nil) (ex-locals (ex-fparams ar) (ex-fbcm tm ar)))
                              (ex-tr :m (ex-abody ar) 0 (ex-fcmb tm ar)))))))
(defun ex-clause (tm ar)
  (if (ex-avar ar) (list (ex-anf ar) (ex-fbtr tm ar) :rest) (list (ex-anf ar) (ex-fbtr tm ar))))
(defun ex-clauses (tm ars) (if (atom ars) nil (cons (ex-clause tm (car ars)) (ex-clauses tm (cdr ars)))))
(defun ex-def (tm) (ex-clauses tm (nth 1 tm)))
(defun ex-arwf (tm ar defs)
  (and (natp (nth 0 ar)) (natp (nth 2 ar))
       (not (intersectp-equal (ex-inners (nth 2 tm)) (ex-fparams ar)))
       (or (not (natp (nth 4 tm))) (not (member-equal (nth 4 tm) (ex-fparams ar))))
       (ex-vwf :m (ex-abody ar) 0 (ex-fcmb tm ar) (ex-flp ar) defs)
       ; a body that clears a capture or the self slot runs once: no recur to the fn
       (or (ex-nomem (ex-clr :m (ex-abody ar) 0) (ex-fcm tm ar)) (ex-vwf :m (ex-abody ar) 0 (ex-fcmb tm ar) nil defs))))
(defun ex-arswf (tm ars defs) (if (atom ars) t (and (ex-arwf tm (car ars) defs) (ex-arswf tm (cdr ars) defs))))
(defun ex-tmwf (tm defs)
  (and (nat-listp (ex-inners (nth 2 tm))) (no-duplicatesp-equal (ex-inners (nth 2 tm)))
       (or (not (natp (nth 4 tm))) (not (member-equal (nth 4 tm) (ex-inners (nth 2 tm)))))
       (ex-arswf tm (nth 1 tm) defs)))
; every def a template's, the template well formed in defs
(defun ex-defs-ok (ds defs)
  (if (atom ds)
      (null ds)
    (and (consp (car ds)) (equal (cdar ds) (ex-def (caar ds))) (ex-tmwf (caar ds) defs) (ex-defs-ok (cdr ds) defs))))

; the loop-free core, well formed as ex-vwf is outside a loop: what
; exec-cost bounds (a loop's turns depend on its iterations, a call's on its
; callee), a Var and a fn leaves as a constant is
(defun ex-lfwf (flg e i cm)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (and (consp e)
         (case flg
           (:do (cond ((zp nk) t)
                      ((< i (- nk 1)) (and (ex-lfwf :m (ex-kid-of e i) 0 cm) (ex-lfwf :do e (1+ i) cm)))
                      (t (ex-lfwf :m (ex-kid-of e (- nk 1)) 0 cm))))
           (:let (if (< i n2)
                     (and (equal k 11) (not (member-equal (+ (ex-s2 e) i) cm)) (ex-lfwf :m (ex-kid-of e i) 0 cm)
                          (ex-lfwf :let e (1+ i) (append cm (list (+ (ex-s2 e) i)))))
                   (and (equal k 11) (ex-lfwf :m (ex-kid-of e n2) 0 cm))))
           ((:rec :call :coll :cs :ct :fin) nil)
           (otherwise
            (cond ((member-equal k (quote (1 3 14))) t)
                  ((equal k 2) (and (member-equal (ex-i2 e) cm) (not (ex-mark e))))
                  ((equal k 4) (and (or (equal nk 2) (equal nk 3))
                                    (ex-lfwf :m (ex-kid-of e 0) 0 cm) (ex-lfwf :m (ex-kid-of e 1) 0 cm)
                                    (or (equal nk 2) (ex-lfwf :m (ex-kid-of e 2) 0 cm))))
                  ((equal k 5) (ex-lfwf :do e 0 cm))
                  ((equal k 11) (and (equal nk (1+ n2)) (ex-lfwf :let e 0 cm)))
                  (t nil)))))))

(defun ex-agree (cm env fr)
  (if (atom cm)
      (atom env)
    (and (consp env)
         (or (not (natp (car cm))) (equal (car env) (nth (car cm) fr)))
         (ex-agree (cdr cm) (cdr env) fr))))

; ---- the scope ----------------------------------------------------------------------------------

(defthm ex-agree-local
  (implies (and (ex-agree cm env fr) (member-equal s cm) (natp s))
           (equal (nth (ex-pos s cm) env) (nth s fr))))

(defthm ex-agree-write
  (implies (and (not (member-equal s cm)) (natp s))
           (equal (ex-agree cm env (update-nth s v fr)) (ex-agree cm env fr))))

(defthm ex-agree-len (implies (ex-agree cm env fr) (equal (len env) (len cm))) :rule-classes :forward-chaining)

(defthm ex-agree-app
  (implies (equal (len a) (len x))
           (equal (ex-agree (append a b) (append x y) fr) (and (ex-agree a x fr) (ex-agree b y fr))))
  :hints (("Goal" :induct (ex-agree a x fr))))

(defthm ex-agree-append
  (implies (and (ex-agree cm env fr) (natp s))
           (equal (ex-agree (append cm (list s)) (append env (list v)) fr)
                  (equal v (nth s fr)))))

(defthm ex-len-append (equal (len (append a b)) (+ (len a) (len b))))
(defthm ex-len-0 (equal (equal (len x) 0) (not (consp x))))
(defthm ex-len-blank (equal (len (ex-blank ls cm)) (len cm)))
(defthm ex-blank-append (equal (ex-blank ls (append a b)) (append (ex-blank ls a) (ex-blank ls b))))
(defthm ex-agree-blank (implies (ex-agree cm env fr) (ex-agree (ex-blank ls cm) env fr)))
(defthm ex-blank-id (implies (ex-nomem ls cm) (equal (ex-blank ls cm) cm)))
(defthm ex-nomem-blank (ex-nomem ls (ex-blank ls cm)))
; CLEARING (milestone 4): blanking twice is blanking by both, and a scope
; that agrees blanked by a agrees blanked by more
(defthm ex-member-app (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))
(defthm ex-sub-mem (implies (and (member-equal x a) (subsetp-equal a b)) (member-equal x b)))
(defthm ex-blank-blank (equal (ex-blank b (ex-blank a cm)) (ex-blank (append a b) cm)))
(defthm ex-nomem-append (equal (ex-nomem (append a b) cm) (and (ex-nomem a cm) (ex-nomem b cm))))
(defthm ex-blank-nil (equal (ex-blank nil cm) cm))
(defthm ex-blank-app-nomem (implies (ex-nomem b cm) (equal (ex-blank (append a b) cm) (ex-blank a cm))))
(defthm ex-blank-sub (implies (subsetp-equal a b) (equal (ex-blank b (ex-blank a cm)) (ex-blank b cm))) :rule-classes nil
  :hints (("Goal" :in-theory (disable ex-blank-blank))))
(defthm ex-agree-blank-mono
  (implies (and (ex-agree (ex-blank a cm) env fr) (subsetp-equal a b)) (ex-agree (ex-blank b cm) env fr))
  :hints (("Goal" :in-theory (disable ex-blank-blank ex-agree-blank) :use (ex-blank-sub (:instance ex-agree-blank (ls b) (cm (ex-blank a cm)))))))
(defthm ex-member-blank (implies (and (member-equal s (ex-blank a cm)) s) (member-equal s cm)))
(defthm ex-blank-nomem (implies (and (member-equal s ls) s) (not (member-equal s (ex-blank ls cm)))))
; a marked read clears its slot: the scope blanked of it agrees after
(defthm ex-agree-clear
  (implies (and (ex-agree cm env fr) (natp s)) (ex-agree (ex-blank (list s) cm) env (update-nth s v fr)))
  :hints (("Goal" :in-theory (disable ex-agree-write ex-blank-blank) :use ((:instance ex-agree-write (cm (ex-blank (list s) cm)))))))
(defthm ex-sub-app1 (implies (subsetp-equal a b) (subsetp-equal a (append b c))))
(defthm ex-sub-app2 (implies (subsetp-equal a c) (subsetp-equal a (append b c))))
(defthm ex-sub-cons (implies (subsetp-equal a b) (subsetp-equal a (cons x b))))
(defthm ex-sub-refl (subsetp-equal a a))
(defthm ex-sub-app (equal (subsetp-equal (append a b) c) (and (subsetp-equal a c) (subsetp-equal b c))))
(defthm ex-nat-listp-slots (nat-listp (ex-slots s n)))
(defthm ex-len-slots (equal (len (ex-slots s n)) (nfix n)))
(defthm ex-len-locals (equal (len (ex-locals ls cm)) (len ls)))
(defthm ex-app-assoc (equal (append (append a b) c) (append a (append b c))))
(defthm ex-app-nil (implies (true-listp x) (equal (append x nil) x)))
(defthm ex-take-len (implies (and (true-listp x) (equal n (len x))) (equal (take n x) x)))

(defthm ex-slots-below (implies (< j (nfix s)) (not (member-equal j (ex-slots s n)))))

(defthm ex-nth-write
  (implies (and (natp j) (not (member-equal j (ex-slots s (len vs)))))
           (equal (nth j (ex-write s vs fr)) (nth j fr))))

(defthm ex-agree-written-len
  (ex-agree (ex-slots s (len vs)) vs (ex-write s vs fr))
  :hints (("Goal" :induct (ex-write s vs fr))))

(defthm ex-agree-written
  (implies (equal n (len vs)) (ex-agree (ex-slots s n) vs (ex-write s vs fr))))

(defthm ex-agree-write-blank
  (implies (and (ex-agree cm env fr) (equal n (len vs)))
           (ex-agree (ex-blank (cons nil (ex-slots s n)) cm) env (ex-write s vs fr)))
  :hints (("Goal" :induct (ex-agree cm env fr))))

(defthm ex-pos-bound (implies (member-equal s cm) (< (ex-pos s cm) (len cm))) :rule-classes :linear)

(defthm ex-locals-mx
  (implies (and (ex-agree cm env fr) (subsetp-equal ls cm) (nat-listp ls))
           (and (equal (car (mx2-args (ex-locals ls cm) env caps defs fuel)) :val)
                (ex-agree ls (cdr (mx2-args (ex-locals ls cm) env caps defs fuel)) fr)))
  :hints (("Goal" :induct (ex-locals ls cm)
                  :expand ((:free (x y) (mx2-args (cons x y) env caps defs fuel))
                           (:free (x) (mx2 (cons :local x) env caps defs fuel))))))

(defthm ex-locals-xwf
  (implies (subsetp-equal ls cm) (x2wf-args (ex-locals ls cm) (len cm))))

(defthm ex-locals-true-listp (true-listp (ex-locals ls cm)))

; mx2-loop reads only its loop's body
(defun ex-mxl-ind (e base vs caps defs fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel) (list e base vs caps defs) (ex-mxl-ind e base (cdr (mx2 (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel))))

(defthm ex-mx-loop-body
  (implies (and (consp e) (cadr e))
           (equal (mx2-loop e base vs caps defs fuel) (mx2-loop (list :loop nil (caddr e)) base vs caps defs fuel)))
  :hints (("Goal" :induct (ex-mxl-ind e base vs caps defs fuel)
                  :expand ((mx2-loop e base vs caps defs fuel)
                           (:free (vs) (mx2-loop (list :loop nil (caddr e)) base vs caps defs fuel))))))

(defthm ex-cslot-natp (natp (ex-cslot e j)) :rule-classes :type-prescription)
(in-theory (disable ex-kind ex-i2 ex-s2 ex-nk ex-c ex-mark ex-kids ex-rstart ex-rn ex-cslot))

; ---- THE TRANSLATION IS WELL FORMED -------------------------------------------------------

(defun ex-rindc (e i cm)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (< (nfix i) (ex-nk e)) (ex-rindc e (1+ (nfix i)) (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) cm)) (list i cm)))
(defthm ex-tr-rec-true-listp (true-listp (ex-tr :rec e i cm))
  :hints (("Goal" :induct (ex-rindc e i cm) :in-theory (disable ex-kid-of) :expand ((ex-tr :rec e i cm)))))
(defthm ex-tr-rec-len
  (implies (and (consp e) (<= (nfix i) (ex-nk e))) (equal (len (ex-tr :rec e i cm)) (- (ex-nk e) (nfix i))))
  :hints (("Goal" :induct (ex-rindc e i cm) :in-theory (disable ex-kid-of) :expand ((ex-tr :rec e i cm)))))

; a try's parts: the catch walk and the finally
(defthm ex-trh-xwf
  (implies (and (natp p) (x2wf-args hs (1+ p))) (x2wf (ex-trh cs hs p) (1+ p) nil))
  :hints (("Goal" :induct (ex-trh cs hs p) :expand ((x2wf-args hs (1+ p))))))
(defthm ex-trtry-xwf
  (implies (and (natp p) (x2wf b p nil) (x2wf-args hs (1+ p)) (or (not fin) (x2wf f (1+ p) nil)))
           (x2wf (ex-trtry b hs f cs fin p) p k)))
(in-theory (disable ex-trtry))

; a case's walk: its thens and default each in the case's tail
(defun ex-x2wfk (es n k) (if (atom es) t (and (x2wf (car es) n k) (ex-x2wfk (cdr es) n k))))
(defthm ex-trcs-xwf
  (implies (and (natp p) (ex-x2wfk ts (1+ p) k) (x2wf d (1+ p) k)) (x2wf (ex-trcs ct ts d p) (1+ p) k))
  :hints (("Goal" :induct (ex-trcs ct ts d p))))
(in-theory (disable ex-trcs))

; a letfn's lets: their captures locals in its scope, its body past them
(defthm ex-xwf-args-app (equal (x2wf-args (append a b) n) (and (x2wf-args a n) (x2wf-args b n)))
  :hints (("Goal" :induct (len a) :expand ((:free (x y) (x2wf-args (cons x y) n)) (x2wf-args a n)))))
(defthm ex-lfcaps-xwf (implies (and (ex-lfin os s n cm) (natp m) (<= (len cm) m)) (x2wf-args (ex-lfcaps os s n cm) m))
  :hints (("Goal" :induct (ex-lfcaps os s n cm) :expand ((:free (x y) (x2wf-args (cons x y) m))))))
(defthm ex-lfargs-xwf (implies (and (ex-lfok e j cm defs) (natp m) (<= (len cm) m)) (x2wf-args (ex-lfargs e j cm) m))
  :hints (("Goal" :induct (ex-lfargs e j cm) :in-theory (disable ex-lfos))))
(defun ex-trlf-ind (e j n)
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix j)))))
  (if (< (nfix j) (ex-i2 e)) (ex-trlf-ind e (1+ (nfix j)) (1+ n)) n))
(defthm ex-trlf-xwf
  (implies (and (ex-lfok e 0 cm defs) (natp n) (<= (len cm) n) (x2wf x (+ n (nfix (- (ex-i2 e) (nfix j)))) k))
           (x2wf (ex-trlf e j cm x) n k))
  :hints (("Goal" :induct (ex-trlf-ind e j n) :in-theory (disable ex-lfargs ex-lfshape ex-lfok)
                  :expand ((:free (y m) (x2wf (cons :let y) m k)) (:free (y m) (x2wf (cons :mkgrp y) m nil))))))

(defun ex-xgood (flg e i cm lp defs)
  (implies (ex-vwf flg e i cm lp defs)
           (case flg
             ((:rec :call :coll) (x2wf-args (ex-tr flg e i cm) (len cm)))
             (:cs (x2wf-args (ex-tr flg e i cm) (1+ (len cm))))
             (:ct (ex-x2wfk (ex-tr flg e i cm) (len cm) (ex-k lp)))
             (:fin (or (not (< 1 (ex-nk e))) (x2wf (ex-tr flg e i cm) (1+ (len cm)) nil)))
             (otherwise (x2wf (ex-tr flg e i cm) (len cm) (ex-k lp))))))

(defthm ex-tr-xwf-flag
  (ex-xgood flg e i cm lp defs)
  :rule-classes nil
  :hints (("Goal" :induct (ex-vwf flg e i cm lp defs)
                  :in-theory (disable ex-kid-of ex-lffns ex-lfok ex-trlf)
                  :expand ((:free (flg cm) (ex-tr flg e i cm)) (:free (flg cm lp) (ex-vwf flg e i cm lp defs))
                           (:free (x y n) (x2wf-args (cons x y) n))))))

; THE TRANSLATION OF A WELL-FORMED TREE IS THE VM'S WELL FORMED
(defthm ex-tr-xwf
  (implies (ex-vwf :m e 0 cm lp defs) (x2wf (ex-tr :m e 0 cm) (len cm) (ex-k lp)))
  :hints (("Goal" :use ((:instance ex-tr-xwf-flag (flg :m) (i 0))))))

; a catch's body and scope, clause k of the walk
(defun ex-csind2 (k i) (if (zp k) i (ex-csind2 (1- k) (1+ (nfix i)))))
(defthm ex-tr-cs-nth
  (implies (and (consp e) (natp i) (natp k) (< (+ i k) (len (ex-c e))))
           (equal (nth k (ex-tr :cs e i cm)) (ex-tr :m (ex-cbody e (+ i k)) 0 (append cm (list (ex-cslot e (+ i k)))))))
  :rule-classes nil
  :hints (("Goal" :induct (ex-csind2 k i) :expand ((ex-tr :cs e i cm)))))
(defthm ex-tr-cs-nth0
  (implies (and (consp e) (natp k) (< k (len (ex-c e))))
           (equal (nth k (ex-tr :cs e 0 cm)) (ex-tr :m (ex-cbody e k) 0 (append cm (list (ex-cslot e k))))))
  :hints (("Goal" :use ((:instance ex-tr-cs-nth (i 0))))))
(defthm ex-vwf-cs-nth
  (implies (and (consp e) (natp i) (natp k) (< (+ i k) (len (ex-c e))) (ex-vwf :cs e i cm lp defs))
           (and (not (member-equal (ex-cslot e (+ i k)) cm))
                (ex-vwf :m (ex-cbody e (+ i k)) 0 (append cm (list (ex-cslot e (+ i k)))) nil defs)))
  :rule-classes nil
  :hints (("Goal" :induct (ex-csind2 k i) :expand ((ex-vwf :cs e i cm lp defs)))))
(defthm ex-vwf-cs-nth0
  (implies (and (ex-vwf :cs e 0 cm nil defs) (consp e) (natp k) (< k (len (ex-c e))))
           (and (not (member-equal (ex-cslot e k) cm))
                (ex-vwf :m (ex-cbody e k) 0 (append cm (list (ex-cslot e k))) nil defs)))
  :hints (("Goal" :use ((:instance ex-vwf-cs-nth (i 0) (lp nil))))))

; a case's entry k: its then's translation and its well-formedness
(defthm ex-tr-ct-nth
  (implies (and (consp e) (natp i) (natp k) (< (+ i k) (len (ex-c e))))
           (equal (nth k (ex-tr :ct e i cm)) (ex-tr :m (ex-cthen e (+ i k)) 0 cm)))
  :rule-classes nil
  :hints (("Goal" :induct (ex-csind2 k i) :expand ((ex-tr :ct e i cm)))))
(defthm ex-tr-ct-nth0
  (implies (and (consp e) (natp k) (< k (len (ex-c e))))
           (equal (nth k (ex-tr :ct e 0 cm)) (ex-tr :m (ex-cthen e k) 0 cm)))
  :hints (("Goal" :use ((:instance ex-tr-ct-nth (i 0))))))
(defthm ex-vwf-ct-nth
  (implies (and (consp e) (natp i) (natp k) (< (+ i k) (len (ex-c e))) (ex-vwf :ct e i cm lp defs))
           (ex-vwf :m (ex-cthen e (+ i k)) 0 cm lp defs))
  :rule-classes nil
  :hints (("Goal" :induct (ex-csind2 k i) :expand ((ex-vwf :ct e i cm lp defs)))))
(defthm ex-vwf-ct-nth0
  (implies (and (ex-vwf :ct e 0 cm lp defs) (consp e) (natp k) (< k (len (ex-c e))))
           (ex-vwf :m (ex-cthen e k) 0 cm lp defs))
  :hints (("Goal" :use ((:instance ex-vwf-ct-nth (i 0))))))

; ---- THE THEOREM ----------------------------------------------------------------------------------
;
; the places: :m, :do, :let and :rec as ex-ev's; :iter a loop's body e
; restarting, cm and env the scope outside the loop's own positions (the
; lets' blanked), tmp the values its positions hold this round

; a recur's record never answers a value, a loop's never a recur
(defun ex-rind2 (e i tmp fr fuel)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (< (nfix i) (ex-nk e))
      (let ((r (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
        (ex-rind2 e (1+ (nfix i)) (append tmp (list (val (car r)))) (cadr r) fuel))
    (list tmp fr)))
(defthm ex-rec-not-val (not (equal (car (car (ex-ev :rec e i tmp fr fuel))) :val))
  :hints (("Goal" :induct (ex-rind2 e i tmp fr fuel) :in-theory (disable ex-kid-of)
                  :expand ((ex-ev :rec e i tmp fr fuel)))))
(defun ex-iind (e fr fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel) fr (ex-iind e (cadr (ex-ev :m e 0 nil fr fuel)) (1- fuel))))
(defthm ex-iter-not-recur (not (equal (car (car (ex-ev :iter e 0 nil fr fuel))) :recur))
  :hints (("Goal" :induct (ex-iind e fr fuel) :in-theory (disable ex-kid-of)
                  :expand ((ex-ev :iter e 0 nil fr fuel)))))
