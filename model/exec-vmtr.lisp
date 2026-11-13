; THE TREE'S TRANSLATION TO VMX2 (model/exec-vm.lisp's first part): the
; translation ex-tr, well-formedness ex-vwf (the good values ex-xvs are exec-xvs.lisp), the
; scope's agreement and the translation's x2wf. exec-vm.lisp's header
; says what they are; this book is it split for size, nothing restated.

(in-package "ACL2")

(include-book "exec")
(include-book "exec-xvs")
(include-book "exec-vmcs")

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
               ((member k '(11 12 13)) (ex-clr :let e 0))
               ((equal k 16) (ex-clr :rec e 0))
               ((equal k 17) (ex-clr :m (ex-kid-of e 0) 0))
               ((equal k 18) (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0) (ex-clr :fin e 0)))
               ((member k '(7 8 9 22 23 10 20 24 21)) (ex-clr :coll e 0))
               ((equal k 19) (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :m (ex-kid-of e 1) 0) (ex-clr :ct e 0)))
               ((equal k 6) (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :call e 1)))
               (t nil)))))))

; a letfn's fns clear nothing: it clears what its body does
(defthm ex-clr-lf (implies (and (consp e) (ex-lffns e j) (natp j) (<= j (ex-i2 e))) (equal (ex-clr :let e j) (ex-clr :m (ex-kid-of e (ex-i2 e)) 0)))
  :hints (("Goal" :induct (ex-lffns e j) :in-theory (disable ex-kid-of) :expand ((ex-clr :let e j) (ex-lffns e j) (ex-clr :m (ex-kid-of e j) 0)))))

(defun ex-tr (flg e i cm)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        '(:const nil)
      (case flg
        (:do (cond ((zp nk) '(:const nil))
                   ((< i (- nk 1)) (list :let (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr :do e (1+ i) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (list nil)))))
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
               ((equal k 15) (list :prim (ex-cop e) (list* :mkclo (ex-c e) (ex-locals (ex-outers (nth 2 (ex-c e))) cm))))
               ((equal k 26) (ex-tr :m (ex-c e) 0 (ex-blank cm cm)))
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
               ((member k '(7 8 9 22 23 10 20 24 21)) (list* :prim (ex-cop e) (ex-tr :coll e 0 cm)))
               ((equal k 19) (list :let (ex-tr :m (ex-kid-of e 0) 0 cm)
                                   (ex-trcs (ex-c e) (ex-tr :ct e 0 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)))
                                            (ex-tr :m (ex-kid-of e 1) 0 (append (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) (list nil)))
                                            (len cm))))
               (t '(:const nil))))))))

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
                      ((< i (- nk 1)) (and (ex-vwf :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf :do e (1+ i) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (list nil)) lp defs)))
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
           (:coll (and (member k '(7 8 9 22 23 10 20 24 21))
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
                  ((equal k 26) (and (null lp) (ex-vwf :m (ex-c e) 0 (ex-blank cm cm) nil defs)))
                  ((or (equal k 14) (equal k 15)) (and (consp (assoc-equal (ex-c e) defs))
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
                  ((equal k 13) (and (equal nk (1+ n2)) (ex-lffns e 0) (ex-lfok e 0 cm defs)
                                     (ex-nomem (cons nil (ex-slots (ex-s2 e) n2)) cm)
                                     (ex-vwf :m (ex-kid-of e n2) 0 (append cm (ex-slots (ex-s2 e) n2)) lp defs)))
                  ((equal k 16) (and (consp lp) (equal (ex-rstart e) (car lp)) (equal (ex-rn e) (cdr lp))
                                     (equal nk (cdr lp)) (ex-vwf :rec e 0 cm lp defs)))
                  ((equal k 17) (and (equal nk 1) (ex-vwf :m (ex-kid-of e 0) 0 cm nil defs)))
                  ((equal k 18) (and (or (equal nk 1) (equal nk 2)) (ex-vwf :m (ex-kid-of e 0) 0 cm nil defs)
                                     (ex-vwf :cs e 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm) nil defs)
                                     (ex-vwf :fin e 0 (ex-blank (append (ex-clr :m (ex-kid-of e 0) 0) (ex-clr :cs e 0)) cm) nil defs)))
                  ((member k '(7 8 9 22 23 10 20 24 21)) (ex-vwf :coll e 0 cm nil defs))
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
; the clause's body: ex-fbtr's with the captures read in place (exec-vmcs's
; ex-cs) -- no lets of them: the parameters, then the self slot's let and
; the loop -- so a capture's read is (:capt j), as vm.inc's
(defun ex-fbin (tm ar)
  (let ((m (len (ex-inners (nth 2 tm)))))
    (list :let (list* :mkclo tm (ex-capts 0 m))
          (list :loop (cons '(:const nil) (ex-locals (ex-fparams ar) (ex-fbcm tm ar)))
                (ex-tr :m (ex-abody ar) 0 (ex-fcmb tm ar))))))
(defun ex-fbtc (tm ar) (ex-cs nil (ex-fbin tm ar) (ex-anp ar) (len (ex-inners (nth 2 tm)))))
(defthm ex-fbtr-fbin (equal (ex-fbtr tm ar) (ex-clets 0 (len (ex-inners (nth 2 tm))) (ex-fbin tm ar))) :rule-classes nil)
(in-theory (disable ex-fbin))
(defun ex-clause (tm ar)
  (if (ex-avar ar) (list (ex-anf ar) (ex-fbtc tm ar) :rest) (list (ex-anf ar) (ex-fbtc tm ar))))
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
