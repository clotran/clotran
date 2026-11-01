; THE TREE EVALUATOR'S MEANING IS THE VM'S (model/exec.lisp against
; model/vmx.lisp): for the core without loops -- constants, locals, if, do,
; let* -- what ex-ev answers is what vmx's mx answers of the tree's
; translation, and vmx-proof proves the VM runs mx (vcsx-correct).
;
; The tree names a local by its SLOT in the fn's frame, which the analyzer
; numbers by reservation, never reusing one in scope; mx names it by its
; POSITION in an environment a let grows by one. The translation (ex-tr)
; carries cm, the slots in scope by position: a local is (:local p) for
; its slot's position p, a let a nest of mx's one-binding lets, a do an if
; on each value but the last with the rest on both branches (the core is
; pure: a value only chooses between equal branches). The relation
; (ex-agree cm env fr): position p's value is slot (nth p cm)'s.
;
; THE THEOREM (ex-vm-agree): a well-formed loop-free core tree whose
; scope agrees answers, when ex-ev gives a value, that same value from mx
; of its translation, the scope still agreeing after. With
; ex-machine-correct (exec-proof), the machine exec.inc's run_loop is
; answers what the VM answers. Loops and recurs: milestone 1b of
; model/exec-PLAN.md (vmx binds a loop's inits at once, the tree one after
; another).

(in-package "ACL2")

(include-book "exec")
(include-book "vmx")

(defthm ex-i2-natp (natp (ex-i2 e)) :rule-classes :type-prescription)
(defthm ex-s2-natp (natp (ex-s2 e)) :rule-classes :type-prescription)
(defthm ex-nk-natp (natp (ex-nk e)) :rule-classes :type-prescription)

(defun ex-vrank (flg) (case flg ((:do :let) 0) (otherwise 1)))
(defun ex-vleft (flg e i) (case flg (:let (nfix (- (ex-i2 e) (nfix i)))) (:do (nfix (- (ex-nk e) (nfix i)))) (otherwise 0)))

(defun ex-pos (s cm) (cond ((atom cm) 0) ((equal s (car cm)) 0) (t (1+ (ex-pos s (cdr cm))))))

(defun ex-tr (flg e i cm)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        '(:const nil)
      (case flg
        (:do (cond ((zp nk) '(:const nil))
                   ((< i (- nk 1)) (let ((r (ex-tr :do e (1+ i) cm))) (list :if (ex-tr :m (ex-kid-of e i) 0 cm) r r)))
                   (t (ex-tr :m (ex-kid-of e (- nk 1)) 0 cm))))
        (:let (if (< i n2)
                  (list :let (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr :let e (1+ i) (append cm (list (+ (ex-s2 e) i)))))
                (ex-tr :m (ex-kid-of e n2) 0 cm)))
        (otherwise
         (cond ((equal k 1) (list :const (ex-c e)))
               ((equal k 2) (list :local (ex-pos (ex-i2 e) cm)))
               ((equal k 4) (list :if (ex-tr :m (ex-kid-of e 0) 0 cm) (ex-tr :m (ex-kid-of e 1) 0 cm)
                                  (if (< 2 nk) (ex-tr :m (ex-kid-of e 2) 0 cm) '(:const nil))))
               ((equal k 5) (ex-tr :do e 0 cm))
               ((equal k 11) (ex-tr :let e 0 cm))
               (t '(:const nil))))))))

; well-formed: the loop-free core, every local in scope and unmarked (no
; clearing: that is anpass-sound's, joined in milestone 4), every let's
; slot new to the scope
(defun ex-vwf (flg e i cm)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (and (consp e)
         (case flg
           (:do (cond ((zp nk) t)
                      ((< i (- nk 1)) (and (ex-vwf :m (ex-kid-of e i) 0 cm) (ex-vwf :do e (1+ i) cm)))
                      (t (ex-vwf :m (ex-kid-of e (- nk 1)) 0 cm))))
           (:let (if (< i n2)
                     (and (equal k 11) (not (member-equal (+ (ex-s2 e) i) cm)) (ex-vwf :m (ex-kid-of e i) 0 cm)
                          (ex-vwf :let e (1+ i) (append cm (list (+ (ex-s2 e) i)))))
                   (and (equal k 11) (ex-vwf :m (ex-kid-of e n2) 0 cm))))
           (otherwise
            (cond ((equal k 1) t)
                  ((equal k 2) (and (member-equal (ex-i2 e) cm) (not (ex-mark e))))
                  ((equal k 4) (and (or (equal nk 2) (equal nk 3))
                                    (ex-vwf :m (ex-kid-of e 0) 0 cm) (ex-vwf :m (ex-kid-of e 1) 0 cm)
                                    (or (equal nk 2) (ex-vwf :m (ex-kid-of e 2) 0 cm))))
                  ((equal k 5) (ex-vwf :do e 0 cm))
                  ((equal k 11) (and (equal nk (1+ n2)) (ex-vwf :let e 0 cm)))
                  (t nil)))))))

(defun ex-agree (cm env fr)
  (if (atom cm)
      (atom env)
    (and (consp env) (equal (car env) (nth (car cm) fr)) (ex-agree (cdr cm) (cdr env) fr))))

; ---- the scope ----------------------------------------------------------------------------------

(defthm ex-agree-local
  (implies (and (ex-agree cm env fr) (member-equal s cm))
           (equal (nth (ex-pos s cm) env) (nth s fr))))

(defthm ex-agree-write
  (implies (and (not (member-equal s cm)) (natp s) (nat-listp cm))
           (equal (ex-agree cm env (update-nth s v fr)) (ex-agree cm env fr))))

(defthm ex-agree-append
  (implies (ex-agree cm env fr)
           (equal (ex-agree (append cm (list s)) (append env (list v)) fr)
                  (equal v (nth s fr)))))

(defthm ex-agree-prefix
  (implies (and (ex-agree (append cm x) (append env y) fr) (equal (len cm) (len env)))
           (ex-agree cm env fr))
  :hints (("Goal" :induct (ex-agree cm env fr))))

(defthm ex-nat-listp-append (implies (and (nat-listp a) (natp s)) (nat-listp (append a (list s)))))

(defthm ex-agree-len (implies (ex-agree cm env fr) (equal (len env) (len cm))) :rule-classes :forward-chaining)

(in-theory (disable ex-kind ex-i2 ex-s2 ex-nk ex-c ex-mark ex-kids))

; ---- THE THEOREM ----------------------------------------------------------------------------------

(defun ex-vgood (flg e i tmp cm env fr fuel caps defs)
  (implies (and (ex-vwf flg e i cm) (ex-agree cm env fr) (nat-listp cm) (member-equal flg '(:m :do :let)))
           (let ((r (ex-ev flg e i tmp fr fuel)))
             (implies (valp (car r))
                      (and (equal (mx (ex-tr flg e i cm) env caps defs fuel) (car r))
                           (ex-agree cm env (cadr r)))))))

(set-irrelevant-formals-ok t)
(defun ex-vind (flg e i tmp cm env fr fuel caps defs)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        (list tmp)
      (case flg
        (:do (cond ((zp nk) nil)
                   ((< i (- nk 1))
                    (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                      (list (ex-vind :m (ex-kid-of e i) 0 nil cm env fr fuel caps defs)
                            (ex-vind :do e (1+ i) tmp cm env (cadr r) fuel caps defs))))
                   (t (ex-vind :m (ex-kid-of e (- nk 1)) 0 nil cm env fr fuel caps defs))))
        (:let (if (< i n2)
                  (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                    (list (ex-vind :m (ex-kid-of e i) 0 nil cm env fr fuel caps defs)
                          (ex-vind :let e (1+ i) tmp (append cm (list (+ (ex-s2 e) i))) (append env (list (val (car r))))
                                   (update-nth (+ (ex-s2 e) i) (val (car r)) (cadr r)) fuel caps defs)))
                (ex-vind :m (ex-kid-of e n2) 0 nil cm env fr fuel caps defs)))
        (otherwise
         (cond ((equal k 4)
                (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                  (list (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs)
                        (ex-vind :m (ex-kid-of e 1) 0 nil cm env (cadr r) fuel caps defs)
                        (ex-vind :m (ex-kid-of e 2) 0 nil cm env (cadr r) fuel caps defs))))
               ((equal k 5) (ex-vind :do e 0 nil cm env fr fuel caps defs))
               ((equal k 11) (ex-vind :let e 0 nil cm env fr fuel caps defs))
               (t nil)))))))

(defthm ex-vm-agree-flag
  (ex-vgood flg e i tmp cm env fr fuel caps defs)
  :rule-classes nil
  :hints (("Goal" :induct (ex-vind flg e i tmp cm env fr fuel caps defs)
                  :in-theory (disable ex-kid-of)
                  :expand ((:free (flg cm) (ex-tr flg e i cm)) (:free (flg cm) (ex-vwf flg e i cm))
                           (:free (flg fr tmp) (ex-ev flg e i tmp fr fuel))
                           (:free (x env) (mx (cons :if x) env caps defs fuel))
                           (:free (x env) (mx (cons :let x) env caps defs fuel))
                           (:free (x env) (mx (cons :const x) env caps defs fuel))
                           (:free (x env) (mx (cons :local x) env caps defs fuel))))))

; A LOOP-FREE CORE TREE ANSWERS WHAT THE VM'S MEANING DOES
(defthm ex-vm-agree
  (implies (and (ex-vwf :m e 0 cm) (ex-agree cm env fr) (nat-listp cm) (valp (car (ex-ev :m e 0 nil fr fuel))))
           (equal (mx (ex-tr :m e 0 cm) env caps defs fuel) (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :use ((:instance ex-vm-agree-flag (flg :m) (i 0) (tmp nil))))))
