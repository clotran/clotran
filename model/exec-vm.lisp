; THE TREE EVALUATOR'S MEANING IS THE VM'S (model/exec.lisp against
; model/vmx.lisp): for the core -- constants, locals, if, do, let*, loop*
; and recur -- what ex-ev answers is what vmx's mx answers of the tree's
; translation, and vmx-proof proves the VM runs mx (vcsx-correct), so the
; VM run of the translation answers the tree's value (ex-vm-runs, in exec-vmrun).
;
; The tree names a local by its SLOT in the fn's frame, which the analyzer
; numbers by reservation, never reusing one in scope; mx names it by its
; POSITION in an environment a let grows by one. The translation (ex-tr)
; carries cm, the slots in scope by position: a local is (:local p) for
; its slot's position p, a let a nest of mx's one-binding lets, a do an if
; on each value but the last with the rest on both branches (the core is
; pure: a value only chooses between equal branches). The relation
; (ex-agree cm env fr): position p's value is slot (nth p cm)'s, for each
; position whose cm entry is a slot (a nil entry is a position no name
; reaches any more).
;
; A LOOP. The tree binds a loop's inits one after another, each seeing
; the ones before; vmx's :loop binds its inits at once. So a loop of n
; bindings in slots s .. s+n-1 is n of mx's lets (the inits, in order)
; around (:loop (nil, copies of the n positions) body): the body's scope
; is the lets' positions blanked -- after a recur they hold the first
; round's values, and no name reaches them -- then a dummy and the
; copies, so its slots name the loop's own positions. A recur is (:recur
; nil args...): the dummy makes every loop bind at least one, as xwf asks,
; and keeps a zero-binding loop one translation.
;
; THE THEOREM (ex-vm-agree): a well-formed core tree in no loop's tail
; whose scope agrees answers, when ex-ev gives a value, that same value
; from mx of its translation, the scope still agreeing after; and it
; never answers a recur (ex-recur-stays) -- a recur's values reach only
; its loop's slots, which mx's recur gives its loop's positions. The
; translation of a well-formed tree is xwf (ex-tr-xwf), so with
; vcsx-correct: ex-vm-runs (exec-vmrun). With ex-machine-correct (exec-proof), the
; machine exec.inc's run_loop is answers what the VM answers.

(in-package "ACL2")

(include-book "exec")
(include-book "vmx")

(defthm ex-i2-natp (natp (ex-i2 e)) :rule-classes :type-prescription)
(defthm ex-s2-natp (natp (ex-s2 e)) :rule-classes :type-prescription)
(defthm ex-nk-natp (natp (ex-nk e)) :rule-classes :type-prescription)
(defthm ex-rstart-natp2 (natp (ex-rstart e)) :rule-classes :type-prescription)
(defthm ex-rn-natp2 (natp (ex-rn e)) :rule-classes :type-prescription)

(defun ex-vrank (flg) (case flg ((:do :let :rec) 0) (otherwise 1)))
(defun ex-vleft (flg e i)
  (case flg (:let (nfix (- (ex-i2 e) (nfix i)))) ((:do :rec) (nfix (- (ex-nk e) (nfix i)))) (otherwise 0)))

(defun ex-pos (s cm) (cond ((atom cm) 0) ((equal s (car cm)) 0) (t (1+ (ex-pos s (cdr cm))))))

; slots s .. s+n-1; a loop's scope list: the dummy, then its slots
(defun ex-slots (s n) (if (zp n) nil (cons (nfix s) (ex-slots (1+ (nfix s)) (1- n)))))
(defun ex-lsl (lp) (cons nil (ex-slots (car lp) (cdr lp))))
; the arity xwf asks a recur in the tail of loop lp (nil: none may stand)
(defun ex-k (lp) (if (consp lp) (1+ (nfix (cdr lp))) nil))
; cm with every entry of ls blanked
(defun ex-blank (ls cm)
  (if (atom cm) cm (cons (if (member-equal (car cm) ls) nil (car cm)) (ex-blank ls (cdr cm)))))
; no entry of cm but nil is in ls
(defun ex-nomem (ls cm)
  (if (atom cm) t (and (or (null (car cm)) (not (member-equal (car cm) ls))) (ex-nomem ls (cdr cm)))))
(defun ex-locals (ls cm) (if (atom ls) nil (cons (list :local (ex-pos (car ls) cm)) (ex-locals (cdr ls) cm))))

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
        (:let (cond ((< i n2)
                     (list :let (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr :let e (1+ i) (append cm (list (+ (ex-s2 e) i))))))
                    ((equal k 12)
                     (let ((ls (cons nil (ex-slots (ex-s2 e) n2))))
                       (list :loop (cons '(:const nil) (ex-locals (cdr ls) cm))
                             (ex-tr :m (ex-kid-of e n2) 0 (append (ex-blank ls cm) ls)))))
                    (t (ex-tr :m (ex-kid-of e n2) 0 cm))))
        (:rec (if (< i nk) (cons (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr :rec e (1+ i) cm)) nil))
        (otherwise
         (cond ((equal k 1) (list :const (ex-c e)))
               ((equal k 2) (list :local (ex-pos (ex-i2 e) cm)))
               ((equal k 4) (list :if (ex-tr :m (ex-kid-of e 0) 0 cm) (ex-tr :m (ex-kid-of e 1) 0 cm)
                                  (if (< 2 nk) (ex-tr :m (ex-kid-of e 2) 0 cm) '(:const nil))))
               ((equal k 5) (ex-tr :do e 0 cm))
               ((or (equal k 11) (equal k 12)) (ex-tr :let e 0 cm))
               ((equal k 16) (list* :recur '(:const nil) (ex-tr :rec e 0 cm)))
               (t '(:const nil))))))))

; well-formed: the core, every local in scope and unmarked (no clearing:
; that is anpass-sound's, joined in milestone 4), every let's and loop's
; slot new to the scope, a recur only in the tail of a loop lp -- (s . n),
; its first slot and count of bindings, nil outside every loop's tail --
; writing that loop's slots with as many values
(defun ex-vwf (flg e i cm lp)
  (declare (xargs :measure (make-ord 2 (1+ (acl2-count e)) (make-ord 1 (1+ (ex-vrank flg)) (ex-vleft flg e i)))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (and (consp e)
         (case flg
           (:do (cond ((zp nk) t)
                      ((< i (- nk 1)) (and (ex-vwf :m (ex-kid-of e i) 0 cm nil) (ex-vwf :do e (1+ i) cm lp)))
                      (t (ex-vwf :m (ex-kid-of e (- nk 1)) 0 cm lp))))
           (:let (cond ((< i n2)
                        (and (or (equal k 11) (equal k 12)) (not (member-equal (+ (ex-s2 e) i) cm))
                             (ex-vwf :m (ex-kid-of e i) 0 cm nil)
                             (ex-vwf :let e (1+ i) (append cm (list (+ (ex-s2 e) i))) lp)))
                       ((equal k 11) (ex-vwf :m (ex-kid-of e n2) 0 cm lp))
                       ((equal k 12)
                        (let ((ls (cons nil (ex-slots (ex-s2 e) n2))))
                          (and (subsetp-equal (cdr ls) cm)
                               (ex-vwf :m (ex-kid-of e n2) 0 (append (ex-blank ls cm) ls) (cons (ex-s2 e) n2)))))
                       (t nil)))
           (:rec (and (equal k 16) (consp lp) (equal (ex-rstart e) (car lp)) (equal (ex-rn e) (cdr lp))
                      (equal nk (cdr lp))
                      (if (< i nk)
                          (and (ex-vwf :m (ex-kid-of e i) 0 cm nil) (ex-vwf :rec e (1+ i) cm lp))
                        (equal i nk))))
           (otherwise
            (cond ((equal k 1) t)
                  ((equal k 2) (and (member-equal (ex-i2 e) cm) (not (ex-mark e))))
                  ((equal k 4) (and (or (equal nk 2) (equal nk 3))
                                    (ex-vwf :m (ex-kid-of e 0) 0 cm nil) (ex-vwf :m (ex-kid-of e 1) 0 cm lp)
                                    (or (equal nk 2) (ex-vwf :m (ex-kid-of e 2) 0 cm lp))))
                  ((equal k 5) (ex-vwf :do e 0 cm lp))
                  ((equal k 11) (and (equal nk (1+ n2)) (ex-vwf :let e 0 cm lp)))
                  ((equal k 12) (and (equal nk (1+ n2)) (ex-nomem (cons nil (ex-slots (ex-s2 e) n2)) cm)
                                     (ex-vwf :let e 0 cm lp)))
                  ((equal k 16) (and (consp lp) (equal (ex-rstart e) (car lp)) (equal (ex-rn e) (cdr lp))
                                     (equal nk (cdr lp)) (ex-vwf :rec e 0 cm lp)))
                  (t nil)))))))

; the loop-free core, well formed as ex-vwf is outside a loop: what
; exec-cost bounds (a loop's turns depend on its iterations)
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
           (:rec nil)
           (otherwise
            (cond ((equal k 1) t)
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
           (and (equal (car (mx-args (ex-locals ls cm) env caps defs fuel)) :val)
                (ex-agree ls (cdr (mx-args (ex-locals ls cm) env caps defs fuel)) fr)))
  :hints (("Goal" :induct (ex-locals ls cm)
                  :expand ((:free (x y) (mx-args (cons x y) env caps defs fuel))
                           (:free (x) (mx (cons :local x) env caps defs fuel))))))

(defthm ex-locals-xwf
  (implies (subsetp-equal ls cm) (xwf-args (ex-locals ls cm) (len cm))))

(defthm ex-locals-true-listp (true-listp (ex-locals ls cm)))

; mx-loop reads only its loop's body
(defun ex-mxl-ind (e base vs caps defs fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel) (list e base vs caps defs) (ex-mxl-ind e base (cdr (mx (caddr e) (append base vs) caps defs fuel)) caps defs (1- fuel))))

(defthm ex-mx-loop-body
  (implies (and (consp e) (cadr e))
           (equal (mx-loop e base vs caps defs fuel) (mx-loop (list :loop nil (caddr e)) base vs caps defs fuel)))
  :hints (("Goal" :induct (ex-mxl-ind e base vs caps defs fuel)
                  :expand ((mx-loop e base vs caps defs fuel)
                           (:free (vs) (mx-loop (list :loop nil (caddr e)) base vs caps defs fuel))))))

(in-theory (disable ex-kind ex-i2 ex-s2 ex-nk ex-c ex-mark ex-kids ex-rstart ex-rn))

; ---- THE TRANSLATION IS WELL FORMED -------------------------------------------------------

(defun ex-rind (e i) (declare (xargs :measure (nfix (- (ex-nk e) (nfix i))))) (if (< (nfix i) (ex-nk e)) (ex-rind e (1+ (nfix i))) i))
(defthm ex-tr-rec-true-listp (true-listp (ex-tr :rec e i cm))
  :hints (("Goal" :induct (ex-rind e i) :in-theory (disable ex-kid-of) :expand ((ex-tr :rec e i cm)))))
(defthm ex-tr-rec-len
  (implies (and (consp e) (<= (nfix i) (ex-nk e))) (equal (len (ex-tr :rec e i cm)) (- (ex-nk e) (nfix i))))
  :hints (("Goal" :induct (ex-rind e i) :in-theory (disable ex-kid-of) :expand ((ex-tr :rec e i cm)))))

(defun ex-xgood (flg e i cm lp)
  (implies (ex-vwf flg e i cm lp)
           (if (equal flg :rec)
               (xwf-args (ex-tr flg e i cm) (len cm))
             (xwf (ex-tr flg e i cm) (len cm) (ex-k lp)))))

(defthm ex-tr-xwf-flag
  (ex-xgood flg e i cm lp)
  :rule-classes nil
  :hints (("Goal" :induct (ex-vwf flg e i cm lp)
                  :in-theory (disable ex-kid-of)
                  :expand ((:free (flg cm) (ex-tr flg e i cm)) (:free (flg cm lp) (ex-vwf flg e i cm lp))
                           (:free (x y n) (xwf-args (cons x y) n))))))

; THE TRANSLATION OF A WELL-FORMED TREE IS THE VM'S WELL FORMED
(defthm ex-tr-xwf
  (implies (ex-vwf :m e 0 cm lp) (xwf (ex-tr :m e 0 cm) (len cm) (ex-k lp)))
  :hints (("Goal" :use ((:instance ex-tr-xwf-flag (flg :m) (i 0))))))

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

(defun ex-vhyp (flg e i tmp cm env fr lp)
  (if (equal flg :iter)
      (and (consp lp) (ex-vwf :m e 0 (append cm (ex-lsl lp)) lp)
           (ex-agree (append cm (ex-lsl lp)) (append env tmp) fr)
           (ex-nomem (ex-lsl lp) cm) (equal (len env) (len cm)))
    (and (member-equal flg '(:m :do :let :rec)) (ex-vwf flg e i cm lp) (ex-agree cm env fr)
         (or (not (equal flg :rec)) (and (true-listp tmp) (equal (len tmp) (nfix i)))))))

(defun ex-vpost (flg e i tmp cm env lp caps defs fuel r)
  (let ((res (car r)) (fr2 (cadr r)) (ls (ex-lsl lp)))
    (case flg
      (:iter (implies (valp res)
                      (and (equal (mx-loop (list :loop nil (ex-tr :m e 0 (append cm ls))) env tmp caps defs fuel) res)
                           (ex-agree cm env fr2))))
      (:rec (implies (equal (car res) :recur)
                     (let ((m (mx-args (ex-tr :rec e i cm) env caps defs fuel)))
                       (and (valp m) (ex-agree (cdr ls) (append tmp (val m)) fr2)
                            (ex-agree (ex-blank ls cm) env fr2)))))
      (otherwise
       (let ((m (mx (ex-tr flg e i cm) env caps defs fuel)))
         (and (implies (valp res)
                       (and (equal m res)
                            (if (and (equal flg :let) (equal (ex-kind e) 12))
                                (ex-agree (ex-blank (ex-lsl (cons (ex-s2 e) (ex-i2 e))) cm) env fr2)
                              (ex-agree cm env fr2))))
              (implies (equal (car res) :recur)
                       (and (consp lp) (equal (car m) :recur) (ex-agree ls (cdr m) fr2)
                            (ex-agree (ex-blank ls cm) env fr2)))))))))

(defun ex-vgood (flg e i tmp cm env fr fuel caps defs lp)
  (implies (ex-vhyp flg e i tmp cm env fr lp)
           (ex-vpost flg e i tmp cm env lp caps defs fuel
                     (ex-ev flg e i (if (equal flg :iter) nil tmp) fr fuel))))

(set-irrelevant-formals-ok t)
(defun ex-vind (flg e i tmp cm env fr fuel caps defs lp)
  (declare (xargs :measure (make-ord 3 (1+ (nfix fuel))
                                     (make-ord 2 (1+ (acl2-count e))
                                               (make-ord 1 (1+ (ex-rank flg)) (ex-left flg e i))))
                  :well-founded-relation o<
                  :hints (("Goal" :in-theory (disable ex-kid-of)))))
  (let ((k (ex-kind e)) (nk (ex-nk e)) (n2 (ex-i2 e)) (i (nfix i)))
    (if (not (consp e))
        (list tmp)
      (case flg
        (:iter (let* ((bcm (append cm (ex-lsl lp))) (benv (append env tmp))
                      (r (ex-ev :m e 0 nil fr fuel))
                      (m (mx (ex-tr :m e 0 bcm) benv caps defs fuel)))
                 (if (zp fuel)
                     (ex-vind :m e 0 nil bcm benv fr fuel caps defs lp)
                   (list (ex-vind :m e 0 nil bcm benv fr fuel caps defs lp)
                         (ex-vind :iter e 0 (cdr m) cm env (cadr r) (1- fuel) caps defs lp)))))
        (:do (cond ((zp nk) nil)
                   ((< i (- nk 1))
                    (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                      (list (ex-vind :m (ex-kid-of e i) 0 nil cm env fr fuel caps defs nil)
                            (ex-vind :do e (1+ i) tmp cm env (cadr r) fuel caps defs lp))))
                   (t (ex-vind :m (ex-kid-of e (- nk 1)) 0 nil cm env fr fuel caps defs lp))))
        (:let (cond ((< i n2)
                     (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                       (list (ex-vind :m (ex-kid-of e i) 0 nil cm env fr fuel caps defs nil)
                             (ex-vind :let e (1+ i) tmp (append cm (list (+ (ex-s2 e) i))) (append env (list (val (car r))))
                                      (update-nth (+ (ex-s2 e) i) (val (car r)) (cadr r)) fuel caps defs lp))))
                    ((equal k 12)
                     (let* ((ls (cons nil (ex-slots (ex-s2 e) n2)))
                            (vs (val (mx-args (ex-locals (cdr ls) cm) env caps defs fuel))))
                       (ex-vind :iter (ex-kid-of e n2) 0 (cons nil vs) (ex-blank ls cm) env fr fuel caps defs
                                (cons (ex-s2 e) n2))))
                    (t (ex-vind :m (ex-kid-of e n2) 0 nil cm env fr fuel caps defs lp))))
        (:rec (if (< i nk)
                  (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                    (list (ex-vind :m (ex-kid-of e i) 0 nil cm env fr fuel caps defs nil)
                          (ex-vind :rec e (1+ i) (append tmp (list (val (car r)))) cm env (cadr r) fuel caps defs lp)))
                nil))
        (otherwise
         (cond ((equal k 4)
                (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                  (list (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
                        (ex-vind :m (ex-kid-of e 1) 0 nil cm env (cadr r) fuel caps defs lp)
                        (ex-vind :m (ex-kid-of e 2) 0 nil cm env (cadr r) fuel caps defs lp))))
               ((equal k 5) (ex-vind :do e 0 nil cm env fr fuel caps defs lp))
               ((or (equal k 11) (equal k 12)) (ex-vind :let e 0 nil cm env fr fuel caps defs lp))
               ((equal k 16) (ex-vind :rec e 0 nil cm env fr fuel caps defs lp))
               (t nil)))))))

(defthm ex-vm-agree-flag
  (ex-vgood flg e i tmp cm env fr fuel caps defs lp)
  :rule-classes nil
  :hints (("Goal" :induct (ex-vind flg e i tmp cm env fr fuel caps defs lp)
                  :in-theory (disable ex-kid-of)
                  :expand ((:free (flg cm) (ex-tr flg e i cm)) (:free (flg cm lp) (ex-vwf flg e i cm lp))
                           (:free (flg fr tmp) (ex-ev flg e i tmp fr fuel))
                           (:free (x env) (mx (cons :if x) env caps defs fuel))
                           (:free (x env) (mx (cons :let x) env caps defs fuel))
                           (:free (x env) (mx (cons :const x) env caps defs fuel))
                           (:free (x env) (mx (cons :local x) env caps defs fuel))
                           (:free (x env) (mx (cons :loop x) env caps defs fuel))
                           (:free (x env) (mx (cons :recur x) env caps defs fuel))
                           (:free (x y env) (mx-args (cons x y) env caps defs fuel))
                           (:free (env) (mx-args nil env caps defs fuel))
                           (:free (x base vs) (mx-loop (list :loop nil x) base vs caps defs fuel))))))

; A WELL-FORMED CORE TREE ANSWERS WHAT THE VM'S MEANING DOES
(defthm ex-vm-agree
  (implies (and (ex-vwf :m e 0 cm nil) (ex-agree cm env fr) (valp (car (ex-ev :m e 0 nil fr fuel))))
           (equal (mx (ex-tr :m e 0 cm) env caps defs fuel) (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :use ((:instance ex-vm-agree-flag (flg :m) (i 0) (tmp nil) (lp nil))))))

; ... and outside every loop's tail it never answers a recur: a recur's
; values become its loop's slots, never a value
(defthm ex-recur-stays
  (implies (and (ex-vwf :m e 0 cm nil) (ex-agree cm env fr))
           (not (equal (car (car (ex-ev :m e 0 nil fr fuel))) :recur)))
  :hints (("Goal" :use ((:instance ex-vm-agree-flag (flg :m) (i 0) (tmp nil) (lp nil))))))
