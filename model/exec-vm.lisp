; THE TREE EVALUATOR'S MEANING IS THE VM'S (model/exec.lisp against
; model/vmx.lisp): for the core -- constants, locals, Vars, if, do, let*,
; loop*, recur, fns and calls -- what ex-ev answers is what vmx's mx answers of the tree's
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
; FNS AND CALLS. A Var is (:const its value) (the namespace is the host's;
; the machine reads the value from the node). A fn is (:mkclo template
; locals of its outer slots): the tree's closure and mx's are one value. A
; call is (:callv head args): mx runs the arguments before the head, the
; tree after, which the scope's agreement after each makes no matter. mx's
; defs are keyed by the template itself (vcsx-correct asks only alistp and
; xdefs-ok, and both look a name up by equal), the def (n body): lets of
; the captures and of the closure remade, for the self slot, around the
; loop translation of the parameters, so a recur to the fn is that loop's.
; Templates are restricted (ex-tmwf) to one non-variadic arity with
; distinct parameter, capture and self slots -- the machine leaves the rest
; to the host's apply. Every closure-shaped value has its template in the
; defs (ex-xvs), threaded through the scope, results and recur values.
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

(defun ex-vrank (flg) (case flg ((:do :let :rec :call) 0) (otherwise 1)))
(defun ex-vleft (flg e i)
  (case flg (:let (nfix (- (ex-i2 e) (nfix i)))) ((:do :rec :call) (nfix (- (ex-nk e) (nfix i)))) (otherwise 0)))

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
; a template's capture pairs (outer inner): their outer and inner slots, as ex-caps and ex-bind-caps walk them
(defun ex-outers (capv) (if (or (atom capv) (atom (cdr capv))) nil (cons (car capv) (ex-outers (cddr capv)))))
(defun ex-inners (capv) (if (or (atom capv) (atom (cdr capv))) nil (cons (cadr capv) (ex-inners (cddr capv)))))

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
        (:call (if (< i nk) (cons (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr :call e (1+ i) cm)) nil))
        (otherwise
         (cond ((or (equal k 1) (equal k 3)) (list :const (ex-c e)))
               ((equal k 14) (list* :mkclo (ex-c e) (ex-locals (ex-outers (nth 2 (ex-c e))) cm)))
               ((equal k 6) (list* :callv (ex-tr :m (ex-kid-of e 0) 0 cm) (ex-tr :call e 1 cm)))
               ((equal k 2) (list :local (ex-pos (ex-i2 e) cm)))
               ((equal k 4) (list :if (ex-tr :m (ex-kid-of e 0) 0 cm) (ex-tr :m (ex-kid-of e 1) 0 cm)
                                  (if (< 2 nk) (ex-tr :m (ex-kid-of e 2) 0 cm) '(:const nil))))
               ((equal k 5) (ex-tr :do e 0 cm))
               ((or (equal k 11) (equal k 12)) (ex-tr :let e 0 cm))
               ((equal k 16) (list* :recur '(:const nil) (ex-tr :rec e 0 cm)))
               (t '(:const nil))))))))

; THE VALUES (milestone 2b): every closure-shaped value one whose template
; is in defs (so mx's :callv finds its def), its captures as many as the
; template's pairs and good themselves; any other value is good
(defun ex-xvs (defs l)
  (if (atom l)
      t
    (and (let ((v (car l)))
           (or (not (clop v))
               (and (equal v (clo (cadr v) (caddr v))) (consp (assoc-equal (cadr v) defs))
                    (true-listp (caddr v)) (equal (len (caddr v)) (len (ex-inners (nth 2 (cadr v)))))
                    (ex-xvs defs (caddr v)))))
         (ex-xvs defs (cdr l)))))

; well-formed: the core, every local in scope and unmarked (no clearing:
; that is anpass-sound's, joined in milestone 4), every let's and loop's
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
                      ((< i (- nk 1)) (and (ex-vwf :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf :do e (1+ i) cm lp defs)))
                      (t (ex-vwf :m (ex-kid-of e (- nk 1)) 0 cm lp defs))))
           (:let (cond ((< i n2)
                        (and (or (equal k 11) (equal k 12)) (not (member-equal (+ (ex-s2 e) i) cm))
                             (ex-vwf :m (ex-kid-of e i) 0 cm nil defs)
                             (ex-vwf :let e (1+ i) (append cm (list (+ (ex-s2 e) i))) lp defs)))
                       ((equal k 11) (ex-vwf :m (ex-kid-of e n2) 0 cm lp defs))
                       ((equal k 12)
                        (let ((ls (cons nil (ex-slots (ex-s2 e) n2))))
                          (and (subsetp-equal (cdr ls) cm)
                               (ex-vwf :m (ex-kid-of e n2) 0 (append (ex-blank ls cm) ls) (cons (ex-s2 e) n2) defs))))
                       (t nil)))
           (:rec (and (equal k 16) (consp lp) (equal (ex-rstart e) (car lp)) (equal (ex-rn e) (cdr lp))
                      (equal nk (cdr lp))
                      (if (< i nk)
                          (and (ex-vwf :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf :rec e (1+ i) cm lp defs))
                        (equal i nk))))
           (:call (and (equal k 6)
                       (if (< i nk)
                           (and (ex-vwf :m (ex-kid-of e i) 0 cm nil defs) (ex-vwf :call e (1+ i) cm lp defs))
                         t)))
           (otherwise
            (cond ((or (equal k 1) (equal k 3)) (ex-xvs defs (list (ex-c e))))
                  ((equal k 2) (and (member-equal (ex-i2 e) cm) (not (ex-mark e))))
                  ((equal k 14) (and (consp (assoc-equal (ex-c e) defs))
                                     (nat-listp (ex-outers (nth 2 (ex-c e))))
                                     (subsetp-equal (ex-outers (nth 2 (ex-c e))) cm)))
                  ((equal k 6) (and (< 0 nk) (ex-vwf :m (ex-kid-of e 0) 0 cm nil defs) (ex-vwf :call e 1 cm lp defs)))
                  ((equal k 4) (and (or (equal nk 2) (equal nk 3))
                                    (ex-vwf :m (ex-kid-of e 0) 0 cm nil defs) (ex-vwf :m (ex-kid-of e 1) 0 cm lp defs)
                                    (or (equal nk 2) (ex-vwf :m (ex-kid-of e 2) 0 cm lp defs))))
                  ((equal k 5) (ex-vwf :do e 0 cm lp defs))
                  ((equal k 11) (and (equal nk (1+ n2)) (ex-vwf :let e 0 cm lp defs)))
                  ((equal k 12) (and (equal nk (1+ n2)) (ex-nomem (cons nil (ex-slots (ex-s2 e) n2)) cm)
                                     (ex-vwf :let e 0 cm lp defs)))
                  ((equal k 16) (and (consp lp) (equal (ex-rstart e) (car lp)) (equal (ex-rn e) (cdr lp))
                                     (equal nk (cdr lp)) (ex-vwf :rec e 0 cm lp defs)))
                  (t nil)))))))

; A FN'S TEMPLATE (name arities caps nslots self), restricted: one arity,
; not variadic, of n parameters in slots start .. start+n-1; the capture
; pairs' inner slots and the self slot (if any) distinct from them and each
; other. Its def in mx, keyed by the template itself: (n body), the body
; lets of (:capt j) for the m captures and of the closure remade,
; (:mkclo template (:capt 0) ..), for the self slot -- the scope bcm, the
; parameters, the inner slots and the self slot by position (mx's
; arguments, then the lets) -- around the 1b loop of the parameters'
; copies, so a recur to the fn is that loop's.
(defun ex-far (tm) (car (nth 1 tm)))
(defun ex-fn (tm) (nfix (nth 0 (ex-far tm))))
(defun ex-fstart (tm) (nfix (nth 2 (ex-far tm))))
(defun ex-fbody-of (tm) (nth 3 (ex-far tm)))
(defun ex-fself (tm) (if (natp (nth 4 tm)) (nth 4 tm) nil))
(defun ex-fparams (tm) (ex-slots (ex-fstart tm) (ex-fn tm)))
(defun ex-fbcm (tm) (append (ex-fparams tm) (ex-inners (nth 2 tm)) (list (ex-fself tm))))
(defun ex-flp (tm) (cons (ex-fstart tm) (ex-fn tm)))
(defun ex-fcm (tm) (ex-blank (ex-lsl (ex-flp tm)) (ex-fbcm tm)))
(defun ex-fcmb (tm) (append (ex-fcm tm) (ex-lsl (ex-flp tm))))
(defun ex-capts (j m) (if (zp m) nil (cons (list :capt (nfix j)) (ex-capts (1+ (nfix j)) (1- m)))))
(defun ex-clets (j m x) (if (zp m) x (list :let (list :capt (nfix j)) (ex-clets (1+ (nfix j)) (1- m) x))))
(defun ex-fbtr (tm)
  (let ((m (len (ex-inners (nth 2 tm)))))
    (ex-clets 0 m (list :let (list* :mkclo tm (ex-capts 0 m))
                        (list :loop (cons '(:const nil) (ex-locals (ex-fparams tm) (ex-fbcm tm)))
                              (ex-tr :m (ex-fbody-of tm) 0 (ex-fcmb tm)))))))
(defun ex-def (tm) (list (ex-fn tm) (ex-fbtr tm)))
(defun ex-tmwf (tm defs)
  (let ((ar (ex-far tm)))
    (and (consp (nth 1 tm)) (atom (cdr (nth 1 tm))) (not (truthy (nth 1 ar)))
         (natp (nth 0 ar)) (natp (nth 2 ar)) (nat-listp (ex-inners (nth 2 tm)))
         (no-duplicatesp-equal (ex-inners (nth 2 tm))) (not (intersectp-equal (ex-inners (nth 2 tm)) (ex-fparams tm)))
         (or (not (natp (nth 4 tm)))
             (and (not (member-equal (nth 4 tm) (ex-fparams tm))) (not (member-equal (nth 4 tm) (ex-inners (nth 2 tm))))))
         (ex-vwf :m (ex-fbody-of tm) 0 (ex-fcmb tm) (ex-flp tm) defs))))
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
           ((:rec :call) nil)
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

(defun ex-xgood (flg e i cm lp defs)
  (implies (ex-vwf flg e i cm lp defs)
           (if (or (equal flg :rec) (equal flg :call))
               (xwf-args (ex-tr flg e i cm) (len cm))
             (xwf (ex-tr flg e i cm) (len cm) (ex-k lp)))))

(defthm ex-tr-xwf-flag
  (ex-xgood flg e i cm lp defs)
  :rule-classes nil
  :hints (("Goal" :induct (ex-vwf flg e i cm lp defs)
                  :in-theory (disable ex-kid-of)
                  :expand ((:free (flg cm) (ex-tr flg e i cm)) (:free (flg cm lp) (ex-vwf flg e i cm lp defs))
                           (:free (x y n) (xwf-args (cons x y) n))))))

; THE TRANSLATION OF A WELL-FORMED TREE IS THE VM'S WELL FORMED
(defthm ex-tr-xwf
  (implies (ex-vwf :m e 0 cm lp defs) (xwf (ex-tr :m e 0 cm) (len cm) (ex-k lp)))
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

; ---- VALUES, FNS AND CALLS ------------------------------------------------------------------------

(defthm ex-xvs-append (equal (ex-xvs defs (append a b)) (and (ex-xvs defs a) (ex-xvs defs b))))
(defthm ex-xvs-cons (implies (syntaxp (not (equal b ''nil)))
                             (equal (ex-xvs defs (cons a b)) (and (ex-xvs defs (list a)) (ex-xvs defs b))))
  :hints (("Goal" :expand ((ex-xvs defs (cons a b)) (ex-xvs defs (list a))))))
(defthm ex-xvs-nth (implies (ex-xvs defs l) (ex-xvs defs (list (nth j l)))))
(defthm ex-xvs-fr
  (implies (and (ex-agree cm env fr) (member-equal s cm) (natp s) (ex-xvs defs env))
           (ex-xvs defs (list (nth s fr))))
  :hints (("Goal" :in-theory (disable ex-xvs ex-agree-local)
                  :use ((:instance ex-xvs-nth (j (ex-pos s cm)) (l env)) ex-agree-local))))
(defthm ex-locals-valp (equal (car (mx-args (ex-locals ls cm) env caps defs fuel)) :val)
  :hints (("Goal" :induct (ex-locals ls cm)
                  :expand ((:free (x y) (mx-args (cons x y) env caps defs fuel))
                           (:free (x) (mx (cons :local x) env caps defs fuel))))))
(defthm ex-xvs-locals
  (implies (ex-xvs defs env) (ex-xvs defs (cdr (mx-args (ex-locals ls cm) env caps d2 fuel))))
  :hints (("Goal" :induct (ex-locals ls cm) :in-theory (disable ex-xvs)
                  :expand ((:free (x y) (mx-args (cons x y) env caps d2 fuel))
                           (:free (x) (mx (cons :local x) env caps d2 fuel))
                           (ex-xvs defs nil)))))
(defthm ex-locals-indep
  (implies (syntaxp (not (and (equal caps ''nil) (equal defs ''nil) (equal fuel ''0))))
           (equal (mx-args (ex-locals ls cm) env caps defs fuel) (mx-args (ex-locals ls cm) env nil nil 0)))
  :hints (("Goal" :induct (ex-locals ls cm)
                  :expand ((:free (x y caps defs fuel) (mx-args (cons x y) env caps defs fuel))
                           (:free (x caps defs fuel) (mx (cons :local x) env caps defs fuel))))))

(defthm ex-len-caps (equal (len (ex-caps capv fr)) (len (ex-inners capv))))
(defthm ex-true-listp-caps (true-listp (ex-caps capv fr)))
(defthm ex-caps-mx
  (implies (and (ex-agree cm env fr) (subsetp-equal (ex-outers capv) cm) (nat-listp (ex-outers capv)))
           (equal (mx-args (ex-locals (ex-outers capv) cm) env caps defs fuel) (cons :val (ex-caps capv fr))))
  :hints (("Goal" :induct (ex-caps capv fr)
                  :expand ((:free (x y) (mx-args (cons x y) env caps defs fuel))
                           (:free (x) (mx (cons :local x) env caps defs fuel))))))
(defthm ex-xvs-caps
  (implies (and (ex-agree cm env fr) (subsetp-equal (ex-outers capv) cm) (nat-listp (ex-outers capv)) (ex-xvs defs env))
           (ex-xvs defs (ex-caps capv fr)))
  :hints (("Goal" :induct (ex-caps capv fr))))

; the frame a call binds
(defthm ex-nth-bind-caps
  (implies (and (natp j) (not (member-equal j (ex-inners capv))) (nat-listp (ex-inners capv)))
           (equal (nth j (ex-bind-caps capv caps fr)) (nth j fr))))
(defthm ex-agree-bind-caps-other
  (implies (and (nat-listp (ex-inners capv)) (not (intersectp-equal (ex-inners capv) cm)))
           (equal (ex-agree cm env (ex-bind-caps capv caps fr)) (ex-agree cm env fr))))
(defthm ex-agree-bind-caps
  (implies (and (nat-listp (ex-inners capv)) (no-duplicatesp-equal (ex-inners capv))
                (equal (len caps) (len (ex-inners capv))))
           (ex-agree (ex-inners capv) caps (ex-bind-caps capv caps fr)))
  :hints (("Goal" :induct (ex-bind-caps capv caps fr))))

(defthm ex-arity-one
  (implies (and (consp ars) (atom (cdr ars)) (not (truthy (nth 1 (car ars)))))
           (equal (ex-arity ars n) (if (equal (nth 0 (car ars)) n) (car ars) nil))))

(defthm ex-defs-ok-assoc
  (implies (and (ex-defs-ok ds defs) (consp (assoc-equal tm ds)))
           (and (equal (cdr (assoc-equal tm ds)) (ex-def tm)) (ex-tmwf tm defs))))
(defthm ex-defs-ok-alistp (implies (ex-defs-ok ds defs) (alistp ds)))

; a callee's mx: :callv past its head and arguments
(defun ex-mxcall (f args defs fuel)
  (if (not (clop f))
      (list :err)
    (let ((def (cdr (assoc-eq (clo-f f) defs))))
      (cond ((not (consp def)) (list :err))
            ((not (equal (len args) (nfix (car def)))) (list :err))
            ((zp fuel) (list :out))
            (t (mx (cadr def) args (clo-caps f) defs (1- fuel)))))))
(defthm ex-mx-callv
  (equal (mx (cons :callv x) env caps defs fuel)
         (let ((rs (mx-args (cdr x) env caps defs fuel)))
           (if (not (valp rs))
               rs
             (let ((rf (mx (car x) env caps defs fuel)))
               (if (not (valp rf)) rf (ex-mxcall (val rf) (val rs) defs fuel))))))
  :hints (("Goal" :expand ((mx (cons :callv x) env caps defs fuel)))))
(defthm ex-mx-mkclo
  (equal (mx (cons :mkclo x) env caps defs fuel)
         (let ((rs (mx-args (cdr x) env caps defs fuel))) (if (valp rs) (cons :val (clo (car x) (val rs))) rs)))
  :hints (("Goal" :expand ((mx (cons :mkclo x) env caps defs fuel)))))

; the body's lets
(defun ex-nths (j m l) (if (zp m) nil (cons (nth (nfix j) l) (ex-nths (1+ (nfix j)) (1- m) l))))
(defthm ex-capts-mx (equal (mx-args (ex-capts j m) env caps defs fuel) (cons :val (ex-nths j m caps)))
  :hints (("Goal" :induct (ex-capts j m)
                  :expand ((:free (x y) (mx-args (cons x y) env caps defs fuel))
                           (:free (x) (mx (cons :capt x) env caps defs fuel))))))
(defun ex-clets-ind (j m env caps)
  (if (zp m) env (ex-clets-ind (1+ (nfix j)) (1- m) (append env (list (nth (nfix j) caps))) caps)))
(defthm ex-clets-mx
  (implies (true-listp env)
           (equal (mx (ex-clets j m x) env caps defs fuel) (mx x (append env (ex-nths j m caps)) caps defs fuel)))
  :hints (("Goal" :induct (ex-clets-ind j m env caps)
                  :expand ((:free (y env) (mx (cons :let y) env caps defs fuel))
                           (:free (y) (mx (cons :capt y) env caps defs fuel))))))
(defthm ex-nthcdr-step
  (implies (and (natp j) (< j (len l))) (equal (cons (nth j l) (nthcdr j (cdr l))) (nthcdr j l)))
  :hints (("Goal" :induct (nthcdr j l))))
(defthm ex-nthcdr-len (implies (true-listp l) (not (nthcdr (len l) l))))
(defthm ex-nths-nthcdr
  (implies (and (natp j) (true-listp l) (equal (+ j (nfix m)) (len l))) (equal (ex-nths j m l) (nthcdr j l)))
  :hints (("Goal" :induct (ex-nths j m l))))
(defthm ex-nths-all
  (implies (and (true-listp l) (equal m (len l))) (equal (ex-nths 0 m l) l))
  :hints (("Goal" :use ((:instance ex-nths-nthcdr (j 0))))))

(defun ex-fenv (f args) (append args (caddr f) (list f)))
(defun ex-fvs (f args)
  (cdr (mx-args (ex-locals (ex-fparams (cadr f)) (ex-fbcm (cadr f))) (ex-fenv f args) nil nil 0)))

(defthm ex-len-inners-outers (equal (len (ex-outers capv)) (len (ex-inners capv))))
(defthm ex-subset-app (subsetp-equal a (append a b)))

; what a call's entry needs of the callee f: a good value whose template's
; def is defs', callable with the arguments' count
(defun ex-ehyp (f args defs)
  (and (ex-xvs defs (list f)) (ex-defs-ok defs defs) (ex-callable f (len args))
       (ex-xvs defs args) (true-listp args)))

(defthm ex-ehyp-facts
  (implies (ex-ehyp f args defs)
           (and (ex-tmwf (cadr f) defs) (equal (len args) (ex-fn (cadr f)))
                (equal f (clo (cadr f) (caddr f)))
                (equal (ex-fbody f (len args)) (ex-fbody-of (cadr f)))
                (equal (cdr (assoc-equal (cadr f) defs)) (ex-def (cadr f)))
                (true-listp (caddr f)) (equal (len (caddr f)) (len (ex-inners (nth 2 (cadr f)))))
                (ex-xvs defs (caddr f)) (true-listp args)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance ex-defs-ok-assoc (ds defs) (tm (cadr f)))) :do-not-induct t
                  :in-theory (e/d (ex-tmwf ex-fn ex-far) (ex-defs-ok-assoc)))))


(defthm ex-fbcm-agree
  (implies (ex-ehyp f args defs)
           (ex-agree (ex-fbcm (cadr f)) (ex-fenv f args) (ex-bind f args)))
  :hints (("Goal" :use ex-ehyp-facts
                  :in-theory (e/d (ex-tmwf ex-far ex-fn ex-fstart ex-fself ex-fparams ex-fbcm ex-bind) (ex-ehyp)))))

(defthm ex-enter-fbody
  (implies (ex-ehyp f args defs) (equal (ex-fbody f (len args)) (ex-fbody-of (cadr f))))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (disable ex-ehyp ex-fbody ex-fbody-of))))
(defthm ex-enter-vwf
  (implies (ex-ehyp f args defs)
           (ex-vwf :m (ex-fbody-of (cadr f)) 0 (append (ex-fcm (cadr f)) (cons nil (ex-slots (ex-fstart (cadr f)) (ex-fn (cadr f)))))
                   (cons (ex-fstart (cadr f)) (ex-fn (cadr f))) defs))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (e/d (ex-tmwf) (ex-ehyp)))))
(defthm ex-enter-agree-cm
  (implies (ex-ehyp f args defs) (ex-agree (ex-fcm (cadr f)) (ex-fenv f args) (ex-bind f args)))
  :hints (("Goal" :in-theory (e/d (ex-fcm) (ex-ehyp ex-fenv ex-bind ex-fbcm)))))
(defthm ex-enter-agree-params
  (implies (ex-ehyp f args defs)
           (ex-agree (ex-slots (ex-fstart (cadr f)) (ex-fn (cadr f))) (ex-fvs f args) (ex-bind f args)))
  :hints (("Goal" :in-theory (e/d (ex-fvs ex-fparams) (ex-ehyp ex-fenv ex-bind ex-locals-indep))
                  :use (ex-fbcm-agree
                        (:instance ex-locals-mx (ls (ex-fparams (cadr f))) (cm (ex-fbcm (cadr f))) (env (ex-fenv f args))
                                   (fr (ex-bind f args)) (caps nil) (defs nil) (fuel 0)))
                  :expand ((ex-fbcm (cadr f))))))
(defthm ex-enter-len
  (implies (ex-ehyp f args defs) (equal (len (ex-fenv f args)) (len (ex-fcm (cadr f)))))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (e/d (ex-fcm ex-fbcm ex-fparams ex-fenv) (ex-ehyp)))))
(defthm ex-enter-xvs-env
  (implies (ex-ehyp f args defs) (ex-xvs defs (ex-fenv f args)))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (e/d (ex-fenv ex-ehyp) (ex-tmwf ex-defs-ok ex-callable)))))
(defthm ex-enter-xvs-vs
  (implies (ex-ehyp f args defs) (ex-xvs defs (ex-fvs f args)))
  :hints (("Goal" :in-theory (e/d (ex-fvs) (ex-ehyp ex-fenv ex-locals-indep)))))
(defthm ex-enter-nomem (ex-nomem (cons nil (ex-slots (ex-fstart tm) (ex-fn tm))) (ex-fcm tm))
  :hints (("Goal" :in-theory (e/d (ex-fcm) (ex-fbcm ex-fn ex-fstart ex-blank)))))
(defthm ex-car-assoc (implies (consp (assoc-equal x l)) (equal (car (assoc-equal x l)) x)))
(defthm ex-assoc-def
  (implies (and (ex-defs-ok defs defs) (consp (assoc-equal tm defs)))
           (equal (assoc-equal tm defs) (cons tm (ex-def tm))))
  :hints (("Goal" :use ((:instance ex-defs-ok-assoc (ds defs)))
                  :in-theory (disable ex-defs-ok-assoc ex-def ex-defs-ok))))
(defthm ex-enter-mx1
  (implies (and (ex-ehyp f args defs) (not (zp fuel)))
           (equal (ex-mxcall f args defs fuel) (mx (ex-fbtr (cadr f)) args (caddr f) defs (+ -1 fuel))))
  :hints (("Goal" :use ex-ehyp-facts
                  :in-theory (e/d (ex-mxcall ex-def ex-ehyp ex-callable) (ex-fbtr ex-tmwf ex-defs-ok ex-arity)))))
(defthm ex-fbtr-mx
  (implies (and (true-listp args) (true-listp caps) (equal (len caps) (len (ex-inners (nth 2 tm)))))
           (equal (mx (ex-fbtr tm) args caps defs fuel)
                  (mx-loop (list :loop nil (ex-tr :m (ex-fbody-of tm) 0 (ex-fcmb tm)))
                           (append args caps (list (clo tm caps)))
                           (cons nil (cdr (mx-args (ex-locals (ex-fparams tm) (ex-fbcm tm))
                                                   (append args caps (list (clo tm caps))) nil nil 0)))
                           caps defs fuel)))
  :hints (("Goal" :use ((:instance ex-mx-loop-body
                                   (e (list :loop (cons '(:const nil) (ex-locals (ex-fparams tm) (ex-fbcm tm)))
                                            (ex-tr :m (ex-fbody-of tm) 0 (ex-fcmb tm))))
                                   (base (append args caps (list (clo tm caps))))
                                   (vs (cons nil (cdr (mx-args (ex-locals (ex-fparams tm) (ex-fbcm tm))
                                                               (append args caps (list (clo tm caps))) nil nil 0))))))
                  :in-theory (e/d (ex-fbtr) (ex-mx-loop-body ex-fbcm ex-fparams ex-fcm ex-fcmb ex-fbody-of clo))
                  :expand ((:free (y env) (mx (cons :let y) env caps defs fuel))
                           (:free (y env) (mx (cons :loop y) env caps defs fuel))
                           (:free (x y env) (mx-args (cons x y) env caps defs fuel))
                           (:free (env) (mx '(:const nil) env caps defs fuel))))))
(defthm ex-enter-mx
  (implies (and (ex-ehyp f args defs) (not (zp fuel)))
           (equal (ex-mxcall f args defs fuel)
                  (mx-loop (list :loop nil (ex-tr :m (ex-fbody-of (cadr f)) 0
                                                  (append (ex-fcm (cadr f)) (cons nil (ex-slots (ex-fstart (cadr f)) (ex-fn (cadr f)))))))
                           (ex-fenv f args) (cons nil (ex-fvs f args)) (caddr f) defs (+ -1 fuel))))
  :hints (("Goal" :use ex-ehyp-facts
                  :in-theory (e/d (ex-fvs ex-fenv) (ex-ehyp ex-fbtr ex-fbcm ex-fparams ex-fcm ex-fbody-of)))))

(defthm ex-enter-ehyp
  (implies (and (ex-enters (car tmp) (len (cdr tmp))) (consp tmp) (ex-xvs defs tmp) (true-listp (cdr tmp)) (ex-defs-ok defs defs))
           (ex-ehyp (car tmp) (cdr tmp) defs))
  :hints (("Goal" :expand ((ex-xvs defs tmp)) :in-theory (enable ex-enters))))


; the same, of a call's record: its callee (car tmp), its arguments (cdr tmp)
(defthm ex-call-fbody
  (implies (and (ex-enters (car tmp) (len (cdr tmp))) (consp tmp) (ex-xvs defs tmp) (true-listp (cdr tmp)) (ex-defs-ok defs defs))
           (equal (ex-fbody (car tmp) (len (cdr tmp))) (ex-fbody-of (cadr (car tmp)))))
  :hints (("Goal" :use ((:instance ex-enter-fbody (f (car tmp)) (args (cdr tmp))) ex-enter-ehyp)
                  :in-theory (disable ex-enter-fbody ex-enter-ehyp))))
(defthm ex-call-vwf
  (implies (and (ex-enters (car tmp) (len (cdr tmp))) (consp tmp) (ex-xvs defs tmp) (true-listp (cdr tmp)) (ex-defs-ok defs defs))
           (ex-vwf :m (ex-fbody-of (cadr (car tmp))) 0 (append (ex-fcm (cadr (car tmp))) (cons nil (ex-slots (ex-fstart (cadr (car tmp))) (ex-fn (cadr (car tmp)))))) (cons (ex-fstart (cadr (car tmp))) (ex-fn (cadr (car tmp)))) defs))
  :hints (("Goal" :use ((:instance ex-enter-vwf (f (car tmp)) (args (cdr tmp))) ex-enter-ehyp)
                  :in-theory (disable ex-enter-vwf ex-enter-ehyp))))
(defthm ex-call-agree-cm
  (implies (and (ex-enters (car tmp) (len (cdr tmp))) (consp tmp) (ex-xvs defs tmp) (true-listp (cdr tmp)) (ex-defs-ok defs defs))
           (ex-agree (ex-fcm (cadr (car tmp))) (ex-fenv (car tmp) (cdr tmp)) (ex-bind (car tmp) (cdr tmp))))
  :hints (("Goal" :use ((:instance ex-enter-agree-cm (f (car tmp)) (args (cdr tmp))) ex-enter-ehyp)
                  :in-theory (disable ex-enter-agree-cm ex-enter-ehyp))))
(defthm ex-call-agree-params
  (implies (and (ex-enters (car tmp) (len (cdr tmp))) (consp tmp) (ex-xvs defs tmp) (true-listp (cdr tmp)) (ex-defs-ok defs defs))
           (ex-agree (ex-slots (ex-fstart (cadr (car tmp))) (ex-fn (cadr (car tmp)))) (ex-fvs (car tmp) (cdr tmp)) (ex-bind (car tmp) (cdr tmp))))
  :hints (("Goal" :use ((:instance ex-enter-agree-params (f (car tmp)) (args (cdr tmp))) ex-enter-ehyp)
                  :in-theory (disable ex-enter-agree-params ex-enter-ehyp))))
(defthm ex-call-len
  (implies (and (ex-enters (car tmp) (len (cdr tmp))) (consp tmp) (ex-xvs defs tmp) (true-listp (cdr tmp)) (ex-defs-ok defs defs))
           (equal (len (ex-fenv (car tmp) (cdr tmp))) (len (ex-fcm (cadr (car tmp))))))
  :hints (("Goal" :use ((:instance ex-enter-len (f (car tmp)) (args (cdr tmp))) ex-enter-ehyp)
                  :in-theory (disable ex-enter-len ex-enter-ehyp))))
(defthm ex-call-xvs-env
  (implies (and (ex-enters (car tmp) (len (cdr tmp))) (consp tmp) (ex-xvs defs tmp) (true-listp (cdr tmp)) (ex-defs-ok defs defs))
           (ex-xvs defs (ex-fenv (car tmp) (cdr tmp))))
  :hints (("Goal" :use ((:instance ex-enter-xvs-env (f (car tmp)) (args (cdr tmp))) ex-enter-ehyp)
                  :in-theory (disable ex-enter-xvs-env ex-enter-ehyp))))
(defthm ex-call-xvs-vs
  (implies (and (ex-enters (car tmp) (len (cdr tmp))) (consp tmp) (ex-xvs defs tmp) (true-listp (cdr tmp)) (ex-defs-ok defs defs))
           (ex-xvs defs (ex-fvs (car tmp) (cdr tmp))))
  :hints (("Goal" :use ((:instance ex-enter-xvs-vs (f (car tmp)) (args (cdr tmp))) ex-enter-ehyp)
                  :in-theory (disable ex-enter-xvs-vs ex-enter-ehyp))))
(defthm ex-call-mx
  (implies (and (ex-enters (car tmp) (len (cdr tmp))) (consp tmp) (ex-xvs defs tmp) (true-listp (cdr tmp)) (ex-defs-ok defs defs) (not (zp fuel)))
           (equal (ex-mxcall (car tmp) (cdr tmp) defs fuel)
                  (mx-loop (list :loop nil (ex-tr :m (ex-fbody-of (cadr (car tmp))) 0
                                                  (append (ex-fcm (cadr (car tmp))) (cons nil (ex-slots (ex-fstart (cadr (car tmp))) (ex-fn (cadr (car tmp))))))))
                           (ex-fenv (car tmp) (cdr tmp)) (cons nil (ex-fvs (car tmp) (cdr tmp))) (caddr (car tmp)) defs (+ -1 fuel))))
  :hints (("Goal" :use ((:instance ex-enter-mx (f (car tmp)) (args (cdr tmp))) ex-enter-ehyp)
                  :in-theory (disable ex-enter-mx ex-enter-ehyp))))

(defthm ex-linked-ev
  (implies (ex-linked h) (equal (ex-ev :m h 0 tmp fr fuel) (list (cons :val (ex-c h)) fr 1)))
  :hints (("Goal" :expand ((ex-ev :m h 0 tmp fr fuel)))))

; a call never answers a recur: its callee's body restarts on one
(defun ex-cind (e i tmp fr fuel)
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i)))))
  (if (< (nfix i) (ex-nk e))
      (let ((r (ex-ev :m (ex-kid-of e (nfix i)) 0 nil fr fuel)))
        (ex-cind e (1+ (nfix i)) (append tmp (list (val (car r)))) (cadr r) fuel))
    (list tmp fr)))
(defthm ex-call-not-recur (not (equal (car (car (ex-ev :call e i tmp fr fuel))) :recur))
  :hints (("Goal" :induct (ex-cind e i tmp fr fuel) :in-theory (disable ex-kid-of)
                  :expand ((ex-ev :call e i tmp fr fuel)))))

(defthm ex-xvs-nil (ex-xvs defs nil))
(defthm ex-xvs-nil1 (ex-xvs defs (list nil)))
(defthm ex-xvs-clo
  (implies (and (consp (assoc-equal tm defs)) (ex-xvs defs caps) (true-listp caps)
                (equal (len caps) (len (ex-inners (nth 2 tm)))))
           (ex-xvs defs (list (list :clo tm caps)))))

(in-theory (disable ex-fn ex-fstart ex-fbody-of ex-fself ex-fbcm ex-fcm ex-fbtr ex-def ex-tmwf ex-fenv ex-fvs
                    ex-callable ex-enters ex-bind ex-mxcall ex-ehyp ex-fbody))

(defun ex-vhyp (flg e i tmp cm env fr lp defs)
  (and (ex-defs-ok defs defs)
       (if (equal flg :iter)
           (and (consp lp) (ex-vwf :m e 0 (append cm (ex-lsl lp)) lp defs)
                (ex-agree (append cm (ex-lsl lp)) (append env tmp) fr)
                (ex-nomem (ex-lsl lp) cm) (equal (len env) (len cm)) (ex-xvs defs (append env tmp)))
         (and (member-equal flg '(:m :do :let :rec :call)) (ex-vwf flg e i cm lp defs) (ex-agree cm env fr)
              (ex-xvs defs env)
              (or (not (equal flg :rec)) (and (true-listp tmp) (equal (len tmp) (nfix i)) (ex-xvs defs tmp)))
              (or (not (equal flg :call)) (and (consp tmp) (true-listp tmp) (ex-xvs defs tmp)))))))

(defun ex-vpost (flg e i tmp cm env lp caps defs fuel r)
  (let ((res (car r)) (fr2 (cadr r)) (ls (ex-lsl lp)))
    (case flg
      (:iter (implies (valp res)
                      (and (equal (mx-loop (list :loop nil (ex-tr :m e 0 (append cm ls))) env tmp caps defs fuel) res)
                           (ex-agree cm env fr2) (ex-xvs defs (list (val res))))))
      (:rec (implies (equal (car res) :recur)
                     (let ((m (mx-args (ex-tr :rec e i cm) env caps defs fuel)))
                       (and (valp m) (ex-agree (cdr ls) (append tmp (val m)) fr2)
                            (ex-agree (ex-blank ls cm) env fr2) (ex-xvs defs (append tmp (val m)))))))
      (:call (implies (valp res)
                      (let ((m (mx-args (ex-tr :call e i cm) env caps defs fuel)))
                        (and (valp m) (equal (ex-mxcall (car tmp) (append (cdr tmp) (val m)) defs fuel) res)
                             (ex-agree cm env fr2) (ex-xvs defs (list (val res)))))))
      (otherwise
       (let ((m (mx (ex-tr flg e i cm) env caps defs fuel)))
         (and (implies (valp res)
                       (and (equal m res) (ex-xvs defs (list (val res)))
                            (if (and (equal flg :let) (equal (ex-kind e) 12))
                                (ex-agree (ex-blank (ex-lsl (cons (ex-s2 e) (ex-i2 e))) cm) env fr2)
                              (ex-agree cm env fr2))))
              (implies (equal (car res) :recur)
                       (and (consp lp) (equal (car m) :recur) (ex-agree ls (cdr m) fr2)
                            (ex-agree (ex-blank ls cm) env fr2) (ex-xvs defs (cdr m))))))))))

(defun ex-vgood (flg e i tmp cm env fr fuel caps defs lp)
  (implies (ex-vhyp flg e i tmp cm env fr lp defs)
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
        (:call (cond ((< i nk)
                      (let ((r (ex-ev :m (ex-kid-of e i) 0 nil fr fuel)))
                        (list (ex-vind :m (ex-kid-of e i) 0 nil cm env fr fuel caps defs nil)
                              (ex-vind :call e (1+ i) (append tmp (list (val (car r)))) cm env (cadr r) fuel caps defs lp))))
                     ((zp fuel) nil)
                     (t (let ((f (car tmp)) (args (cdr tmp)))
                          (ex-vind :iter (ex-fbody f (len args)) 0 (cons nil (ex-fvs f args)) (ex-fcm (cadr f))
                                   (ex-fenv f args) (ex-bind f args) (1- fuel) (caddr f) defs
                                   (cons (ex-fstart (cadr f)) (ex-fn (cadr f))))))))
        (otherwise
         (cond ((equal k 4)
                (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                  (list (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
                        (ex-vind :m (ex-kid-of e 1) 0 nil cm env (cadr r) fuel caps defs lp)
                        (ex-vind :m (ex-kid-of e 2) 0 nil cm env (cadr r) fuel caps defs lp))))
               ((equal k 5) (ex-vind :do e 0 nil cm env fr fuel caps defs lp))
               ((or (equal k 11) (equal k 12)) (ex-vind :let e 0 nil cm env fr fuel caps defs lp))
               ((equal k 16) (ex-vind :rec e 0 nil cm env fr fuel caps defs lp))
               ((equal k 6)
                (let ((r (ex-ev :m (ex-kid-of e 0) 0 nil fr fuel)))
                  (list (ex-vind :m (ex-kid-of e 0) 0 nil cm env fr fuel caps defs nil)
                        (ex-vind :call e 1 (list (val (car r))) cm env (cadr r) fuel caps defs lp))))
               (t nil)))))))

(defthm ex-vm-agree-flag
  (ex-vgood flg e i tmp cm env fr fuel caps defs lp)
  :rule-classes nil
  :hints (("Goal" :induct (ex-vind flg e i tmp cm env fr fuel caps defs lp)
                  :in-theory (disable ex-kid-of ex-xvs)
                  :expand ((:free (flg cm) (ex-tr flg e i cm)) (:free (flg cm lp) (ex-vwf flg e i cm lp defs))
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

; A WELL-FORMED TREE ANSWERS WHAT THE VM'S MEANING DOES, its defs the
; templates' and its scope's values good
(defthm ex-vm-agree
  (implies (and (ex-vwf :m e 0 cm nil defs) (ex-defs-ok defs defs) (ex-agree cm env fr) (ex-xvs defs env)
                (valp (car (ex-ev :m e 0 nil fr fuel))))
           (equal (mx (ex-tr :m e 0 cm) env caps defs fuel) (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :use ((:instance ex-vm-agree-flag (flg :m) (i 0) (tmp nil) (lp nil))))))

; ... and outside every loop's tail it never answers a recur: a recur's
; values become its loop's slots, never a value
(defthm ex-recur-stays
  (implies (and (ex-vwf :m e 0 cm nil defs) (ex-defs-ok defs defs) (ex-agree cm env fr) (ex-xvs defs env))
           (not (equal (car (car (ex-ev :m e 0 nil fr fuel))) :recur)))
  :hints (("Goal" :use ((:instance ex-vm-agree-flag (flg :m) (i 0) (tmp nil) (lp nil))))))

; THE DEFS ARE THE VM'S: every def's body xwf at its arity (vmx's xdefs-ok)
(defthm ex-xwf-capts (xwf-args (ex-capts j m) n))
(defun ex-clets-ind2 (j m n) (if (zp m) n (ex-clets-ind2 (1+ (nfix j)) (1- m) (1+ n))))
(defthm ex-xwf-clets (implies (natp n) (equal (xwf (ex-clets j m x) n k) (xwf x (+ n (nfix m)) k)))
  :hints (("Goal" :induct (ex-clets-ind2 j m n) :expand ((:free (y n) (xwf (cons :let y) n k))))))
(defthm ex-len-fbcm (equal (len (ex-fbcm tm)) (+ (ex-fn tm) (len (ex-inners (nth 2 tm))) 1))
  :hints (("Goal" :in-theory (enable ex-fbcm ex-fn))))
(defthm ex-len-fcm (equal (len (ex-fcm tm)) (len (ex-fbcm tm))) :hints (("Goal" :in-theory (enable ex-fcm))))
(defthm ex-params-sub (subsetp-equal (ex-fparams tm) (ex-fbcm tm)) :hints (("Goal" :in-theory (enable ex-fbcm))))
(defthm ex-len-fparams (equal (len (ex-fparams tm)) (ex-fn tm)) :hints (("Goal" :in-theory (enable ex-fn))))
(defthm ex-tmwf-vwf
  (implies (ex-tmwf tm defs) (ex-vwf :m (ex-fbody-of tm) 0 (ex-fcmb tm) (ex-flp tm) defs))
  :hints (("Goal" :in-theory (enable ex-tmwf))))
(defthm ex-fbtr-xwf
  (implies (ex-tmwf tm defs) (xwf (ex-fbtr tm) (ex-fn tm) nil))
  :hints (("Goal" :in-theory (e/d (ex-fbtr) (ex-tr-xwf ex-fparams ex-tmwf-vwf))
                  :use ((:instance ex-tr-xwf (e (ex-fbody-of tm)) (cm (ex-fcmb tm)) (lp (ex-flp tm))) ex-tmwf-vwf
                        (:instance ex-locals-xwf (ls (ex-fparams tm)) (cm (ex-fbcm tm))))
                  :expand ((:free (y n) (xwf (cons :let y) n nil)) (:free (y n k) (xwf (cons :loop y) n k))
                           (:free (y n) (xwf (cons :mkclo y) n nil)) (:free (x y n) (xwf-args (cons x y) n))))))
(defthm ex-defs-xdefs (implies (ex-defs-ok ds defs) (xdefs-ok ds))
  :hints (("Goal" :in-theory (enable ex-def))))
