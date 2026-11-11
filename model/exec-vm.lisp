; THE TREE EVALUATOR'S MEANING IS THE VM'S (model/exec.lisp against
; model/vmx2.lisp): for the core -- constants, locals, Vars, if, do, let*,
; loop*, recur, fns of any arities and calls -- what ex-ev answers is what
; vmx2's mx2 answers of the tree's translation, and vmx2-proof proves the
; VM runs mx2 (vcs2-correct), so the VM run of the translation answers the
; tree's value (ex-vm-runs, in exec-vmrun).
;
; The tree names a local by its SLOT in the fn's frame, which the analyzer
; numbers by reservation, never reusing one in scope; mx2 names it by its
; POSITION in an environment a let grows by one. The translation (ex-tr)
; carries cm, the slots in scope by position: a local is (:local p) for
; its slot's position p, a let a nest of mx2's one-binding lets, a do an if
; on each value but the last with the rest on both branches (the core is
; pure: a value only chooses between equal branches). The relation
; (ex-agree cm env fr): position p's value is slot (nth p cm)'s, for each
; position whose cm entry is a slot (a nil entry is a position no name
; reaches any more).
;
; A LOOP. The tree binds a loop's inits one after another, each seeing
; the ones before; vmx's :loop binds its inits at once. So a loop of n
; bindings in slots s .. s+n-1 is n of mx2's lets (the inits, in order)
; around (:loop (nil, copies of the n positions) body): the body's scope
; is the lets' positions blanked -- after a recur they hold the first
; round's values, and no name reaches them -- then a dummy and the
; copies, so its slots name the loop's own positions. A recur is (:recur
; nil args...): the dummy makes every loop bind at least one, as x2wf asks,
; and keeps a zero-binding loop one translation.
;
; FNS AND CALLS. A Var is (:const its value) (the namespace is the host's;
; the machine reads the value from the node). A fn is (:mkclo template
; locals of its outer slots): the tree's closure and mx2's are one value. A
; call is head first, as the tree runs it (exec-PLAN 3b, ex-trcall): (:let
; head (:if (:prim :ifn (:local p)) (:applyv (:local p) args) (:throw
; (:const :not-fn)))), p the head's new position, the arguments in scope
; cm ++ (nil) -- :callv's call, or apply's spread when the head's value is
; apply, as the tree's ex-callee spreads it (apply is a value; only the
; head's value tells), after the runtime's cast to IFn the tree's pc 1
; asks (ex-ifn) -- so a throw in the head, the cast or an argument is the
; same throw in both. mx2's
; defs are keyed by the template itself (vcs2-correct asks only x2defs-ok,
; and both look a name up by equal), the def a clause for each arity, (nf
; body) or (nf body :rest): lets of the captures and of the closure remade,
; for the self slot, around the loop translation of the parameters (a
; variadic arity's rest among them, a list, as mx2's split-rest makes it),
; so a recur to the fn is that loop's. The arity a call's count picks is
; the one mx2's pick-arity picks (ex-pick-arity): the fixed one, else the
; variadic one. Templates ask (ex-tmwf) each arity's parameter slots apart
; from the capture and self slots. Every closure-shaped value has its
; template in the defs, and no value is the symbol :clo, so a rest list is
; never closure-shaped (ex-xvs), threaded through the scope, results and
; recur values; no value is the symbol :recur-marker either, so no good
; list holds the tree's recur marker (ex-xvs-no-mk) and apply's spread of
; good values is never refused for one. A call of a closure no arity fits
; throws :arity in both (ex-ev's :thrown, mx2's). The runtime's part
; (prim, unconstrained) is two hypotheses: its cast to IFn throws nothing
; (ex-ifnok), and a call of apply the tree refuses -- fewer than two
; arguments, a closure's with no seq -- it refuses with the tree's :arity
; and :not-seq (ex-apok).
;
; THE THEOREM (ex-vm-agree): a well-formed core tree in no loop's tail
; whose scope agrees answers, when ex-ev gives a value or a throw, that
; same answer from mx2 of its translation, the scope still agreeing after
; (a throw's frame the one the tree's unwinding sees); and it
; never answers a recur (ex-recur-stays) -- a recur's values reach only
; its loop's slots, which mx2's recur gives its loop's positions. The
; translation of a well-formed tree is x2wf (ex-tr-xwf), so with
; vcs2-correct: ex-vm-runs (exec-vmrun). With ex-machine-correct (exec-proof), the
; machine exec.inc's run_loop is answers what the VM answers.

(in-package "ACL2")

(include-book "exec")
(include-book "vmx2")

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
               ((equal k 6) (ex-trcall (ex-tr :m (ex-kid-of e 0) 0 cm) (ex-tr :call e 1 (append cm (list nil))) (len cm)))
               ((equal k 2) (list :local (ex-pos (ex-i2 e) cm)))
               ((equal k 4) (list :if (ex-tr :m (ex-kid-of e 0) 0 cm) (ex-tr :m (ex-kid-of e 1) 0 cm)
                                  (if (< 2 nk) (ex-tr :m (ex-kid-of e 2) 0 cm) '(:const nil))))
               ((equal k 5) (ex-tr :do e 0 cm))
               ((or (equal k 11) (equal k 12)) (ex-tr :let e 0 cm))
               ((equal k 16) (list* :recur '(:const nil) (ex-tr :rec e 0 cm)))
               (t '(:const nil))))))))

; THE VALUES (milestone 2b): every closure-shaped value one whose template
; is in defs (so mx2's :callv finds its def), its captures as many as the
; template's pairs and good themselves; any other value is good but the
; symbol :recur-marker (the tree's recur marker's) and
; symbol :clo itself, so a variadic call's rest list of good values is
; never closure-shaped (the model's list is the machine's seq, and :clo is
; no value a program holds); and a list's elements good too, so apply's
; spread of a good seq is good arguments (2c-iii: apply is a value like
; any other, its call spread by vmx2's :applyv)
(defun ex-xvs (defs l)
  (if (atom l)
      t
    (and (let ((v (car l)))
           (and (not (equal v :clo)) (not (equal v :recur-marker))
                (if (clop v)
                    (and (equal v (clo (cadr v) (caddr v))) (consp (assoc-equal (cadr v) defs))
                         (true-listp (caddr v)) (equal (len (caddr v)) (len (ex-inners (nth 2 (cadr v)))))
                         (ex-xvs defs (caddr v)))
                  (ex-xvs defs v))))
         (ex-xvs defs (cdr l)))))

; THE CALL A GOOD RECORD MAKES, apply's spread or itself, is a good record
(defthm ex-xvs-elem (implies (and (ex-xvs defs (list v)) (not (clop v))) (ex-xvs defs v))
  :hints (("Goal" :expand ((ex-xvs defs (list v))))))
(defthm ex-xvs-last (implies (ex-xvs defs l) (ex-xvs defs (list (car (last l))))))
(defthm ex-xvs-take (implies (ex-xvs defs l) (ex-xvs defs (take n l)))
  :hints (("Goal" :induct (take n l) :expand ((ex-xvs defs l) (:free (a b) (ex-xvs defs (cons a b)))))))
(defthm ex-xvs-append (equal (ex-xvs defs (append a b)) (and (ex-xvs defs a) (ex-xvs defs b))))
; A LAZY SEQ'S ELEMENTS are what the runtime's realisations give (seqk's
; sk-real, constrained by nothing): the agreement asks they be good values
; too, as it asks it of the scope's -- ex-lzok, the runtime handing the
; machine only closures it knows. Then a good seq's elements, every kind,
; are good.
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
(defthm ex-xvs-list1 (implies (and (ex-xvs defs x) (not (equal x :clo)) (not (equal x :recur-marker))) (ex-xvs defs (list x)))
  :hints (("Goal" :expand ((ex-xvs defs (list x)) (ex-xvs defs x)))))
(defthm ex-xvs-nthcdr-l (implies (ex-xvs defs l) (ex-xvs defs (nthcdr n l)))
  :hints (("Goal" :induct (nthcdr n l) :expand ((ex-xvs defs l)))))
(defthm ex-xvs-sk-topv (implies (ex-xvs defs v) (ex-xvs defs (sk-topv v)))
  :hints (("Goal" :induct (sk-topv v) :expand ((ex-xvs defs v) (:free (a b) (ex-xvs defs (cons a b)))))))
(defthm ex-sk-cval-good (implies (ex-xvs defs (car c)) (ex-xvs defs (sk-cval c)))
  :hints (("Goal" :in-theory (enable sk-cval) :expand ((ex-xvs defs (car c)) (:free (b) (ex-xvs defs (cons :vec b)))))))
(defthm ex-sk-cval-noclo (implies (sk-more (sk-d c)) (and (consp (sk-cval c)) (not (equal (sk-cval c) :clo)) (not (equal (sk-cval c) :recur-marker))))
  :hints (("Goal" :in-theory (enable sk-cval sk-d sk-kind sk-step sk-topv))))
(defthm ex-xvs-consv (implies (and (ex-xvs defs xs) (ex-xvs defs s)) (ex-xvs defs (sk-consv xs s)))
  :hints (("Goal" :induct (sk-consv xs s) :expand ((ex-xvs defs xs) (:free (a b) (ex-xvs defs (cons a b)))))))
(defthm ex-consv-consp (implies (consp xs) (consp (sk-consv xs s))))
(defthm ex-consv-noclo (implies (consp xs) (and (not (equal (sk-consv xs s) :clo)) (not (equal (sk-consv xs s) :recur-marker)))))
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
           (:fin nil)
           (otherwise
            (cond ((or (equal k 1) (equal k 3)) (ex-xvs defs (list (ex-c e))))
                  ((equal k 2) (and (member-equal (ex-i2 e) cm) (not (ex-mark e))))
                  ((equal k 14) (and (consp (assoc-equal (ex-c e) defs))
                                     (nat-listp (ex-outers (nth 2 (ex-c e))))
                                     (subsetp-equal (ex-outers (nth 2 (ex-c e))) cm)))
                  ((equal k 6) (and (< 0 nk) (ex-vwf :m (ex-kid-of e 0) 0 cm nil defs) (ex-vwf :call e 1 (append cm (list nil)) lp defs)))
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
       (ex-vwf :m (ex-abody ar) 0 (ex-fcmb tm ar) (ex-flp ar) defs)))
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
               (x2wf-args (ex-tr flg e i cm) (len cm))
             (x2wf (ex-tr flg e i cm) (len cm) (ex-k lp)))))

(defthm ex-tr-xwf-flag
  (ex-xgood flg e i cm lp defs)
  :rule-classes nil
  :hints (("Goal" :induct (ex-vwf flg e i cm lp defs)
                  :in-theory (disable ex-kid-of)
                  :expand ((:free (flg cm) (ex-tr flg e i cm)) (:free (flg cm lp) (ex-vwf flg e i cm lp defs))
                           (:free (x y n) (x2wf-args (cons x y) n))))))

; THE TRANSLATION OF A WELL-FORMED TREE IS THE VM'S WELL FORMED
(defthm ex-tr-xwf
  (implies (ex-vwf :m e 0 cm lp defs) (x2wf (ex-tr :m e 0 cm) (len cm) (ex-k lp)))
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

(defthm ex-xvs-cons (implies (syntaxp (not (equal b ''nil)))
                             (equal (ex-xvs defs (cons a b)) (and (ex-xvs defs (list a)) (ex-xvs defs b))))
  :hints (("Goal" :expand ((ex-xvs defs (cons a b)) (ex-xvs defs (list a))))))
(defthm ex-xvs-nth (implies (ex-xvs defs l) (ex-xvs defs (list (nth j l)))))
(defthm ex-xvs-fr
  (implies (and (ex-agree cm env fr) (member-equal s cm) (natp s) (ex-xvs defs env))
           (ex-xvs defs (list (nth s fr))))
  :hints (("Goal" :in-theory (disable ex-xvs ex-agree-local)
                  :use ((:instance ex-xvs-nth (j (ex-pos s cm)) (l env)) ex-agree-local))))
(defthm ex-locals-valp (equal (car (mx2-args (ex-locals ls cm) env caps defs fuel)) :val)
  :hints (("Goal" :induct (ex-locals ls cm)
                  :expand ((:free (x y) (mx2-args (cons x y) env caps defs fuel))
                           (:free (x) (mx2 (cons :local x) env caps defs fuel))))))
(defthm ex-xvs-locals
  (implies (ex-xvs defs env) (ex-xvs defs (cdr (mx2-args (ex-locals ls cm) env caps d2 fuel))))
  :hints (("Goal" :induct (ex-locals ls cm) :in-theory (disable ex-xvs)
                  :expand ((:free (x y) (mx2-args (cons x y) env caps d2 fuel))
                           (:free (x) (mx2 (cons :local x) env caps d2 fuel))
                           (ex-xvs defs nil)))))
(defthm ex-locals-indep
  (implies (syntaxp (not (and (equal caps ''nil) (equal defs ''nil) (equal fuel ''0))))
           (equal (mx2-args (ex-locals ls cm) env caps defs fuel) (mx2-args (ex-locals ls cm) env nil nil 0)))
  :hints (("Goal" :induct (ex-locals ls cm)
                  :expand ((:free (x y caps defs fuel) (mx2-args (cons x y) env caps defs fuel))
                           (:free (x caps defs fuel) (mx2 (cons :local x) env caps defs fuel))))))

(defthm ex-len-caps (equal (len (ex-caps capv fr)) (len (ex-inners capv))))
(defthm ex-true-listp-caps (true-listp (ex-caps capv fr)))
(defthm ex-caps-mx
  (implies (and (ex-agree cm env fr) (subsetp-equal (ex-outers capv) cm) (nat-listp (ex-outers capv)))
           (equal (mx2-args (ex-locals (ex-outers capv) cm) env caps defs fuel) (cons :val (ex-caps capv fr))))
  :hints (("Goal" :induct (ex-caps capv fr)
                  :expand ((:free (x y) (mx2-args (cons x y) env caps defs fuel))
                           (:free (x) (mx2 (cons :local x) env caps defs fuel))))))
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

; the arity a call picks (ex-arity, its fixed pass then its variadic one)
; and the clause mx2's pick-arity picks are one
(defthm ex-arity-pass-consp (implies (ex-arity-pass ars n p) (consp (ex-arity-pass ars n p))))
(defthm ex-arity-pass0
  (implies (ex-arity-pass ars n 0)
           (and (not (truthy (nth 1 (ex-arity-pass ars n 0)))) (equal (nth 0 (ex-arity-pass ars n 0)) n))))
(defthm ex-arity-pass1
  (implies (ex-arity-pass ars n 1)
           (and (truthy (nth 1 (ex-arity-pass ars n 1))) (natp (nth 0 (ex-arity-pass ars n 1)))
                (<= (nth 0 (ex-arity-pass ars n 1)) n)))
  :rule-classes ((:rewrite) (:linear :corollary (implies (ex-arity-pass ars n 1) (<= (nth 0 (ex-arity-pass ars n 1)) n)))))
(defthm ex-arwf-nat
  (implies (ex-arwf tm ar defs) (and (natp (car ar)) (natp (caddr ar))))
  :rule-classes :forward-chaining)
(defthm ex-arswf-cons
  (equal (ex-arswf tm (cons a ars) defs) (and (ex-arwf tm a defs) (ex-arswf tm ars defs))))
(in-theory (disable ex-arwf))
(defthm ex-arswf-pass
  (implies (and (ex-arswf tm ars defs) (ex-arity-pass ars n p)) (ex-arwf tm (ex-arity-pass ars n p) defs))
  :hints (("Goal" :induct (ex-arity-pass ars n p))))
(defthm ex-arswf-arity
  (implies (and (ex-arswf tm ars defs) (ex-arity ars n)) (ex-arwf tm (ex-arity ars n) defs)))
(defthm ex-pick-fixed
  (implies (and (ex-arswf tm ars defs) (natp m))
           (equal (pick-fixed (ex-clauses tm ars) m)
                  (if (ex-arity-pass ars m 0) (ex-clause tm (ex-arity-pass ars m 0)) nil)))
  :hints (("Goal" :in-theory (e/d (ex-anf ex-avar) (ex-fbtr)))))
(defthm ex-pick-rest
  (implies (and (ex-arswf tm ars defs) (natp m))
           (equal (pick-rest (ex-clauses tm ars) m)
                  (if (ex-arity-pass ars m 1) (ex-clause tm (ex-arity-pass ars m 1)) nil)))
  :hints (("Goal" :in-theory (e/d (ex-anf ex-avar) (ex-fbtr)))))
(defthm ex-pick-arity
  (implies (and (ex-arswf tm ars defs) (natp m))
           (equal (pick-arity (ex-clauses tm ars) m) (if (ex-arity ars m) (ex-clause tm (ex-arity ars m)) nil)))
  :hints (("Goal" :in-theory (disable ex-clause ex-clauses ex-arswf))))
(defthm ex-split-rest (equal (split-rest n vs) (ex-rest-args n vs)) :hints (("Goal" :in-theory (enable split-rest ex-rest-args))))

; a variadic call's locals: as many as its parameters, good when the
; arguments are (the rest list of good values is never closure-shaped)
(defthm ex-len-take (equal (len (take n l)) (nfix n)))
(defthm ex-len-bargs
  (implies (and (ex-arity ars (len args)) (true-listp args))
           (equal (len (ex-bargs (ex-arity ars (len args)) args)) (ex-anp (ex-arity ars (len args)))))
  :hints (("Goal" :in-theory (e/d (ex-anp ex-anf ex-avar ex-bargs ex-rest-args) (ex-arity-pass))
                  :cases ((ex-arity-pass ars (len args) 0)))))
(defthm ex-true-listp-bargs (implies (true-listp args) (true-listp (ex-bargs ar args)))
  :hints (("Goal" :in-theory (enable ex-bargs ex-rest-args))))
(defthm ex-xvs-nthcdr (implies (and (ex-xvs defs l) (true-listp l)) (ex-xvs defs (list (nthcdr n l))))
  :hints (("Goal" :induct (nthcdr n l) :expand ((ex-xvs defs l) (:free (a) (ex-xvs defs (list a)))))))
(defthm ex-xvs-bargs (implies (and (ex-xvs defs args) (true-listp args)) (ex-xvs defs (ex-bargs ar args)))
  :hints (("Goal" :in-theory (enable ex-bargs ex-rest-args))))

(defthm ex-defs-ok-assoc
  (implies (and (ex-defs-ok ds defs) (consp (assoc-equal tm ds)))
           (and (equal (cdr (assoc-equal tm ds)) (ex-def tm)) (ex-tmwf tm defs))))
(defthm ex-defs-ok-alistp (implies (ex-defs-ok ds defs) (alistp ds)))

; a callee's mx2: :callv past its head and arguments, and :applyv's, past
; apply's spread
(defun ex-mxcl (f args cls defs fuel)
  (if (not (clop f))
      (let ((a (prim :invoke (cons f args)))) (if (throwp a) (cons :thrown (cdr a)) (cons :val a)))
    (let ((cl (pick-arity cls (len args))))
      (cond ((not (consp cl)) (cons :thrown :arity))
            ((zp fuel) (list :out))
            (t (mx2 (cadr cl) (if (restp cl) (split-rest (nfix (car cl)) args) args) (clo-caps f) defs (1- fuel)))))))
; the clauses a callee dispatches in: its template's def, or for apply's
; hand-over (ex-hclo) the variadic clause of the closure it stands for as
; the fixed one of req + 1 (vmx2's x2-hcls)
(defun ex-mxcls (f defs)
  (if (equal (ex-self f) f) (cdr (assoc-equal (clo-f f) defs)) (x2-hcls (cdr (assoc-equal (clo-f (ex-self f)) defs)))))
(defun ex-mxcall0 (f args defs fuel) (ex-mxcl f args (ex-mxcls f defs) defs fuel))
(defun ex-mxcall (f args defs fuel)
  (let ((c (x2-fn :applyv f args defs)))
    (ex-mxcl c (x2-vals :applyv f args defs) (x2-cls :applyv f args defs (cdr (assoc-equal (clo-f c) defs))) defs fuel)))
(defthm ex-mx-applyv
  (equal (mx2 (cons :applyv x) env caps defs fuel)
         (let ((rs (mx2-args (cdr x) env caps defs fuel)))
           (if (not (valp rs))
               rs
             (let ((rf (mx2 (car x) env caps defs fuel)))
               (if (not (valp rf)) rf (ex-mxcall (val rf) (val rs) defs fuel))))))
  :hints (("Goal" :expand ((mx2 (cons :applyv x) env caps defs fuel)) :in-theory (disable x2-fn x2-vals))))
; a call the tree enters: the VM's spread is the tree's (ex-callee) -- the
; variadic clause's count one in both (x2-req of the def, ex-varnf of the
; template), a hand-over's callee ex-hclo dispatching in x2-hcls
(defthm ex-x2-req-clauses (equal (x2-req (ex-clauses tm ars)) (ex-varnf ars))
  :hints (("Goal" :in-theory (enable ex-clause ex-anf ex-avar restp))))
(defthm ex-hclo-self (implies (ex-clo-shape g) (equal (ex-self (ex-hclo g)) g))
  :hints (("Goal" :in-theory (enable ex-hclo ex-self ex-clo-shape))))
(defthm ex-hclo-count (< (acl2-count g) (acl2-count (ex-hclo g))) :rule-classes nil
  :hints (("Goal" :in-theory (enable ex-hclo))))
(defthm ex-hclo-not-self (not (equal (ex-hclo g) g))
  :hints (("Goal" :in-theory (disable ex-hclo) :use ex-hclo-count)))
(defthm ex-hclo-not-self2 (not (equal g (ex-hclo g)))
  :hints (("Goal" :in-theory (disable ex-hclo) :use ex-hclo-count)))
(defthm ex-self-clo (equal (ex-self (list :clo a b)) (list :clo a b)) :hints (("Goal" :in-theory (enable ex-self))))
(defthm ex-mxcl-hclo (implies (ex-clo-shape g) (equal (ex-mxcl (ex-hclo g) args cls defs fuel) (ex-mxcl g args cls defs fuel)))
  :hints (("Goal" :in-theory (enable ex-hclo ex-clo-shape clop clo-caps))))
; apply's spread (vmx2's x2-* over seqk's sk-spread) opened only where asked
(in-theory (disable x2-spreads x2-hands x2-fn x2-vals x2-cls x2-sp sk-spread))
; the pieces: ex-mxcall when apply does not spread, when it does; ex-mxcall0
; of a closure that is its own self, of a hand-over; and apply's spread one
; in both (x2-sp is ex-apsp of a good closure, its def's variadic count
; the template's)
(defthm ex-xvs-cdr (implies (ex-xvs defs l) (ex-xvs defs (cdr l))) :hints (("Goal" :expand ((ex-xvs defs l)))))
(defthm ex-xvs-self (implies (and (ex-xvs defs (list g)) (ex-clo-shape g)) (equal (ex-self g) g))
  :hints (("Goal" :expand ((ex-xvs defs (list g))) :in-theory (enable ex-self ex-clo-shape clop clo))))
(defthm ex-mxcall-noapply
  (implies (not (equal f :apply))
           (equal (ex-mxcall f args defs fuel) (ex-mxcl f args (cdr (assoc-equal (clo-f f) defs)) defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-mxcall x2-fn x2-vals x2-cls x2-hands x2-spreads) (ex-mxcl x2-sp)))))
(defthm ex-mxcall-spread
  (implies (x2-spreads :applyv f args defs)
           (equal (ex-mxcall f args defs fuel)
                  (ex-mxcl (car args) (cadr (x2-sp args defs))
                           (if (equal (car (x2-sp args defs)) :hand)
                               (x2-hcls (cdr (assoc-equal (clo-f (car args)) defs)))
                             (cdr (assoc-equal (clo-f (car args)) defs)))
                           defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-mxcall x2-fn x2-vals x2-cls x2-hands) (ex-mxcl x2-sp x2-spreads x2-hcls)))))
(defthm ex-mxcall0-self
  (implies (equal (ex-self f) f)
           (equal (ex-mxcall0 f args defs fuel) (ex-mxcl f args (cdr (assoc-equal (clo-f f) defs)) defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-mxcall0 ex-mxcls) (ex-mxcl ex-self)))))
(defthm ex-mxcall0-hclo
  (implies (ex-clo-shape g)
           (equal (ex-mxcall0 (ex-hclo g) args defs fuel)
                  (ex-mxcl g args (x2-hcls (cdr (assoc-equal (clo-f g) defs))) defs fuel)))
  :hints (("Goal" :in-theory (e/d (ex-mxcall0 ex-mxcls) (ex-mxcl ex-self x2-hcls ex-hclo)))))
(defthm ex-x2-req-good
  (implies (and (ex-defs-ok defs defs) (ex-xvs defs (list g)) (clop g))
           (equal (x2-req (cdr (assoc-equal (clo-f g) defs))) (ex-varnf (nth 1 (cadr g)))))
  :hints (("Goal" :use ((:instance ex-defs-ok-assoc (ds defs) (tm (cadr g))))
                  :expand ((ex-xvs defs (list g)))
                  :in-theory (e/d (ex-def clo-f) (ex-defs-ok-assoc ex-defs-ok x2-req ex-varnf ex-clauses)))))
(defthm ex-apway-spreads
  (implies (and (equal (ex-apway tmp) 1) (ex-defs-ok defs defs) (ex-xvs defs (list (cadr tmp))))
           (and (equal (x2-sp (cdr tmp) defs) (ex-apsp tmp))
                (x2-spreads :applyv (car tmp) (cdr tmp) defs)
                (ex-clo-shape (cadr tmp))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance ex-x2-req-good (g (cadr tmp))))
                  :in-theory (e/d (x2-sp ex-apsp x2-spreads ex-apway ex-apentry ex-seqp ex-clo-shape clop)
                                  (sk-spread ex-x2-req-good ex-varnf x2-req ex-xvs no-mk)))))
(defthm ex-mxcall-callee
  (implies (and (ex-enters (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) (ex-defs-ok defs defs) (consp tmp) (ex-xvs defs tmp))
           (equal (ex-mxcall (car tmp) (cdr tmp) defs fuel)
                  (ex-mxcall0 (car (ex-callee tmp)) (cdr (ex-callee tmp)) defs fuel)))
  :hints (("Goal" :cases ((equal (ex-apway tmp) 1)) :do-not-induct t
                  :use ((:instance ex-xvs-nth1 (l tmp) (j 0)) (:instance ex-xvs-nth1 (l tmp) (j 1))
                        (:instance ex-xvs-self (g (car tmp))) (:instance ex-xvs-self (g (cadr tmp)))
                        (:instance ex-apway-spreads))
                  :in-theory (e/d (ex-enters ex-callable)
                                  (ex-mxcl ex-mxcall ex-mxcall0 ex-hclo ex-self sk-spread x2-sp x2-spreads ex-apsp ex-xvs ex-arity
                                   ex-wf no-mk ex-xvs-self ex-xvs-nth1 ex-apway-spreads ex-fbody)))
          ("Subgoal 1" :in-theory (e/d (ex-callee ex-enters ex-callable)
                                       (ex-mxcl ex-mxcall ex-mxcall0 ex-hclo ex-self sk-spread x2-sp x2-spreads ex-apsp ex-xvs ex-arity
                                        ex-wf no-mk ex-xvs-self ex-xvs-nth1 ex-apway-spreads ex-fbody)))))
(in-theory (disable ex-mxcall-noapply ex-mxcall-spread ex-mxcall0-self ex-mxcall0-hclo ex-apway-spreads ex-x2-req-good))
(defthm ex-mx-mkclo
  (equal (mx2 (cons :mkclo x) env caps defs fuel)
         (let ((rs (mx2-args (cdr x) env caps defs fuel))) (if (valp rs) (cons :val (clo (car x) (val rs))) rs)))
  :hints (("Goal" :expand ((mx2 (cons :mkclo x) env caps defs fuel)))))

; the body's lets
(defun ex-nths (j m l) (if (zp m) nil (cons (nth (nfix j) l) (ex-nths (1+ (nfix j)) (1- m) l))))
(defthm ex-capts-mx (equal (mx2-args (ex-capts j m) env caps defs fuel) (cons :val (ex-nths j m caps)))
  :hints (("Goal" :induct (ex-capts j m)
                  :expand ((:free (x y) (mx2-args (cons x y) env caps defs fuel))
                           (:free (x) (mx2 (cons :capt x) env caps defs fuel))))))
(defun ex-clets-ind (j m env caps)
  (if (zp m) env (ex-clets-ind (1+ (nfix j)) (1- m) (append env (list (nth (nfix j) caps))) caps)))
(defthm ex-clets-mx
  (implies (true-listp env)
           (equal (mx2 (ex-clets j m x) env caps defs fuel) (mx2 x (append env (ex-nths j m caps)) caps defs fuel)))
  :hints (("Goal" :induct (ex-clets-ind j m env caps)
                  :expand ((:free (y env) (mx2 (cons :let y) env caps defs fuel))
                           (:free (y) (mx2 (cons :capt y) env caps defs fuel))))))
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

; a call of f with args: the arity it picks, mx2's environment for that
; arity's body (the arguments -- a variadic one's rest a list -- the
; captures, the closure), and the values the parameters' copies take. f
; is a closure, or apply's hand-over of one (ex-hclo, its arities the hand
; arity): ex-ftm the template of the closure it stands for (ex-self) --
; the def mx2 runs, the closure its self slot holds
(defun ex-ftm (f) (cadr (ex-self f)))
(defun ex-car (f args) (ex-arity (nth 1 (cadr f)) (len args)))
(defun ex-fenv (f args) (append (ex-bargs (ex-car f args) args) (caddr f) (list (ex-self f))))
(defun ex-fvs (f args)
  (cdr (mx2-args (ex-locals (ex-fparams (ex-car f args)) (ex-fbcm (ex-ftm f) (ex-car f args))) (ex-fenv f args) nil nil 0)))

(defthm ex-len-inners-outers (equal (len (ex-outers capv)) (len (ex-inners capv))))
(defthm ex-subset-app (subsetp-equal a (append a b)))
(defthm ex-anp-natp (natp (ex-anp ar)) :rule-classes :type-prescription)
(defthm ex-anf-natp (natp (ex-anf ar)) :rule-classes :type-prescription)
(defthm ex-astart-natp (natp (ex-astart ar)) :rule-classes :type-prescription)
; THE HAND ARITY (ex-hars): the variadic one as a fixed one of one more
; parameter -- the same parameters, start and body: well formed with it,
; its clause's body the variadic one's, its clauses x2-hcls's
(defun ex-har (ar) (list* (1+ (nfix (nth 0 ar))) nil (cddr ar)))
(defun ex-hars2 (ars)
  (cond ((atom ars) nil) ((truthy (nth 1 (car ars))) (list (ex-har (car ars)))) (t (ex-hars2 (cdr ars)))))
(defthm ex-hars-is (equal (ex-hars ars) (ex-hars2 ars)) :hints (("Goal" :in-theory (enable ex-hars))))
(defthm ex-har-parts
  (implies (truthy (nth 1 ar))
           (and (equal (ex-anp (ex-har ar)) (ex-anp ar)) (equal (ex-astart (ex-har ar)) (ex-astart ar))
                (equal (ex-abody (ex-har ar)) (ex-abody ar)) (not (ex-avar (ex-har ar)))
                (equal (ex-anf (ex-har ar)) (+ 1 (ex-anf ar)))
                (natp (nth 0 (ex-har ar))) (equal (nth 2 (ex-har ar)) (nth 2 ar))))
  :hints (("Goal" :in-theory (enable ex-anp ex-anf ex-avar ex-astart ex-abody))))
(defthm ex-har-car (natp (car (ex-har ar))) :rule-classes :type-prescription)
(defthm ex-har-cddr (equal (cddr (ex-har ar)) (cddr ar)))
(in-theory (disable ex-anf ex-avar ex-anp ex-astart ex-abody ex-har))
(defthm ex-har-fbtr (implies (truthy (nth 1 ar)) (equal (ex-fbtr tm (ex-har ar)) (ex-fbtr tm ar)))
  :hints (("Goal" :in-theory (enable ex-fbtr ex-fparams ex-fbcm ex-flp ex-fcm ex-fcmb))))
(defthm ex-har-arwf (implies (and (truthy (nth 1 ar)) (ex-arwf tm ar defs)) (ex-arwf tm (ex-har ar) defs))
  :hints (("Goal" :in-theory (enable ex-arwf ex-fparams ex-fbcm ex-flp ex-fcm ex-fcmb))))
(defthm ex-hars-arswf (implies (ex-arswf tm ars defs) (ex-arswf tm (ex-hars2 ars) defs))
  :hints (("Goal" :induct (ex-hars2 ars))))
(defthm ex-hars-clauses (equal (x2-hcls (ex-clauses tm ars)) (ex-clauses tm (ex-hars2 ars)))
  :hints (("Goal" :induct (ex-hars2 ars) :in-theory (e/d (ex-clause x2-hcls restp ex-avar) (ex-fbtr)) :expand ((ex-clauses tm ars)))))
(defthm ex-hclo-parts
  (and (equal (cadr (ex-hclo g)) (update-nth 1 (ex-hars2 (nth 1 (cadr g))) (cadr g)))
       (equal (caddr (ex-hclo g)) (caddr g)) (clop (ex-hclo g)) (equal (clo-caps (ex-hclo g)) (caddr g))
       (ex-clo-shape (ex-hclo g)))
  :hints (("Goal" :in-theory (enable ex-hclo clop clo-caps ex-clo-shape))))
(in-theory (disable ex-hclo))

; what a call's entry needs of the callee f: a closure, or apply's
; hand-over of one, the closure a good value whose template's def is
; defs', f callable with the arguments' count
(defun ex-ehyp (f args defs)
  (and (ex-xvs defs (list (ex-self f))) (ex-clo-shape (ex-self f)) (or (equal (ex-self f) f) (equal f (ex-hclo (ex-self f))))
       (ex-defs-ok defs defs) (ex-callable f (len args)) (ex-xvs defs args) (true-listp args)))

(defmacro ex-efacts ()
  '(and (ex-tmwf (ex-ftm f) defs) (ex-arwf (ex-ftm f) (ex-car f args) defs) (ex-arswf (ex-ftm f) (nth 1 (cadr f)) defs)
        (ex-arity (nth 1 (cadr f)) (len args))
        (equal (len (ex-bargs (ex-car f args) args)) (ex-anp (ex-car f args)))
        (true-listp (ex-bargs (ex-car f args) args)) (ex-xvs defs (ex-bargs (ex-car f args) args))
        (equal (ex-self f) (clo (ex-ftm f) (caddr f)))
        (equal (ex-fbody f (len args)) (ex-abody (ex-car f args)))
        (equal (cdr (assoc-equal (ex-ftm f) defs)) (ex-def (ex-ftm f)))
        (equal (ex-mxcls f defs) (ex-clauses (ex-ftm f) (nth 1 (cadr f))))
        (equal (nth 2 (cadr f)) (nth 2 (ex-ftm f))) (equal (nth 3 (cadr f)) (nth 3 (ex-ftm f)))
        (equal (nth 4 (cadr f)) (nth 4 (ex-ftm f)))
        (clop f) (equal (clo-caps f) (caddr f))
        (true-listp (caddr f)) (equal (len (caddr f)) (len (ex-inners (nth 2 (ex-ftm f)))))
        (ex-xvs defs (caddr f)) (true-listp args)))
(defthm ex-ehyp-facts-plain
  (implies (and (ex-ehyp f args defs) (equal (ex-self f) f)) (ex-efacts))
  :rule-classes nil
  :hints (("Goal" :use ((:instance ex-defs-ok-assoc (ds defs) (tm (cadr f))))
                  :do-not-induct t
                  :in-theory (e/d (ex-tmwf ex-car ex-abody ex-fbody ex-callable ex-ftm ex-mxcls ex-def clo-f clop clo-caps
                                   ex-clo-shape)
                                  (ex-defs-ok-assoc ex-arwf ex-bargs ex-arity ex-anp)))))
(defthm ex-ehyp-facts-hclo
  (implies (and (ex-ehyp f args defs) (equal f (ex-hclo g)) (ex-clo-shape g)) (ex-efacts))
  :rule-classes nil
  :hints (("Goal" :use ((:instance ex-defs-ok-assoc (ds defs) (tm (cadr g))))
                  :do-not-induct t
                  :in-theory (e/d (ex-tmwf ex-car ex-abody ex-fbody ex-callable ex-ftm ex-mxcls ex-def clo-f clop clo-caps
                                   ex-clo-shape)
                                  (ex-defs-ok-assoc ex-arwf ex-bargs ex-arity ex-anp ex-self)))))
(defthm ex-ehyp-facts
  (implies (ex-ehyp f args defs) (ex-efacts))
  :rule-classes nil
  :hints (("Goal" :use (ex-ehyp-facts-plain (:instance ex-ehyp-facts-hclo (g (ex-self f))))
                  :in-theory (theory 'minimal-theory) :expand ((ex-ehyp f args defs)))))
; the callee's parts its template's (a hand-over's, the closure's it stands for)
(defthm ex-ehyp-nths
  (implies (ex-ehyp f args defs)
           (and (equal (nth 2 (cadr f)) (nth 2 (ex-ftm f))) (equal (nth 3 (cadr f)) (nth 3 (ex-ftm f)))
                (equal (nth 4 (cadr f)) (nth 4 (ex-ftm f)))))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (disable ex-ehyp ex-ftm))))
(in-theory (disable ex-ftm))

(defthm ex-fbcm-agree
  (implies (ex-ehyp f args defs)
           (ex-agree (ex-fbcm (ex-ftm f) (ex-car f args)) (ex-fenv f args) (ex-bind f args)))
  :hints (("Goal" :use ex-ehyp-facts
                  :in-theory (e/d (ex-tmwf ex-arwf ex-astart ex-fself ex-fparams ex-fbcm ex-bind ex-car ex-fenv)
                                  (ex-ehyp ex-bargs ex-arity ex-anp ex-slots ex-vwf)))))

(defthm ex-enter-fbody
  (implies (ex-ehyp f args defs) (equal (ex-fbody f (len args)) (ex-abody (ex-car f args))))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (disable ex-ehyp ex-fbody ex-abody ex-car))))
(defthm ex-enter-vwf
  (implies (ex-ehyp f args defs)
           (ex-vwf :m (ex-abody (ex-car f args)) 0
                   (append (ex-fcm (ex-ftm f) (ex-car f args)) (cons nil (ex-slots (ex-astart (ex-car f args)) (ex-anp (ex-car f args)))))
                   (cons (ex-astart (ex-car f args)) (ex-anp (ex-car f args))) defs))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (e/d (ex-arwf) (ex-ehyp ex-car ex-fcm ex-astart ex-anp ex-abody)))))
(defthm ex-enter-agree-cm
  (implies (ex-ehyp f args defs) (ex-agree (ex-fcm (ex-ftm f) (ex-car f args)) (ex-fenv f args) (ex-bind f args)))
  :hints (("Goal" :in-theory (e/d (ex-fcm) (ex-ehyp ex-fenv ex-bind ex-fbcm ex-car)))))
(defthm ex-enter-agree-params
  (implies (ex-ehyp f args defs)
           (ex-agree (ex-slots (ex-astart (ex-car f args)) (ex-anp (ex-car f args))) (ex-fvs f args) (ex-bind f args)))
  :hints (("Goal" :in-theory (e/d (ex-fvs ex-fparams) (ex-ehyp ex-fenv ex-bind ex-locals-indep ex-car))
                  :use (ex-fbcm-agree
                        (:instance ex-locals-mx (ls (ex-fparams (ex-car f args))) (cm (ex-fbcm (ex-ftm f) (ex-car f args)))
                                   (env (ex-fenv f args)) (fr (ex-bind f args)) (caps nil) (defs nil) (fuel 0)))
                  :expand ((ex-fbcm (ex-ftm f) (ex-car f args))))))
(defthm ex-enter-len
  (implies (ex-ehyp f args defs) (equal (len (ex-fenv f args)) (len (ex-fcm (ex-ftm f) (ex-car f args)))))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (e/d (ex-fcm ex-fbcm ex-fparams ex-fenv) (ex-ehyp ex-car ex-bargs)))))
(defthm ex-enter-xvs-env
  (implies (ex-ehyp f args defs) (ex-xvs defs (ex-fenv f args)))
  :hints (("Goal" :use ex-ehyp-facts :in-theory (e/d (ex-fenv ex-ehyp) (ex-tmwf ex-defs-ok ex-callable ex-car ex-bargs)))))
(defthm ex-enter-xvs-vs
  (implies (ex-ehyp f args defs) (ex-xvs defs (ex-fvs f args)))
  :hints (("Goal" :in-theory (e/d (ex-fvs) (ex-ehyp ex-fenv ex-locals-indep ex-car)))))
(defthm ex-enter-nomem (ex-nomem (cons nil (ex-slots (ex-astart ar) (ex-anp ar))) (ex-fcm tm ar))
  :hints (("Goal" :in-theory (e/d (ex-fcm) (ex-fbcm ex-anp ex-astart ex-blank)))))
(defthm ex-car-assoc (implies (consp (assoc-equal x l)) (equal (car (assoc-equal x l)) x)))
(defthm ex-assoc-def
  (implies (and (ex-defs-ok defs defs) (consp (assoc-equal tm defs)))
           (equal (assoc-equal tm defs) (cons tm (ex-def tm))))
  :hints (("Goal" :use ((:instance ex-defs-ok-assoc (ds defs)))
                  :in-theory (disable ex-defs-ok-assoc ex-def ex-defs-ok))))
(defthm ex-enter-mx1
  (implies (and (ex-ehyp f args defs) (not (zp fuel)))
           (equal (ex-mxcall0 f args defs fuel)
                  (mx2 (ex-fbtr (ex-ftm f) (ex-car f args)) (ex-bargs (ex-car f args) args) (caddr f) defs (+ -1 fuel))))
  :hints (("Goal" :use (ex-ehyp-facts
                        (:instance ex-pick-arity (tm (ex-ftm f)) (ars (nth 1 (cadr f))) (m (len args))))
                  :in-theory (e/d (ex-mxcall0 ex-mxcl ex-car ex-clause ex-bargs ex-anf ex-avar)
                                  (ex-fbtr ex-arwf ex-defs-ok ex-arity ex-pick-arity ex-ehyp ex-arswf ex-rest-args ex-mxcls ex-self
                                   ex-clauses ex-tmwf)))))
(defthm ex-fbtr-mx
  (implies (and (true-listp args) (true-listp caps) (equal (len caps) (len (ex-inners (nth 2 tm)))))
           (equal (mx2 (ex-fbtr tm ar) args caps defs fuel)
                  (mx2-loop (list :loop nil (ex-tr :m (ex-abody ar) 0 (ex-fcmb tm ar)))
                            (append args caps (list (clo tm caps)))
                            (cons nil (cdr (mx2-args (ex-locals (ex-fparams ar) (ex-fbcm tm ar))
                                                     (append args caps (list (clo tm caps))) nil nil 0)))
                            caps defs fuel)))
  :hints (("Goal" :use ((:instance ex-mx-loop-body
                                   (e (list :loop (cons '(:const nil) (ex-locals (ex-fparams ar) (ex-fbcm tm ar)))
                                            (ex-tr :m (ex-abody ar) 0 (ex-fcmb tm ar))))
                                   (base (append args caps (list (clo tm caps))))
                                   (vs (cons nil (cdr (mx2-args (ex-locals (ex-fparams ar) (ex-fbcm tm ar))
                                                                (append args caps (list (clo tm caps))) nil nil 0))))))
                  :in-theory (e/d (ex-fbtr) (ex-mx-loop-body ex-fbcm ex-fparams ex-fcm ex-fcmb ex-abody clo))
                  :expand ((:free (y env) (mx2 (cons :let y) env caps defs fuel))
                           (:free (y env) (mx2 (cons :loop y) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2 '(:const nil) env caps defs fuel))))))
(defthm ex-enter-mx
  (implies (and (ex-ehyp f args defs) (not (zp fuel)))
           (equal (ex-mxcall0 f args defs fuel)
                  (mx2-loop (list :loop nil (ex-tr :m (ex-abody (ex-car f args)) 0
                                                   (append (ex-fcm (ex-ftm f) (ex-car f args))
                                                           (cons nil (ex-slots (ex-astart (ex-car f args)) (ex-anp (ex-car f args)))))))
                            (ex-fenv f args) (cons nil (ex-fvs f args)) (caddr f) defs (+ -1 fuel))))
  :hints (("Goal" :use ex-ehyp-facts
                  :in-theory (e/d (ex-fvs ex-fenv ex-fcmb) (ex-ehyp ex-fbtr ex-fbcm ex-fparams ex-fcm ex-abody ex-car ex-bargs
                                                            ex-mxcall0)))))

; the callee a good call record's apply makes, as an entered call's
(defthm ex-apsp-good
  (implies (and (equal (ex-apway tmp) 1) (ex-xvs defs tmp) (ex-lzok defs))
           (and (ex-xvs defs (cadr (ex-apsp tmp))) (true-listp (cadr (ex-apsp tmp)))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance ex-sk-spread-good (req (ex-varnf (nth 1 (cadr (cadr tmp))))) (fx (butlast (cddr tmp) 1))
                                   (v (car (last (cdr tmp)))))
                        (:instance ex-xvs-noclo (v (car (last (cdr tmp)))))
                        (:instance ex-xvs-last (l (cdr tmp)))
                        (:instance ex-xvs-cdr (l tmp)) (:instance ex-xvs-cdr (l (cdr tmp)))
                        (:instance ex-xvs-butlast (l (cddr tmp)) (n 1)))
                  :in-theory (e/d (ex-apway ex-apentry ex-seqp ex-apsp sk-spread-true-listp)
                                  (ex-lzok ex-xvs sk-spread ex-sk-spread-good ex-xvs-noclo ex-xvs-last ex-xvs-cdr ex-xvs-butlast
                                   last butlast ex-varnf no-mk)))))
(in-theory (disable ex-apsp-good))
(defthm ex-callee-ehyp
  (implies (and (ex-enters (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) (consp tmp) (true-listp tmp) (ex-xvs defs tmp)
                (ex-lzok defs) (ex-defs-ok defs defs))
           (ex-ehyp (car (ex-callee tmp)) (cdr (ex-callee tmp)) defs))
  :hints (("Goal" :cases ((equal (ex-apway tmp) 1)) :do-not-induct t
                  :use ((:instance ex-xvs-nth1 (l tmp) (j 0)) (:instance ex-xvs-nth1 (l tmp) (j 1))
                        (:instance ex-xvs-self (g (car tmp))) (:instance ex-xvs-self (g (cadr tmp)))
                        (:instance ex-xvs-cdr (l tmp))
                        (:instance ex-apway-spreads) (:instance ex-apsp-good))
                  :in-theory (e/d (ex-enters ex-callable)
                                  (ex-xvs ex-xvs-self ex-xvs-nth1 ex-xvs-cdr ex-wf no-mk ex-arity ex-apway-spreads ex-apsp-good
                                   ex-apsp ex-hclo ex-self ex-lzok ex-fbody x2-sp ex-defs-ok)))
          ("Subgoal 1" :in-theory (e/d (ex-callee ex-enters ex-callable)
                                       (ex-xvs ex-xvs-self ex-xvs-nth1 ex-xvs-cdr ex-wf no-mk ex-arity ex-apway-spreads ex-apsp-good
                                        ex-apsp ex-hclo ex-self ex-lzok ex-fbody x2-sp ex-defs-ok)))))

; the same, of a call's record: its callee (car tmp), its arguments (cdr tmp)
; (ex-defs-ok first: it binds defs, which the rules' left sides do not name,
; so ex-ehyp of apply's callee is rewritten by ex-callee-ehyp, not looked up)
(defmacro ex-chyp () '(and (ex-defs-ok defs defs) (ex-ehyp (car tmp) (cdr tmp) defs)))
(defmacro ex-cr () '(ex-car (car tmp) (cdr tmp)))
(defthm ex-call-fbody
  (implies (ex-chyp) (equal (ex-fbody (car tmp) (len (cdr tmp))) (ex-abody (ex-cr))))
  :hints (("Goal" :by (:instance ex-enter-fbody (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-vwf
  (implies (ex-chyp)
           (ex-vwf :m (ex-abody (ex-cr)) 0 (append (ex-fcm (ex-ftm (car tmp)) (ex-cr)) (cons nil (ex-slots (ex-astart (ex-cr)) (ex-anp (ex-cr)))))
                   (cons (ex-astart (ex-cr)) (ex-anp (ex-cr))) defs))
  :hints (("Goal" :by (:instance ex-enter-vwf (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-agree-cm
  (implies (ex-chyp) (ex-agree (ex-fcm (ex-ftm (car tmp)) (ex-cr)) (ex-fenv (car tmp) (cdr tmp)) (ex-bind (car tmp) (cdr tmp))))
  :hints (("Goal" :by (:instance ex-enter-agree-cm (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-agree-params
  (implies (ex-chyp)
           (ex-agree (ex-slots (ex-astart (ex-cr)) (ex-anp (ex-cr))) (ex-fvs (car tmp) (cdr tmp)) (ex-bind (car tmp) (cdr tmp))))
  :hints (("Goal" :by (:instance ex-enter-agree-params (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-len
  (implies (ex-chyp) (equal (len (ex-fenv (car tmp) (cdr tmp))) (len (ex-fcm (ex-ftm (car tmp)) (ex-cr)))))
  :hints (("Goal" :by (:instance ex-enter-len (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-xvs-env
  (implies (ex-chyp) (ex-xvs defs (ex-fenv (car tmp) (cdr tmp))))
  :hints (("Goal" :by (:instance ex-enter-xvs-env (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-xvs-vs
  (implies (ex-chyp) (ex-xvs defs (ex-fvs (car tmp) (cdr tmp))))
  :hints (("Goal" :by (:instance ex-enter-xvs-vs (f (car tmp)) (args (cdr tmp))))))
(defthm ex-call-mx
  (implies (and (ex-chyp) (not (zp fuel)))
           (equal (ex-mxcall0 (car tmp) (cdr tmp) defs fuel)
                  (mx2-loop (list :loop nil (ex-tr :m (ex-abody (ex-cr)) 0
                                                   (append (ex-fcm (ex-ftm (car tmp)) (ex-cr))
                                                           (cons nil (ex-slots (ex-astart (ex-cr)) (ex-anp (ex-cr)))))))
                            (ex-fenv (car tmp) (cdr tmp)) (cons nil (ex-fvs (car tmp) (cdr tmp))) (caddr (car tmp)) defs (+ -1 fuel))))
  :hints (("Goal" :by (:instance ex-enter-mx (f (car tmp)) (args (cdr tmp))))))

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

(in-theory (disable ex-anf ex-avar ex-anp ex-astart ex-abody ex-fself ex-fbcm ex-fcm ex-fbtr ex-def ex-tmwf ex-arwf
                    ex-car ex-fenv ex-fvs ex-callable ex-enters ex-bind ex-mxcall ex-mxcall0 ex-ehyp ex-fbody ex-arerr ex-bargs ex-mxcl ex-mxcls))


; ---- A THROW (exec-PLAN 3b) -------------------------------------------------------------------
;
; The runtime's answers the agreement on a throw asks of it: its cast to
; IFn throws nothing (ex-ifnok: clj's cast either passes or is the tree's
; :not-fn), and a call of apply the tree refuses -- fewer than two
; arguments (ex-apway 2), a closure's with no seq (3) -- it refuses too,
; with the tree's :arity and :not-seq (ex-apok), as clj's apply throws.
(defun-sk ex-ifnok () (forall h (not (throwp (prim :ifn (list h))))))
(defun ex-aperr (tmp) (if (equal (ex-apway tmp) 2) :arity :not-seq))
(defun-sk ex-apok ()
  (forall tmp (implies (or (equal (ex-apway tmp) 2) (equal (ex-apway tmp) 3))
                       (equal (prim :invoke tmp) (cons :throw (ex-aperr tmp))))))
(in-theory (disable ex-ifnok ex-apok))

(defthm ex-nth-len-append (equal (nth (len a) (append a (list v))) v) :hints (("Goal" :induct (len a))))
; a call's translation, head first: the head, then the cast, then :applyv
(defthm ex-mx-trcall
  (implies (and (ex-ifnok) (equal p (len env)))
           (equal (mx2 (ex-trcall h args p) env caps defs fuel)
                  (let ((rh (mx2 h env caps defs fuel)))
                    (cond ((not (valp rh)) rh)
                          ((not (ex-ifn (val rh))) '(:thrown . :not-fn))
                          (t (let ((rs (mx2-args args (append env (list (val rh))) caps defs fuel)))
                               (if (valp rs) (ex-mxcall (val rh) (val rs) defs fuel) rs)))))))
  :hints (("Goal" :in-theory (e/d (ex-ifn ex-trcall) (ex-mxcall))
                  :use ((:instance ex-ifnok-necc (h (val (mx2 h env caps defs fuel)))))
                  :expand ((:free (x env) (mx2 (cons :let x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :if x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :prim x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :throw x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :const x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :local x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))))))
(in-theory (disable ex-trcall))

; a good list holds no recur marker (no good value ends in :recur-marker)
(defthm ex-xvs-no-mk (implies (ex-xvs defs l) (no-mk l))
  :hints (("Goal" :induct (ex-xvs defs l) :in-theory (enable clop) :expand ((ex-xvs defs l) (ex-xvs defs (car l))))))

; apply's refusals: fewer than two arguments, never spread
(defthm ex-apway-apply (implies (or (equal (ex-apway tmp) 2) (equal (ex-apway tmp) 3)) (equal (car tmp) :apply))
  :rule-classes :forward-chaining :hints (("Goal" :in-theory (enable ex-apway ex-apentry))))
(defthm ex-mxcall-ap2
  (implies (and (equal (ex-apway tmp) 2) (ex-apok))
           (equal (ex-mxcall (car tmp) (cdr tmp) defs fuel) '(:thrown . :arity)))
  :hints (("Goal" :use ((:instance ex-apok-necc))
                  :in-theory (e/d (ex-mxcall ex-mxcl x2-fn x2-vals x2-spreads ex-apway ex-apentry ex-aperr clop) (ex-apok-necc)))))
; a closure's and no seq: a good spread holds no marker, so its kind is not
; :ok or :hand, or its last value is a closure -- vmx2 does not spread
(defthm ex-ap3-nospread
  (implies (and (equal (ex-apway tmp) 3) (ex-defs-ok defs defs) (ex-lzok defs) (ex-xvs defs tmp))
           (not (x2-spreads :applyv (car tmp) (cdr tmp) defs)))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance ex-x2-req-good (g (cadr tmp)))
                        (:instance ex-sk-spread-good (req (ex-varnf (nth 1 (cadr (cadr tmp))))) (fx (butlast (cddr tmp) 1))
                                   (v (car (last (cdr tmp)))))
                        (:instance ex-xvs-no-mk (l (cadr (ex-apsp tmp))))
                        (:instance ex-xvs-noclo (v (car (last (cdr tmp)))))
                        (:instance ex-xvs-last (l (cdr tmp)))
                        (:instance ex-xvs-nth1 (l tmp) (j 1))
                        (:instance ex-xvs-cdr (l tmp)) (:instance ex-xvs-cdr (l (cdr tmp)))
                        (:instance ex-xvs-butlast (l (cddr tmp)) (n 1)))
                  :in-theory (e/d (x2-sp ex-apsp x2-spreads ex-apway ex-apentry ex-seqp ex-clo-shape clop)
                                  (ex-lzok ex-xvs sk-spread ex-sk-spread-good ex-xvs-noclo ex-xvs-last ex-xvs-cdr ex-xvs-butlast
                                   ex-x2-req-good ex-xvs-no-mk ex-xvs-nth1 last butlast ex-varnf x2-req no-mk)))))
(defthm ex-mxcall-ap3
  (implies (and (equal (ex-apway tmp) 3) (ex-apok) (ex-defs-ok defs defs) (ex-lzok defs) (ex-xvs defs tmp) (consp tmp))
           (equal (ex-mxcall (car tmp) (cdr tmp) defs fuel) '(:thrown . :not-seq)))
  :hints (("Goal" :use ((:instance ex-apok-necc) (:instance ex-ap3-nospread) (:instance ex-apway-apply))
                  :in-theory (e/d (ex-mxcall ex-mxcl x2-fn x2-vals ex-aperr clop)
                                  (ex-apok-necc ex-ap3-nospread ex-apway-apply x2-spreads ex-apway ex-defs-ok ex-lzok ex-xvs)))))
; the arity error: a closure with no arity of the count, in the VM no
; clause of it either -- its own, or a hand-over's variadic one as fixed
(defthm ex-mxcl-noarity
  (implies (and (ex-arswf tm ars defs) (not (consp (ex-arity ars (len args)))) (clop f))
           (equal (ex-mxcl f args (ex-clauses tm ars) defs fuel) '(:thrown . :arity)))
  :hints (("Goal" :use ((:instance ex-arswf-arity (n (len args))) (:instance ex-arwf-nat (ar (ex-arity ars (len args)))))
                  :in-theory (e/d (ex-mxcl) (ex-clauses ex-arswf ex-arity ex-arswf-arity ex-arwf-nat ex-arwf)))))
(defthm ex-mxcall-arerr
  (implies (and (ex-arerr (car (ex-callee tmp)) (len (cdr (ex-callee tmp)))) (ex-defs-ok defs defs) (ex-lzok defs)
                (consp tmp) (ex-xvs defs tmp))
           (equal (ex-mxcall (car tmp) (cdr tmp) defs fuel) '(:thrown . :arity)))
  :hints (("Goal" :cases ((equal (ex-apway tmp) 1)) :do-not-induct t
                  :use ((:instance ex-xvs-nth1 (l tmp) (j 0)) (:instance ex-xvs-nth1 (l tmp) (j 1))
                        (:instance ex-defs-ok-assoc (ds defs) (tm (cadr (car tmp))))
                        (:instance ex-defs-ok-assoc (ds defs) (tm (cadr (cadr tmp))))
                        (:instance ex-apway-spreads))
                  :expand ((ex-xvs defs (list (car tmp))) (ex-xvs defs (list (cadr tmp))))
                  :in-theory (e/d (ex-callee ex-arerr ex-def ex-tmwf clo-f ex-mxcall-noapply ex-mxcall-spread ex-clo-shape clop)
                                  (ex-mxcl ex-mxcall ex-hclo ex-self sk-spread x2-sp x2-spreads ex-apsp ex-arity
                                   ex-xvs-nth1 ex-apway-spreads ex-defs-ok-assoc ex-defs-ok ex-arswf ex-clauses ex-lzok)))))

(defun ex-vhyp (flg e i tmp cm env fr lp defs)
  (and (ex-defs-ok defs defs) (ex-lzok defs) (ex-ifnok) (ex-apok)
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
      (:iter (implies (or (valp res) (thrownp res))
                      (and (equal (mx2-loop (list :loop nil (ex-tr :m e 0 (append cm ls))) env tmp caps defs fuel) res)
                           (ex-agree cm env fr2) (ex-xvs defs (list (val res))))))
      (:rec (let ((m (mx2-args (ex-tr :rec e i cm) env caps defs fuel)))
              (and (implies (equal (car res) :recur)
                            (and (valp m) (ex-agree (cdr ls) (append tmp (val m)) fr2)
                                 (ex-agree (ex-blank ls cm) env fr2) (ex-xvs defs (append tmp (val m)))))
                   (implies (thrownp res)
                            (and (equal m res) (ex-agree cm env fr2) (ex-xvs defs (list (val res))))))))
      (:call (let ((m (mx2-args (ex-tr :call e i cm) env caps defs fuel)))
               (and (implies (valp res)
                             (and (valp m) (equal (ex-mxcall (car tmp) (append (cdr tmp) (val m)) defs fuel) res)
                                  (ex-agree cm env fr2) (ex-xvs defs (list (val res)))))
                    (implies (thrownp res)
                             (and (equal (if (valp m) (ex-mxcall (car tmp) (append (cdr tmp) (val m)) defs fuel) m) res)
                                  (ex-agree cm env fr2) (ex-xvs defs (list (val res))))))))
      (otherwise
       (let ((m (mx2 (ex-tr flg e i cm) env caps defs fuel)))
         (and (implies (or (valp res) (thrownp res))
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
                      (m (mx2 (ex-tr :m e 0 bcm) benv caps defs fuel)))
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
                            (vs (val (mx2-args (ex-locals (cdr ls) cm) env caps defs fuel))))
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
                     (t (let* ((f (car (ex-callee tmp))) (args (cdr (ex-callee tmp))) (ar (ex-car f args)))
                          (ex-vind :iter (ex-fbody f (len args)) 0 (cons nil (ex-fvs f args)) (ex-fcm (ex-ftm f) ar)
                                   (ex-fenv f args) (ex-bind f args) (1- fuel) (caddr f) defs
                                   (cons (ex-astart ar) (ex-anp ar)))))))
        (:fin nil)
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
                        (ex-vind :call e 1 (list (val (car r))) (append cm (list nil)) (append env (list (val (car r))))
                                 (cadr r) fuel caps defs lp))))
               (t nil)))))))

(defthm ex-vm-agree-flag
  (ex-vgood flg e i tmp cm env fr fuel caps defs lp)
  :rule-classes nil :otf-flg t
  :hints (("Goal" :induct (ex-vind flg e i tmp cm env fr fuel caps defs lp)
                  :in-theory (disable ex-kid-of ex-xvs)
                  :expand ((:free (flg cm) (ex-tr flg e i cm)) (:free (flg cm lp) (ex-vwf flg e i cm lp defs))
                           (:free (flg fr tmp) (ex-ev flg e i tmp fr fuel))
                           (:free (x env) (mx2 (cons :if x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :let x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :const x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :local x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :loop x) env caps defs fuel))
                           (:free (x env) (mx2 (cons :recur x) env caps defs fuel))
                           (:free (x y env) (mx2-args (cons x y) env caps defs fuel))
                           (:free (env) (mx2-args nil env caps defs fuel))
                           (:free (x base vs) (mx2-loop (list :loop nil x) base vs caps defs fuel))))))

; A WELL-FORMED TREE ANSWERS WHAT THE VM'S MEANING DOES, its defs the
; templates' and its scope's values good
(defthm ex-vm-agree
  (implies (and (ex-vwf :m e 0 cm nil defs) (ex-defs-ok defs defs) (ex-lzok defs) (ex-ifnok) (ex-apok) (ex-agree cm env fr)
                (ex-xvs defs env) (or (valp (car (ex-ev :m e 0 nil fr fuel))) (thrownp (car (ex-ev :m e 0 nil fr fuel)))))
           (equal (mx2 (ex-tr :m e 0 cm) env caps defs fuel) (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :use ((:instance ex-vm-agree-flag (flg :m) (i 0) (tmp nil) (lp nil))))))

; ... and outside every loop's tail it never answers a recur: a recur's
; values become its loop's slots, never a value
(defthm ex-recur-stays
  (implies (and (ex-vwf :m e 0 cm nil defs) (ex-defs-ok defs defs) (ex-lzok defs) (ex-ifnok) (ex-apok) (ex-agree cm env fr)
                (ex-xvs defs env))
           (not (equal (car (car (ex-ev :m e 0 nil fr fuel))) :recur)))
  :hints (("Goal" :use ((:instance ex-vm-agree-flag (flg :m) (i 0) (tmp nil) (lp nil))))))

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
