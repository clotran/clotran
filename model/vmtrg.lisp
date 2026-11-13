; THE VM'S TRANSLATION, GENERATED (src/f/gen/vm_tr_gen.inc,
; scripts/acl2-fortran -b vmtrg): exec-vmtr's ex-tr at the level the
; Fortran is generated from, guard-verified, for the kinds whose encoding
; vm.inc and ex-tr share -- a constant, a local, if, do, let* and throw --
; every other kind the host's (vtg-other: vm.inc's hand-written vm_tr,
; which calls back here for these kinds). exec-PLAN's Lane 3 says what
; is left.
;
; THE OUTPUT is built on a stack, as anbuild builds nodes, so the
; generated code never holds an expression in a variable: a node's
; translation leaves one expression on top, and vtg-node makes (op items..)
; of the top n. THE SCOPE is ex-tr's cm, the slots in scope by position,
; kept by the host: vtg-bind appends a slot, vtg-dead a dead position (a
; do's value no one reads), vtg-blank blanks what a node
; may clear (ex-clr), vtg-save / vtg-restore keep and give back the whole
; scope, vtg-local reads a slot's position. In clotran the stack is the
; context's value stack and the scope vm.inc's vm_tr_ctx (its map from
; slot to local, its depth); the shims are vm.inc's vtg_*, each stated
; here. vtg-local reads a fn's capture in place, (:capt j), as the
; clause's body does (exec-vmtr's ex-fbtc, exec-vmcs's ex-cs; the scope's
; vtb-cs the clause's parameter and capture counts). Two shims are named,
; not exact: vtg_blank blanks nothing and vtg_restore undoes only binds --
; a blanked slot is read by no tree ex-vwf admits (exec-vm's ex-vm-agree
; asks it), so the positions it would read agree.
;
; Proved: vtg-tr-ex-tr -- on a tree of these kinds (vtg-frag) the
; generated translation pushes exactly ex-tr's, its captures read in place
; (ex-cs), leaving the scope as it found it.
; vtg-steps-bound -- its work at most 9 steps a node it reaches (vtg-size):
; each node's shims a constant number.

(in-package "ACL2")

(include-book "exec-vmtr")

(defconst *vtg40* 1099511627776)

; ---- THE TREE'S READS (vm.inc's vtg_kind .. vtg_c on the OBJ_AST) -----------------------------

(defun vtg-nth (n x)
  (declare (xargs :guard (natp n)))
  (if (atom x) nil (if (zp n) (car x) (vtg-nth (1- n) (cdr x)))))
(defthm vtg-nth-is-nth (equal (vtg-nth n x) (nth n x)))
(defun vtg-int (x) (declare (xargs :guard t)) (if (and (natp x) (< x *vtg40*)) x 0))
(defun vtg-kind (e) (declare (xargs :guard t)) (vtg-int (vtg-nth 0 e)))
(defun vtg-i2 (e) (declare (xargs :guard t)) (vtg-int (vtg-nth 1 e)))
(defun vtg-s2 (e) (declare (xargs :guard t)) (vtg-int (vtg-nth 4 e)))
(defun vtg-c (e) (declare (xargs :guard t)) (vtg-nth 3 e))
(defun vtg-nk (e) (declare (xargs :guard t)) (vtg-int (len (vtg-nth 2 e))))
(defun vtg-kid (e j) (declare (xargs :guard (natp j))) (vtg-nth j (vtg-nth 2 e)))

(defthm vtg-int-range (and (natp (vtg-int x)) (< (vtg-int x) *vtg40*))
  :rule-classes ((:type-prescription :corollary (natp (vtg-int x))) (:linear :corollary (< (vtg-int x) *vtg40*))))
(defthm vtg-nth-count (<= (acl2-count (vtg-nth n x)) (acl2-count x)) :rule-classes :linear)
(defthm vtg-nth-count-cons (implies (consp x) (< (acl2-count (vtg-nth n x)) (acl2-count x))) :rule-classes :linear)
(defthm vtg-kid-count (implies (consp e) (< (acl2-count (vtg-kid e j)) (acl2-count e))) :rule-classes (:linear :rewrite)
  :hints (("Goal" :in-theory (disable vtg-nth-is-nth) :expand ((vtg-nth 2 e) (vtg-nth 1 (cdr e))))))
(defthm vtg-kind-consp (implies (not (equal (vtg-kind e) 0)) (consp e)) :rule-classes :forward-chaining)
(defthm vtg-kid-count-k (implies (not (equal (vtg-kind e) 0)) (< (acl2-count (vtg-kid e j)) (acl2-count e)))
  :rule-classes :linear :hints (("Goal" :in-theory (disable vtg-kid-count) :use vtg-kid-count)))
(defthm vtg-i2-range (< (vtg-i2 e) *vtg40*) :rule-classes :linear)
(defthm vtg-nk-range (< (vtg-nk e) *vtg40*) :rule-classes :linear)
(in-theory (disable vtg-int vtg-kid vtg-kind vtg-i2 vtg-s2 vtg-nk vtg-c))

; ---- THE BUILDER AND THE SCOPE ----------------------------------------------------------------

(defstobj vtb (vtb-stk :type t :initially nil) (vtb-cm :type t :initially nil) (vtb-sv :type t :initially nil)
  (vtb-cs :type t :initially nil))

(defun vtg-push (v vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-stk (cons v (vtb-stk vtb)) vtb))
(defun vtg-popn (n l acc)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom l)) (mv acc l) (vtg-popn (- n 1) (cdr l) (cons (car l) acc))))
(defun vtg-op (op) (declare (xargs :guard t)) (case op (1 :if) (2 :let) (otherwise :throw)))

; (:const v), (:const nil) (vtg_const, vtg_nil)
(defun vtg-const (v vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push (list :const v) vtb))
(defun vtg-nil (vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push '(:const nil) vtb))
; a slot's read: its position in the scope, the fn's captures read in
; place -- cs is (np . m), the clause's np parameters and m captures, the
; captures' positions np .. np+m-1 of the scope -- as exec-vmcs's ex-cs
; reads them: (:capt j) for capture j, a position past them m lower
; (vtg_local: vm_slot_ref, its map the positions so lowered)
(defun vtg-local (s vtb)
  (declare (xargs :stobjs vtb :guard t))
  (let ((cs (vtb-cs vtb)))
    (vtg-push (ec-call (ex-cloc (ec-call (ex-pos s (vtb-cm vtb))) (if (consp cs) (car cs) 0) (if (consp cs) (cdr cs) 0))) vtb)))
; (op items..) of the top n, the deepest first (vtg_node)
(defun vtg-node (op n vtb)
  (declare (xargs :stobjs vtb :guard (and (signed-byte-p 64 op) (signed-byte-p 64 n))))
  (mv-let (items rest) (vtg-popn (nfix n) (vtb-stk vtb) nil)
    (update-vtb-stk (cons (cons (vtg-op op) items) rest) vtb)))
; slot s a new position (vtg_bind: the slot's local the depth, the depth one more)
(defun vtg-bind (s vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-cm (append (true-list-fix (vtb-cm vtb)) (list s)) vtb))
; a dead local: a new position no slot names (vtg_dead: the depth one more)
(defun vtg-dead (vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-cm (append (true-list-fix (vtb-cm vtb)) (list nil)) vtb))
; what x may clear blanked (vtg_blank: nothing, named above)
(defun vtg-blank (x vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-cm (ec-call (ex-blank (ec-call (ex-clr :m x 0)) (vtb-cm vtb))) vtb))
; the scope kept, and given back (vtg_save, vtg_restore: the depth and the binds since)
(defun vtg-save (vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-sv (cons (vtb-cm vtb) (vtb-sv vtb)) vtb))
(defun vtg-restore (vtb)
  (declare (xargs :stobjs vtb :guard t))
  (let* ((sv (vtb-sv vtb)) (vtb (update-vtb-cm (if (consp sv) (car sv) nil) vtb)))
    (update-vtb-sv (if (consp sv) (cdr sv) nil) vtb)))

; every other kind: vm.inc's own translation (vtg_other: vm_tr), pushing
; one expression and leaving the scope as it was
(encapsulate (((vtg-other * vtb) => vtb :formals (x vtb) :guard t))
  (local (defun vtg-other (x vtb) (declare (xargs :stobjs vtb :guard t) (ignore x)) (vtg-nil vtb))))

; ---- THE TRANSLATION --------------------------------------------------------------------------

; flg 0: node e; flg 1: a let*'s bindings from i, then its body; flg 2: a
; do's children from i
(defun vtg-m (flg e i)
  (make-ord 1 (1+ (acl2-count e))
            (cond ((equal flg 1) (nfix (- (vtg-i2 e) (nfix i)))) ((equal flg 2) (nfix (- (vtg-nk e) (nfix i)))) (t *vtg40*))))

(defun vtg-tr (flg e i vtb)
  (declare (xargs :stobjs vtb :guard (and (natp flg) (natp i) (< i *vtg40*)) :verify-guards nil
                  :measure (vtg-m flg e i) :well-founded-relation o<))
  (if (equal flg 1)
      (if (equal (vtg-kind e) 11)
          (let ((i (nfix i)))
            (if (< i (vtg-i2 e))
                (let* ((vtb (vtg-tr 0 (vtg-kid e i) 0 vtb))
                       (vtb (vtg-save vtb))
                       (vtb (vtg-blank (vtg-kid e i) vtb))
                       (vtb (vtg-bind (+ (vtg-s2 e) i) vtb))
                       (vtb (vtg-tr 1 e (+ 1 i) vtb))
                       (vtb (vtg-restore vtb)))
                  (vtg-node 2 2 vtb))
              (vtg-tr 0 (vtg-kid e (vtg-i2 e)) 0 vtb)))
        (vtg-other e vtb))
    (if (equal flg 2)
        (if (equal (vtg-kind e) 5)
            (let ((i (nfix i)) (nk (vtg-nk e)))
              (cond ((zp nk) (vtg-nil vtb))
                    ((< i (- nk 1))
                     (let* ((vtb (vtg-tr 0 (vtg-kid e i) 0 vtb))
                            (vtb (vtg-save vtb))
                            (vtb (vtg-blank (vtg-kid e i) vtb))
                            (vtb (vtg-dead vtb))
                            (vtb (vtg-tr 2 e (+ 1 i) vtb))
                            (vtb (vtg-restore vtb)))
                       (vtg-node 2 2 vtb)))
                    (t (vtg-tr 0 (vtg-kid e (- nk 1)) 0 vtb))))
          (vtg-other e vtb))
    (let ((k (vtg-kind e)))
      (cond ((equal k 1) (vtg-const (vtg-c e) vtb))
            ((equal k 2) (vtg-local (vtg-i2 e) vtb))
            ((equal k 4)
             (let* ((vtb (vtg-tr 0 (vtg-kid e 0) 0 vtb))
                    (vtb (vtg-save vtb))
                    (vtb (vtg-blank (vtg-kid e 0) vtb))
                    (vtb (vtg-tr 0 (vtg-kid e 1) 0 vtb))
                    (vtb (if (< 2 (vtg-nk e)) (vtg-tr 0 (vtg-kid e 2) 0 vtb) (vtg-nil vtb)))
                    (vtb (vtg-restore vtb)))
               (vtg-node 1 3 vtb)))
            ((equal k 17) (let ((vtb (vtg-tr 0 (vtg-kid e 0) 0 vtb))) (vtg-node 3 1 vtb)))
            ((equal k 11) (vtg-tr 1 e 0 vtb))
            ((equal k 5) (vtg-tr 2 e 0 vtb))
            (t (vtg-other e vtb)))))))

(verify-guards vtg-tr :hints (("Goal" :in-theory (disable vtg-blank vtg-bind vtg-dead vtg-save vtg-restore vtg-node vtg-local vtg-const vtg-nil))))

; ---- IT IS EX-TR ------------------------------------------------------------------------------

; a node the generated kinds make up, its numbers in the reads' range
(defun vtg-ok (e)
  (and (consp e) (natp (nth 0 e)) (< (nth 0 e) *vtg40*) (natp (nth 1 e)) (< (nth 1 e) *vtg40*)
       (natp (nth 4 e)) (< (nth 4 e) *vtg40*) (< (len (nth 2 e)) *vtg40*)))
(defun vtg-frag (flg e i)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o<))
  (cond ((not (vtg-ok e)) nil)
        ((equal flg 1)
         (and (equal (vtg-kind e) 11)
              (if (< (nfix i) (vtg-i2 e))
                  (and (vtg-frag 0 (vtg-kid e (nfix i)) 0) (vtg-frag 1 e (+ 1 (nfix i))))
                (vtg-frag 0 (vtg-kid e (vtg-i2 e)) 0))))
        ((equal flg 2)
         (and (equal (vtg-kind e) 5)
              (cond ((zp (vtg-nk e)) t)
                    ((< (nfix i) (- (vtg-nk e) 1)) (and (vtg-frag 0 (vtg-kid e (nfix i)) 0) (vtg-frag 2 e (+ 1 (nfix i)))))
                    (t (vtg-frag 0 (vtg-kid e (- (vtg-nk e) 1)) 0)))))
        (t (let ((k (vtg-kind e)))
             (cond ((member k '(1 2)) t)
                   ((equal k 4) (and (vtg-frag 0 (vtg-kid e 0) 0) (vtg-frag 0 (vtg-kid e 1) 0)
                                     (or (<= (vtg-nk e) 2) (vtg-frag 0 (vtg-kid e 2) 0))))
                   ((equal k 17) (vtg-frag 0 (vtg-kid e 0) 0))
                   ((equal k 11) (vtg-frag 1 e 0))
                   ((equal k 5) (vtg-frag 2 e 0))
                   (t nil))))))

(defthm vtg-reads-ex
  (implies (vtg-ok e)
           (and (equal (vtg-kind e) (ex-kind e)) (equal (vtg-i2 e) (ex-i2 e)) (equal (vtg-s2 e) (ex-s2 e))
                (equal (vtg-nk e) (ex-nk e)) (equal (vtg-c e) (ex-c e))))
  :hints (("Goal" :in-theory (enable vtg-int vtg-kind vtg-i2 vtg-s2 vtg-nk vtg-c ex-kind ex-i2 ex-s2 ex-nk ex-c ex-kids))))
(defthm vtg-kid-ex (equal (vtg-kid e j) (ex-kid-of e (nfix j))) :hints (("Goal" :in-theory (enable vtg-kid ex-kid-of ex-kids))))

(defthm true-list-fix-id (implies (true-listp x) (equal (true-list-fix x) x)))
(defthm true-listp-ex-blank (implies (true-listp cm) (true-listp (ex-blank ls cm))))

; ex-tr, one lemma a kind
(defthm ex-tr-gen-kinds
  (implies (consp e)
           (and (implies (equal (ex-kind e) 1) (equal (ex-tr :m e 0 cm) (list :const (ex-c e))))
                (implies (equal (ex-kind e) 2) (equal (ex-tr :m e 0 cm) (list :local (ex-pos (ex-i2 e) cm))))
                (implies (equal (ex-kind e) 4)
                         (equal (ex-tr :m e 0 cm)
                                (list :if (ex-tr :m (ex-kid-of e 0) 0 cm)
                                      (ex-tr :m (ex-kid-of e 1) 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm))
                                      (if (< 2 (ex-nk e)) (ex-tr :m (ex-kid-of e 2) 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm)) '(:const nil)))))
                (implies (equal (ex-kind e) 17) (equal (ex-tr :m e 0 cm) (list :throw (ex-tr :m (ex-kid-of e 0) 0 cm))))
                (implies (equal (ex-kind e) 11) (equal (ex-tr :m e 0 cm) (ex-tr :let e 0 cm)))
                (implies (and (equal (ex-kind e) 11) (natp i) (< i (ex-i2 e)))
                         (equal (ex-tr :let e i cm)
                                (list :let (ex-tr :m (ex-kid-of e i) 0 cm)
                                      (ex-tr :let e (1+ i) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (list (+ (ex-s2 e) i)))))))
                (implies (and (equal (ex-kind e) 11) (natp i) (<= (ex-i2 e) i))
                         (equal (ex-tr :let e i cm) (ex-tr :m (ex-kid-of e (ex-i2 e)) 0 cm)))
                (implies (equal (ex-kind e) 5) (equal (ex-tr :m e 0 cm) (ex-tr :do e 0 cm)))
                (implies (zp (ex-nk e)) (equal (ex-tr :do e i cm) '(:const nil)))
                (implies (and (natp i) (< i (- (ex-nk e) 1)))
                         (equal (ex-tr :do e i cm)
                                (list :let (ex-tr :m (ex-kid-of e i) 0 cm)
                                      (ex-tr :do e (1+ i) (append (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm) (list nil))))))
                (implies (and (natp i) (not (zp (ex-nk e))) (<= (- (ex-nk e) 1) i))
                         (equal (ex-tr :do e i cm) (ex-tr :m (ex-kid-of e (- (ex-nk e) 1)) 0 cm)))))
  :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank) :expand ((ex-tr :m e 0 cm) (ex-tr :let e i cm)))))

; THE STATE as its three fields, and each shim on it
(defun vtg-st (stk cm sv cs) (list stk cm sv cs))
(defun vtg-np (cs) (if (consp cs) (car cs) 0))
(defun vtg-nm (cs) (if (consp cs) (cdr cs) 0))
(defthm vtg-shims
  (and (equal (vtg-const v (vtg-st s c sv cs)) (vtg-st (cons (list :const v) s) c sv cs))
       (equal (vtg-nil (vtg-st s c sv cs)) (vtg-st (cons '(:const nil) s) c sv cs))
       (equal (vtg-local n (vtg-st s c sv cs)) (vtg-st (cons (ex-cs nil (list :local (ex-pos n c)) (vtg-np cs) (vtg-nm cs)) s) c sv cs))
       (equal (vtg-save (vtg-st s c sv cs)) (vtg-st s c (cons c sv) cs))
       (equal (vtg-restore (vtg-st s c (cons c0 sv) cs)) (vtg-st s c0 sv cs))
       (equal (vtg-blank x (vtg-st s c sv cs)) (vtg-st s (ex-blank (ex-clr :m x 0) c) sv cs))
       (equal (vtg-bind n (vtg-st s c sv cs)) (vtg-st s (append (true-list-fix c) (list n)) sv cs))
       (equal (vtg-dead (vtg-st s c sv cs)) (vtg-st s (append (true-list-fix c) (list nil)) sv cs))
       (equal (vtg-node 1 3 (vtg-st (list* z y x s) c sv cs)) (vtg-st (cons (list :if x y z) s) c sv cs))
       (equal (vtg-node 2 2 (vtg-st (list* y x s) c sv cs)) (vtg-st (cons (list :let x y) s) c sv cs))
       (equal (vtg-node 3 1 (vtg-st (list* x s) c sv cs)) (vtg-st (cons (list :throw x) s) c sv cs)))
  :hints (("Goal" :expand ((:free (n l acc) (vtg-popn n l acc))))))

(defthm ex-blank-nil-true (implies (true-listp c) (true-listp (append c (list n)))))
(defthm vtg-ok-consp (implies (vtg-ok e) (consp e)) :rule-classes :forward-chaining)
; the rewrite of the captures, through the nodes the generated kinds make
(defthm vtg-cs-nodes
  (and (equal (ex-cs nil (list :const v) np m) (list :const v))
       (equal (ex-cs nil (list :if x y z) np m) (list :if (ex-cs nil x np m) (ex-cs nil y np m) (ex-cs nil z np m)))
       (equal (ex-cs nil (list :let x y) np m) (list :let (ex-cs nil x np m) (ex-cs nil y np m)))
       (equal (ex-cs nil (list :throw x) np m) (list :throw (ex-cs nil x np m)))))
(in-theory (disable ex-cs vtg-np vtg-nm))
(in-theory (disable ex-tr vtg-st vtg-const vtg-nil vtg-local vtg-save vtg-restore vtg-blank vtg-bind vtg-dead vtg-node vtg-frag vtg-ok))

(defthm vtg-frag-facts
  (implies (vtg-frag flg e i)
           (and (vtg-ok e) (implies (equal flg 1) (equal (vtg-kind e) 11)) (implies (equal flg 2) (equal (vtg-kind e) 5))
                (implies (not (member flg '(1 2))) (member (vtg-kind e) (quote (1 2 4 5 11 17))))))
  :rule-classes :forward-chaining :hints (("Goal" :expand ((vtg-frag flg e i)))))

; ex-tr's translation x with the captures read in place
(defun vtg-cw (x cs) (ex-cs nil x (vtg-np cs) (vtg-nm cs)))
; the induction: vtg-tr's, each call on the state it is handed
(defun vtg-ind (flg e i s c sv cs)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o< :verify-guards nil :hints (("Goal" :in-theory (disable vtg-kid-ex)))))
  (declare (irrelevant s c sv cs))
  (if (equal flg 1)
      (if (equal (vtg-kind e) 11)
          (if (< (nfix i) (vtg-i2 e))
              (let ((k (vtg-kid e (nfix i))))
                (list (vtg-ind 0 k 0 s c sv cs)
                      (vtg-ind 1 e (+ 1 (nfix i)) (cons (vtg-cw (ex-tr :m k 0 c) cs) s)
                               (append (ex-blank (ex-clr :m k 0) c) (list (+ (vtg-s2 e) (nfix i)))) (cons c sv) cs)))
            (vtg-ind 0 (vtg-kid e (vtg-i2 e)) 0 s c sv cs))
        nil)
    (if (equal flg 2)
        (if (equal (vtg-kind e) 5)
            (cond ((zp (vtg-nk e)) nil)
                  ((< (nfix i) (- (vtg-nk e) 1))
                   (let ((k (vtg-kid e (nfix i))))
                     (list (vtg-ind 0 k 0 s c sv cs)
                           (vtg-ind 2 e (+ 1 (nfix i)) (cons (vtg-cw (ex-tr :m k 0 c) cs) s)
                                    (append (ex-blank (ex-clr :m k 0) c) (list nil)) (cons c sv) cs))))
                  (t (vtg-ind 0 (vtg-kid e (- (vtg-nk e) 1)) 0 s c sv cs)))
          nil)
    (let ((k (vtg-kind e)))
      (cond ((equal k 4)
             (let* ((k0 (vtg-kid e 0)) (c1 (ex-blank (ex-clr :m k0 0) c)) (t0 (vtg-cw (ex-tr :m k0 0 c) cs)))
               (list (vtg-ind 0 k0 0 s c sv cs)
                     (vtg-ind 0 (vtg-kid e 1) 0 (cons t0 s) c1 (cons c sv) cs)
                     (vtg-ind 0 (vtg-kid e 2) 0 (cons (vtg-cw (ex-tr :m (vtg-kid e 1) 0 c1) cs) (cons t0 s)) c1 (cons c sv) cs))))
            ((equal k 17) (vtg-ind 0 (vtg-kid e 0) 0 s c sv cs))
            ((equal k 11) (vtg-ind 1 e 0 s c sv cs))
            ((equal k 5) (vtg-ind 2 e 0 s c sv cs))
            (t nil))))))

; what vtg-tr pushes: ex-tr's at the place flg names, the captures read in place
(defun vtg-want (flg e i c cs)
  (vtg-cw (cond ((equal flg 1) (ex-tr :let e (nfix i) c)) ((equal flg 2) (ex-tr :do e (nfix i) c)) (t (ex-tr :m e 0 c))) cs))

(defthm vtg-tr-st
  (implies (and (vtg-frag flg e i) (true-listp c))
           (equal (vtg-tr flg e i (vtg-st s c sv cs))
                  (vtg-st (cons (vtg-want flg e i c cs) s) c sv cs)))
  :hints (("Goal" :induct (vtg-ind flg e i s c sv cs)
                  :in-theory (disable ex-kid-of ex-clr ex-blank)
                  :expand ((:free (flg) (vtg-frag flg e i)) (:free (flg) (vtg-tr flg e i (vtg-st s c sv cs)))))
          (and stable-under-simplificationp '(:in-theory (e/d (vtg-kid-ex vtg-ok) (ex-kid-of ex-clr ex-blank))))))

(defthm list4-id (implies (and (true-listp x) (equal (len x) 4)) (equal (list (car x) (cadr x) (caddr x) (cadddr x)) x))
  :hints (("Goal" :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x)) (len (cddddr x)) (true-listp x) (true-listp (cdr x))
                            (true-listp (cddr x)) (true-listp (cdddr x)) (true-listp (cddddr x))))))
(defthm vtb-as-st (implies (vtbp vtb) (equal (vtg-st (vtb-stk vtb) (vtb-cm vtb) (vtb-sv vtb) (vtb-cs vtb)) vtb))
  :hints (("Goal" :in-theory (e/d (vtg-st) (list4-id)) :use ((:instance list4-id (x vtb))))))
(defthm vtg-st-fields
  (and (equal (vtb-stk (vtg-st s c sv cs)) s) (equal (vtb-cm (vtg-st s c sv cs)) c) (equal (vtb-sv (vtg-st s c sv cs)) sv)
       (equal (vtb-cs (vtg-st s c sv cs)) cs))
  :hints (("Goal" :in-theory (enable vtg-st))))

; and so on the stobj: on a tree of the generated kinds the generated
; translation pushes exactly ex-tr's, the captures read in place (the
; fn's clause body's, exec-vmtr's ex-fbtc), the scope and the saves as
; they were
(defthm vtg-tr-ex-tr
  (implies (and (vtg-frag flg e i) (vtbp vtb) (true-listp (vtb-cm vtb)))
           (and (equal (vtb-stk (vtg-tr flg e i vtb))
                       (cons (vtg-want flg e i (vtb-cm vtb) (vtb-cs vtb)) (vtb-stk vtb)))
                (equal (vtb-cm (vtg-tr flg e i vtb)) (vtb-cm vtb))
                (equal (vtb-sv (vtg-tr flg e i vtb)) (vtb-sv vtb))
                (equal (vtb-cs (vtg-tr flg e i vtb)) (vtb-cs vtb))))
  :hints (("Goal" :use ((:instance vtg-tr-st (s (vtb-stk vtb)) (c (vtb-cm vtb)) (sv (vtb-sv vtb)) (cs (vtb-cs vtb))))
                  :in-theory (disable vtg-tr-st vtg-tr vtb-stk vtb-cm vtb-sv vtb-cs vtbp))))

; ---- THE COST ---------------------------------------------------------------------------------
;
; vtg-steps: vtg-tr's work as the generated code does it -- a step a call
; (a cycle among them) and a step a shim, vtg_other's own work its host's;
; vtg-size: the nodes it reaches, a let's bindings and body among them.
; vtg-steps-bound: at most 9 steps a node -- each node's shims a constant.
(defun vtg-steps (flg e i)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex)))))
  (if (equal flg 1)
      (if (equal (vtg-kind e) 11)
          (if (< (nfix i) (vtg-i2 e))
              (+ 6 (vtg-steps 0 (vtg-kid e (nfix i)) 0) (vtg-steps 1 e (+ 1 (nfix i))))
            (+ 1 (vtg-steps 0 (vtg-kid e (vtg-i2 e)) 0)))
        2)
    (if (equal flg 2)
        (if (equal (vtg-kind e) 5)
            (cond ((zp (vtg-nk e)) 2)
                  ((< (nfix i) (- (vtg-nk e) 1)) (+ 7 (vtg-steps 0 (vtg-kid e (nfix i)) 0) (vtg-steps 2 e (+ 1 (nfix i)))))
                  (t (+ 1 (vtg-steps 0 (vtg-kid e (- (vtg-nk e) 1)) 0))))
          2)
    (let ((k (vtg-kind e)))
      (cond ((equal k 4) (+ 5 (vtg-steps 0 (vtg-kid e 0) 0) (vtg-steps 0 (vtg-kid e 1) 0)
                            (if (< 2 (vtg-nk e)) (vtg-steps 0 (vtg-kid e 2) 0) 1)))
            ((equal k 17) (+ 2 (vtg-steps 0 (vtg-kid e 0) 0)))
            ((equal k 11) (+ 1 (vtg-steps 1 e 0)))
            ((equal k 5) (+ 1 (vtg-steps 2 e 0)))
            (t 2))))))
(defun vtg-size (flg e i)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex)))))
  (if (equal flg 1)
      (if (equal (vtg-kind e) 11)
          (if (< (nfix i) (vtg-i2 e))
              (+ (vtg-size 0 (vtg-kid e (nfix i)) 0) (vtg-size 1 e (+ 1 (nfix i))))
            (vtg-size 0 (vtg-kid e (vtg-i2 e)) 0))
        1)
    (if (equal flg 2)
        (if (equal (vtg-kind e) 5)
            (cond ((zp (vtg-nk e)) 1)
                  ((< (nfix i) (- (vtg-nk e) 1)) (+ (vtg-size 0 (vtg-kid e (nfix i)) 0) (vtg-size 2 e (+ 1 (nfix i)))))
                  (t (vtg-size 0 (vtg-kid e (- (vtg-nk e) 1)) 0)))
          1)
    (let ((k (vtg-kind e)))
      (cond ((equal k 4) (+ 1 (vtg-size 0 (vtg-kid e 0) 0) (vtg-size 0 (vtg-kid e 1) 0)
                            (if (< 2 (vtg-nk e)) (vtg-size 0 (vtg-kid e 2) 0) 0)))
            ((equal k 17) (+ 1 (vtg-size 0 (vtg-kid e 0) 0)))
            ((equal k 11) (+ 1 (vtg-size 1 e 0)))
            ((equal k 5) (+ 1 (vtg-size 2 e 0)))
            (t 1))))))
(defthm vtg-steps-bound-flag
  (<= (vtg-steps flg e i) (if (member flg '(1 2)) (+ 1 (* 9 (vtg-size flg e i))) (- (* 9 (vtg-size flg e i)) 7)))
  :rule-classes nil
  :hints (("Goal" :induct (vtg-steps flg e i) :in-theory (disable vtg-kid-ex)
                  :expand ((:free (flg) (vtg-steps flg e i)) (:free (flg) (vtg-size flg e i))))))
(defthm vtg-steps-bound (<= (vtg-steps 0 e 0) (* 9 (vtg-size 0 e 0)))
  :rule-classes :linear :hints (("Goal" :use ((:instance vtg-steps-bound-flag (flg 0) (i 0))))))
