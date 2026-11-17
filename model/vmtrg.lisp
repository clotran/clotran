; THE VM'S TRANSLATION, GENERATED (src/f/gen/vm_tr_gen.inc,
; scripts/acl2-fortran -b vmtrg): exec-vmtr's ex-tr at the level the
; Fortran is generated from, guard-verified, for the kinds whose encoding
; vm.inc and ex-tr share -- a constant, a local, a Var, if, do, let*, loop,
; recur and throw --
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
; A LOOP is ex-tr's two shapes: inits reading none of the loop's slots
; before them (vtg-lind, generated: ex-lind over ex-rd, vtg_rdcap reading
; a fn's captures) give (:loop (init ..) body); else the inits are lets and
; (:loop ((:local p) ..) body) rebinds the slots (vtg-binds: vtg_bind each).
; A recur is (:recur arg ..). vtg-node 0 makes the inits' list.
;
; Proved: vtg-tr-ex-tr -- on a tree of these kinds (vtg-frag) the
; generated translation pushes exactly ex-tr's, its captures read in place
; (ex-cs), leaving the scope as it found it; vtg-rd-ex, vtg-lind-ex -- the
; loop's test is ex-lind on a tree in the reads' range (vtg-okt).
; vtg-steps-bound -- its work at most 16 steps a node it reaches (vtg-size):
; each node's shims a constant number; vtg-lind-steps-bound -- the loop's
; test at most 6 steps a node it walks.
; vtg-tlr-ex-tlr -- vtg-tlr, vm_clause's loop test, is exec-vmtr's ex-tlr
; (a recur to the fn); vtg-tlr-steps-bound -- 5 steps a node it reaches.
;
; A VAR (exec-PLAN Lane 3 item 3, first slice). Encoding: ex-tr's kind 3 is
; vm.inc's, (:prim :clotran.vm/deref (:const v)), v the tree's (ex-c e);
; generated here by one shim, vtg_deref (vm_deref_of of vm_var_ref).
; Hypotheses, named not proved: exec-vm's ex-derefok -- the host's deref of
; v answers v (the namespace's root, a direct link's epoch re-read); vm.inc's
; constant is the Var or the linked node where the model's is the value; and
; ex-vwf asks a Var's v not shaped as prim's throw, (:throw . x) (exec-clrvm's
; ex-vwf0 the same). ex-vm-agree, ex-recur-stays, ex-vm-runs, ex-anp-runs gain
; (ex-derefok), otherwise unchanged. Cost: a Var 2 steps here as before
; (vtg-steps' default, one shim); mx2 one prim call more a Var read.

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
; whether a fn's or lazy seq's captures name a slot in lo .. hi-1 (vtg_rdcap:
; vm_reads_in's N_FN case on the template's capture pairs)
(defun vtg-rdcap (e lo hi) (declare (xargs :guard t)) (ec-call (ex-rdin (ec-call (ex-outers (vtg-nth 2 (vtg-c e)))) lo hi)))

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
(defthm vtg-s2-range (< (vtg-s2 e) *vtg40*) :rule-classes :linear)
(in-theory (disable vtg-int vtg-kid vtg-kind vtg-i2 vtg-s2 vtg-nk vtg-c))

; ---- THE BUILDER AND THE SCOPE ----------------------------------------------------------------

(defstobj vtb (vtb-stk :type t :initially nil) (vtb-cm :type t :initially nil) (vtb-sv :type t :initially nil)
  (vtb-cs :type t :initially nil))

(defun vtg-push (v vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-stk (cons v (vtb-stk vtb)) vtb))
(defun vtg-popn (n l acc)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom l)) (mv acc l) (vtg-popn (- n 1) (cdr l) (cons (car l) acc))))
(defun vtg-op (op) (declare (xargs :guard t)) (case op (1 :if) (2 :let) (4 :loop) (5 :recur) (otherwise :throw)))

; (:const v), (:const nil) (vtg_const, vtg_nil)
(defun vtg-const (v vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push (list :const v) vtb))
(defun vtg-nil (vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push '(:const nil) vtb))
; a Var: (:prim :clotran.vm/deref (:const v)), the host's deref (vtg_deref:
; vm_deref_of of vm_var_ref -- named: its constant is the Var, or the
; node itself when direct-linked (the link epoch), where the model's is the
; Var's value; exec-vm's ex-derefok says the deref answers that value)
(defun vtg-deref (e vtb) (declare (xargs :stobjs vtb :guard t)) (vtg-push (list :prim :clotran.vm/deref (list :const (vtg-c e))) vtb))
; a slot's read: its position in the scope, the fn's captures read in
; place -- cs is (np . m), the clause's np parameters and m captures, the
; captures' positions np .. np+m-1 of the scope -- as exec-vmcs's ex-cs
; reads them: (:capt j) for capture j, a position past them m lower
; (vtg_local: vm_slot_ref, its map the positions so lowered)
(defun vtg-local (s vtb)
  (declare (xargs :stobjs vtb :guard t))
  (let ((cs (vtb-cs vtb)))
    (vtg-push (ec-call (ex-cloc (ec-call (ex-pos s (vtb-cm vtb))) (if (consp cs) (car cs) 0) (if (consp cs) (cdr cs) 0))) vtb)))
; (op items..) of the top n, the deepest first, op 0 the items alone (vtg_node)
(defun vtg-node (op n vtb)
  (declare (xargs :stobjs vtb :guard (and (signed-byte-p 64 op) (signed-byte-p 64 n))))
  (mv-let (items rest) (vtg-popn (nfix n) (vtb-stk vtb) nil)
    (update-vtb-stk (cons (if (equal op 0) items (cons (vtg-op op) items)) rest) vtb)))
; slot s a new position (vtg_bind: the slot's local the depth, the depth one more)
(defun vtg-bind (s vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-cm (append (true-list-fix (vtb-cm vtb)) (list s)) vtb))
; a dead local: a new position no slot names (vtg_dead: the depth one more)
(defun vtg-dead (vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-cm (append (true-list-fix (vtb-cm vtb)) (list nil)) vtb))
; what x may clear blanked (vtg_blank: nothing, named above)
(defun vtg-blank (x vtb) (declare (xargs :stobjs vtb :guard t)) (update-vtb-cm (ec-call (ex-blank (ec-call (ex-clr :m x 0)) (vtb-cm vtb))) vtb))
; a loop's slots s .. s+n-1 new positions, their old ones blanked (vtg_binds:
; vtg_bind each, its map the slot's new local)
(defun vtg-binds (s n vtb)
  (declare (xargs :stobjs vtb :guard t))
  (let ((ls (ec-call (ex-slots s n)))) (update-vtb-cm (ec-call (binary-append (ec-call (ex-blank ls (true-list-fix (vtb-cm vtb)))) ls)) vtb)))
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

;; WHETHER A LOOP'S INITS ARE INDEPENDENT (exec-vmtr's ex-rd, ex-lind): vtg-rd
; flg 0 whether node e reads a slot in lo .. hi-1, flg 1 whether children i..
; of e do; vtg-lind whether init i.. reads none of the loop's slots before it
(defthm vtg-nk-consp (implies (< 0 (vtg-nk e)) (consp e)) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable vtg-nk vtg-int vtg-nth))))
(defthm vtg-kid-count-nk (implies (< (nfix i) (vtg-nk e)) (< (acl2-count (vtg-kid e i)) (acl2-count e)))
  :rule-classes :linear :hints (("Goal" :use vtg-nk-consp :in-theory (disable vtg-nk-consp))))
(defun vtg-rd (flg e i lo hi)
  (declare (xargs :guard (and (natp flg) (natp i) (< i *vtg40*) (natp lo) (natp hi)) :verify-guards nil
                  :measure (make-ord 1 (1+ (acl2-count e)) (if (equal flg 1) (nfix (- (vtg-nk e) (nfix i))) *vtg40*))
                  :well-founded-relation o<))
  (if (equal flg 1)
      (let ((i (nfix i)))
        (if (< i (vtg-nk e))
            (if (vtg-rd 0 (vtg-kid e i) 0 lo hi) t (vtg-rd 1 e (+ 1 i) lo hi))
          nil))
    (let ((k (vtg-kind e)))
      (cond ((or (equal k 1) (equal k 3)) nil)
            ((equal k 2) (and (<= lo (vtg-i2 e)) (< (vtg-i2 e) hi)))
            ((or (equal k 14) (equal k 15)) (vtg-rdcap e lo hi))
            ((or (equal k 4) (equal k 5) (equal k 17) (equal k 7) (equal k 8) (equal k 9) (equal k 22) (equal k 21)
                 (equal k 6) (equal k 11) (equal k 12) (equal k 16))
             (vtg-rd 1 e 0 lo hi))
            (t t)))))
(verify-guards vtg-rd)
(defun vtg-lind (e i)
  (declare (xargs :guard (and (natp i) (< i *vtg40*)) :measure (nfix (- (vtg-i2 e) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (vtg-i2 e))
        (if (vtg-rd 0 (vtg-kid e i) 0 (vtg-s2 e) (+ (vtg-s2 e) i)) nil (vtg-lind e (+ 1 i)))
      t)))
; the reads of slots s+j .. s+n-1, in order (a dependent loop's (:local p)s)
(defun vtg-locs (s j n vtb)
  (declare (xargs :stobjs vtb :guard (and (natp s) (natp j) (natp n) (< s *vtg40*) (< n *vtg40*))
                  :measure (nfix (- (nfix n) (nfix j)))))
  (let ((j (nfix j)))
    (if (< j (nfix n)) (let ((vtb (vtg-local (+ s j) vtb))) (vtg-locs s (+ 1 j) n vtb)) vtb)))

; flg 0: node e; flg 1: a let*'s or a dependent loop's bindings from i, then
; its body; flg 2: a do's children from i; flg 3: a loop's inits or a
; recur's args from i, each pushed; flg 5: an independent loop's body after
; its inits from i are blanked
(defun vtg-m (flg e i)
  (make-ord 1 (1+ (acl2-count e))
            (cond ((or (equal flg 1) (equal flg 5)) (nfix (- (vtg-i2 e) (nfix i))))
                  ((equal flg 2) (nfix (- (vtg-nk e) (nfix i))))
                  ((equal flg 3) (nfix (- (if (equal (vtg-kind e) 16) (vtg-nk e) (vtg-i2 e)) (nfix i))))
                  (t *vtg40*))))

(defun vtg-tr (flg e i vtb)
  (declare (xargs :stobjs vtb :guard (and (natp flg) (natp i) (< i *vtg40*)) :verify-guards nil
                  :measure (vtg-m flg e i) :well-founded-relation o<))
  (cond
   ((equal flg 1)
    (if (or (equal (vtg-kind e) 11) (equal (vtg-kind e) 12))
        (let ((i (nfix i)))
          (if (< i (vtg-i2 e))
              (let* ((vtb (vtg-tr 0 (vtg-kid e i) 0 vtb))
                     (vtb (vtg-save vtb))
                     (vtb (vtg-blank (vtg-kid e i) vtb))
                     (vtb (vtg-bind (+ (vtg-s2 e) i) vtb))
                     (vtb (vtg-tr 1 e (+ 1 i) vtb))
                     (vtb (vtg-restore vtb)))
                (vtg-node 2 2 vtb))
            (if (equal (vtg-kind e) 12)
                ; (:loop ((:local p) ..) body), the slots then the loop's
                (let* ((vtb (vtg-locs (vtg-s2 e) 0 (vtg-i2 e) vtb))
                       (vtb (vtg-node 0 (vtg-i2 e) vtb))
                       (vtb (vtg-save vtb))
                       (vtb (vtg-binds (vtg-s2 e) (vtg-i2 e) vtb))
                       (vtb (vtg-tr 0 (vtg-kid e (vtg-i2 e)) 0 vtb))
                       (vtb (vtg-restore vtb)))
                  (vtg-node 4 2 vtb))
              (vtg-tr 0 (vtg-kid e (vtg-i2 e)) 0 vtb))))
      (vtg-other e vtb)))
   ((equal flg 2)
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
      (vtg-other e vtb)))
   ((equal flg 3)
    (if (or (equal (vtg-kind e) 12) (equal (vtg-kind e) 16))
        (let ((i (nfix i)))
          (if (< i (if (equal (vtg-kind e) 16) (vtg-nk e) (vtg-i2 e)))
              (let* ((vtb (vtg-tr 0 (vtg-kid e i) 0 vtb))
                     (vtb (vtg-save vtb))
                     (vtb (vtg-blank (vtg-kid e i) vtb))
                     (vtb (vtg-tr 3 e (+ 1 i) vtb)))
                (vtg-restore vtb))
            vtb))
      (vtg-other e vtb)))
   ((equal flg 5)
    (if (equal (vtg-kind e) 12)
        (let ((i (nfix i)))
          (if (< i (vtg-i2 e))
              (let* ((vtb (vtg-save vtb))
                     (vtb (vtg-blank (vtg-kid e i) vtb))
                     (vtb (vtg-tr 5 e (+ 1 i) vtb)))
                (vtg-restore vtb))
            (let* ((vtb (vtg-save vtb))
                   (vtb (vtg-binds (vtg-s2 e) (vtg-i2 e) vtb))
                   (vtb (vtg-tr 0 (vtg-kid e (vtg-i2 e)) 0 vtb)))
              (vtg-restore vtb))))
      (vtg-other e vtb)))
   (t
    (let ((k (vtg-kind e)))
      (cond ((equal k 1) (vtg-const (vtg-c e) vtb))
            ((equal k 3) (vtg-deref e vtb))
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
            ; a loop whose inits read none before them: (:loop (init ..) body)
            ((equal k 12)
             (if (vtg-lind e 1)
                 (let* ((vtb (vtg-tr 3 e 0 vtb))
                        (vtb (vtg-node 0 (vtg-i2 e) vtb))
                        (vtb (vtg-tr 5 e 0 vtb)))
                   (vtg-node 4 2 vtb))
               (vtg-tr 1 e 0 vtb)))
            ((equal k 16) (let ((vtb (vtg-tr 3 e 0 vtb))) (vtg-node 5 (vtg-nk e) vtb)))
            (t (vtg-other e vtb)))))))

(verify-guards vtg-tr :hints (("Goal" :in-theory (disable vtg-blank vtg-bind vtg-binds vtg-locs vtg-dead vtg-save vtg-restore vtg-node vtg-local vtg-const vtg-deref vtg-nil))))

; whether the clause's body recurs to the fn -- exec-vmtr's ex-tlr, a recur
; in a tail place no loop is round: vm_clause's loop round the body only
; then (ex-fbtc). A let's bindings and a do's all but last are no tail.
(defun vtg-tlr (e)
  (declare (xargs :guard t :measure (acl2-count e)))
  (let ((k (vtg-kind e)) (nk (vtg-nk e)))
    (cond ((equal k 16) t)
          ((equal k 4) (if (vtg-tlr (vtg-kid e 1)) t (if (< 2 nk) (vtg-tlr (vtg-kid e 2)) nil)))
          ((equal k 5) (if (zp nk) nil (vtg-tlr (vtg-kid e (- nk 1)))))
          ((or (equal k 11) (equal k 13)) (vtg-tlr (vtg-kid e (vtg-i2 e))))
          (t nil))))

; ---- IT IS EX-TR ------------------------------------------------------------------------------

; a node the generated kinds make up, its numbers in the reads' range
(defun vtg-ok (e)
  (and (consp e) (natp (nth 0 e)) (< (nth 0 e) *vtg40*) (natp (nth 1 e)) (< (nth 1 e) *vtg40*)
       (natp (nth 4 e)) (< (nth 4 e) *vtg40*) (< (len (nth 2 e)) *vtg40*)))
; every node of x in the reads' range (flg t: a list of nodes): what vtg-rd reads
(defun vtg-okt (flg x)
  (declare (xargs :measure (acl2-count x)))
  (cond ((atom x) t)
        (flg (and (vtg-okt nil (car x)) (vtg-okt t (cdr x))))
        (t (and (vtg-ok x) (vtg-okt t (vtg-nth 2 x))))))
(defun vtg-frag (flg e i)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o<))
  (cond ((not (vtg-ok e)) nil)
        ((equal flg 1)
         (and (or (equal (vtg-kind e) 11) (and (equal (vtg-kind e) 12) (vtg-okt nil e) (not (vtg-lind e 1))))
              (if (< (nfix i) (vtg-i2 e))
                  (and (vtg-frag 0 (vtg-kid e (nfix i)) 0) (vtg-frag 1 e (+ 1 (nfix i))))
                (vtg-frag 0 (vtg-kid e (vtg-i2 e)) 0))))
        ((equal flg 2)
         (and (equal (vtg-kind e) 5)
              (cond ((zp (vtg-nk e)) t)
                    ((< (nfix i) (- (vtg-nk e) 1)) (and (vtg-frag 0 (vtg-kid e (nfix i)) 0) (vtg-frag 2 e (+ 1 (nfix i)))))
                    (t (vtg-frag 0 (vtg-kid e (- (vtg-nk e) 1)) 0)))))
        ((equal flg 3)
         (and (or (equal (vtg-kind e) 12) (equal (vtg-kind e) 16))
              (if (< (nfix i) (if (equal (vtg-kind e) 16) (vtg-nk e) (vtg-i2 e)))
                  (and (vtg-frag 0 (vtg-kid e (nfix i)) 0) (vtg-frag 3 e (+ 1 (nfix i))))
                t)))
        ((equal flg 5)
         (and (equal (vtg-kind e) 12) (vtg-okt nil e) (vtg-lind e 1)
              (if (< (nfix i) (vtg-i2 e)) (vtg-frag 5 e (+ 1 (nfix i))) (vtg-frag 0 (vtg-kid e (vtg-i2 e)) 0))))
        (t (let ((k (vtg-kind e)))
             (cond ((member k '(1 2 3)) t)
                   ((equal k 4) (and (vtg-frag 0 (vtg-kid e 0) 0) (vtg-frag 0 (vtg-kid e 1) 0)
                                     (or (<= (vtg-nk e) 2) (vtg-frag 0 (vtg-kid e 2) 0))))
                   ((equal k 17) (vtg-frag 0 (vtg-kid e 0) 0))
                   ((equal k 11) (vtg-frag 1 e 0))
                   ((equal k 5) (vtg-frag 2 e 0))
                   ((equal k 12) (and (vtg-okt nil e) (if (vtg-lind e 1) (and (vtg-frag 3 e 0) (vtg-frag 5 e 0)) (vtg-frag 1 e 0))))
                   ((equal k 16) (vtg-frag 3 e 0))
                   (t nil))))))

(defthm vtg-reads-ex
  (implies (vtg-ok e)
           (and (equal (vtg-kind e) (ex-kind e)) (equal (vtg-i2 e) (ex-i2 e)) (equal (vtg-s2 e) (ex-s2 e))
                (equal (vtg-nk e) (ex-nk e)) (equal (vtg-c e) (ex-c e))))
  :hints (("Goal" :in-theory (enable vtg-int vtg-kind vtg-i2 vtg-s2 vtg-nk vtg-c ex-kind ex-i2 ex-s2 ex-nk ex-c ex-kids))))
(defthm vtg-kid-ex (equal (vtg-kid e j) (ex-kid-of e (nfix j))) :hints (("Goal" :in-theory (enable vtg-kid ex-kid-of ex-kids))))

; vtg-rd is ex-rd, vtg-lind ex-lind, on a tree in the reads' range
(defthm vtg-okt-nth (implies (vtg-okt t l) (vtg-okt nil (nth j l))))
(defthm vtg-okt-kid (implies (vtg-okt nil e) (vtg-okt nil (ex-kid-of e j)))
  :hints (("Goal" :in-theory (enable ex-kid-of ex-kids) :expand ((vtg-okt nil e)))))
(defthm vtg-okt-ok (implies (and (vtg-okt nil e) (consp e)) (vtg-ok e)) :hints (("Goal" :expand ((vtg-okt nil e)))))
(defthm vtg-atom-reads (implies (not (consp e)) (and (equal (vtg-kind e) 0) (equal (vtg-i2 e) 0) (equal (vtg-nk e) 0)))
  :hints (("Goal" :in-theory (enable vtg-int vtg-kind vtg-i2 vtg-nk))))
(defthm vtg-okt-reads
  (implies (vtg-okt nil e)
           (and (equal (vtg-kind e) (if (consp e) (ex-kind e) 0)) (equal (vtg-i2 e) (ex-i2 e)) (equal (vtg-nk e) (ex-nk e))
                (equal (vtg-s2 e) (ex-s2 e))))
  :hints (("Goal" :cases ((consp e)) :in-theory (enable ex-i2 ex-nk ex-kids ex-s2 vtg-s2 vtg-int))))
(defthm vtg-rd-ex
  (implies (and (vtg-okt nil e) (natp lo) (natp hi) (or (not (equal flg 1)) (consp e)))
           (equal (vtg-rd flg e i lo hi) (ex-rd (equal flg 1) e i lo hi)))
  :hints (("Goal" :induct (vtg-rd flg e i lo hi) :in-theory (e/d (vtg-rdcap) (vtg-okt ex-kid-of vtg-ok))
                  :expand ((vtg-rd flg e i lo hi) (ex-rd nil e i lo hi) (ex-rd t e i lo hi)))))
(defthm vtg-lind-ex (implies (vtg-okt nil e) (equal (vtg-lind e i) (ex-lind e i)))
  :hints (("Goal" :induct (vtg-lind e i) :in-theory (disable vtg-okt ex-kid-of vtg-ok vtg-rd) :expand ((ex-lind e i) (vtg-lind e i)))))

(defthm true-list-fix-id (implies (true-listp x) (equal (true-list-fix x) x)))
(defthm true-listp-ex-blank (implies (true-listp cm) (true-listp (ex-blank ls cm))))

; ex-tr, one lemma a kind
(defthm ex-tr-gen-kinds
  (implies (consp e)
           (and (implies (equal (ex-kind e) 1) (equal (ex-tr :m e 0 cm) (list :const (ex-c e))))
                (implies (equal (ex-kind e) 3) (equal (ex-tr :m e 0 cm) (list :prim :clotran.vm/deref (list :const (ex-c e)))))
                (implies (equal (ex-kind e) 2) (equal (ex-tr :m e 0 cm) (list :local (ex-pos (ex-i2 e) cm))))
                (implies (equal (ex-kind e) 4)
                         (equal (ex-tr :m e 0 cm)
                                (list :if (ex-tr :m (ex-kid-of e 0) 0 cm)
                                      (ex-tr :m (ex-kid-of e 1) 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm))
                                      (if (< 2 (ex-nk e)) (ex-tr :m (ex-kid-of e 2) 0 (ex-blank (ex-clr :m (ex-kid-of e 0) 0) cm)) '(:const nil)))))
                (implies (equal (ex-kind e) 17) (equal (ex-tr :m e 0 cm) (list :throw (ex-tr :m (ex-kid-of e 0) 0 cm))))
                (implies (equal (ex-kind e) 11) (equal (ex-tr :m e 0 cm) (ex-tr :let e 0 cm)))
                (implies (and (or (equal (ex-kind e) 11) (and (equal (ex-kind e) 12) (not (ex-lind e 1)))) (natp i) (< i (ex-i2 e)))
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
(defthm ex-tr-loop-kinds
  (implies (consp e)
           (and (implies (and (equal (ex-kind e) 12) (ex-lind e 1))
                         (equal (ex-tr :m e 0 cm) (list :loop (ex-tr :lin e 0 cm) (ex-tr :let e 0 cm))))
                (implies (and (equal (ex-kind e) 12) (not (ex-lind e 1))) (equal (ex-tr :m e 0 cm) (ex-tr :let e 0 cm)))
                (implies (equal (ex-kind e) 16) (equal (ex-tr :m e 0 cm) (cons :recur (ex-tr :rec e 0 cm))))
                (implies (and (equal (ex-kind e) 12) (ex-lind e 1) (natp i) (< i (ex-i2 e)))
                         (equal (ex-tr :let e i cm) (ex-tr :let e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm))))
                (implies (and (equal (ex-kind e) 12) (ex-lind e 1) (natp i) (<= (ex-i2 e) i))
                         (equal (ex-tr :let e i cm)
                                (ex-tr :m (ex-kid-of e (ex-i2 e)) 0 (append (ex-blank (ex-slots (ex-s2 e) (ex-i2 e)) cm) (ex-slots (ex-s2 e) (ex-i2 e))))))
                (implies (and (equal (ex-kind e) 12) (not (ex-lind e 1)) (natp i) (<= (ex-i2 e) i))
                         (equal (ex-tr :let e i cm)
                                (list :loop (ex-locals (ex-slots (ex-s2 e) (ex-i2 e)) cm)
                                      (ex-tr :m (ex-kid-of e (ex-i2 e)) 0 (append (ex-blank (ex-slots (ex-s2 e) (ex-i2 e)) cm) (ex-slots (ex-s2 e) (ex-i2 e)))))))
                (implies (and (natp i) (< i (ex-i2 e)))
                         (equal (ex-tr :lin e i cm) (cons (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr :lin e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm)))))
                (implies (and (natp i) (<= (ex-i2 e) i)) (equal (ex-tr :lin e i cm) nil))
                (implies (and (natp i) (< i (ex-nk e)))
                         (equal (ex-tr :rec e i cm) (cons (ex-tr :m (ex-kid-of e i) 0 cm) (ex-tr :rec e (1+ i) (ex-blank (ex-clr :m (ex-kid-of e i) 0) cm)))))
                (implies (and (natp i) (<= (ex-nk e) i)) (equal (ex-tr :rec e i cm) nil))))
  :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank ex-lind ex-locals ex-slots)
                  :expand ((ex-tr :m e 0 cm) (ex-tr :let e i cm) (ex-tr :lin e i cm) (ex-tr :rec e i cm)))))
; how many a loop's inits and a recur's args are, the loop's slots and their reads
(defun vtg-lin-ind (e i c)
  (declare (irrelevant c))
  (declare (xargs :measure (nfix (- (ex-nk e) (nfix i))) :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank)))))
  (if (< (nfix i) (ex-nk e)) (vtg-lin-ind e (1+ (nfix i)) (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) c)) t))
(defun vtg-lin-ind2 (e i c)
  (declare (irrelevant c))
  (declare (xargs :measure (nfix (- (ex-i2 e) (nfix i))) :hints (("Goal" :in-theory (disable ex-kid-of ex-clr ex-blank)))))
  (if (< (nfix i) (ex-i2 e)) (vtg-lin-ind2 e (1+ (nfix i)) (ex-blank (ex-clr :m (ex-kid-of e (nfix i)) 0) c)) t))
(defthm vtg-len-rec
  (implies (consp e) (and (equal (len (ex-tr :rec e i c)) (nfix (- (ex-nk e) (nfix i)))) (true-listp (ex-tr :rec e i c))))
  :hints (("Goal" :induct (vtg-lin-ind e i c) :in-theory (disable ex-kid-of ex-clr ex-blank ex-tr) :expand ((ex-tr :rec e i c)))))
(defthm vtg-len-lin
  (implies (consp e) (and (equal (len (ex-tr :lin e i c)) (nfix (- (ex-i2 e) (nfix i)))) (true-listp (ex-tr :lin e i c))))
  :hints (("Goal" :induct (vtg-lin-ind2 e i c) :in-theory (disable ex-kid-of ex-clr ex-blank ex-tr) :expand ((ex-tr :lin e i c)))))
(defthm vtg-len-slots (and (equal (len (ex-slots s n)) (nfix n)) (true-listp (ex-slots s n))))
(defthm vtg-len-locals (and (equal (len (ex-locals ls c)) (len ls)) (true-listp (ex-locals ls c))))
(defthm vtg-len-cs (and (equal (len (ex-cs t x np m)) (len x)) (implies (true-listp x) (true-listp (ex-cs t x np m))))
  :hints (("Goal" :induct (len x) :expand ((ex-cs t x np m)))))

; THE STATE as its three fields, and each shim on it
(defun vtg-st (stk cm sv cs) (list stk cm sv cs))
(defun vtg-np (cs) (if (consp cs) (car cs) 0))
(defun vtg-nm (cs) (if (consp cs) (cdr cs) 0))
(defthm vtg-shims
  (and (equal (vtg-const v (vtg-st s c sv cs)) (vtg-st (cons (list :const v) s) c sv cs))
       (equal (vtg-nil (vtg-st s c sv cs)) (vtg-st (cons '(:const nil) s) c sv cs))
       (equal (vtg-deref e (vtg-st s c sv cs)) (vtg-st (cons (list :prim :clotran.vm/deref (list :const (vtg-c e))) s) c sv cs))
       (equal (vtg-local n (vtg-st s c sv cs)) (vtg-st (cons (ex-cs nil (list :local (ex-pos n c)) (vtg-np cs) (vtg-nm cs)) s) c sv cs))
       (equal (vtg-save (vtg-st s c sv cs)) (vtg-st s c (cons c sv) cs))
       (equal (vtg-restore (vtg-st s c (cons c0 sv) cs)) (vtg-st s c0 sv cs))
       (equal (vtg-blank x (vtg-st s c sv cs)) (vtg-st s (ex-blank (ex-clr :m x 0) c) sv cs))
       (equal (vtg-bind n (vtg-st s c sv cs)) (vtg-st s (append (true-list-fix c) (list n)) sv cs))
       (equal (vtg-binds n k (vtg-st s c sv cs)) (vtg-st s (append (ex-blank (ex-slots n k) (true-list-fix c)) (ex-slots n k)) sv cs))
       (equal (vtg-dead (vtg-st s c sv cs)) (vtg-st s (append (true-list-fix c) (list nil)) sv cs))
       (equal (vtg-node 1 3 (vtg-st (list* z y x s) c sv cs)) (vtg-st (cons (list :if x y z) s) c sv cs))
       (equal (vtg-node 2 2 (vtg-st (list* y x s) c sv cs)) (vtg-st (cons (list :let x y) s) c sv cs))
       (equal (vtg-node 4 2 (vtg-st (list* y x s) c sv cs)) (vtg-st (cons (list :loop x y) s) c sv cs))
       (equal (vtg-node 3 1 (vtg-st (list* x s) c sv cs)) (vtg-st (cons (list :throw x) s) c sv cs)))
  :hints (("Goal" :expand ((:free (n l acc) (vtg-popn n l acc))))))
; n items pushed in order, made one list (op 0) or node
(defun vtg-pind (l s k) (if (consp l) (vtg-pind (cdr l) (cons (car l) s) (+ 1 k)) (list s k)))
(defthm vtg-popn-rev
  (implies (natp k) (equal (vtg-popn (+ (len l) k) (revappend l s) acc) (vtg-popn k s (append l acc))))
  :hints (("Goal" :induct (vtg-pind l s k) :expand ((vtg-popn (+ 1 k) (cons (car l) s) (append (cdr l) acc)) (revappend l s)))))
(defthm vtg-node-rev
  (implies (and (equal n (len l)) (true-listp l))
           (equal (vtg-node op n (vtg-st (revappend l s) c sv cs))
                  (vtg-st (cons (if (equal op 0) l (cons (vtg-op op) l)) s) c sv cs)))
  :hints (("Goal" :use ((:instance vtg-popn-rev (k 0) (acc nil))) :in-theory (disable vtg-popn-rev vtg-op)
                  :expand ((:free (x acc) (vtg-popn 0 x acc))))))
(defthm ex-blank-nil-true (implies (true-listp c) (true-listp (append c (list n)))))
(defthm vtg-ok-consp (implies (vtg-ok e) (consp e)) :rule-classes :forward-chaining)
; the rewrite of the captures, through the nodes the generated kinds make
(defthm vtg-cs-nodes
  (and (equal (ex-cs nil (list :const v) np m) (list :const v))
       (equal (ex-cs nil (list :prim op (list :const v)) np m) (list :prim op (list :const v)))
       (equal (ex-cs nil (list :if x y z) np m) (list :if (ex-cs nil x np m) (ex-cs nil y np m) (ex-cs nil z np m)))
       (equal (ex-cs nil (list :let x y) np m) (list :let (ex-cs nil x np m) (ex-cs nil y np m)))
       (equal (ex-cs nil (list :loop x y) np m) (list :loop (ex-cs t x np m) (ex-cs nil y np m)))
       (equal (ex-cs nil (cons :recur x) np m) (cons :recur (ex-cs t x np m)))
       (equal (ex-cs nil (list :throw x) np m) (list :throw (ex-cs nil x np m)))))
(in-theory (disable ex-cs vtg-np vtg-nm ex-lind ex-rd vtg-rd))
(in-theory (disable ex-tr vtg-st vtg-const vtg-deref vtg-nil vtg-local vtg-save vtg-restore vtg-blank vtg-bind vtg-binds vtg-dead vtg-node vtg-frag vtg-ok
                    vtg-locs vtg-lind vtg-okt))

(defun vtg-locs-ind (s j n stk c cs)
  (declare (xargs :measure (nfix (- (nfix n) (nfix j)))))
  (if (< (nfix j) (nfix n))
      (vtg-locs-ind s (+ 1 (nfix j)) n (cons (ex-cs nil (list :local (ex-pos (+ s (nfix j)) c)) (vtg-np cs) (vtg-nm cs)) stk) c cs)
    (list s stk c cs)))
(defthm vtg-slots-zp (implies (zp n) (equal (ex-slots s n) nil)))
(defthm vtg-locs-st
  (implies (and (natp s) (natp j) (natp n))
           (equal (vtg-locs s j n (vtg-st stk c sv cs))
                  (vtg-st (revappend (ex-cs t (ex-locals (ex-slots (+ s j) (- n j)) c) (vtg-np cs) (vtg-nm cs)) stk) c sv cs)))
  :hints (("Goal" :induct (vtg-locs-ind s j n stk c cs) :in-theory (disable vtg-local vtg-np vtg-nm)
                  :expand ((ex-slots (+ s j) (- n j)) (vtg-locs s j n (vtg-st stk c sv cs))))))

(defthm vtg-frag-facts
  (implies (vtg-frag flg e i)
           (and (vtg-ok e)
                (implies (equal flg 1) (or (equal (vtg-kind e) 11) (and (equal (vtg-kind e) 12) (vtg-okt nil e) (not (vtg-lind e 1)))))
                (implies (equal flg 2) (equal (vtg-kind e) 5))
                (implies (equal flg 3) (or (equal (vtg-kind e) 12) (equal (vtg-kind e) 16)))
                (implies (equal flg 5) (and (equal (vtg-kind e) 12) (vtg-okt nil e) (vtg-lind e 1)))
                (implies (not (member flg '(1 2 3 5))) (member (vtg-kind e) (quote (1 2 3 4 5 11 12 16 17))))
                (implies (and (not (member flg '(1 2 3 5))) (equal (vtg-kind e) 12)) (vtg-okt nil e))))
  :rule-classes :forward-chaining :hints (("Goal" :expand ((vtg-frag flg e i)))))

; ex-tr's translation x with the captures read in place
(defun vtg-cw (x cs) (ex-cs nil x (vtg-np cs) (vtg-nm cs)))
(defun vtg-cwl (x cs) (ex-cs t x (vtg-np cs) (vtg-nm cs)))
; the induction: vtg-tr's, each call on the state it is handed
(defun vtg-ind (flg e i s c sv cs)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o< :verify-guards nil :hints (("Goal" :in-theory (disable vtg-kid-ex)))))
  (declare (irrelevant s c sv cs))
  (let ((ls (ex-slots (vtg-s2 e) (vtg-i2 e))))
    (cond
     ((equal flg 1)
      (if (or (equal (vtg-kind e) 11) (equal (vtg-kind e) 12))
          (if (< (nfix i) (vtg-i2 e))
              (let ((k (vtg-kid e (nfix i))))
                (list (vtg-ind 0 k 0 s c sv cs)
                      (vtg-ind 1 e (+ 1 (nfix i)) (cons (vtg-cw (ex-tr :m k 0 c) cs) s)
                               (append (ex-blank (ex-clr :m k 0) c) (list (+ (vtg-s2 e) (nfix i)))) (cons c sv) cs)))
            (if (equal (vtg-kind e) 12)
                (vtg-ind 0 (vtg-kid e (vtg-i2 e)) 0 (cons (vtg-cwl (ex-locals ls c) cs) s) (append (ex-blank ls c) ls) (cons c sv) cs)
              (vtg-ind 0 (vtg-kid e (vtg-i2 e)) 0 s c sv cs)))
        nil))
     ((equal flg 2)
      (if (equal (vtg-kind e) 5)
          (cond ((zp (vtg-nk e)) nil)
                ((< (nfix i) (- (vtg-nk e) 1))
                 (let ((k (vtg-kid e (nfix i))))
                   (list (vtg-ind 0 k 0 s c sv cs)
                         (vtg-ind 2 e (+ 1 (nfix i)) (cons (vtg-cw (ex-tr :m k 0 c) cs) s)
                                  (append (ex-blank (ex-clr :m k 0) c) (list nil)) (cons c sv) cs))))
                (t (vtg-ind 0 (vtg-kid e (- (vtg-nk e) 1)) 0 s c sv cs)))
        nil))
     ((equal flg 3)
      (if (and (or (equal (vtg-kind e) 12) (equal (vtg-kind e) 16)) (< (nfix i) (if (equal (vtg-kind e) 16) (vtg-nk e) (vtg-i2 e))))
          (let ((k (vtg-kid e (nfix i))))
            (list (vtg-ind 0 k 0 s c sv cs)
                  (vtg-ind 3 e (+ 1 (nfix i)) (cons (vtg-cw (ex-tr :m k 0 c) cs) s) (ex-blank (ex-clr :m k 0) c) (cons c sv) cs)))
        nil))
     ((equal flg 5)
      (if (equal (vtg-kind e) 12)
          (if (< (nfix i) (vtg-i2 e))
              (vtg-ind 5 e (+ 1 (nfix i)) s (ex-blank (ex-clr :m (vtg-kid e (nfix i)) 0) c) (cons c sv) cs)
            (vtg-ind 0 (vtg-kid e (vtg-i2 e)) 0 s (append (ex-blank ls c) ls) (cons c sv) cs))
        nil))
     (t
      (let ((k (vtg-kind e)))
        (cond ((equal k 4)
               (let* ((k0 (vtg-kid e 0)) (c1 (ex-blank (ex-clr :m k0 0) c)) (t0 (vtg-cw (ex-tr :m k0 0 c) cs)))
                 (list (vtg-ind 0 k0 0 s c sv cs)
                       (vtg-ind 0 (vtg-kid e 1) 0 (cons t0 s) c1 (cons c sv) cs)
                       (vtg-ind 0 (vtg-kid e 2) 0 (cons (vtg-cw (ex-tr :m (vtg-kid e 1) 0 c1) cs) (cons t0 s)) c1 (cons c sv) cs))))
              ((equal k 17) (vtg-ind 0 (vtg-kid e 0) 0 s c sv cs))
              ((equal k 11) (vtg-ind 1 e 0 s c sv cs))
              ((equal k 5) (vtg-ind 2 e 0 s c sv cs))
              ((equal k 12)
               (if (vtg-lind e 1)
                   (list (vtg-ind 3 e 0 s c sv cs) (vtg-ind 5 e 0 (cons (vtg-cwl (ex-tr :lin e 0 c) cs) s) c sv cs))
                 (vtg-ind 1 e 0 s c sv cs)))
              ((equal k 16) (vtg-ind 3 e 0 s c sv cs))
              (t nil)))))))

; what vtg-tr pushes: ex-tr's at the place flg names, the captures read in
; place -- one expression, or (flg 3) the inits' or args' each in order
(defun vtg-want (flg e i c cs)
  (vtg-cw (cond ((or (equal flg 1) (equal flg 5)) (ex-tr :let e (nfix i) c)) ((equal flg 2) (ex-tr :do e (nfix i) c)) (t (ex-tr :m e 0 c))) cs))
(defun vtg-out (flg e i c cs s)
  (if (equal flg 3)
      (revappend (vtg-cwl (if (equal (vtg-kind e) 16) (ex-tr :rec e (nfix i) c) (ex-tr :lin e (nfix i) c)) cs) s)
    (cons (vtg-want flg e i c cs) s)))

(defthm vtg-tr-st
  (implies (and (vtg-frag flg e i) (true-listp c))
           (equal (vtg-tr flg e i (vtg-st s c sv cs))
                  (vtg-st (vtg-out flg e i c cs s) c sv cs)))
  :hints (("Goal" :induct (vtg-ind flg e i s c sv cs)
                  :in-theory (disable ex-kid-of ex-clr ex-blank ex-slots ex-locals)
                  :expand ((:free (flg) (vtg-frag flg e i)) (:free (flg) (vtg-tr flg e i (vtg-st s c sv cs)))))
          (and stable-under-simplificationp '(:in-theory (e/d (vtg-kid-ex vtg-ok) (ex-kid-of ex-clr ex-blank ex-slots ex-locals))))))

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
; translation pushes exactly ex-tr's (vtg-out: at flg 0 one expression), the captures read in place (the
; fn's clause body's, exec-vmtr's ex-fbtc), the scope and the saves as
; they were
(defthm vtg-tr-ex-tr
  (implies (and (vtg-frag flg e i) (vtbp vtb) (true-listp (vtb-cm vtb)))
           (and (equal (vtb-stk (vtg-tr flg e i vtb)) (vtg-out flg e i (vtb-cm vtb) (vtb-cs vtb) (vtb-stk vtb)))
                (equal (vtb-cm (vtg-tr flg e i vtb)) (vtb-cm vtb))
                (equal (vtb-sv (vtg-tr flg e i vtb)) (vtb-sv vtb))
                (equal (vtb-cs (vtg-tr flg e i vtb)) (vtb-cs vtb))))
  :hints (("Goal" :use ((:instance vtg-tr-st (s (vtb-stk vtb)) (c (vtb-cm vtb)) (sv (vtb-sv vtb)) (cs (vtb-cs vtb))))
                  :in-theory (disable vtg-tr-st vtg-tr vtb-stk vtb-cm vtb-sv vtb-cs vtbp))))

; vtg-tlr is ex-tlr on a tree whose nodes it reaches are in the reads'
; range and no case (vm_scan refuses case: the fn runs on the tree)
(defun vtg-tlr-ok (e)
  (declare (xargs :measure (acl2-count e) :hints (("Goal" :in-theory (disable vtg-kid-ex vtg-reads-ex)))))
  (and (vtg-ok e) (not (equal (vtg-kind e) 19))
       (let ((k (vtg-kind e)) (nk (vtg-nk e)))
         (cond ((equal k 4) (and (vtg-tlr-ok (vtg-kid e 1)) (or (<= nk 2) (vtg-tlr-ok (vtg-kid e 2)))))
               ((equal k 5) (or (zp nk) (vtg-tlr-ok (vtg-kid e (- nk 1)))))
               ((or (equal k 11) (equal k 13)) (vtg-tlr-ok (vtg-kid e (vtg-i2 e))))
               (t t)))))
(defun vtg-tli (i n) (declare (xargs :measure (nfix (- (nfix n) (nfix i))))) (if (< (nfix i) (nfix n)) (vtg-tli (1+ (nfix i)) n) t))
(defthm ex-tlr-let-at
  (implies (consp e) (equal (ex-tlr :let e i) (and (equal (ex-kind e) 11) (ex-tlr :m (ex-kid-of e (ex-i2 e)) 0))))
  :hints (("Goal" :induct (vtg-tli i (ex-i2 e)) :in-theory (disable ex-kid-of) :expand ((ex-tlr :let e i)))))
(defthm ex-tlr-do-at
  (implies (consp e) (equal (ex-tlr :do e i) (if (zp (ex-nk e)) nil (ex-tlr :m (ex-kid-of e (- (ex-nk e) 1)) 0))))
  :hints (("Goal" :induct (vtg-tli i (- (ex-nk e) 1)) :in-theory (disable ex-kid-of) :expand ((ex-tlr :do e i)))))
(defthm vtg-tlr-ex-tlr
  (implies (vtg-tlr-ok e) (equal (vtg-tlr e) (ex-tlr :m e 0)))
  :hints (("Goal" :induct (vtg-tlr e) :in-theory (disable ex-kid-of)
                  :expand ((ex-tlr :m e 0) (vtg-tlr-ok e) (vtg-tlr e)))))

; ---- THE COST ---------------------------------------------------------------------------------
;
;; vtg-steps: vtg-tr's work as the generated code does it -- a step a call
; (a cycle among them) and a step a shim, vtg_binds n+1 (a bind a slot),
; vtg_lind one (its own walk vtg-lind-steps-bound), vtg_other's own work its
; host's; vtg-size: the nodes it reaches, a let's bindings and body among
; them, a loop's slots once more (read or bound again, their inits blanked).
; vtg-steps-bound: at most 16 steps a node -- each node's shims a constant.
(defun vtg-steps (flg e i)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex)))))
  (let ((k (vtg-kind e)) (n2 (vtg-i2 e)) (body (vtg-kid e (vtg-i2 e))))
    (cond
     ((equal flg 1)
      (if (or (equal k 11) (equal k 12))
          (if (< (nfix i) n2)
              (+ 6 (vtg-steps 0 (vtg-kid e (nfix i)) 0) (vtg-steps 1 e (+ 1 (nfix i))))
            (if (equal k 12) (+ 7 (* 3 n2) (vtg-steps 0 body 0)) (+ 1 (vtg-steps 0 body 0))))
        2))
     ((equal flg 2)
      (if (equal k 5)
          (cond ((zp (vtg-nk e)) 2)
                ((< (nfix i) (- (vtg-nk e) 1)) (+ 7 (vtg-steps 0 (vtg-kid e (nfix i)) 0) (vtg-steps 2 e (+ 1 (nfix i)))))
                (t (+ 1 (vtg-steps 0 (vtg-kid e (- (vtg-nk e) 1)) 0))))
        2))
     ((equal flg 3)
      (if (and (or (equal k 12) (equal k 16)) (< (nfix i) (if (equal k 16) (vtg-nk e) n2)))
          (+ 4 (vtg-steps 0 (vtg-kid e (nfix i)) 0) (vtg-steps 3 e (+ 1 (nfix i))))
        2))
     ((equal flg 5)
      (if (equal k 12)
          (if (< (nfix i) n2) (+ 4 (vtg-steps 5 e (+ 1 (nfix i)))) (+ 5 n2 (vtg-steps 0 body 0)))
        2))
     (t
      (cond ((equal k 4) (+ 5 (vtg-steps 0 (vtg-kid e 0) 0) (vtg-steps 0 (vtg-kid e 1) 0)
                            (if (< 2 (vtg-nk e)) (vtg-steps 0 (vtg-kid e 2) 0) 1)))
            ((equal k 17) (+ 2 (vtg-steps 0 (vtg-kid e 0) 0)))
            ((equal k 11) (+ 1 (vtg-steps 1 e 0)))
            ((equal k 5) (+ 1 (vtg-steps 2 e 0)))
            ((equal k 12) (if (vtg-lind e 1) (+ 4 (vtg-steps 3 e 0) (vtg-steps 5 e 0)) (+ 2 (vtg-steps 1 e 0))))
            ((equal k 16) (+ 2 (vtg-steps 3 e 0)))
            (t 2))))))
(defun vtg-size (flg e i)
  (declare (xargs :measure (vtg-m flg e i) :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex)))))
  (let ((k (vtg-kind e)) (n2 (vtg-i2 e)) (body (vtg-kid e (vtg-i2 e))))
    (cond
     ((equal flg 1)
      (if (or (equal k 11) (equal k 12))
          (if (< (nfix i) n2)
              (+ (vtg-size 0 (vtg-kid e (nfix i)) 0) (vtg-size 1 e (+ 1 (nfix i))))
            (if (equal k 12) (+ n2 (vtg-size 0 body 0)) (vtg-size 0 body 0)))
        1))
     ((equal flg 2)
      (if (equal k 5)
          (cond ((zp (vtg-nk e)) 1)
                ((< (nfix i) (- (vtg-nk e) 1)) (+ (vtg-size 0 (vtg-kid e (nfix i)) 0) (vtg-size 2 e (+ 1 (nfix i)))))
                (t (vtg-size 0 (vtg-kid e (- (vtg-nk e) 1)) 0)))
        1))
     ((equal flg 3)
      (if (and (or (equal k 12) (equal k 16)) (< (nfix i) (if (equal k 16) (vtg-nk e) n2)))
          (+ (vtg-size 0 (vtg-kid e (nfix i)) 0) (vtg-size 3 e (+ 1 (nfix i))))
        1))
     ((equal flg 5)
      (if (equal k 12)
          (if (< (nfix i) n2) (+ 1 (vtg-size 5 e (+ 1 (nfix i)))) (+ n2 (vtg-size 0 body 0)))
        1))
     (t
      (cond ((equal k 4) (+ 1 (vtg-size 0 (vtg-kid e 0) 0) (vtg-size 0 (vtg-kid e 1) 0)
                            (if (< 2 (vtg-nk e)) (vtg-size 0 (vtg-kid e 2) 0) 0)))
            ((equal k 17) (+ 1 (vtg-size 0 (vtg-kid e 0) 0)))
            ((equal k 11) (+ 1 (vtg-size 1 e 0)))
            ((equal k 5) (+ 1 (vtg-size 2 e 0)))
            ((equal k 12) (if (vtg-lind e 1) (+ 1 (vtg-size 3 e 0) (vtg-size 5 e 0)) (+ 1 (vtg-size 1 e 0))))
            ((equal k 16) (+ 1 (vtg-size 3 e 0)))
            (t 1))))))
(defthm vtg-steps-bound-flag
  (<= (vtg-steps flg e i) (if (member flg '(1 2 3 5)) (+ 1 (* 16 (vtg-size flg e i))) (- (* 16 (vtg-size flg e i)) 7)))
  :rule-classes nil
  :hints (("Goal" :induct (vtg-steps flg e i) :in-theory (disable vtg-kid-ex vtg-lind)
                  :expand ((:free (flg) (vtg-steps flg e i)) (:free (flg) (vtg-size flg e i))))))
(defthm vtg-steps-bound (<= (vtg-steps 0 e 0) (* 16 (vtg-size 0 e 0)))
  :rule-classes :linear :hints (("Goal" :use ((:instance vtg-steps-bound-flag (flg 0) (i 0))))))

; vtg-lind's work: vtg-rd's walk to its end (an answer found only stops it
; sooner), 2 steps a node and a child it walks (vtg-rd-size), vtg_rdcap
; one; the inits' walks and 3 steps an init (vtg-lind-size).
; vtg-lind-steps-bound: at most 6 steps a node it reaches.
(defun vtg-rd-walks (k)
  (member k '(4 5 17 7 8 9 22 21 6 11 12 16)))
(defun vtg-rd-steps (flg e i)
  (declare (xargs :measure (make-ord 1 (1+ (acl2-count e)) (if (equal flg 1) (nfix (- (vtg-nk e) (nfix i))) *vtg40*))
                  :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex)))))
  (if (equal flg 1)
      (if (< (nfix i) (vtg-nk e)) (+ 2 (vtg-rd-steps 0 (vtg-kid e (nfix i)) 0) (vtg-rd-steps 1 e (+ 1 (nfix i)))) 1)
    (if (vtg-rd-walks (vtg-kind e)) (+ 2 (vtg-rd-steps 1 e 0)) 2)))
(defun vtg-rd-size (flg e i)
  (declare (xargs :measure (make-ord 1 (1+ (acl2-count e)) (if (equal flg 1) (nfix (- (vtg-nk e) (nfix i))) *vtg40*))
                  :well-founded-relation o< :hints (("Goal" :in-theory (disable vtg-kid-ex)))))
  (if (equal flg 1)
      (if (< (nfix i) (vtg-nk e)) (+ (vtg-rd-size 0 (vtg-kid e (nfix i)) 0) (vtg-rd-size 1 e (+ 1 (nfix i)))) 0)
    (if (vtg-rd-walks (vtg-kind e)) (+ 1 (vtg-rd-size 1 e 0)) 1)))
(defthm vtg-rd-steps-bound
  (<= (vtg-rd-steps flg e i) (if (equal flg 1) (+ 1 (* 5 (vtg-rd-size flg e i))) (- (* 5 (vtg-rd-size flg e i)) 2)))
  :rule-classes nil
  :hints (("Goal" :induct (vtg-rd-steps flg e i) :in-theory (disable vtg-kid-ex vtg-rd-walks)
                  :expand ((:free (flg) (vtg-rd-steps flg e i)) (:free (flg) (vtg-rd-size flg e i))))))
(defthm vtg-rd-steps-bound0 (<= (vtg-rd-steps 0 e i) (- (* 5 (vtg-rd-size 0 e i)) 2)) :rule-classes :linear
  :hints (("Goal" :use ((:instance vtg-rd-steps-bound (flg 0))))))
(defthm vtg-rd-size-pos (<= 1 (vtg-rd-size 0 e i)) :rule-classes :linear
  :hints (("Goal" :expand ((vtg-rd-size 0 e i)))))
(defun vtg-lind-steps (e i)
  (declare (xargs :measure (nfix (- (vtg-i2 e) (nfix i)))))
  (if (< (nfix i) (vtg-i2 e)) (+ 3 (vtg-rd-steps 0 (vtg-kid e (nfix i)) 0) (vtg-lind-steps e (+ 1 (nfix i)))) 1))
(defun vtg-lind-size (e i)
  (declare (xargs :measure (nfix (- (vtg-i2 e) (nfix i)))))
  (if (< (nfix i) (vtg-i2 e)) (+ (vtg-rd-size 0 (vtg-kid e (nfix i)) 0) (vtg-lind-size e (+ 1 (nfix i)))) 0))
(defthm vtg-lind-steps-bound (<= (vtg-lind-steps e i) (+ 1 (* 6 (vtg-lind-size e i))))
  :rule-classes :linear
  :hints (("Goal" :induct (vtg-lind-steps e i) :in-theory (disable vtg-kid-ex vtg-rd-steps vtg-rd-size)
                  :expand ((vtg-lind-steps e i) (vtg-lind-size e i)))))

; vtg-tlr's work: a node it reaches its reads (kind, count, a kid, i2) and
; the call, 5 steps; the nodes it reaches vtg-tlr-size. vtg-tlr-steps-bound.
(defun vtg-tlr-size (e)
  (declare (xargs :measure (acl2-count e) :hints (("Goal" :in-theory (disable vtg-kid-ex vtg-reads-ex)))))
  (let ((k (vtg-kind e)) (nk (vtg-nk e)))
    (cond ((equal k 4) (+ 1 (vtg-tlr-size (vtg-kid e 1)) (if (< 2 nk) (vtg-tlr-size (vtg-kid e 2)) 0)))
          ((equal k 5) (if (zp nk) 1 (+ 1 (vtg-tlr-size (vtg-kid e (- nk 1))))))
          ((or (equal k 11) (equal k 13)) (+ 1 (vtg-tlr-size (vtg-kid e (vtg-i2 e)))))
          (t 1))))
(defun vtg-tlr-steps (e)
  (declare (xargs :measure (acl2-count e) :hints (("Goal" :in-theory (disable vtg-kid-ex vtg-reads-ex)))))
  (let ((k (vtg-kind e)) (nk (vtg-nk e)))
    (cond ((equal k 16) 2)
          ((equal k 4) (+ 5 (if (vtg-tlr (vtg-kid e 1)) (vtg-tlr-steps (vtg-kid e 1))
                              (+ (vtg-tlr-steps (vtg-kid e 1)) (if (< 2 nk) (vtg-tlr-steps (vtg-kid e 2)) 0)))))
          ((equal k 5) (if (zp nk) 3 (+ 4 (vtg-tlr-steps (vtg-kid e (- nk 1))))))
          ((or (equal k 11) (equal k 13)) (+ 4 (vtg-tlr-steps (vtg-kid e (vtg-i2 e)))))
          (t 3))))
(defthm vtg-tlr-steps-bound (<= (vtg-tlr-steps e) (* 5 (vtg-tlr-size e)))
  :rule-classes :linear :hints (("Goal" :induct (vtg-tlr-steps e) :in-theory (disable vtg-kid-ex))))
