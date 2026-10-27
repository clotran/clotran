; THE ANALYZER'S NODE ASSEMBLY, PROVED (model/anbuild.lisp): every
; operation keeps the locals and the builder what they are (anb-preserves),
; so the clique's guards hold (verified here, which is what lets
; scripts/acl2-fortran generate it); and a whole analysis with no error
; leaves exactly one node on the builder, over what was there, well-formed
; by anpass's reads, every subtree so (anb-an-wf) -- the induction anform's
; one step (anf-step) left open, closed: by induction on the form, over
; every special form, the host's nodes (a var, a call, a macro's expansion,
; a collection, a literal) assumed well-formed as anb-host's constraint says.
; Then what the nodes carry: a def's metadata node (anb-def-meta), a fn's
; own name bound to its self slot in its root block and its captures exactly
; the capture records anlocal keeps for the fn (anb-fn-name, anb-fn-caps), a
; symbol bound locally the binding its lexical meaning is (anb-an-local).
;
; The clique is mutually recursive; its induction is the flag function
; anb-fl, the clique's bodies with each call a call of anb-fl on a flag and
; the union of the formals (x b i p q), written from anbuild.lisp's text by
; scripts/anbuild-flag (check-vm-gen checks it is current) and proved to be
; the clique here (anb-fl-is-case).

(in-package "ACL2")

(include-book "anbuild")
(include-book "anpass")

; ---- THE CHECKS' CODES ARE WORDS --------------------------------------------------------------

(defthm anb-codes-small
  (and (natp (anf-if n)) (< (anf-if n) 64) (natp (anf-quote n)) (< (anf-quote n) 64)
       (natp (anf-throw n)) (< (anf-throw n) 64) (natp (anf-set n)) (< (anf-set n) 64)
       (natp (anf-set-target x)) (< (anf-set-target x) 64) (natp (anf-dot x)) (< (anf-dot x) 64)
       (natp (anf-new x)) (< (anf-new x) 64) (natp (anl-shape x)) (< (anl-shape x) 64)
       (natp (anl-name-code x)) (< (anl-name-code x) 64)
       (implies (equal w 0) (and (natp (anf-def x w)) (< (anf-def x w) 64))))
  :hints (("Goal" :in-theory (enable frf-kind frm-kind))))
(defthm anb-catch-code-small (and (natp (anf-catch f)) (< (anf-catch f) 64)))
(defthm anb-try-step-sb64
  (implies (signed-byte-p 64 st) (and (integerp (anf-try-step st f lastp w)) (signed-byte-p 64 (anf-try-step st f lastp w))))
  :hints (("Goal" :in-theory (enable frf-word))))
(defthm anb-def-place-small (and (natp (anf-def x 1)) (< (anf-def x 1) 4)) :hints (("Goal" :in-theory (enable frf-kind))))
(defthm anl-pw-code-small (and (natp (anl-pw pv i n st nreq rest 0)) (< (anl-pw pv i n st nreq rest 0) 64)))
(defthm anl-params-code-small (and (natp (anl-params pv 0)) (< (anl-params pv 0) 64))
  :hints (("Goal" :in-theory (e/d (anl-params) (anl-pw-code-small)) :use ((:instance anl-pw-code-small (i 0) (n (frm-count pv)) (st 0) (nreq 0) (rest 0))))))
(defthm anl-arity-code-small
  (implies (and (anlsp anls) (signed-byte-p 64 nreq))
           (and (natp (car (anl-arity b nreq rest anls))) (< (car (anl-arity b nreq rest anls)) 64)))
  :hints (("Goal" :in-theory (enable anl-arity))))
(defthm anl-arity-end-small (and (natp (anl-arity-end b anls)) (< (anl-arity-end b anls) 64)) :hints (("Goal" :in-theory (enable anl-arity-end))))
(defthm anb-try-fin-range (and (natp (anb-try-fin cls)) (<= (anb-try-fin cls) 1)) :rule-classes ((:type-prescription :corollary (natp (anb-try-fin cls))) (:linear :corollary (<= (anb-try-fin cls) 1))))

; and as bounds linear arithmetic uses
(defmacro anb-small (name term &optional (hyp 't) (hints 'nil))
  `(defthm ,name (implies ,hyp (and (integerp ,term) (<= 0 ,term) (< ,term 64))) :hints ,hints
     :rule-classes ((:type-prescription :corollary (implies ,hyp (integerp ,term)))
                    (:linear :corollary (implies ,hyp (and (<= 0 ,term) (< ,term 64)))))))
(anb-small anf-if-small (anf-if n))
(anb-small anf-quote-small (anf-quote n))
(anb-small anf-throw-small (anf-throw n))
(anb-small anf-set-small (anf-set n))
(anb-small anf-set-target-small (anf-set-target x))
(anb-small anf-dot-small (anf-dot x))
(anb-small anf-new-small (anf-new x))
(anb-small anl-shape-small (anl-shape x))
(anb-small anl-name-code-small (anl-name-code x))
(anb-small anf-def-small (anf-def x 0))
(anb-small anf-def-init-small (anf-def x 1))
(anb-small anf-catch-small (anf-catch f) t (("Goal" :use anb-catch-code-small :in-theory (disable anb-catch-code-small))))
(anb-small anl-params-small (anl-params pv 0) t (("Goal" :use anl-params-code-small :in-theory (disable anl-params-code-small))))
(anb-small anl-arity-end-small2 (anl-arity-end b anls) t (("Goal" :use anl-arity-end-small :in-theory (disable anl-arity-end-small))))
(anb-small anl-arity-small (car (anl-arity b nreq rest anls)) (and (anlsp anls) (signed-byte-p 64 nreq)) (("Goal" :use anl-arity-code-small :in-theory (disable anl-arity-code-small))))
(defthm anb-try-step-bounds
  (implies (signed-byte-p 64 st)
           (and (<= -9223372036854775808 (anf-try-step st f lastp w)) (< (anf-try-step st f lastp w) 9223372036854775808)))
  :hints (("Goal" :use anb-try-step-sb64 :in-theory (disable anb-try-step-sb64)))
  :rule-classes :linear)

; ---- THE BUILDER STAYS ONE ------------------------------------------------------------------------

(defthm anbp-update (implies (anbp anb) (anbp (update-anb-stk v anb))))
(defthm anb-stk-update (equal (anb-stk (update-anb-stk v anb)) v))
(in-theory (disable anbp update-anb-stk anb-stk))
(defthm anb-defend-anbp (implies (and (anlsp anls) (anbp anb)) (anbp (mv-nth 2 (anb-defend x b i2 anls anb)))))
(defthm anb-defend-anlsp (implies (and (anlsp anls) (anbp anb)) (anlsp (mv-nth 1 (anb-defend x b i2 anls anb)))))

; ---- THE INDUCTION -------------------------------------------------------------------------------

;; BEGIN anbuild-flag -- written by scripts/anbuild-flag from model/anbuild.lisp; do not edit
; the flag function: the clique's bodies, every call one of anb-fl; then
; that it is the clique, each member's guard, the preservation by
; induction on it and each member's
(defun anb-fl (fl x b i p q anls anb) (declare (xargs :stobjs (anls anb) :verify-guards nil :measure (case fl (0 (anb-m x 3 0 7)) (1 (anb-m x 2 0 6)) (2 (anb-m x 1 2 8)) (3 (anb-m x 1 0 2)) (4 (anb-m x 1 1 3)) (5 (anb-m x 1 (nfix (- *anl40* (nfix i))) 2)) (6 (anb-m x 1 2 8)) (7 (anb-m x 1 (nfix (- *anl40* (nfix i))) 2)) (8 (anb-m x 1 2 8)) (9 (anb-m x 1 2 8)) (10 (anb-m x 1 0 2)) (11 (anb-m x 1 3 8)) (12 (anb-m x 1 3 8)) (13 (anb-m x 1 3 8)) (14 (anb-m x 1 3 8)) (15 (anb-m x 1 3 9)) (16 (anb-m x 1 0 2)) (otherwise (anb-m x 0 0 4))))) (case fl (0 (anb-fl 1 x b 0 0 0 anls anb)) (1 (cond ((equal (frf-kind x) 2) (mv-let (slot bx anls) (anl-lookup b (frm-sid x) anls) (if (<= 0 bx) (let ((anb (anb-local x slot anb))) (mv 0 anls anb)) (anb-host x b anls anb)))) ((not (equal (frf-kind x) 3)) (anb-host x b anls anb)) (t (let ((sp (frf-sp x)) (n (frf-len x))) (case sp (1 (let ((code (anf-if n))) (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb)) (mv-let (e anls anb) (anb-fl 3 (frf-rest x) b (- n 1) 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-node 4 0 (- n 1) anb))) (mv 0 anls anb))))))) (2 (anb-fl 4 (frf-rest x) b 0 0 0 anls anb)) (3 (anb-fl 2 x b 0 0 0 anls anb)) (4 (let ((code (anf-quote n))) (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb)) (let ((anb (anb-const (frf-nth x 1) anb))) (mv 0 anls anb))))) (5 (let ((code (anf-throw n))) (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb)) (mv-let (e anls anb) (anb-fl 0 (frf-nth x 1) b 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-node 17 0 1 anb))) (mv 0 anls anb))))))) (6 (anb-fl 9 x b 0 0 0 anls anb)) (7 (let* ((code (anf-set n)) (code (if (equal code 0) (anf-set-target (frf-nth x 1)) code))) (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb)) (anb-fl 11 x b 0 0 0 anls anb)))) (8 (let ((code (anf-dot x))) (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb)) (anb-fl 12 x b 0 0 0 anls anb)))) (9 (let ((code (anf-new x))) (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb)) (anb-fl 13 x b 0 0 0 anls anb)))) (11 (anb-fl 6 x b 0 11 0 anls anb)) (12 (anb-fl 6 x b 0 12 0 anls anb)) (13 (anb-fl 14 x b 0 0 0 anls anb)) (14 (anb-fl 15 x b 0 0 0 anls anb)) (15 (anb-fl 8 x b 0 0 0 anls anb)) (otherwise (anb-host x b anls anb))))))) (2 (let ((code (anf-def x 0))) (if (not (equal code 0)) (let ((anb (anb-refuse code x anb))) (mv code anls anb)) (let* ((init (anf-def x 1)) (anb (anb-defvar x anb))) (if (< 0 init) (let ((anb (anb-hint (frf-nth x 1) anb))) (mv-let (e anls anb) (anb-fl 0 (frf-nth x init) b 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (anb-defend x b 1 anls anb)))) (anb-defend x b 0 anls anb)))))) (3 (if (or (not (natp i)) (equal i 0) (equal (frf-len x) 0)) (mv 0 anls anb) (mv-let (e anls anb) (anb-fl 0 (frf-nth x 0) b 0 0 0 anls anb) (if (or (not (equal e 0)) (< (frf-len x) 2)) (mv e anls anb) (anb-fl 3 (frf-rest x) b (- i 1) 0 0 anls anb))))) (4 (mv-let (e anls anb) (anb-fl 3 x b (frf-len x) 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-node 5 0 (frf-len x) anb))) (mv 0 anls anb))))) (5 (if (and (natp i) (< i (frm-pairs x))) (let* ((k (frm-nth x (* 2 i))) (code (anl-name-code k))) (if (not (equal code 0)) (let ((anb (anb-refuse code k anb))) (mv code anls anb)) (let ((anb (anb-hint k anb))) (mv-let (e anls anb) (anb-fl 0 (frm-nth x (+ 1 (* 2 i))) b 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let* ((slot (+ p i)) (anls (anl-bind b (frm-bid k) slot anls)) (e (anb-let-kind k b slot q))) (if (not (equal e 0)) (mv e anls anb) (anb-fl 5 x b (+ 1 i) p q anls anb)))))))) (mv 0 anls anb))) (6 (let* ((bv (frf-nth x 1)) (code (anl-shape bv))) (if (not (equal code 0)) (let ((anb (anb-refuse code bv anb))) (mv code anls anb)) (mv-let (c anls) (anb-child b anls) (let* ((n (frm-pairs bv)) (loopp (if (equal p 12) 1 0))) (mv-let (start anls) (anl-reserve c n anls) (let ((ret (if (equal loopp 1) (anb-loop-open c start n) 0))) (mv-let (e anls anb) (anb-fl 5 bv c 0 start loopp anls anb) (if (not (equal e 0)) (mv e anls anb) (mv-let (e anls anb) (anb-fl 4 (frf-rest (frf-rest x)) c 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((e (if (equal loopp 1) (anb-let-ret c ret) 0))) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-node-s p n (+ 1 n) start anb))) (mv 0 anls anb))))))))))))))) (7 (if (and (natp i) (< i (frm-pairs x))) (mv-let (e anls anb) (anb-fl 0 (frm-nth x (+ 1 (* 2 i))) b 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (anb-fl 7 x b (+ 1 i) 0 0 anls anb))) (mv 0 anls anb))) (8 (let* ((bv (frf-nth x 1)) (code (anl-shape bv))) (if (not (equal code 0)) (let ((anb (anb-refuse code bv anb))) (mv code anls anb)) (mv-let (c anls) (anb-child b anls) (let ((n (frm-pairs bv))) (mv-let (start anls) (anl-reserve c n anls) (mv-let (code anls anb) (anb-lfnames bv 0 c start anls anb) (if (not (equal code 0)) (mv code anls anb) (mv-let (e anls anb) (anb-fl 7 bv c 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (mv-let (e anls anb) (anb-fl 4 (frf-rest (frf-rest x)) c 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-node-s 13 n (+ 1 n) start anb))) (mv 0 anls anb)))))))))))))) (9 (let* ((xs (frf-rest x)) (nb (anb-try-n xs))) (mv-let (e anls anb) (anb-fl 3 xs b nb 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let* ((anb (anb-node 5 0 nb anb)) (cls (anb-drop xs nb))) (mv-let (e anls anb) (anb-fl 10 cls b 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-trynode (anb-try-fin cls) anb))) (mv 0 anls anb))))))))) (10 (if (equal (frf-len x) 0) (mv 0 anls anb) (let* ((f (frf-nth x 0)) (lastp (if (< (frf-len x) 2) 1 0)) (code (anf-try-step p f lastp 0)) (op (anf-try-step p f lastp 1)) (st2 (anf-try-step p f lastp 2))) (cond ((not (equal code 0)) (let ((anb (anb-refuse code f anb))) (mv code anls anb))) ((equal op 1) (let ((code (anf-catch f))) (if (not (equal code 0)) (let ((anb (anb-refuse-catch code f anb))) (mv code anls anb)) (mv-let (c anls) (anb-child b anls) (mv-let (slot anls) (anl-reserve c 1 anls) (let ((anls (anl-bind c (frm-bid (frf-nth f 2)) slot anls))) (mv-let (e anls anb) (anb-fl 4 (frf-rest (frf-rest (frf-rest f))) c 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-catch f slot anb))) (if (< (frf-len x) 2) (mv 0 anls anb) (anb-fl 10 (frf-rest x) b 0 st2 0 anls anb))))))))))) ((equal op 2) (anb-fl 4 (frf-rest f) b 0 0 0 anls anb)) ((< (frf-len x) 2) (mv 0 anls anb)) (t (anb-fl 10 (frf-rest x) b 0 st2 0 anls anb)))))) (11 (let ((k (anb-set-kind x b))) (cond ((equal k 2) (anb-host2 1 x b anls anb)) ((and (equal k 1) (equal (frf-kind (frf-nth x 1)) 3)) (mv-let (e anls anb) (anb-fl 0 (frf-nth (frf-nth x 1) 1) b 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (mv-let (e anls anb) (anb-fl 0 (frf-nth x 2) b 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-setnode x 2 anb))) (mv 0 anls anb))))))) ((equal k 0) (mv-let (e anls anb) (anb-fl 0 (frf-nth x 2) b 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-setnode x 1 anb))) (mv 0 anls anb))))) (t (mv 1 anls anb))))) (12 (if (not (equal (anf-dot-member (frf-len x) (frf-norm (frf-nth x 2))) 0)) (if (equal (frf-class (frf-nth x 1)) 1) (let ((anb (anb-refuse 37 x anb))) (mv 37 anls anb)) (mv-let (e anls anb) (anb-fl 0 (frf-nth x 1) b 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-refuse 37 x anb))) (mv 37 anls anb))))) (let ((k (anb-dot-kind x b))) (cond ((equal k 2) (anb-host2 2 x b anls anb)) ((equal k 1) (let ((anb (anb-const (frf-nth x 1) anb))) (let ((args (if (equal (frf-kind (frf-norm (frf-nth x 2))) 3) (frf-rest (frf-norm (frf-nth x 2))) (frf-rest (frf-rest (frf-rest x)))))) (mv-let (e anls anb) (anb-fl 3 args b (frf-len args) 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-dotnode x 1 (+ 1 (frf-len args)) anb))) (mv 0 anls anb))))))) ((equal k 0) (mv-let (e anls anb) (anb-fl 0 (frf-nth x 1) b 0 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((args (if (equal (frf-kind (frf-norm (frf-nth x 2))) 3) (frf-rest (frf-norm (frf-nth x 2))) (frf-rest (frf-rest (frf-rest x)))))) (mv-let (e anls anb) (anb-fl 3 args b (frf-len args) 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-dotnode x 0 (+ 1 (frf-len args)) anb))) (mv 0 anls anb)))))))) (t (mv 1 anls anb)))))) (13 (if (equal (anb-new-kind x) 2) (anb-host2 3 x b anls anb) (let ((args (frf-rest (frf-rest x)))) (mv-let (e anls anb) (anb-fl 3 args b (frf-len args) 0 0 anls anb) (if (not (equal e 0)) (mv e anls anb) (let ((anb (anb-newnode x (frf-len args) anb))) (mv 0 anls anb))))))) (14 (let ((args (frf-rest x))) (if (not (equal (anb-recur-open x b) 0)) (mv 1 anls anb) (mv-let (e anls anb) (anb-fl 3 args b (frf-len args) 0 0 anls anb) (cond ((not (equal e 0)) (mv e anls anb)) ((not (equal (anb-recur-check x b (frf-len args)) 0)) (mv 1 anls anb)) (t (let ((anb (anb-recurnode x b (frf-len args) anb))) (mv 0 anls anb)))))))) (15 (let* ((nm (frf-nth x 1)) (named (if (equal (frm-kind nm) 2) 1 0))) (mv-let (r anls) (anb-newfn b anls) (mv-let (self anls) (anb-self r nm anls) (let* ((h (anb-fn-open x r self)) (xs (if (equal named 1) (frf-rest (frf-rest x)) (frf-rest x))) (n (if (equal (frm-kind (frf-nth xs 0)) 1) 1 (frf-len xs)))) (cond ((not (equal h 0)) (mv h anls anb)) ((equal (frm-kind (frf-nth xs 0)) 1) (mv-let (e anls anb) (anb-fl 17 xs r 0 0 0 anls anb) (cond ((not (equal e 0)) (mv e anls anb)) ((not (equal (anl-arity-end r anls) 0)) (let ((anb (anb-refuse 12 x anb))) (mv 12 anls anb))) ((not (equal (anb-fn-check x r n) 0)) (mv 1 anls anb)) (t (let* ((anls (anl-caps-of r anls)) (anb (anb-fnclose x r n anls anb))) (mv 0 anls anb)))))) (t (mv-let (e anls anb) (anb-fl 16 xs r (frf-len xs) 0 0 anls anb) (cond ((not (equal e 0)) (mv e anls anb)) ((not (equal (anl-arity-end r anls) 0)) (let ((anb (anb-refuse 12 x anb))) (mv 12 anls anb))) ((not (equal (anb-fn-check x r n) 0)) (mv 1 anls anb)) (t (let* ((anls (anl-caps-of r anls)) (anb (anb-fnclose x r n anls anb))) (mv 0 anls anb)))))))))))) (16 (if (or (not (natp i)) (equal i 0) (equal (frf-len x) 0)) (mv 0 anls anb) (mv-let (e anls anb) (anb-fl 17 (frf-nth x 0) b 0 0 0 anls anb) (if (or (not (equal e 0)) (< (frf-len x) 2)) (mv e anls anb) (anb-fl 16 (frf-rest x) b (- i 1) 0 0 anls anb))))) (otherwise (let* ((cl (frf-norm x)) (pv (frf-nth cl 0))) (if (not (equal (frm-kind pv) 1)) (let ((anb (anb-refuse 13 cl anb))) (mv 13 anls anb)) (let ((code (anl-params pv 0))) (if (not (equal code 0)) (let ((anb (anb-refuse code (frm-nth pv (anl-params pv 1)) anb))) (mv code anls anb)) (let ((nreq (anl-params pv 2)) (rest (anl-params pv 3))) (mv-let (mb anls) (anb-child b anls) (mv-let (start anls) (anl-reserve mb (+ nreq rest) anls) (let* ((anls (anb-params pv 0 mb start anls)) (h (anb-method-open cl b mb start nreq rest))) (cond ((equal h 1) (mv 1 anls anb)) ((equal h 2) (mv-let (e anls anb) (anb-host2 4 cl mb anls anb) (cond ((not (equal e 0)) (mv e anls anb)) ((not (equal (anb-method-check mb) 0)) (mv 1 anls anb)) (t (mv-let (code anls) (anl-arity b nreq rest anls) (if (not (equal code 0)) (let ((anb (anb-refuse code cl anb))) (mv code anls anb)) (let ((anb (anb-arity cl mb start nreq rest anb))) (mv 0 anls anb)))))))) (t (mv-let (e anls anb) (anb-fl 4 (frf-rest cl) mb 0 0 0 anls anb) (cond ((not (equal e 0)) (mv e anls anb)) ((not (equal (anb-method-check mb) 0)) (mv 1 anls anb)) (t (mv-let (code anls) (anl-arity b nreq rest anls) (if (not (equal code 0)) (let ((anb (anb-refuse code cl anb))) (mv code anls anb)) (let ((anb (anb-arity cl mb start nreq rest anb))) (mv 0 anls anb))))))))))))))))))))

(defthm anb-fl-is-case (equal (anb-fl fl x b i p q anls anb) (case fl (0 (anb-sub x b anls anb)) (1 (anb-an x b anls anb)) (2 (anb-deff x b anls anb)) (3 (anb-listn x i b anls anb)) (4 (anb-body x b anls anb)) (5 (anb-binds x i b p q anls anb)) (6 (anb-let x b p anls anb)) (7 (anb-lfinits x i b anls anb)) (8 (anb-letfn x b anls anb)) (9 (anb-try x b anls anb)) (10 (anb-try-walk x p b anls anb)) (11 (anb-set x b anls anb)) (12 (anb-dot x b anls anb)) (13 (anb-new x b anls anb)) (14 (anb-recur x b anls anb)) (15 (anb-fn x b anls anb)) (16 (anb-methods x i b anls anb)) (otherwise (anb-method x b anls anb)))) :hints (("Goal" :induct (anb-fl fl x b i p q anls anb) :expand ((:free (fl) (anb-fl fl x b i p q anls anb)) (anb-sub x b anls anb) (anb-an x b anls anb) (anb-deff x b anls anb) (anb-listn x i b anls anb) (anb-body x b anls anb) (anb-binds x i b p q anls anb) (anb-let x b p anls anb) (anb-lfinits x i b anls anb) (anb-letfn x b anls anb) (anb-try x b anls anb) (anb-try-walk x p b anls anb) (anb-set x b anls anb) (anb-dot x b anls anb) (anb-new x b anls anb) (anb-recur x b anls anb) (anb-fn x b anls anb) (anb-methods x i b anls anb) (anb-method x b anls anb)))) :rule-classes nil)

(defun anb-hyp (fl b i p q) (case fl (0 (signed-byte-p 64 b)) (1 (signed-byte-p 64 b)) (2 (signed-byte-p 64 b)) (3 (and (integerp i) (signed-byte-p 64 b))) (4 (signed-byte-p 64 b)) (5 (and (natp i) (signed-byte-p 64 b) (integerp p) (<= -1 p) (< p *anl40*) (signed-byte-p 64 q))) (6 (and (signed-byte-p 64 b) (member p (quote (11 12))))) (7 (and (natp i) (signed-byte-p 64 b))) (8 (signed-byte-p 64 b)) (9 (signed-byte-p 64 b)) (10 (and (signed-byte-p 64 p) (signed-byte-p 64 b))) (11 (signed-byte-p 64 b)) (12 (signed-byte-p 64 b)) (13 (signed-byte-p 64 b)) (14 (signed-byte-p 64 b)) (15 (signed-byte-p 64 b)) (16 (and (integerp i) (signed-byte-p 64 b))) (otherwise (signed-byte-p 64 b))))

(defthm anb-fl-preserves (implies (and (anlsp anls) (anbp anb) (anb-hyp fl b i p q)) (and (anlsp (mv-nth 1 (anb-fl fl x b i p q anls anb))) (anbp (mv-nth 2 (anb-fl fl x b i p q anls anb))))) :hints (("Goal" :induct (anb-fl fl x b i p q anls anb) :in-theory (disable anb-host-push anb-host-meta-push) :expand ((anb-fl fl x b i p q anls anb)))))

(defthm anb-sub-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 b)) (and (anlsp (mv-nth 1 (anb-sub x b anls anb))) (anbp (mv-nth 2 (anb-sub x b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 0) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 0) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-an-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 b)) (and (anlsp (mv-nth 1 (anb-an x b anls anb))) (anbp (mv-nth 2 (anb-an x b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 1) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 1) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-deff-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 b)) (and (anlsp (mv-nth 1 (anb-deff x b anls anb))) (anbp (mv-nth 2 (anb-deff x b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 2) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 2) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-listn-preserves (implies (and (anlsp anls) (anbp anb) (and (integerp n) (signed-byte-p 64 b))) (and (anlsp (mv-nth 1 (anb-listn xs n b anls anb))) (anbp (mv-nth 2 (anb-listn xs n b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 3) (x xs) (b b) (i n) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 3) (x xs) (b b) (i n) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-body-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 b)) (and (anlsp (mv-nth 1 (anb-body xs b anls anb))) (anbp (mv-nth 2 (anb-body xs b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 4) (x xs) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 4) (x xs) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-binds-preserves (implies (and (anlsp anls) (anbp anb) (and (natp i) (signed-byte-p 64 c) (integerp start) (<= -1 start) (< start *anl40*) (signed-byte-p 64 loopp))) (and (anlsp (mv-nth 1 (anb-binds bv i c start loopp anls anb))) (anbp (mv-nth 2 (anb-binds bv i c start loopp anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 5) (x bv) (b c) (i i) (p start) (q loopp) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 5) (x bv) (b c) (i i) (p start) (q loopp) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-let-preserves (implies (and (anlsp anls) (anbp anb) (and (signed-byte-p 64 b) (member kind (quote (11 12))))) (and (anlsp (mv-nth 1 (anb-let x b kind anls anb))) (anbp (mv-nth 2 (anb-let x b kind anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 6) (x x) (b b) (i 0) (p kind) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 6) (x x) (b b) (i 0) (p kind) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-lfinits-preserves (implies (and (anlsp anls) (anbp anb) (and (natp i) (signed-byte-p 64 c))) (and (anlsp (mv-nth 1 (anb-lfinits bv i c anls anb))) (anbp (mv-nth 2 (anb-lfinits bv i c anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 7) (x bv) (b c) (i i) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 7) (x bv) (b c) (i i) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-letfn-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 b)) (and (anlsp (mv-nth 1 (anb-letfn x b anls anb))) (anbp (mv-nth 2 (anb-letfn x b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 8) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 8) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-try-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 b)) (and (anlsp (mv-nth 1 (anb-try x b anls anb))) (anbp (mv-nth 2 (anb-try x b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 9) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 9) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-try-walk-preserves (implies (and (anlsp anls) (anbp anb) (and (signed-byte-p 64 st) (signed-byte-p 64 b))) (and (anlsp (mv-nth 1 (anb-try-walk cls st b anls anb))) (anbp (mv-nth 2 (anb-try-walk cls st b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 10) (x cls) (b b) (i 0) (p st) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 10) (x cls) (b b) (i 0) (p st) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-set-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 b)) (and (anlsp (mv-nth 1 (anb-set x b anls anb))) (anbp (mv-nth 2 (anb-set x b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 11) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 11) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-dot-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 b)) (and (anlsp (mv-nth 1 (anb-dot x b anls anb))) (anbp (mv-nth 2 (anb-dot x b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 12) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 12) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-new-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 b)) (and (anlsp (mv-nth 1 (anb-new x b anls anb))) (anbp (mv-nth 2 (anb-new x b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 13) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 13) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-recur-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 b)) (and (anlsp (mv-nth 1 (anb-recur x b anls anb))) (anbp (mv-nth 2 (anb-recur x b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 14) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 14) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-fn-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 b)) (and (anlsp (mv-nth 1 (anb-fn x b anls anb))) (anbp (mv-nth 2 (anb-fn x b anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 15) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 15) (x x) (b b) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-methods-preserves (implies (and (anlsp anls) (anbp anb) (and (integerp n) (signed-byte-p 64 r))) (and (anlsp (mv-nth 1 (anb-methods ms n r anls anb))) (anbp (mv-nth 2 (anb-methods ms n r anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 16) (x ms) (b r) (i n) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 16) (x ms) (b r) (i n) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
(defthm anb-method-preserves (implies (and (anlsp anls) (anbp anb) (signed-byte-p 64 r)) (and (anlsp (mv-nth 1 (anb-method m r anls anb))) (anbp (mv-nth 2 (anb-method m r anls anb))))) :hints (("Goal" :use ((:instance anb-fl-is-case (fl 17) (x m) (b r) (i 0) (p 0) (q 0) (anls anls) (anb anb)) (:instance anb-fl-preserves (fl 17) (x m) (b r) (i 0) (p 0) (q 0) (anls anls) (anb anb))) :in-theory (disable anb-fl-preserves))))
;; END anbuild-flag

; ---- THE GUARDS ------------------------------------------------------------------------------------

(verify-guards anb-an)

; ---- A WHOLE ANALYSIS LEAVES ONE WELL-FORMED NODE ------------------------------------------------

; k well-formed nodes on top of old
(defun anb-topk (k new old)
  (if (zp k) (equal new old)
    (and (consp new) (anf-wf (car new)) (anb-topk (- k 1) (cdr new) old))))

; catch entries on top of old, each handler well-formed
(defun anb-catches (new old)
  (declare (xargs :measure (acl2-count new)))
  (if (equal new old) t
    (and (consp new) (anb-catchp (car new)) (anf-wf (anl-nth 2 (car new))) (anb-catches (cdr new) old))))

; how many forms a list form has
(defun anb-len (x) (if (equal (frf-kind x) 3) (len (cdr x)) 0))

; what each member of the clique leaves on the builder when it answers no
; error: one node (most), the first n forms' (anb-listn, anb-methods), a
; pair's each from i (anb-binds, anb-lfinits), a try's catches and its
; finally (anb-try-walk)
(defun anb-eff (fl x i old new)
  (case fl
    ((3 16) (anb-topk (min (nfix i) (anb-len x)) new old))
    ((5 7) (anb-topk (nfix (- (frm-pairs x) (nfix i))) new old))
    (10 (if (equal (anb-try-fin x) 1)
            (and (consp new) (anf-wf (car new)) (anb-catches (cdr new) old))
          (anb-catches new old)))
    (otherwise (anb-topk 1 new old))))

(defthm anb-topk-0 (implies (zp k) (equal (anb-topk k new old) (equal new old))))
(defthm anb-topk-1 (equal (anb-topk 1 new old) (and (consp new) (anf-wf (car new)) (equal (cdr new) old))))
(defthm anb-topk-1-fc (implies (anb-topk 1 new old) (and (consp new) (anf-wf (car new)) (equal (cdr new) old)))
  :rule-classes :forward-chaining)
(defthm anb-topk-push
  (implies (and (anb-topk k s2 s1) (anb-topk 1 s1 s0) (natp k)) (anb-topk (+ 1 k) s2 s0))
  :hints (("Goal" :in-theory (disable anb-topk-1))))
(defthm anb-topk-push3
  (implies (and (anb-topk 1 s2 s1) (anb-topk k s1 s0) (natp k)) (anb-topk (+ 1 k) s2 s0))
  :hints (("Goal" :in-theory (disable anb-topk-push))))
(defthm anb-topk-push2
  (implies (and (anb-topk (+ -1 k) s2 s1) (anb-topk 1 s1 s0) (posp k)) (anb-topk k s2 s0))
  :hints (("Goal" :use ((:instance anb-topk-push (k (+ -1 k)))) :in-theory (disable anb-topk-push anb-topk-1))))

(defthm anb-popn-topk
  (implies (and (anb-topk k l old) (natp k) (anf-wfs acc))
           (and (equal (mv-nth 1 (anb-popn k l acc)) old)
                (anf-wfs (car (anb-popn k l acc)))
                (equal (len (car (anb-popn k l acc))) (+ k (len acc))))))

(defthm anb-wf-not-catch (implies (anf-wf x) (not (anb-catchp x))))
(defthm anb-popc-catches
  (implies (and (anb-catches l old) (not (anb-catchp (car old))) (anf-wfs (anb-handlers acc)))
           (and (equal (mv-nth 1 (anb-popc l acc)) old)
                (anf-wfs (anb-handlers (car (anb-popc l acc)))))))
(defthm anb-popc-node (implies (and (consp l) (anf-wf (car l))) (equal (anb-popc l acc) (mv acc l))))
(defthm anb-catches-refl (anb-catches s s))
(defthm anb-catches-trans
  (implies (and (anb-catches s2 s1) (anb-catches s1 s0)) (anb-catches s2 s0)))

(defthm anl-len-is-len (equal (anl-len l) (len l)))
(defthm anb-len-rest
  (implies (< 1 (frf-len x)) (equal (anb-len (frf-rest x)) (- (anb-len x) 1)))
  :hints (("Goal" :in-theory (enable frf-rest frf-len frf-kind frm-kind))))
(defthm frf-len-le-anb-len (<= (frf-len x) (anb-len x))
  :hints (("Goal" :in-theory (enable frf-len frf-kind frm-kind))) :rule-classes :linear)
(defthm frf-len-0-anb-len (implies (equal (frf-len x) 0) (equal (anb-len x) 0))
  :hints (("Goal" :in-theory (enable frf-len frf-kind frm-kind))))
(defthm frf-len-1-anb-len (implies (equal (frf-len x) 1) (equal (anb-len x) 1))
  :hints (("Goal" :in-theory (enable frf-len frf-kind frm-kind))))
(defthm frf-len-kind (implies (< 0 (frf-len x)) (equal (frf-kind x) 3)) :hints (("Goal" :in-theory (enable frf-len))))
(defthm anb-len-nat (natp (anb-len x)) :rule-classes :type-prescription)
(defthm anf-kind-ok-if (implies (and (integerp n) (<= 2 n) (<= n 3)) (anf-kind-ok 4 i2 n)))
(defthm anf-if-0 (implies (equal (anf-if n) 0) (and (<= 3 n) (<= n 4))) :rule-classes :forward-chaining)
(defthm anb-try-n-le-len (<= (anb-try-n xs) (anb-len xs)) :rule-classes :linear
  :hints (("Goal" :induct (anb-try-n xs) :in-theory (disable anb-len))))
(in-theory (disable anb-len))

(defthm anb-integer-listp-append (implies (and (integer-listp a) (integer-listp b)) (integer-listp (append a b))))
(defthm anb-caps-ints (implies (anlsp anls) (integer-listp (anb-caps i anls))))

; ---- WHAT EACH OF THE BUILDER'S OPERATIONS LEAVES --------------------------------------------------

(defthm anb-node-topk
  (implies (and (anb-topk n (anb-stk anb) s0) (natp n) (anf-kind-ok kind i2 n) (not (member kind '(10 14 18))))
           (anb-topk 1 (anb-stk (anb-node kind i2 n anb)) s0))
  :hints (("Goal" :in-theory (disable anf-kind-ok anb-popn))))
(defthm anb-const-topk (anb-topk 1 (anb-stk (anb-const x anb)) (anb-stk anb)))
(defthm anb-local-topk (anb-topk 1 (anb-stk (anb-local x slot anb)) (anb-stk anb)))
(defthm anb-host-topk
  (implies (equal (car (anb-host x b anls anb)) 0)
           (anb-topk 1 (anb-stk (mv-nth 2 (anb-host x b anls anb))) (anb-stk anb)))
  :hints (("Goal" :use anb-host-push :in-theory (disable anb-host-push))))
(defthm anb-host2-topk
  (implies (equal (car (anb-host2 w x b anls anb)) 0)
           (anb-topk 1 (anb-stk (mv-nth 2 (anb-host2 w x b anls anb))) (anb-stk anb)))
  :hints (("Goal" :use anb-host2-push :in-theory (disable anb-host2-push))))
(defthm anb-meta-topk
  (implies (equal (car (anb-meta x b anls anb)) 0)
           (and (member (mv-nth 1 (anb-meta x b anls anb)) '(0 1))
                (anb-topk (mv-nth 1 (anb-meta x b anls anb)) (anb-stk (mv-nth 3 (anb-meta x b anls anb))) (anb-stk anb))))
  :hints (("Goal" :use anb-host-meta-push :in-theory (disable anb-host-meta-push))))
(defthm anb-def-topk
  (implies (and (anb-topk m (anb-stk anb) s1) (anb-topk i2 s1 s0) (member m '(0 1)) (member i2 '(0 1)))
           (anb-topk 1 (anb-stk (anb-def x i2 m anb)) s0)))
(defthm anb-defend-topk
  (implies (and (equal (car (anb-defend x b i2 anls anb)) 0) (anb-topk i2 (anb-stk anb) s0) (member i2 '(0 1)))
           (anb-topk 1 (anb-stk (mv-nth 2 (anb-defend x b i2 anls anb))) s0))
  :hints (("Goal" :use ((:instance anb-meta-topk)
                        (:instance anb-def-topk (m (mv-nth 1 (anb-meta x b anls anb))) (anb (mv-nth 3 (anb-meta x b anls anb)))
                                   (s1 (anb-stk anb))))
           :in-theory (disable anb-def anb-meta anb-topk anb-topk-1 anb-meta-topk anb-def-topk))))
(defthm anb-catch-topk
  (implies (anb-topk 1 (anb-stk anb) s0) (anb-catches (anb-stk (anb-catch f slot anb)) s0)))
(defthm anb-trynode-topk-0
  (implies (and (anb-catches (anb-stk anb) s1) (anb-topk 1 s1 s0))
           (anb-topk 1 (anb-stk (anb-trynode 0 anb)) s0))
  :hints (("Goal" :in-theory (disable anb-popc anb-catches))))
(defthm anb-trynode-topk-body
  (implies (anb-topk 1 (anb-stk anb) s0) (anb-topk 1 (anb-stk (anb-trynode 0 anb)) s0))
  :hints (("Goal" :use ((:instance anb-trynode-topk-0 (s1 (anb-stk anb)))) :in-theory (disable anb-trynode-topk-0))))
(defthm anb-trynode-topk-1
  (implies (and (anb-catches (cdr (anb-stk anb)) s1) (consp (anb-stk anb)) (anf-wf (car (anb-stk anb))) (anb-topk 1 s1 s0))
           (anb-topk 1 (anb-stk (anb-trynode 1 anb)) s0))
  :hints (("Goal" :in-theory (disable anb-popc anb-catches))))
(defthm anb-fnnode-topk
  (implies (and (anb-topk n (anb-stk anb) s0) (natp n) (integer-listp caps))
           (anb-topk 1 (anb-stk (anb-fnnode n caps anb)) s0))
  :hints (("Goal" :in-theory (disable anb-popn))))

(defthm anb-ops-anbp
  (implies (anbp anb)
           (and (anbp (anb-node kind i2 n anb)) (anbp (anb-const x anb)) (anbp (anb-local x slot anb))
                (anbp (anb-def x i2 m anb)) (anbp (anb-catch f slot anb)) (anbp (anb-trynode fin anb))
                (anbp (anb-fnnode n caps anb)))))
(defthm anb-meta-types
  (implies (and (anlsp anls) (anbp anb))
           (and (anlsp (mv-nth 2 (anb-meta x b anls anb))) (anbp (mv-nth 3 (anb-meta x b anls anb))))))

(in-theory (disable anb-node anb-const anb-local anb-def anb-defend anb-meta anb-catch anb-trynode anb-fnnode anb-popn anb-popc))

; THE INDUCTION CLOSED: every member of the clique, answering no error,
; leaves what anb-eff says on the builder
(defthm anb-fl-wf
  (implies (and (equal (car (anb-fl fl x b i p q anls anb)) 0) (anlsp anls) (anbp anb) (anb-hyp fl b i p q))
           (anb-eff fl x i (anb-stk anb) (anb-stk (mv-nth 2 (anb-fl fl x b i p q anls anb)))))
  :hints (("Goal" :induct (anb-fl fl x b i p q anls anb)
           :expand ((anb-fl fl x b i p q anls anb))
           :in-theory (disable anf-if anf-def anf-quote anf-throw anf-set anf-set-target anf-dot anf-new anf-catch
                               anl-shape anl-name-code frm-pairs anb-topk anb-catches anb-caps anb-topk-1))))

; and so one form: a whole analysis with no error leaves exactly one node
; over what was there, well-formed by anpass's reads, every subtree so
(defthm anb-an-wf
  (implies (and (equal (car (anb-an x b anls anb)) 0) (anlsp anls) (anbp anb) (signed-byte-p 64 b))
           (and (consp (anb-stk (mv-nth 2 (anb-an x b anls anb))))
                (anf-wf (car (anb-stk (mv-nth 2 (anb-an x b anls anb)))))
                (equal (cdr (anb-stk (mv-nth 2 (anb-an x b anls anb)))) (anb-stk anb))))
  :hints (("Goal" :use ((:instance anb-fl-is-case (fl 1) (i 0) (p 0) (q 0))
                        (:instance anb-fl-wf (fl 1) (i 0) (p 0) (q 0)))
           :in-theory (disable anb-fl-wf anb-an))))

; well-formed is a node anpass's reads decode, every child one: its
; theorems (anp-live-spec, tr-sound, anp-clears-sound, tr-tail) are of
; any tree; this one is the analyzer's, its kinds and its children's
; counts the ones exec.inc runs
(defthm anf-kind-ok-kind (implies (anf-kind-ok k i2 nk) (and (integerp k) (<= 1 k) (<= k 28)))
  :rule-classes :forward-chaining)
(defthm anp-nth-is-nth (implies (natp i) (equal (anp-nth i l) (nth i l))))
(defthm anf-wf-ast-p (implies (anf-wf x) (ast-p x))
  :hints (("Goal" :expand ((anf-wf x)) :in-theory (e/d (ast-p) (anf-kind-ok)))))

(defthm anb-an-ast-p
  (implies (and (equal (car (anb-an x b anls anb)) 0) (anlsp anls) (anbp anb) (signed-byte-p 64 b))
           (ast-p (car (anb-stk (mv-nth 2 (anb-an x b anls anb))))))
  :hints (("Goal" :use anb-an-wf :in-theory (disable anb-an-wf anb-an))))
