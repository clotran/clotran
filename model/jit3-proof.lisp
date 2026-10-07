; clotran's JIT, formally (PLAN step 31, stage 2b): the theorems.
;
;   jit3-sim      the register-allocated machine code is the bytecode,
;                 block for block: memory below the frame's base is the
;                 bytecode's stack, and each slot of the frame is where
;                 the allocator's state says -- its register, memory, or
;                 both -- for any bytecode the depth check passes
;   jit3-correct  and a compiled program answers its meaning through it

(in-package "ACL2")

(include-book "jit3")
(include-book "jit2-proof")

; ---- STRAIGHT-LINE CODE -------------------------------------------------------------
;
; Loads, stores, moves and register arithmetic: each goes on to the next
; instruction. A run of them is xseq, so a block's effect can be taken
; piece by piece.

(defun straight-ins (ins)
  (member-equal (car ins) '(:movi :ldr :str :mov :add :lt :capt)))

(defun straightp (seq)
  (if (atom seq) t (and (straight-ins (car seq)) (straightp (cdr seq)))))

; what a straight instruction does, wherever it sits
(defun xstep (ins ns)
  (let* ((pc (car ns)) (fb (nfix (cadr ns))) (sp (nfix (caddr ns))) (stk (cadddr ns))
         (ctl (car (cddddr ns))) (x (cadr (cddddr ns))))
    (case (car ins)
      (:movi (list (1+ pc) fb sp stk ctl (xset (cadr ins) (caddr ins) x)))
      (:ldr (list (1+ pc) fb sp stk ctl
                  (xset (cadr ins) (nth (nfix (+ (nbase (caddr ins) fb sp) (ifix (cadddr ins)))) stk) x)))
      (:str (list (1+ pc) fb sp
                  (update-nth (nfix (+ (nbase (caddr ins) fb sp) (ifix (cadddr ins)))) (xr (cadr ins) x) stk)
                  ctl x))
      (:mov (list (1+ pc) fb sp stk ctl (xset (cadr ins) (xr (caddr ins) x) x)))
      (:add (list (1+ pc) fb sp stk ctl
                  (xset (cadr ins) (+ (fix (xr (caddr ins) x)) (fix (xr (cadddr ins) x))) x)))
      (:lt (list (1+ pc) fb sp stk ctl
                 (xset (cadr ins) (bool (< (rfix (xr (caddr ins) x)) (rfix (xr (cadddr ins) x)))) x)))
      (:capt (list (1+ pc) fb sp stk ctl
                   (xset (cadr ins) (nth (nfix (caddr ins)) (clo-caps (xr (cadr ins) x))) x)))
      (otherwise ns))))

(defun xseq (seq ns)
  (if (atom seq) ns (xseq (cdr seq) (xstep (car seq) ns))))

(defthm nstep-straight
  (implies (and (natp (car ns)) (equal (nth (car ns) (car np)) ins) (straight-ins ins))
           (equal (nstep np ns) (xstep ins ns)))
  :hints (("Goal" :in-theory (enable nstep))))

(defthm xstep-pc
  (implies (and (straight-ins ins) (natp (car ns))) (equal (car (xstep ins ns)) (1+ (car ns)))))

(defthm run-straight
  (implies (and (natp (car ns)) (ncode-at (car np) (car ns) seq) (straightp seq))
           (equal (nrun np ns (len seq)) (xseq seq ns)))
  :hints (("Goal" :induct (xseq seq ns) :in-theory (e/d (nrun-step) (xstep nstep nrun-plus))
                  :expand ((ncode-at (car np) (car ns) seq)))))

(defthm xseq-append (equal (xseq (append a b) ns) (xseq b (xseq a ns)))
  :hints (("Goal" :induct (xseq a ns) :in-theory (disable xstep))))
(defthm straightp-append (equal (straightp (append a b)) (and (straightp a) (straightp b))))
(defthm ncode-at-append
  (implies (natp a)
           (equal (ncode-at code a (append b c))
                  (and (ncode-at code a b) (ncode-at code (+ a (len b)) c))))
  :hints (("Goal" :induct (ncode-at code a b))))

; ---- WHAT A STRAIGHT SEQUENCE DOES TO MEMORY AND REGISTERS ----------------------------

; the allocator's code addresses memory by FB only
(defun fb-only (seq)
  (if (atom seq)
      t
    (and (or (not (member-equal (car (car seq)) '(:ldr :str))) (eq (caddr (car seq)) :fb))
         (fb-only (cdr seq)))))

; (memory . registers) after one instruction, and after seq
(defun sexec1 (ins fb mem x)
  (case (car ins)
    (:movi (cons mem (xset (cadr ins) (caddr ins) x)))
    (:ldr (cons mem (xset (cadr ins) (nth (nfix (+ fb (ifix (cadddr ins)))) mem) x)))
    (:str (cons (update-nth (nfix (+ fb (ifix (cadddr ins)))) (xr (cadr ins) x) mem) x))
    (:mov (cons mem (xset (cadr ins) (xr (caddr ins) x) x)))
    (:add (cons mem (xset (cadr ins) (+ (fix (xr (caddr ins) x)) (fix (xr (cadddr ins) x))) x)))
    (:lt (cons mem (xset (cadr ins) (bool (< (rfix (xr (caddr ins) x)) (rfix (xr (cadddr ins) x)))) x)))
    (:capt (cons mem (xset (cadr ins) (nth (nfix (caddr ins)) (clo-caps (xr (cadr ins) x))) x)))
    (otherwise (cons mem x))))

(defun sexec (seq fb mem x)
  (if (atom seq)
      (cons mem x)
    (let ((r (sexec1 (car seq) fb mem x)))
      (sexec (cdr seq) fb (car r) (cdr r)))))

(defun xs-ind (seq pc fb mem x)
  (if (atom seq)
      (list pc fb mem x)
    (let ((r (sexec1 (car seq) fb mem x)))
      (xs-ind (cdr seq) (1+ pc) fb (car r) (cdr r)))))

(defthm xstep-is-sexec1
  (implies (and (straight-ins ins) (or (not (member-equal (car ins) '(:ldr :str))) (eq (caddr ins) :fb))
                (natp pc) (natp fb) (natp sp))
           (equal (xstep ins (list pc fb sp mem ctl x))
                  (list (1+ pc) fb sp (car (sexec1 ins fb mem x)) ctl (cdr (sexec1 ins fb mem x)))))
  :hints (("Goal" :in-theory (enable nbase))))

(defthm xseq-is-sexec
  (implies (and (straightp seq) (fb-only seq) (natp pc) (natp fb) (natp sp))
           (equal (xseq seq (list pc fb sp mem ctl x))
                  (list (+ pc (len seq)) fb sp (car (sexec seq fb mem x)) ctl (cdr (sexec seq fb mem x)))))
  :hints (("Goal" :induct (xs-ind seq pc fb mem x) :in-theory (disable xstep sexec1))))

(defthm sexec-append
  (equal (sexec (append a b) fb mem x)
         (sexec b fb (car (sexec a fb mem x)) (cdr (sexec a fb mem x))))
  :hints (("Goal" :induct (sexec a fb mem x))))

(defthm fb-only-append (equal (fb-only (append a b)) (and (fb-only a) (fb-only b))))
(in-theory (disable xseq-is-sexec))

; ---- THE RELATION ----------------------------------------------------------------------
;
; Slot j of the frame at fb, by the allocator's state: :r its register
; holds it, :b its register and memory, anything else memory.

(defun slot-ok (j st fb stk mem x)
  (let ((v (nth (+ fb j) stk)) (s (st-get j st)))
    (cond ((eq s :r) (equal (nth j x) v))
          ((eq s :b) (and (equal (nth j x) v) (equal (nth (+ fb j) mem) v)))
          (t (equal (nth (+ fb j) mem) v)))))

(defun-sk slots-ok (d st fb stk mem x)
  (forall j (implies (and (natp j) (< j (nfix d))) (slot-ok j st fb stk mem x))))
(in-theory (disable slots-ok))

; below the frame: memory is the stack
(defun-sk below-ok (fb stk mem)
  (forall a (implies (and (natp a) (< a (nfix fb))) (equal (nth a mem) (nth a stk)))))
(in-theory (disable below-ok))

; ---- THE ALLOCATOR'S PIECES ------------------------------------------------------------
;
; Registers: 0 .. K-1 the cached slots, K and K+1 scratch.

(defmacro scratchp (s) `(or (equal ,s (s0)) (equal ,s (s1))))

(defthm st-get-st-set
  (equal (st-get i (st-set j v st))
         (if (and (equal (nfix i) (nfix j)) (< (nfix j) (sk))) v (st-get i st))))
(defthm st-get-past (implies (<= (sk) (nfix j)) (equal (st-get j st) :m)))
(in-theory (disable st-get st-set))

; a scratch register is no slot's
(defthm slots-ok-scratch
  (implies (and (slots-ok d st fb stk mem x) (natp q) (<= (sk) q))
           (slots-ok d st fb stk mem (update-nth q v x)))
  :hints (("Goal" :expand ((slots-ok d st fb stk mem (update-nth q v x)))
                  :use ((:instance slots-ok-necc (j (slots-ok-witness d st fb stk mem (update-nth q v x))))))))

; a slot loaded into its register from memory: now in both
(defthm slots-ok-load
  (implies (and (slots-ok d st fb stk mem x) (natp j) (< j (sk)) (< j (nfix d)) (natp fb)
                (not (member-equal (st-get j st) '(:r :b))))
           (slots-ok d (st-set j :b st) fb stk mem (update-nth j (nth (+ fb j) mem) x)))
  :hints (("Goal" :expand ((slots-ok d (st-set j :b st) fb stk mem (update-nth j (nth (+ fb j) mem) x)))
                  :use ((:instance slots-ok-necc
                                   (j (slots-ok-witness d (st-set j :b st) fb stk mem (update-nth j (nth (+ fb j) mem) x))))
                        (:instance slots-ok-necc)))))

(defthm slot-ok-of-slots-ok
  (implies (and (slots-ok d st fb stk mem x) (natp j) (< j (nfix d)))
           (slot-ok j st fb stk mem x))
  :hints (("Goal" :use slots-ok-necc)))

; READ slot j into a register: its value there, the frame still related,
; no other register touched, memory untouched
(defthm rdl-sem
  (implies (and (slots-ok d st fb stk mem x) (natp j) (< j (nfix d)) (scratchp s) (natp fb))
           (let* ((c (mv-nth 0 (rdl j s st))) (r (mv-nth 1 (rdl j s st))) (st2 (mv-nth 2 (rdl j s st)))
                  (res (sexec c fb mem x)))
             (and (straightp c) (fb-only c)
                  (equal (car res) mem)
                  (equal r (if (< j (sk)) j s))
                  (equal (nth r (cdr res)) (nth (+ fb j) stk))
                  (slots-ok d st2 fb stk mem (cdr res))
                  (implies (and (natp q) (not (equal q r))) (equal (nth q (cdr res)) (nth q x))))))
  :hints (("Goal" :in-theory (disable slots-ok-necc slot-ok-of-slots-ok slots-ok-load)
                  :use ((:instance slot-ok-of-slots-ok)
                        (:instance slots-ok-load)))))

; fewer slots, still related
(defthm slots-ok-smaller
  (implies (and (slots-ok d st fb stk mem x) (<= (nfix d2) (nfix d)))
           (slots-ok d2 st fb stk mem x))
  :hints (("Goal" :expand ((slots-ok d2 st fb stk mem x))
                  :use ((:instance slots-ok-necc (j (slots-ok-witness d2 st fb stk mem x)))))))

; a register at or above the depth holds no slot below it
(defthm slots-ok-reg-above
  (implies (and (slots-ok d st fb stk mem x) (natp q) (<= (nfix d) q))
           (slots-ok d st fb stk mem (update-nth q v x)))
  :hints (("Goal" :expand ((slots-ok d st fb stk mem (update-nth q v x)))
                  :use ((:instance slots-ok-necc (j (slots-ok-witness d st fb stk mem (update-nth q v x))))))))

; WRITE register r's value to slot j, the new top -- three shapes
(defmacro stk2 () '(update-nth (+ fb j) v stk))

; a deep slot: stored
(defthm wrl-deep
  (implies (and (slots-ok j st fb stk mem x) (natp j) (<= (sk) j) (natp fb))
           (slots-ok (1+ j) st fb (stk2) (update-nth (+ fb j) v mem) x))
  :hints (("Goal" :expand ((slots-ok (1+ j) st fb (stk2) (update-nth (+ fb j) v mem) x))
                  :use ((:instance slots-ok-necc (d j)
                                   (j (slots-ok-witness (1+ j) st fb (stk2) (update-nth (+ fb j) v mem) x)))))))

; a slot whose register has the value: marked dirty
(defthm wrl-here
  (implies (and (slots-ok j st fb stk mem x) (natp j) (< j (sk)) (natp fb))
           (slots-ok (1+ j) (st-set j :r st) fb (update-nth (+ fb j) (nth j x) stk) mem x))
  :hints (("Goal" :expand ((slots-ok (1+ j) (st-set j :r st) fb (update-nth (+ fb j) (nth j x) stk) mem x))
                  :use ((:instance slots-ok-necc (d j)
                                   (j (slots-ok-witness (1+ j) (st-set j :r st) fb (update-nth (+ fb j) (nth j x) stk)
                                                        mem x)))))))

; a slot whose register takes the value: moved there, dirty
(defthm wrl-move
  (implies (and (slots-ok j st fb stk mem x) (natp j) (< j (sk)) (natp fb))
           (slots-ok (1+ j) (st-set j :r st) fb (stk2) mem (update-nth j v x)))
  :hints (("Goal" :expand ((slots-ok (1+ j) (st-set j :r st) fb (stk2) mem (update-nth j v x)))
                  :use ((:instance slots-ok-necc (d j)
                                   (j (slots-ok-witness (1+ j) (st-set j :r st) fb (stk2) mem (update-nth j v x))))))))

(defthm below-ok-write-above
  (implies (and (below-ok fb stk mem) (natp fb) (natp a) (<= fb a))
           (and (below-ok fb (update-nth a v stk) mem)
                (below-ok fb (update-nth a v stk) (update-nth a v mem))))
  :hints (("Goal" :expand ((below-ok fb (update-nth a v stk) mem)
                           (below-ok fb (update-nth a v stk) (update-nth a v mem)))
                  :use ((:instance below-ok-necc (a (below-ok-witness fb (update-nth a v stk) mem)))
                        (:instance below-ok-necc (a (below-ok-witness fb (update-nth a v stk) (update-nth a v mem))))))))

(defthm wrl-sem
  (implies (and (slots-ok j st fb stk mem x) (natp j) (natp fb) (natp r))
           (let* ((c (mv-nth 0 (wrl j r st))) (st2 (mv-nth 1 (wrl j r st)))
                  (res (sexec c fb mem x)) (v (nth r x)))
             (and (straightp c) (fb-only c)
                  (slots-ok (1+ j) st2 fb (stk2) (car res) (cdr res))
                  (implies (below-ok fb stk mem) (below-ok fb (stk2) (car res))))))
  :hints (("Goal" :in-theory (disable wrl-deep wrl-here wrl-move)
                  :cases ((<= (sk) j) (equal r j))
                  :use ((:instance wrl-deep (v (nth r x)))
                        (:instance wrl-here)
                        (:instance wrl-move (v (nth r x)))))))

; SPILL: dirty slots stored, now in both
(defthm slots-ok-store
  (implies (and (slots-ok d st fb stk mem x) (natp i) (< i (nfix d)) (< i (sk)) (natp fb)
                (equal (st-get i st) :r))
           (slots-ok d (st-set i :b st) fb stk (update-nth (+ fb i) (nth i x) mem) x))
  :hints (("Goal" :expand ((slots-ok d (st-set i :b st) fb stk (update-nth (+ fb i) (nth i x) mem) x))
                  :use ((:instance slots-ok-necc
                                   (j (slots-ok-witness d (st-set i :b st) fb stk (update-nth (+ fb i) (nth i x) mem) x)))
                        (:instance slots-ok-necc (j i))))))

(defthm below-ok-store-above
  (implies (and (below-ok fb stk mem) (natp fb) (natp i))
           (below-ok fb stk (update-nth (+ fb i) v mem)))
  :hints (("Goal" :expand ((below-ok fb stk (update-nth (+ fb i) v mem)))
                  :use ((:instance below-ok-necc (a (below-ok-witness fb stk (update-nth (+ fb i) v mem))))))))

; no dirty slot from j below b
(defun no-dirty (j b st)
  (declare (xargs :measure (nfix (- (sk) (nfix j)))))
  (if (or (not (natp j)) (>= j (sk)))
      t
    (and (or (>= j (nfix b)) (not (eq (st-get j st) :r))) (no-dirty (1+ j) b st))))

(defun spill-ind (j b st fb mem x)
  (declare (xargs :measure (nfix (- (sk) (nfix j)))))
  (if (or (not (natp j)) (>= j (sk)))
      (list b st fb mem x)
    (spill-ind (1+ j) b st fb
               (if (and (< j (nfix b)) (eq (st-get j st) :r)) (update-nth (nfix (+ fb j)) (nth j x) mem) mem)
               x)))

(defthm spilll-straight
  (and (straightp (car (spilll j b st))) (fb-only (car (spilll j b st))))
  :hints (("Goal" :induct (spilll j b st))))

(defthm spilll-regs (equal (cdr (sexec (car (spilll j b st)) fb mem x)) x)
  :hints (("Goal" :induct (spill-ind j b st fb mem x))))

(defthm spilll-state-below
  (implies (and (natp i) (< i (nfix j)))
           (equal (st-get i (mv-nth 1 (spilll j b st))) (st-get i st)))
  :hints (("Goal" :induct (spilll j b st))))

(defthm spilll-mem-below
  (implies (and (natp i) (natp j) (< i j) (natp fb))
           (equal (nth (+ fb i) (car (sexec (car (spilll j b st)) fb mem x))) (nth (+ fb i) mem)))
  :hints (("Goal" :induct (spill-ind j b st fb mem x))))

; storing a dirty slot's register to its own address changes no relation
(defthm slots-ok-store-keep
  (implies (and (slots-ok d st fb stk mem x) (natp i) (< i (sk)) (natp fb) (equal (st-get i st) :r))
           (slots-ok d st fb stk (update-nth (+ fb i) (nth i x) mem) x))
  :hints (("Goal" :expand ((slots-ok d st fb stk (update-nth (+ fb i) (nth i x) mem) x))
                  :use ((:instance slots-ok-necc
                                   (j (slots-ok-witness d st fb stk (update-nth (+ fb i) (nth i x) mem) x)))))))

; a dirty slot whose memory has caught up: in both
(defthm slots-ok-mark-b
  (implies (and (slots-ok d st fb stk mem x) (natp i) (< i (nfix d)) (< i (sk)) (natp fb)
                (equal (st-get i st) :r) (equal (nth (+ fb i) mem) (nth i x)))
           (slots-ok d (st-set i :b st) fb stk mem x))
  :hints (("Goal" :expand ((slots-ok d (st-set i :b st) fb stk mem x))
                  :use ((:instance slots-ok-necc (j (slots-ok-witness d (st-set i :b st) fb stk mem x)))
                        (:instance slots-ok-necc (j i))))))

(defthm no-dirty-st-set-below
  (implies (and (natp i) (< i (nfix j))) (equal (no-dirty j b (st-set i v st)) (no-dirty j b st)))
  :hints (("Goal" :induct (no-dirty j b st))))

(defthm spilll-sem
  (implies (and (slots-ok d st fb stk mem x) (natp fb) (<= (nfix b) (nfix d)))
           (let ((st2 (mv-nth 1 (spilll j b st))) (m2 (car (sexec (car (spilll j b st)) fb mem x))))
             (and (slots-ok d st2 fb stk m2 x)
                  (no-dirty j b st2)
                  (implies (below-ok fb stk mem) (below-ok fb stk m2)))))
  :hints (("Goal" :induct (spill-ind j b st fb mem x) :in-theory (disable slots-ok-mark-b))
          ("Subgoal *1/2" :use ((:instance slots-ok-mark-b (i j) (st (mv-nth 1 (spilll (1+ j) b st)))
                                           (mem (car (sexec (car (spilll (1+ j) b st)) fb
                                                            (update-nth (+ fb j) (nth j x) mem) x))))
                                (:instance spilll-mem-below (i j) (j (1+ j)) (mem (update-nth (+ fb j) (nth j x) mem)))))))

; everything below the depth in memory
(defun-sk mem-ok (d fb stk mem)
  (forall j (implies (and (natp j) (< j (nfix d))) (equal (nth (+ fb j) mem) (nth (+ fb j) stk)))))
(in-theory (disable mem-ok))

(defthm no-dirty-get
  (implies (and (no-dirty j b st) (natp j) (natp i) (<= j i) (< i (nfix b))) (not (equal (st-get i st) :r)))
  :hints (("Goal" :induct (no-dirty j b st))))

(defthm mem-ok-of-clean
  (implies (and (slots-ok d st fb stk mem x) (no-dirty 0 d st))
           (mem-ok d fb stk mem))
  :hints (("Goal" :expand ((mem-ok d fb stk mem))
                  :use ((:instance slots-ok-necc (j (mem-ok-witness d fb stk mem)))
                        (:instance no-dirty-get (j 0) (b d) (i (mem-ok-witness d fb stk mem)))))))

; a frame held entirely in memory is related in the all-:m state
(defthm st-get-st-mem (equal (st-get j (st-mem)) :m)
  :hints (("Goal" :in-theory (enable st-get)
                  :cases ((equal (nfix j) 0) (equal (nfix j) 1) (equal (nfix j) 2) (equal (nfix j) 3)
                          (equal (nfix j) 4) (equal (nfix j) 5) (equal (nfix j) 6) (equal (nfix j) 7)))))

(defthm st-get-m-const (equal (st-get j (quote (:m :m :m :m :m :m :m :m))) :m)
  :hints (("Goal" :use st-get-st-mem)))

(defthm slots-ok-st-mem
  (implies (mem-ok d fb stk mem) (slots-ok d (st-mem) fb stk mem x))
  :hints (("Goal" :in-theory (disable (:e st-mem) st-mem)
                  :expand ((slots-ok d (st-mem) fb stk mem x))
                  :use ((:instance mem-ok-necc (j (slots-ok-witness d (st-mem) fb stk mem x)))))))

; dropping the dead slots' states changes nothing below the depth
(defthm st-get-dropl
  (implies (natp i)
           (equal (st-get i (dropl j d st))
                  (if (and (natp j) (<= j i) (<= (nfix d) i) (< i (sk))) :m (st-get i st))))
  :hints (("Goal" :induct (dropl j d st))))

(defthm slots-ok-dropl
  (implies (and (slots-ok d2 st fb stk mem x) (<= (nfix d2) (nfix d)))
           (slots-ok d2 (dropl j d st) fb stk mem x))
  :hints (("Goal" :expand ((slots-ok d2 (dropl j d st) fb stk mem x))
                  :use ((:instance slots-ok-necc (d d2) (j (slots-ok-witness d2 (dropl j d st) fb stk mem x)))))))

; ---- THE TRANSLATION'S STRUCTURE --------------------------------------------------------

; one pc's translation from its entry state: its code, and the state
; the next pc's code is translated from (before that pc's own boundary)
(defun lentry (pc bnd st) (if (member-equal pc bnd) (st-mem) st))

(defun lstep (ins pc dmap bnd st)
  (mv-let (blk st2) (jblockl ins (nfix (nth pc dmap)) (nfix (cadr ins)) st)
    (let ((into (member-equal (1+ pc) bnd)))
      (mv-let (cs st3) (if into (spilll 0 (nfix (nth (1+ pc) dmap)) st2) (mv nil st2))
        (cons (append blk cs) (if into (st-mem) st3))))))

; the entry states, as lblocks threads them
(defun lstates (rest pc dmap bnd st)
  (if (atom rest)
      nil
    (let ((e (lentry pc bnd st)))
      (cons e (lstates (cdr rest) (1+ pc) dmap bnd (cdr (lstep (car rest) pc dmap bnd e)))))))

(defthm lblocks-is
  (equal (lblocks rest pc dmap bnd st)
         (if (atom rest)
             nil
           (cons (car (lstep (car rest) pc dmap bnd (lentry pc bnd st)))
                 (lblocks (cdr rest) (1+ pc) dmap bnd (cdr (lstep (car rest) pc dmap bnd (lentry pc bnd st)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable jblockl spilll dropl (:e st-mem)) :expand ((lblocks rest pc dmap bnd st)))))

(defun ls-ind (p rest pc st dmap bnd)
  (if (or (zp p) (atom rest))
      (list p rest pc st)
    (ls-ind (1- p) (cdr rest) (1+ pc) (cdr (lstep (car rest) pc dmap bnd (lentry pc bnd st))) dmap bnd)))

; block p is translated from entry state p
(defthm lblocks-nth
  (implies (and (natp p) (< p (len rest)) (natp pc))
           (equal (nth p (lblocks rest pc dmap bnd st))
                  (car (lstep (nth p rest) (+ pc p) dmap bnd (nth p (lstates rest pc dmap bnd st))))))
  :hints (("Goal" :induct (ls-ind p rest pc st dmap bnd) :in-theory (disable lstep lentry lblocks jblockl spilll))
          ("Subgoal *1/3" :use ((:instance lblocks-is)))
          ("Subgoal *1/2" :use ((:instance lblocks-is)))
          ("Subgoal *1/1" :use ((:instance lblocks-is)))))

; and entry state p+1 is its exit state, or all :m at a boundary
(defthm lstates-succ
  (implies (and (natp p) (< (1+ p) (len rest)) (natp pc))
           (equal (nth (1+ p) (lstates rest pc dmap bnd st))
                  (lentry (+ pc p 1) bnd
                          (cdr (lstep (nth p rest) (+ pc p) dmap bnd (nth p (lstates rest pc dmap bnd st)))))))
  :hints (("Goal" :induct (ls-ind p rest pc st dmap bnd) :in-theory (disable lstep lentry jblockl spilll)
                  :expand ((lstates rest pc dmap bnd st) (:free (s) (lstates (cdr rest) (+ 1 pc) dmap bnd s))))))

(defthm lstates-at-boundary
  (implies (and (natp p) (< p (len rest)) (natp pc) (member-equal (+ pc p) bnd))
           (equal (nth p (lstates rest pc dmap bnd st)) (st-mem)))
  :hints (("Goal" :induct (ls-ind p rest pc st dmap bnd) :in-theory (disable lstep (:e st-mem)))))

; ---- EACH STRAIGHT BYTECODE'S BLOCK, ON MEMORY AND REGISTERS ---------------------------
;
; From a frame related at depth d in state st, the block leaves the
; frame related to the bytecode's stack after the step, at its new depth.

(defmacro bsem-concl (d2 stk2)
  `(let ((res (sexec (mv-nth 0 r) fb mem x)))
     (and (straightp (mv-nth 0 r)) (fb-only (mv-nth 0 r))
          (slots-ok ,d2 (mv-nth 1 r) fb ,stk2 (car res) (cdr res))
          (implies (below-ok fb stk mem) (below-ok fb ,stk2 (car res))))))

(defthm bsem-push
  (implies (and (slots-ok d st fb stk mem x) (natp d) (natp fb))
           (let ((r (jblockl (list :push v) d tgt st)))
             (bsem-concl (1+ d) (update-nth (+ fb d) v stk))))
  :hints (("Goal" :cases ((< d (sk)))
                  :in-theory (disable wrl-deep wrl-move)
                  :use ((:instance wrl-move (j d))
                        (:instance wrl-deep (j d) (x (update-nth (s0) v x)))))))

(defthm bsem-load
  (implies (and (slots-ok d st fb stk mem x) (natp d) (natp fb) (natp i) (< i d))
           (let ((r (jblockl (list :load i) d tgt st)))
             (bsem-concl (1+ d) (update-nth (+ fb d) (nth (+ fb i) stk) stk))))
  :hints (("Goal" :in-theory (disable rdl-sem wrl-sem)
                  :use ((:instance rdl-sem (j i) (s (s0)))
                        (:instance wrl-sem (j d) (r (mv-nth 1 (rdl i (s0) st))) (st (mv-nth 2 (rdl i (s0) st)))
                                   (x (cdr (sexec (mv-nth 0 (rdl i (s0) st)) fb mem x))))))))

(defmacro ra-x () '(cdr (sexec (mv-nth 0 (rdl (- d 2) (s0) st)) fb mem x)))
(defmacro ra-st () '(mv-nth 2 (rdl (- d 2) (s0) st)))
(defmacro rb-x () '(cdr (sexec (mv-nth 0 (rdl (- d 1) (s1) (ra-st))) fb mem (ra-x))))
(defmacro rb-st () '(mv-nth 2 (rdl (- d 1) (s1) (ra-st))))
(defmacro bdst () '(if (< (- d 2) (sk)) (- d 2) (s0)))

(defun binv (op a b) (if (eq op :add) (+ (fix a) (fix b)) (bool (< (rfix a) (rfix b)))))

(defthm bsem-binop
  (implies (and (slots-ok d st fb stk mem x) (natp d) (<= 2 d) (natp fb) (member-equal op '(:add :lt)))
           (let ((r (binopl op d st)))
             (bsem-concl (1- d) (update-nth (+ fb (- d 2))
                                            (binv op (nth (+ fb (- d 2)) stk) (nth (+ fb (- d 1)) stk)) stk))))
  :hints (("Goal" :in-theory (disable rdl-sem wrl-sem slots-ok-reg-above slots-ok-scratch slots-ok-smaller)
                  :use ((:instance rdl-sem (j (- d 2)) (s (s0)))
                        (:instance rdl-sem (j (- d 1)) (s (s1)) (st (ra-st)) (x (ra-x)))
                        (:instance slots-ok-smaller (d2 (- d 2)) (st (rb-st)) (x (rb-x)))
                        (:instance slots-ok-reg-above (d (- d 2)) (st (rb-st)) (x (rb-x)) (q (bdst))
                                   (v (binv op (nth (+ fb (- d 2)) stk) (nth (+ fb (- d 1)) stk))))
                        (:instance slots-ok-scratch (d (- d 2)) (st (rb-st)) (x (rb-x)) (q (bdst))
                                   (v (binv op (nth (+ fb (- d 2)) stk) (nth (+ fb (- d 1)) stk))))
                        (:instance wrl-sem (j (- d 2)) (r (bdst)) (st (rb-st))
                                   (x (update-nth (bdst) (binv op (nth (+ fb (- d 2)) stk) (nth (+ fb (- d 1)) stk))
                                                  (rb-x))))))))

(defmacro jblockl-code-slide (d st) `(mv-nth 0 (jblockl (list :slide) ,d tgt ,st)))

(defthm bsem-slide
  (implies (and (slots-ok d st fb stk mem x) (natp d) (<= 2 d) (natp fb))
           (let ((r (jblockl (list :slide) d tgt st)))
             (and (straightp (mv-nth 0 r)) (fb-only (mv-nth 0 r))
                  (let ((res (sexec (mv-nth 0 r) fb mem x))
                        (stk2 (update-nth (+ fb (- d 2)) (nth (+ fb (- d 1)) stk) stk)))
                    (and (slots-ok (1- d) (mv-nth 1 r) fb stk2 (car res) (cdr res))
                         (implies (below-ok fb stk mem) (below-ok fb stk2 (car res))))))))
  :hints (("Goal" :in-theory (disable rdl-sem wrl-sem slots-ok-smaller slots-ok-dropl)
                  :use ((:instance rdl-sem (j (- d 1)) (s (s0)))
                        (:instance slots-ok-smaller (d2 (- d 2)) (st (mv-nth 2 (rdl (- d 1) (s0) st)))
                                   (x (cdr (sexec (mv-nth 0 (rdl (- d 1) (s0) st)) fb mem x))))
                        (:instance wrl-sem (j (- d 2)) (r (mv-nth 1 (rdl (- d 1) (s0) st)))
                                   (st (mv-nth 2 (rdl (- d 1) (s0) st)))
                                   (x (cdr (sexec (mv-nth 0 (rdl (- d 1) (s0) st)) fb mem x))))
                        (:instance slots-ok-dropl (j 0) (d (1- d)) (d2 (1- d))
                                   (st (mv-nth 1 (wrl (- d 2) (mv-nth 1 (rdl (- d 1) (s0) st))
                                                      (mv-nth 2 (rdl (- d 1) (s0) st)))))
                                   (stk (update-nth (+ fb (- d 2)) (nth (+ fb (- d 1)) stk) stk))
                                   (mem (car (sexec (jblockl-code-slide d st) fb mem x)))
                                   (x (cdr (sexec (jblockl-code-slide d st) fb mem x))))))))

(defmacro cr () '(mv-nth 1 (rdl self (s0) st)))
(defmacro cst () '(mv-nth 2 (rdl self (s0) st)))
(defmacro cx () '(cdr (sexec (mv-nth 0 (rdl self (s0) st)) fb mem x)))
(defmacro cdst () '(if (< d (sk)) d (s0)))
(defmacro cval () '(nth (nfix i) (clo-caps (nth (+ fb self) stk))))

(defthm bsem-capt
  (implies (and (slots-ok d st fb stk mem x) (natp d) (natp fb) (natp self) (< self d))
           (let ((r (jblockl (list :capt self i) d tgt st)))
             (bsem-concl (1+ d) (update-nth (+ fb d) (cval) stk))))
  :hints (("Goal" :in-theory (disable rdl-sem wrl-sem slots-ok-reg-above slots-ok-scratch)
                  :use ((:instance rdl-sem (j self) (s (s0)))
                        (:instance slots-ok-reg-above (st (cst)) (x (cx)) (q (cdst)) (v (nth (cr) (cx))))
                        (:instance slots-ok-scratch (st (cst)) (x (cx)) (q (cdst)) (v (nth (cr) (cx))))
                        (:instance slots-ok-reg-above (st (cst)) (x (update-nth (cdst) (nth (cr) (cx)) (cx))) (q (cdst))
                                   (v (cval)))
                        (:instance slots-ok-scratch (st (cst)) (x (update-nth (cdst) (nth (cr) (cx)) (cx))) (q (cdst))
                                   (v (cval)))
                        (:instance slots-ok-reg-above (st (cst)) (x (cx)) (q (cdst)) (v (cval)))
                        (:instance slots-ok-scratch (st (cst)) (x (cx)) (q (cdst)) (v (cval)))
                        (:instance wrl-sem (j d) (r (cdst)) (st (cst))
                                   (x (update-nth (cdst) (cval) (update-nth (cdst) (nth (cr) (cx)) (cx)))))
                        (:instance wrl-sem (j d) (r (cdst)) (st (cst)) (x (update-nth (cdst) (cval) (cx))))))))

; ---- THE SUFFIX: falling into a boundary --------------------------------------------

(defthm suffix-sem
  (implies (and (slots-ok d2 st2 fb stk2 m1 x1) (natp fb) (natp d2))
           (let* ((into (member-equal (1+ pc) bnd))
                  (sr (if into (spilll 0 d2 st2) (mv nil st2)))
                  (res (sexec (mv-nth 0 sr) fb m1 x1)))
             (and (straightp (mv-nth 0 sr)) (fb-only (mv-nth 0 sr))
                  (slots-ok d2 (lentry (1+ pc) bnd (if into (st-mem) (mv-nth 1 sr))) fb stk2 (car res) (cdr res))
                  (implies (below-ok fb stk2 m1) (below-ok fb stk2 (car res))))))
  :hints (("Goal" :in-theory (e/d (lentry) (spilll spilll-straight spilll-sem mem-ok-of-clean slots-ok-st-mem (:e st-mem)))
                  :use ((:instance spilll-straight (j 0) (b d2) (st st2))
                        (:instance spilll-sem (d d2) (st st2) (stk stk2) (mem m1) (x x1) (j 0) (b d2))
                        (:instance mem-ok-of-clean (d d2) (st (mv-nth 1 (spilll 0 d2 st2))) (stk stk2)
                                   (mem (car (sexec (car (spilll 0 d2 st2)) fb m1 x1))) (x x1))
                        (:instance slots-ok-st-mem (d d2) (stk stk2)
                                   (mem (car (sexec (car (spilll 0 d2 st2)) fb m1 x1))) (x x1))))))

; ---- THE CODE'S LAYOUT ------------------------------------------------------------------

(defthm len-lfix (equal (len (lfix blk blocks)) (len blk)))
(defthm lfix-straight (implies (and (straightp blk) (true-listp blk)) (equal (lfix blk blocks) blk)))
(defthm len-lblocks (equal (len (lblocks rest pc dmap bnd st)) (len rest))
  :hints (("Goal" :in-theory (disable jblockl spilll dropl (:e st-mem)))))

(defthm lnpc-succ
  (implies (and (natp p) (< p (len bs))) (equal (lnpc (1+ p) bs) (+ (lnpc p bs) (len (nth p bs))))))

(defthm natp-lnpc (natp (lnpc p bs)) :rule-classes :type-prescription)

(defthm lcode-layout
  (implies (and (natp p) (< p (len bs)))
           (ncode-at (lcode bs blocks) (lnpc p bs) (lfix (nth p bs) blocks)))
  :hints (("Goal" :induct (lnpc p bs) :in-theory (disable lfix ncode-at ncode-at-append-shift lnpc-succ)
                  :expand ((lcode bs blocks) (lnpc p bs)))
          ("Subgoal *1/2" :use ((:instance ncode-at-append-shift (a (lfix (car bs) blocks)) (c (lcode (cdr bs) blocks))
                                           (i (lnpc (1- p) (cdr bs))) (blk (lfix (nth (1- p) (cdr bs)) blocks)))))))

(defthm lfntab-lookup
  (implies (jfntab-ok ft)
           (equal (cdr (assoc-equal name (lfntab ft blocks)))
                  (if (consp (assoc-equal name ft))
                      (cons (lnpc (nfix (cadr (assoc-equal name ft))) blocks) (cddr (assoc-equal name ft)))
                    nil))))

; ---- THE INVARIANT ----------------------------------------------------------------------

(defmacro bnd3 () '(boundaries prog))
(defmacro blocks3 () '(lblocks (car prog) 0 dmap (bnd3) (st-mem)))
(defmacro states3 () '(lstates (car prog) 0 dmap (bnd3) (st-mem)))

(defun emb3-ctl (ctl blocks)
  (if (atom ctl)
      ctl
    (cons (list (lnpc (nfix (caar ctl)) blocks) (cadar ctl)) (emb3-ctl (cdr ctl) blocks))))

; each return record's pc is entered with the frame in memory: a call
; leaves everything there
(defun ctl-ok3 (ctl states)
  (if (atom ctl) t (and (equal (nth (nfix (caar ctl)) states) (st-mem)) (ctl-ok3 (cdr ctl) states))))

; the machine at the block of the bytecode's pc: the same frame base and
; records, memory below the frame the stack, the frame's slots where the
; pc's entry state says; a stopped bytecode, a stopped machine
(defun l3 (prog dmap s ns)
  (let ((pc (car s)) (fb (cadr s)) (stk (cadddr s)))
    (if (not (natp pc))
        (and (nshape ns) (equal (car ns) pc))
      (and (nshape ns)
           (equal (car ns) (lnpc pc (blocks3)))
           (equal (cadr ns) fb) (natp (caddr ns))
           (equal (car (cddddr ns)) (emb3-ctl (car (cddddr s)) (blocks3)))
           (ctl-ok3 (car (cddddr s)) (states3))
           (below-ok fb stk (cadddr ns))
           (slots-ok (nfix (nth pc dmap)) (nth pc (states3)) fb stk (cadddr ns) (cadr (cddddr ns)))))))

; ---- A STRAIGHT BLOCK -------------------------------------------------------------------

(defthm true-listp-append-iff (equal (true-listp (append a b)) (true-listp b)))
(defthm spilll-true-listp (true-listp (car (spilll j b st))) :hints (("Goal" :induct (spilll j b st))))

; the block's own code related as bsem says, then the suffix
(defthm lstep-straight-sem
  (implies (and (natp fb) (natp d2)
                (straightp (mv-nth 0 (jblockl ins d tgt st))) (fb-only (mv-nth 0 (jblockl ins d tgt st)))
                (true-listp (mv-nth 0 (jblockl ins d tgt st)))
                (equal d (nfix (nth pc dmap))) (equal tgt (nfix (cadr ins))) (equal d2 (nfix (nth (1+ pc) dmap)))
                (slots-ok d2 (mv-nth 1 (jblockl ins d tgt st)) fb stk2
                          (car (sexec (mv-nth 0 (jblockl ins d tgt st)) fb mem x))
                          (cdr (sexec (mv-nth 0 (jblockl ins d tgt st)) fb mem x)))
                (below-ok fb stk2 (car (sexec (mv-nth 0 (jblockl ins d tgt st)) fb mem x))))
           (let* ((l (lstep ins pc dmap bnd st)) (res (sexec (car l) fb mem x)))
             (and (straightp (car l)) (fb-only (car l)) (true-listp (car l))
                  (slots-ok d2 (lentry (1+ pc) bnd (cdr l)) fb stk2 (car res) (cdr res))
                  (below-ok fb stk2 (car res)))))
  :hints (("Goal" :in-theory (e/d (lstep) (jblockl suffix-sem spilll lentry nth (:e st-mem)))
                  :use ((:instance suffix-sem (st2 (mv-nth 1 (jblockl ins d tgt st)))
                                   (m1 (car (sexec (mv-nth 0 (jblockl ins d tgt st)) fb mem x)))
                                   (x1 (cdr (sexec (mv-nth 0 (jblockl ins d tgt st)) fb mem x))))))))

(defmacro l3-lstep () '(lstep (nth (car s) (car prog)) (car s) dmap (bnd3) (nth (car s) (states3))))
(defmacro l3-res () '(sexec (car (l3-lstep)) (cadr s) (cadddr ns) (cadr (cddddr ns))))

; A STRAIGHT BLOCK KEEPS THE INVARIANT, given its effect on the frame
(defthm l3-straight-step
  (implies (and (natp (car s)) (< (1+ (car s)) (len (car prog))) (natp (cadr s))
                (l3 prog dmap s ns)
                (equal (vcs-step prog s) (list (1+ (car s)) (cadr s) sp2 stk2 (car (cddddr s))))
                (straightp (car (l3-lstep))) (fb-only (car (l3-lstep))) (true-listp (car (l3-lstep)))
                (slots-ok (nfix (nth (1+ (car s)) dmap)) (lentry (1+ (car s)) (bnd3) (cdr (l3-lstep)))
                          (cadr s) stk2 (car (l3-res)) (cdr (l3-res)))
                (below-ok (cadr s) stk2 (car (l3-res))))
           (l3 prog dmap (vcs-step prog s)
               (nrun (jit3-checked prog dmap) ns (len (nth (car s) (blocks3))))))
  :hints (("Goal" :in-theory (e/d (jit3-checked)
                                  (lblocks lstates lstep jblockl spilll nrun nrun-step nstep lfix lnpc lcode lfntab
                                   lentry vcs-step sexec xseq run-straight xseq-is-sexec lcode-layout lblocks-nth
                                   lstates-succ lnpc-succ lfix-straight boundaries (:e st-mem) slots-ok below-ok))
                  :use ((:instance lblocks-nth (p (car s)) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstates-succ (p (car s)) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lcode-layout (p (car s)) (bs (blocks3)) (blocks (blocks3)))
                        (:instance lfix-straight (blk (car (l3-lstep))) (blocks (blocks3)))
                        (:instance lnpc-succ (p (car s)) (bs (blocks3)))
                        (:instance six-list (r ns))
                        (:instance run-straight (np (jit3-checked prog dmap)) (seq (car (l3-lstep))))
                        (:instance xseq-is-sexec (seq (car (l3-lstep))) (pc (car ns)) (fb (cadr ns)) (sp (caddr ns))
                                   (mem (cadddr ns)) (ctl (car (cddddr ns))) (x (cadr (cddddr ns))))))))

; ---- EACH STRAIGHT BYTECODE KEEPS THE INVARIANT --------------------------------------

(defthm jblockl-push (implies (equal (car ins) :push) (equal (jblockl ins d tgt st) (jblockl (list :push (cadr ins)) d tgt st))))
(defthm jblockl-load (implies (equal (car ins) :load) (equal (jblockl ins d tgt st) (jblockl (list :load (cadr ins)) d tgt st))))
(defthm jblockl-slide (implies (equal (car ins) :slide) (equal (jblockl ins d tgt st) (jblockl (list :slide) d tgt st))))
(defthm jblockl-capt
  (implies (equal (car ins) :capt) (equal (jblockl ins d tgt st) (jblockl (list :capt (cadr ins) (caddr ins)) d tgt st))))
(defthm jblockl-binop
  (implies (member-equal (car ins) '(:add :lt)) (equal (jblockl ins d tgt st) (binopl (car ins) d st))))
(in-theory (disable jblockl-push jblockl-load jblockl-slide jblockl-capt jblockl-binop))

; the block semantics over the instruction itself
(defthm bsem-push-ins
  (implies (and (slots-ok d st fb stk mem x) (natp d) (natp fb) (equal (car ins) :push))
           (let ((r (jblockl ins d tgt st))) (bsem-concl (1+ d) (update-nth (+ fb d) (cadr ins) stk))))
  :hints (("Goal" :in-theory (disable jblockl bsem-push jblockl-push) :use ((:instance bsem-push (v (cadr ins))) (:instance jblockl-push)))))

(defthm bsem-load-ins
  (implies (and (slots-ok d st fb stk mem x) (natp d) (natp fb) (equal (car ins) :load) (natp (cadr ins)) (< (cadr ins) d))
           (let ((r (jblockl ins d tgt st)))
             (bsem-concl (1+ d) (update-nth (+ fb d) (nth (+ fb (cadr ins)) stk) stk))))
  :hints (("Goal" :in-theory (disable jblockl bsem-load jblockl-load) :use ((:instance bsem-load (i (cadr ins))) (:instance jblockl-load)))))

(defthm bsem-binop-ins
  (implies (and (slots-ok d st fb stk mem x) (natp d) (<= 2 d) (natp fb) (member-equal (car ins) '(:add :lt)))
           (let ((r (jblockl ins d tgt st)))
             (bsem-concl (1- d) (update-nth (+ fb (- d 2))
                                            (binv (car ins) (nth (+ fb (- d 2)) stk) (nth (+ fb (- d 1)) stk)) stk))))
  :hints (("Goal" :in-theory (disable jblockl binopl bsem-binop binv jblockl-binop)
                  :use ((:instance bsem-binop (op (car ins))) (:instance jblockl-binop)))))

(defthm bsem-slide-ins
  (implies (and (slots-ok d st fb stk mem x) (natp d) (<= 2 d) (natp fb) (equal (car ins) :slide))
           (let ((r (jblockl ins d tgt st)))
             (bsem-concl (1- d) (update-nth (+ fb (- d 2)) (nth (+ fb (- d 1)) stk) stk))))
  :hints (("Goal" :in-theory (disable jblockl bsem-slide jblockl-slide) :use ((:instance bsem-slide) (:instance jblockl-slide)))))

(defthm bsem-capt-ins
  (implies (and (slots-ok d st fb stk mem x) (natp d) (natp fb) (equal (car ins) :capt) (natp (cadr ins)) (< (cadr ins) d))
           (let ((r (jblockl ins d tgt st)))
             (bsem-concl (1+ d) (update-nth (+ fb d) (nth (nfix (caddr ins)) (clo-caps (nth (+ fb (cadr ins)) stk))) stk))))
  :hints (("Goal" :in-theory (disable jblockl bsem-capt jblockl-capt)
                  :use ((:instance bsem-capt (self (cadr ins)) (i (caddr ins))) (:instance jblockl-capt)))))
(in-theory (disable bsem-push-ins bsem-load-ins bsem-binop-ins bsem-slide-ins bsem-capt-ins))

; the facts every straight bytecode's step uses
(defmacro sh3 (op)
  `(and (dcheck prog dmap) (bshape s) (dinv prog dmap s) (natp (car s)) (l3 prog dmap s ns)
        (equal (car (nth (car s) (car prog))) ,op)))

; the bytecode's straight steps, its top at FB + depth
(defmacro vin () '(nth (car s) (car prog)))
(defmacro vd () '(nth (car s) dmap))
(defmacro vfb () '(cadr s))
(defmacro vstk () '(cadddr s))

(defthm dinv-normal
  (implies (and (dinv prog dmap s) (natp (car s)) (not (equal (car (vin)) :ret)))
           (and (natp (vd)) (equal (caddr s) (+ (vfb) (vd)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable dinv))))

(defmacro vstep (sp2 stk2)
  `(equal (vcs-step prog s) (list (1+ (car s)) (vfb) ,sp2 ,stk2 (car (cddddr s)))))

(defmacro vm-hyps () '(and (bshape s) (natp (car s)) (natp (vd)) (equal (caddr s) (+ (vfb) (vd)))))

(defthm vm-push-step
  (implies (and (vm-hyps) (equal (car (vin)) :push))
           (vstep (+ (vfb) (vd) 1) (update-nth (+ (vfb) (vd)) (cadr (vin)) (vstk))))
  :rule-classes nil :hints (("Goal" :in-theory (enable vcs-step bshape))))

(defthm vm-load-step
  (implies (and (vm-hyps) (equal (car (vin)) :load) (natp (cadr (vin))))
           (vstep (+ (vfb) (vd) 1) (update-nth (+ (vfb) (vd)) (nth (+ (vfb) (cadr (vin))) (vstk)) (vstk))))
  :rule-classes nil :hints (("Goal" :in-theory (enable vcs-step bshape))))

(defthm vm-binop-step
  (implies (and (vm-hyps) (member-equal (car (vin)) '(:add :lt)) (<= 2 (vd)))
           (vstep (+ (vfb) (vd) -1)
                  (update-nth (+ (vfb) (- (vd) 2))
                              (binv (car (vin)) (nth (+ (vfb) (- (vd) 2)) (vstk)) (nth (+ (vfb) (- (vd) 1)) (vstk)))
                              (vstk))))
  :rule-classes nil :hints (("Goal" :in-theory (enable vcs-step bshape))))

(defthm vm-slide-step
  (implies (and (vm-hyps) (equal (car (vin)) :slide) (<= 2 (vd)))
           (vstep (+ (vfb) (vd) -1) (update-nth (+ (vfb) (- (vd) 2)) (nth (+ (vfb) (- (vd) 1)) (vstk)) (vstk))))
  :rule-classes nil :hints (("Goal" :in-theory (enable vcs-step bshape))))

(defthm vm-capt-step
  (implies (and (vm-hyps) (equal (car (vin)) :capt) (natp (cadr (vin))))
           (vstep (+ (vfb) (vd) 1)
                  (update-nth (+ (vfb) (vd)) (nth (nfix (caddr (vin))) (clo-caps (nth (+ (vfb) (cadr (vin))) (vstk))))
                              (vstk))))
  :rule-classes nil :hints (("Goal" :in-theory (enable vcs-step bshape))))

(defthm jblockl-true-listp (true-listp (car (jblockl ins d tgt st)))
  :hints (("Goal" :in-theory (disable spilll dropl))))

(defthm l3-facts
  (implies (and (l3 prog dmap s ns) (natp (car s)))
           (and (slots-ok (nfix (nth (car s) dmap)) (nth (car s) (states3)) (cadr s) (cadddr s) (cadddr ns) (cadr (cddddr ns)))
                (below-ok (cadr s) (cadddr s) (cadddr ns))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(l3))))

(defmacro def-l3 (name op bsem-inst vm-step)
  `(defthm ,name
     (implies (sh3 ,op)
              (l3 prog dmap (vcs-step prog s) (nrun (jit3-checked prog dmap) ns (len (nth (car s) (blocks3))))))
     :hints (("Goal" :in-theory (e/d (dok)
                                     (vcs-step dinv jblockl-true-listp l3-straight-step lstep-straight-sem dcheck-at l3 lstep jblockl binopl lblocks lstates
                                      nth nth-add1 dcheck slots-ok below-ok sexec rdl wrl spilll dropl boundaries (:e st-mem)
                                      bsem-push bsem-load bsem-binop bsem-slide bsem-capt binv binopl
                                      bsem-push-ins bsem-load-ins bsem-binop-ins bsem-slide-ins bsem-capt-ins
                                      jblockl-push jblockl-load jblockl-slide jblockl-capt jblockl-binop))
                     :use ((:instance l3-straight-step (sp2 (caddr (vcs-step prog s))) (stk2 (cadddr (vcs-step prog s))))
                           (:instance lstep-straight-sem (ins (nth (car s) (car prog))) (pc (car s)) (bnd (bnd3))
                                      (st (nth (car s) (states3))) (fb (cadr s)) (mem (cadddr ns)) (x (cadr (cddddr ns)))
                                      (d (nfix (nth (car s) dmap))) (tgt (nfix (cadr (nth (car s) (car prog)))))
                                      (d2 (nfix (nth (1+ (car s)) dmap))) (stk2 (cadddr (vcs-step prog s))))
                           (:instance dcheck-at (pc (car s)))
                           (:instance dinv-normal)
                           (:instance l3-facts)
                           (:instance jblockl-true-listp (ins (nth (car s) (car prog))) (d (nfix (nth (car s) dmap)))
                                      (tgt (nfix (cadr (nth (car s) (car prog))))) (st (nth (car s) (states3))))
                           (:instance ,vm-step)
                           ,bsem-inst)))))

(defmacro bsem-args ()
  ''((d (nfix (nth (car s) dmap))) (st (nth (car s) (states3))) (fb (cadr s)) (stk (cadddr s))
     (mem (cadddr ns)) (x (cadr (cddddr ns))) (tgt (nfix (cadr (nth (car s) (car prog)))))))

(defmacro ins-args ()
  ''((ins (nth (car s) (car prog))) (d (nfix (nth (car s) dmap))) (st (nth (car s) (states3))) (fb (cadr s))
     (stk (cadddr s)) (mem (cadddr ns)) (x (cadr (cddddr ns))) (tgt (nfix (cadr (nth (car s) (car prog)))))))

(def-l3 l3-push :push
  (:instance bsem-push-ins (ins (nth (car s) (car prog))) (d (nfix (nth (car s) dmap))) (st (nth (car s) (states3)))
             (fb (cadr s)) (stk (cadddr s)) (mem (cadddr ns)) (x (cadr (cddddr ns))) (tgt (nfix (cadr (nth (car s) (car prog))))))
  vm-push-step)
(def-l3 l3-load :load
  (:instance bsem-load-ins (ins (nth (car s) (car prog))) (d (nfix (nth (car s) dmap))) (st (nth (car s) (states3)))
             (fb (cadr s)) (stk (cadddr s)) (mem (cadddr ns)) (x (cadr (cddddr ns))) (tgt (nfix (cadr (nth (car s) (car prog))))))
  vm-load-step)
(def-l3 l3-add :add
  (:instance bsem-binop-ins (ins (nth (car s) (car prog))) (d (nfix (nth (car s) dmap))) (st (nth (car s) (states3)))
             (fb (cadr s)) (stk (cadddr s)) (mem (cadddr ns)) (x (cadr (cddddr ns))) (tgt (nfix (cadr (nth (car s) (car prog))))))
  vm-binop-step)
(def-l3 l3-lt :lt
  (:instance bsem-binop-ins (ins (nth (car s) (car prog))) (d (nfix (nth (car s) dmap))) (st (nth (car s) (states3)))
             (fb (cadr s)) (stk (cadddr s)) (mem (cadddr ns)) (x (cadr (cddddr ns))) (tgt (nfix (cadr (nth (car s) (car prog))))))
  vm-binop-step)
(def-l3 l3-slide :slide
  (:instance bsem-slide-ins (ins (nth (car s) (car prog))) (d (nfix (nth (car s) dmap))) (st (nth (car s) (states3)))
             (fb (cadr s)) (stk (cadddr s)) (mem (cadddr ns)) (x (cadr (cddddr ns))) (tgt (nfix (cadr (nth (car s) (car prog))))))
  vm-slide-step)
(def-l3 l3-capt :capt
  (:instance bsem-capt-ins (ins (nth (car s) (car prog))) (d (nfix (nth (car s) dmap))) (st (nth (car s) (states3)))
             (fb (cadr s)) (stk (cadddr s)) (mem (cadddr ns)) (x (cadr (cddddr ns))) (tgt (nfix (cadr (nth (car s) (car prog))))))
  vm-capt-step)

; ---- BLOCKS THAT END IN A BRANCH OR THE RUNTIME -----------------------------------------

; a spill of a state with nothing dirty is no code
(defthm spilll-clean
  (implies (no-dirty j b st) (equal (car (spilll j b st)) nil))
  :hints (("Goal" :induct (spilll j b st))))

(defthm no-dirty-st-mem (no-dirty j b (st-mem))
  :hints (("Goal" :induct (no-dirty j b (st-mem)))))

(defthm lfix-append (equal (lfix (append a b) blocks) (append (lfix a blocks) (lfix b blocks))))

; a straight instruction goes on to the next
(defthm car-xstep-straight
  (implies (and (straight-ins ins) (natp (car ns))) (equal (car (xstep ins ns)) (1+ (car ns)))))

; straight code, then one instruction
(defthm xseq-pc-after
  (implies (and (straightp seq) (natp (car ns))) (equal (car (xseq seq ns)) (+ (car ns) (len seq))))
  :rule-classes nil
  :hints (("Goal" :induct (xseq seq ns) :in-theory (disable xstep))))

(defthm ncode-at-after-prefix
  (implies (and (ncode-at code a (append pre (list ins))) (natp a))
           (equal (nth (+ a (len pre)) code) ins))
  :hints (("Goal" :induct (ncode-at code a pre))))

(defthm run-prefix-then-one
  (implies (and (natp (car ns)) (ncode-at (car np) (car ns) (append pre (list ins))) (straightp pre) (true-listp pre))
           (equal (nrun np ns (+ 1 (len pre))) (nstep np (xseq pre ns))))
  :hints (("Goal" :in-theory (disable nrun-step run-straight xseq nstep)
                  :use ((:instance nrun-plus (p np) (a (len pre)) (b 1))
                        (:instance run-straight (seq pre))
                        (:instance xseq-pc-after (seq pre)))
                  :expand ((nrun np (xseq pre ns) 1)))))

; ---- BOUNDARIES ---------------------------------------------------------------------------

(defthm member-targets-acc
  (implies (member-equal a acc) (member-equal a (targets rest acc))))

(defthm member-targets
  (implies (and (natp p) (< p (len rest)) (member-equal (car (nth p rest)) '(:jmp :jmpf)))
           (member-equal (nfix (cadr (nth p rest))) (targets rest acc)))
  :hints (("Goal" :induct (list (nth p rest) (targets rest acc)))))

(defthm member-rets-acc
  (implies (member-equal a acc) (member-equal a (rets rest pc acc))))

(defthm member-rets
  (implies (and (natp p) (natp pc) (< p (len rest)) (equal (car (nth p rest)) :ret))
           (member-equal (+ pc p) (rets rest pc acc)))
  :hints (("Goal" :induct (list (nth p rest) (rets rest pc acc)))))

(defthm member-strip-cadrs
  (implies (consp (assoc-equal name ft)) (member-equal (cadr (assoc-equal name ft)) (strip-cadrs ft))))

(defthm member-append-or
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))

(defthm target-boundary
  (implies (and (natp pc) (< pc (len (car prog))) (member-equal (car (nth pc (car prog))) '(:jmp :jmpf)))
           (member-equal (nfix (cadr (nth pc (car prog)))) (boundaries prog)))
  :hints (("Goal" :use ((:instance member-targets (rest (car prog)) (p pc) (acc nil))))))

(defthm ret-boundary
  (implies (and (natp pc) (< pc (len (car prog))) (equal (car (nth pc (car prog))) :ret))
           (member-equal pc (boundaries prog)))
  :hints (("Goal" :use ((:instance member-rets (rest (car prog)) (pc 0) (p pc) (acc nil))))))

(defthm entry-boundary
  (implies (consp (assoc-equal name (cdr prog)))
           (member-equal (cadr (assoc-equal name (cdr prog))) (boundaries prog))))
(in-theory (disable boundaries))

; ---- AFTER A FULL SPILL, MEMORY HOLDS THE FRAME -------------------------------------------

(defthm mem-ok-smaller
  (implies (and (mem-ok d fb stk mem) (<= (nfix d2) (nfix d))) (mem-ok d2 fb stk mem))
  :hints (("Goal" :expand ((mem-ok d2 fb stk mem)) :use ((:instance mem-ok-necc (j (mem-ok-witness d2 fb stk mem)))))))

(defthm mem-ok-nth
  (implies (and (mem-ok d fb stk mem) (natp j) (< j (nfix d)))
           (equal (nth (+ fb j) mem) (nth (+ fb j) stk)))
  :hints (("Goal" :use mem-ok-necc)))

(defun sfm-ind (a k) (if (zp k) a (sfm-ind (1+ a) (1- k))))

(defthm stk-from-mem-ok
  (implies (and (mem-ok d fb stk mem) (natp a) (<= (+ a (nfix k)) (nfix d)) (natp fb))
           (equal (stk-from (+ fb a) k mem) (stk-from (+ fb a) k stk)))
  :hints (("Goal" :induct (sfm-ind a k) :in-theory (enable sreg)
                  :expand ((stk-from (+ fb a) k mem) (stk-from (+ fb a) k stk)))
          ("Subgoal *1/2" :use ((:instance mem-ok-nth (j a))))))

; a full spill: the frame in memory, the registers untouched
(defthm spill-all-sem
  (implies (and (slots-ok d st fb stk mem x) (natp fb) (natp d))
           (let ((m2 (car (sexec (car (spilll 0 d st)) fb mem x))))
             (and (straightp (car (spilll 0 d st))) (fb-only (car (spilll 0 d st))) (true-listp (car (spilll 0 d st)))
                  (equal (cdr (sexec (car (spilll 0 d st)) fb mem x)) x)
                  (mem-ok d fb stk m2)
                  (implies (below-ok fb stk mem) (below-ok fb stk m2)))))
  :hints (("Goal" :in-theory (disable spilll spilll-sem mem-ok-of-clean)
                  :use ((:instance spilll-sem (j 0) (b d))
                        (:instance mem-ok-of-clean (st (mv-nth 1 (spilll 0 d st))) (mem (car (sexec (car (spilll 0 d st)) fb mem x))))))))

; ARRIVING AT A BOUNDARY with the frame in memory is the invariant there,
; whatever the registers hold
(defthm l3-arrive
  (implies (and (natp p) (< p (len (car prog))) (member-equal p (bnd3))
                (mem-ok (nfix (nth p dmap)) fb stk mem) (below-ok fb stk mem) (natp fb) (natp sp)
                (ctl-ok3 ctl (states3)))
           (l3 prog dmap (list p fb sp2 stk ctl)
               (list (lnpc p (blocks3)) fb sp mem (emb3-ctl ctl (blocks3)) x)))
  :hints (("Goal" :in-theory (disable lblocks lstates (:e st-mem) slots-ok-st-mem boundaries)
                  :use ((:instance lstates-at-boundary (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance slots-ok-st-mem (d (nfix (nth p dmap))))))))

(defthm nstep-b
  (implies (and (natp (car ns)) (equal (nth (car ns) (car np)) (list :b tt)))
           (equal (nstep np ns)
                  (list (nfix tt) (nfix (cadr ns)) (nfix (caddr ns)) (cadddr ns) (car (cddddr ns)) (cadr (cddddr ns)))))
  :hints (("Goal" :in-theory (enable nstep))))

; nothing is dirty in the all-:m state, so its spill is no code
(defthm spilll-st-mem-const (equal (car (spilll j b (quote (:m :m :m :m :m :m :m :m)))) nil)
  :hints (("Goal" :use ((:instance spilll-clean (st (st-mem))) (:instance no-dirty-st-mem)))))
(defthm append-nil-tl (implies (true-listp x) (equal (append x nil) x)))

; the jump's block: the dirty slots out, then the branch
(defthm lstep-jmp
  (implies (equal (car ins) :jmp)
           (equal (car (lstep ins pc dmap bnd st))
                  (append (car (spilll 0 (nfix (nth pc dmap)) st)) (list (list :b (nfix (cadr ins)))))))
  :hints (("Goal" :in-theory (e/d (lstep) (spilll nth)))))

(defthm l3-shape
  (implies (and (l3 prog dmap s ns) (natp (car s)))
           (and (nshape ns) (equal (car ns) (lnpc (car s) (blocks3))) (equal (cadr ns) (cadr s)) (natp (caddr ns))
                (equal (car (cddddr ns)) (emb3-ctl (car (cddddr s)) (blocks3)))
                (ctl-ok3 (car (cddddr s)) (states3))))
  :rule-classes nil
  :hints (("Goal" :in-theory (quote (l3)))))

(defthm lfix-b (equal (lfix (list (list :b tt)) blocks) (list (list :b (lnpc (nfix tt) blocks)))))
(defthm lfix-cbf (equal (lfix (list (list :cbf r tt)) blocks) (list (list :cbf r (lnpc (nfix tt) blocks)))))

(defthm vm-jmp-step
  (implies (and (bshape s) (natp (car s)) (equal (car (vin)) :jmp))
           (equal (vcs-step prog s) (list (nfix (cadr (vin))) (vfb) (caddr s) (vstk) (car (cddddr s)))))
  :rule-classes nil :hints (("Goal" :in-theory (enable vcs-step bshape))))

(defmacro jcs () '(car (spilll 0 (nfix (nth (car s) dmap)) (nth (car s) (states3)))))
(defmacro jT () '(lnpc (nfix (cadr (nth (car s) (car prog)))) (blocks3)))

(defthm l3-jmp
  (implies (sh3 :jmp)
           (l3 prog dmap (vcs-step prog s) (nrun (jit3-checked prog dmap) ns (len (nth (car s) (blocks3))))))
  :hints (("Goal" :in-theory (e/d (dok jit3-checked)
                                  (vcs-step dinv l3 lstep jblockl lblocks lstates nth nth-add1 dcheck slots-ok below-ok
                                   sexec spilll boundaries (:e st-mem) nrun nrun-step nstep xseq lfix lcode lnpc lfntab
                                   spill-all-sem l3-arrive lblocks-nth lstep-jmp lcode-layout run-prefix-then-one
                                   xseq-is-sexec ncode-at-after-prefix nstep-b target-boundary mem-ok))
                  :use ((:instance dcheck-at (pc (car s)))
                        (:instance dinv-normal)
                        (:instance l3-facts)
                        (:instance l3-shape)
                        (:instance six-list (r ns))
                        (:instance vm-jmp-step)
                        (:instance lblocks-nth (p (car s)) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstep-jmp (ins (nth (car s) (car prog))) (pc (car s)) (bnd (bnd3))
                                   (st (nth (car s) (states3))))
                        (:instance spill-all-sem (d (nfix (nth (car s) dmap))) (st (nth (car s) (states3)))
                                   (fb (cadr s)) (stk (cadddr s)) (mem (cadddr ns)) (x (cadr (cddddr ns))))
                        (:instance lcode-layout (p (car s)) (bs (blocks3)) (blocks (blocks3)))
                        (:instance lfix-straight (blk (jcs)) (blocks (blocks3)))
                        (:instance run-prefix-then-one (np (jit3-checked prog dmap)) (pre (jcs)) (ins (list :b (jT))))
                        (:instance ncode-at-after-prefix (code (car (jit3-checked prog dmap))) (a (car ns)) (pre (jcs))
                                   (ins (list :b (jT))))
                        (:instance xseq-is-sexec (seq (jcs)) (pc (car ns)) (fb (cadr ns)) (sp (caddr ns)) (mem (cadddr ns))
                                   (ctl (car (cddddr ns))) (x (cadr (cddddr ns))))
                        (:instance nstep-b (np (jit3-checked prog dmap)) (tt (jT))
                                   (ns (xseq (jcs) ns)))
                        (:instance target-boundary (pc (car s)))
                        (:instance l3-arrive (p (nfix (cadr (nth (car s) (car prog))))) (fb (cadr s)) (stk (cadddr s))
                                   (mem (car (sexec (jcs) (cadr s) (cadddr ns) (cadr (cddddr ns)))))
                                   (sp (caddr ns)) (sp2 (caddr s)) (ctl (car (cddddr s))) (x (cadr (cddddr ns))))))))

; arriving at a pc entered all-in-memory, the frame in memory
(defthm l3-arrive2
  (implies (and (natp p) (< p (len (car prog))) (equal (nth p (states3)) (st-mem))
                (mem-ok (nfix (nth p dmap)) fb stk mem) (below-ok fb stk mem) (natp fb) (natp sp)
                (ctl-ok3 ctl (states3)))
           (l3 prog dmap (list p fb sp2 stk ctl)
               (list (lnpc p (blocks3)) fb sp mem (emb3-ctl ctl (blocks3)) x)))
  :hints (("Goal" :in-theory (disable lblocks lstates (:e st-mem) slots-ok-st-mem boundaries)
                  :use ((:instance slots-ok-st-mem (d (nfix (nth p dmap))))))))

; a branch, call or return leaves everything in memory: the next pc's state
(defthm lstep-exit-mem
  (implies (member-equal (car ins) '(:jmp :jmpf :callv :ret))
           (equal (cdr (lstep ins pc dmap bnd st)) (st-mem)))
  :hints (("Goal" :in-theory (e/d (lstep) (spilll nth)))))

(defthm lentry-st-mem (equal (lentry pc bnd (st-mem)) (st-mem)) :hints (("Goal" :in-theory (enable lentry))))

(defmacro fc () '(mv-nth 0 (rdl (- d 1) (s0) st)))
(defmacro fr () '(mv-nth 1 (rdl (- d 1) (s0) st)))
(defmacro fcs () '(car (spilll 0 (- d 1) (mv-nth 2 (rdl (- d 1) (s0) st)))))

(defthm append-assoc3 (equal (append (append a b) c) (append a (append b c))))

(defthm lstep-jmpf
  (implies (and (equal (car ins) :jmpf) (equal d (nfix (nth pc dmap))))
           (equal (car (lstep ins pc dmap bnd st))
                  (append (append (fc) (fcs)) (list (list :cbf (fr) (nfix (cadr ins)))))))
  :hints (("Goal" :in-theory (e/d (lstep) (spilll nth rdl)))))

; the read and the spill before the branch: the value in its register,
; the frame below it in memory
(defthm jmpf-pre-sem
  (implies (and (slots-ok d st fb stk mem x) (natp fb) (natp d) (<= 1 d))
           (let ((res (sexec (append (fc) (fcs)) fb mem x)))
             (and (straightp (append (fc) (fcs))) (fb-only (append (fc) (fcs))) (true-listp (append (fc) (fcs)))
                  (equal (nth (fr) (cdr res)) (nth (+ fb (- d 1)) stk))
                  (mem-ok (- d 1) fb stk (car res))
                  (implies (below-ok fb stk mem) (below-ok fb stk (car res))))))
  :hints (("Goal" :in-theory (union-theories (quote (sexec-append straightp-append fb-only-append true-listp-append-iff
                                                     natp nfix fix zp))
                                             (theory (quote minimal-theory)))
                  :use ((:instance rdl-sem (j (- d 1)) (s (s0)))
                        (:instance slots-ok-smaller (d2 (- d 1)) (st (mv-nth 2 (rdl (- d 1) (s0) st)))
                                   (x (cdr (sexec (fc) fb mem x))))
                        (:instance spill-all-sem (d (- d 1)) (st (mv-nth 2 (rdl (- d 1) (s0) st)))
                                   (mem (car (sexec (fc) fb mem x))) (x (cdr (sexec (fc) fb mem x))))))))

(defthm nstep-cbf
  (implies (and (natp (car ns)) (equal (nth (car ns) (car np)) ins) (equal (car ins) :cbf))
           (equal (nstep np ns)
                  (if (truthy (xr (cadr ins) (cadr (cddddr ns))))
                      (list (1+ (car ns)) (nfix (cadr ns)) (nfix (caddr ns)) (cadddr ns) (car (cddddr ns)) (cadr (cddddr ns)))
                    (list (nfix (caddr ins)) (nfix (cadr ns)) (nfix (caddr ns)) (cadddr ns) (car (cddddr ns)) (cadr (cddddr ns))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable nstep))))

(defthm vm-jmpf-step
  (implies (and (bshape s) (natp (car s)) (equal (car (vin)) :jmpf) (natp (vd)) (<= 1 (vd))
                (equal (caddr s) (+ (vfb) (vd))))
           (equal (vcs-step prog s)
                  (if (truthy (nth (+ (vfb) (- (vd) 1)) (vstk)))
                      (list (1+ (car s)) (vfb) (+ (vfb) (vd) -1) (vstk) (car (cddddr s)))
                    (list (nfix (cadr (vin))) (vfb) (+ (vfb) (vd) -1) (vstk) (car (cddddr s))))))
  :rule-classes nil :hints (("Goal" :in-theory (enable vcs-step bshape))))

(defthm rdl-code-facts
  (and (true-listp (car (rdl j s st))) (straightp (car (rdl j s st))) (fb-only (car (rdl j s st)))))

; a block of straight code ending in a conditional branch, run whole
(defthm run-pre-cbf
  (implies (and (natp npc) (natp fb) (natp sp)
                (ncode-at (car np) npc (append pre (list (list :cbf r tt))))
                (straightp pre) (fb-only pre) (true-listp pre))
           (equal (nrun np (list npc fb sp mem ctl x) (+ 1 (len pre)))
                  (if (truthy (nth (nfix r) (cdr (sexec pre fb mem x))))
                      (list (+ npc (len pre) 1) fb sp (car (sexec pre fb mem x)) ctl (cdr (sexec pre fb mem x)))
                    (list (nfix tt) fb sp (car (sexec pre fb mem x)) ctl (cdr (sexec pre fb mem x))))))
  :hints (("Goal" :in-theory (disable run-prefix-then-one xseq-is-sexec ncode-at-after-prefix nstep nrun nrun-step)
                  :use ((:instance run-prefix-then-one (ns (list npc fb sp mem ctl x)) (ins (list :cbf r tt)))
                        (:instance xseq-is-sexec (seq pre) (pc npc))
                        (:instance ncode-at-after-prefix (code (car np)) (a npc) (ins (list :cbf r tt)))
                        (:instance nstep-cbf (ins (list :cbf r tt))
                                   (ns (list (+ npc (len pre)) fb sp (car (sexec pre fb mem x)) ctl (cdr (sexec pre fb mem x)))))))))

(defmacro jd () '(nfix (nth (car s) dmap)))
(defmacro jst () '(nth (car s) (states3)))
(defmacro jpre () '(append (mv-nth 0 (rdl (- (jd) 1) (s0) (jst)))
                           (car (spilll 0 (- (jd) 1) (mv-nth 2 (rdl (- (jd) 1) (s0) (jst)))))))
(defmacro jr () '(mv-nth 1 (rdl (- (jd) 1) (s0) (jst))))
(defmacro jcbf () '(list :cbf (jr) (lnpc (nfix (cadr (nth (car s) (car prog)))) (blocks3))))
(defmacro jres () '(sexec (jpre) (cadr s) (cadddr ns) (cadr (cddddr ns))))

(defthm l3-jmpf-taken
  (implies (and (sh3 :jmpf) (truthy (nth (+ (cadr s) (- (jd) 1)) (cadddr s))))
           (l3 prog dmap (vcs-step prog s) (nrun (jit3-checked prog dmap) ns (len (nth (car s) (blocks3))))))
  :hints (("Goal" :in-theory (e/d (dok jit3-checked)
                                  (vcs-step dinv l3 lstep jblockl lblocks lstates nth nth-add1 dcheck slots-ok below-ok
                                   sexec spilll rdl boundaries (:e st-mem) nrun nrun-step nstep xseq lfix lcode lnpc lfntab
                                   append-assoc3 jmpf-pre-sem l3-arrive l3-arrive2 lblocks-nth lstep-jmpf lstep-exit-mem
                                   lcode-layout run-prefix-then-one xseq-is-sexec ncode-at-after-prefix target-boundary
                                   lstates-succ mem-ok truthy run-pre-cbf ncode-at-append lfix-append lfix-straight))
                  :use ((:instance dcheck-at (pc (car s)))
                        (:instance dinv-normal)
                        (:instance l3-facts)
                        (:instance l3-shape)
                        (:instance six-list (r ns))
                        (:instance vm-jmpf-step)
                        (:instance lblocks-nth (p (car s)) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstates-succ (p (car s)) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstep-exit-mem (ins (nth (car s) (car prog))) (pc (car s)) (bnd (bnd3)) (st (jst)))
                        (:instance lstep-jmpf (ins (nth (car s) (car prog))) (pc (car s)) (bnd (bnd3)) (st (jst)) (d (jd)))
                        (:instance jmpf-pre-sem (d (jd)) (st (jst)) (fb (cadr s)) (stk (cadddr s)) (mem (cadddr ns))
                                   (x (cadr (cddddr ns))))
                        (:instance lcode-layout (p (car s)) (bs (blocks3)) (blocks (blocks3)))
                        (:instance lfix-straight (blk (jpre)) (blocks (blocks3)))
                        (:instance lfix-append (a (jpre)) (b (list (list :cbf (jr) (nfix (cadr (nth (car s) (car prog)))))))
                                   (blocks (blocks3)))
                        (:instance rdl-code-facts (j (- (jd) 1)) (s (s0)) (st (jst)))
                        (:instance spilll-straight (j 0) (b (- (jd) 1)) (st (mv-nth 2 (rdl (- (jd) 1) (s0) (jst)))))
                        (:instance spilll-true-listp (j 0) (b (- (jd) 1)) (st (mv-nth 2 (rdl (- (jd) 1) (s0) (jst)))))
                        (:instance lnpc-succ (p (car s)) (bs (blocks3)))
                        (:instance run-pre-cbf (np (jit3-checked prog dmap)) (npc (car ns)) (fb (cadr ns)) (sp (caddr ns))
                                   (mem (cadddr ns)) (ctl (car (cddddr ns))) (x (cadr (cddddr ns))) (pre (jpre)) (r (jr))
                                   (tt (lnpc (nfix (cadr (nth (car s) (car prog)))) (blocks3))))
                        (:instance target-boundary (pc (car s)))
                        (:instance l3-arrive2 (p (1+ (car s))) (fb (cadr s)) (stk (cadddr s))
                                   (mem (car (jres))) (sp (caddr ns)) (sp2 (+ (cadr s) (jd) -1)) (ctl (car (cddddr s)))
                                   (x (cdr (jres))))))))

(defthm l3-jmpf-fall
  (implies (and (sh3 :jmpf) (not (truthy (nth (+ (cadr s) (- (jd) 1)) (cadddr s)))))
           (l3 prog dmap (vcs-step prog s) (nrun (jit3-checked prog dmap) ns (len (nth (car s) (blocks3))))))
  :hints (("Goal" :in-theory (e/d (dok jit3-checked)
                                  (vcs-step dinv l3 lstep jblockl lblocks lstates nth nth-add1 dcheck slots-ok below-ok
                                   sexec spilll rdl boundaries (:e st-mem) nrun nrun-step nstep xseq lfix lcode lnpc lfntab
                                   append-assoc3 jmpf-pre-sem l3-arrive l3-arrive2 lblocks-nth lstep-jmpf lstep-exit-mem
                                   lcode-layout run-prefix-then-one xseq-is-sexec ncode-at-after-prefix target-boundary
                                   lstates-succ mem-ok truthy run-pre-cbf ncode-at-append lfix-append lfix-straight))
                  :use ((:instance dcheck-at (pc (car s)))
                        (:instance dinv-normal)
                        (:instance l3-facts)
                        (:instance l3-shape)
                        (:instance six-list (r ns))
                        (:instance vm-jmpf-step)
                        (:instance lblocks-nth (p (car s)) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstates-succ (p (car s)) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstep-exit-mem (ins (nth (car s) (car prog))) (pc (car s)) (bnd (bnd3)) (st (jst)))
                        (:instance lstep-jmpf (ins (nth (car s) (car prog))) (pc (car s)) (bnd (bnd3)) (st (jst)) (d (jd)))
                        (:instance jmpf-pre-sem (d (jd)) (st (jst)) (fb (cadr s)) (stk (cadddr s)) (mem (cadddr ns))
                                   (x (cadr (cddddr ns))))
                        (:instance lcode-layout (p (car s)) (bs (blocks3)) (blocks (blocks3)))
                        (:instance lfix-straight (blk (jpre)) (blocks (blocks3)))
                        (:instance lfix-append (a (jpre)) (b (list (list :cbf (jr) (nfix (cadr (nth (car s) (car prog)))))))
                                   (blocks (blocks3)))
                        (:instance rdl-code-facts (j (- (jd) 1)) (s (s0)) (st (jst)))
                        (:instance spilll-straight (j 0) (b (- (jd) 1)) (st (mv-nth 2 (rdl (- (jd) 1) (s0) (jst)))))
                        (:instance spilll-true-listp (j 0) (b (- (jd) 1)) (st (mv-nth 2 (rdl (- (jd) 1) (s0) (jst)))))
                        (:instance lnpc-succ (p (car s)) (bs (blocks3)))
                        (:instance run-pre-cbf (np (jit3-checked prog dmap)) (npc (car ns)) (fb (cadr ns)) (sp (caddr ns))
                                   (mem (cadddr ns)) (ctl (car (cddddr ns))) (x (cadr (cddddr ns))) (pre (jpre)) (r (jr))
                                   (tt (lnpc (nfix (cadr (nth (car s) (car prog)))) (blocks3))))
                        (:instance target-boundary (pc (car s)))
                        (:instance l3-arrive (p (nfix (cadr (nth (car s) (car prog))))) (fb (cadr s)) (stk (cadddr s))
                                   (mem (car (jres))) (sp (caddr ns)) (sp2 (+ (cadr s) (jd) -1)) (ctl (car (cddddr s)))
                                   (x (cdr (jres))))))))

(defthm l3-jmpf
  (implies (sh3 :jmpf)
           (l3 prog dmap (vcs-step prog s) (nrun (jit3-checked prog dmap) ns (len (nth (car s) (blocks3))))))
  :hints (("Goal" :in-theory (disable l3-jmpf-taken l3-jmpf-fall l3 vcs-step nrun)
                  :use (l3-jmpf-taken l3-jmpf-fall))))

; ---- THE RUNTIME'S RELATIONS --------------------------------------------------------------

; a value written to slot j in memory and on the stack, the slot marked in memory
(defthm wr-mem
  (implies (and (slots-ok j st fb stk mem x) (natp j) (natp fb))
           (slots-ok (1+ j) (st-set j :m st) fb (update-nth (+ fb j) v stk) (update-nth (+ fb j) v mem) x))
  :hints (("Goal" :expand ((slots-ok (1+ j) (st-set j :m st) fb (update-nth (+ fb j) v stk) (update-nth (+ fb j) v mem) x))
                  :use ((:instance slots-ok-necc (d j)
                                   (j (slots-ok-witness (1+ j) (st-set j :m st) fb (update-nth (+ fb j) v stk)
                                                        (update-nth (+ fb j) v mem) x)))))))

(defthm mem-ok-write
  (implies (and (mem-ok j fb stk mem) (natp j) (natp fb))
           (mem-ok (1+ j) fb (update-nth (+ fb j) v stk) (update-nth (+ fb j) v mem)))
  :hints (("Goal" :expand ((mem-ok (1+ j) fb (update-nth (+ fb j) v stk) (update-nth (+ fb j) v mem)))
                  :use ((:instance mem-ok-necc (d j) (j (mem-ok-witness (1+ j) fb (update-nth (+ fb j) v stk)
                                                                        (update-nth (+ fb j) v mem))))))))

; a callee's frame lies in its caller's
(defthm mem-ok-shift
  (implies (and (mem-ok d fb stk mem) (natp a) (natp m) (<= (+ a m) (nfix d)) (natp fb))
           (mem-ok m (+ fb a) stk mem))
  :hints (("Goal" :expand ((:free (b) (mem-ok m b stk mem)))
                  :use ((:instance mem-ok-necc (j (+ a (mem-ok-witness m (+ a fb) stk mem))))))))

(defthm below-ok-shift
  (implies (and (below-ok fb stk mem) (mem-ok d fb stk mem) (natp a) (<= a (nfix d)) (natp fb))
           (below-ok (+ fb a) stk mem))
  :hints (("Goal" :expand ((:free (b) (below-ok b stk mem)))
                  :cases ((< (below-ok-witness (+ a fb) stk mem) fb))
                  :use ((:instance below-ok-necc (a (below-ok-witness (+ a fb) stk mem)))
                        (:instance mem-ok-necc (j (- (below-ok-witness (+ a fb) stk mem) fb)))))))

; a return: the caller's frame below the callee's, and the answer at its base
(defthm ret-mem-ok
  (implies (and (below-ok fb stk mem) (natp rfb) (natp fb) (<= rfb fb))
           (mem-ok (- (1+ fb) rfb) rfb (update-nth fb v stk) (update-nth fb v mem)))
  :hints (("Goal" :in-theory (disable update-nth)
                  :expand ((:free (k) (mem-ok k rfb (update-nth fb v stk) (update-nth fb v mem))))
                  :use ((:instance below-ok-necc (a (+ rfb (mem-ok-witness (+ 1 fb (- rfb)) rfb (update-nth fb v stk)
                                                                          (update-nth fb v mem)))))))))

(defthm ret-below-ok
  (implies (and (below-ok fb stk mem) (natp rfb) (natp fb) (<= rfb fb))
           (below-ok rfb (update-nth fb v stk) (update-nth fb v mem)))
  :hints (("Goal" :in-theory (disable update-nth) :expand ((below-ok rfb (update-nth fb v stk) (update-nth fb v mem)))
                  :use ((:instance below-ok-necc (a (below-ok-witness rfb (update-nth fb v stk) (update-nth fb v mem))))))))

; ---- RUNTIME BLOCKS -----------------------------------------------------------------------

; straight code, then one instruction: the instruction's step from where the code leaves it
(defthm run-pre-one
  (implies (and (natp npc) (natp fb) (natp sp)
                (ncode-at (car np) npc (append pre (list ins)))
                (straightp pre) (fb-only pre) (true-listp pre))
           (and (equal (nrun np (list npc fb sp mem ctl x) (+ 1 (len pre)))
                       (nstep np (list (+ npc (len pre)) fb sp (car (sexec pre fb mem x)) ctl (cdr (sexec pre fb mem x)))))
                (equal (nth (+ npc (len pre)) (car np)) ins)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable run-prefix-then-one xseq-is-sexec ncode-at-after-prefix nstep nrun nrun-step)
                  :use ((:instance run-prefix-then-one (ns (list npc fb sp mem ctl x)))
                        (:instance xseq-is-sexec (seq pre) (pc npc))
                        (:instance ncode-at-after-prefix (code (car np)) (a npc))))))

; a block of straight code ending in a call, run whole
(defthm run-pre-calld
  (implies (and (natp npc) (natp fb) (natp sp) (natp n) (natp d) (<= (1+ n) d)
                (ncode-at (car np) npc (append pre (list (list :calld n d))))
                (straightp pre) (fb-only pre) (true-listp pre))
           (equal (nrun np (list npc fb sp mem ctl x) (+ 1 (len pre)))
                  (let* ((m2 (car (sexec pre fb mem x))) (x2 (cdr (sexec pre fb mem x)))
                         (c (nth (+ fb (- d 1)) m2))
                         (ent (and (clop c) (cdr (assoc-equal (clo-f c) (cdr np))))))
                    (if (or (not (consp ent)) (not (equal n (nfix (cadr ent)))))
                        (list :err fb sp m2 ctl x2)
                      (list (nfix (car ent)) (+ fb (- d (1+ n))) sp m2 (cons (list (+ npc (len pre) 1) fb) ctl) x2)))))
  :hints (("Goal" :in-theory (e/d (sreg) (nstep nrun nrun-step clop))
                  :use ((:instance run-pre-one (ins (list :calld n d)))
                        (:instance nstep-calld (ins (list :calld n d))
                                   (ns (list (+ npc (len pre)) fb sp (car (sexec pre fb mem x)) ctl (cdr (sexec pre fb mem x)))))))))

(defthm lfix-other
  (implies (not (member-equal (car ins) '(:cbf :b))) (equal (lfix (list ins) blocks) (list ins))))

(defthm lstep-callv
  (implies (equal (car ins) :callv)
           (equal (car (lstep ins pc dmap bnd st))
                  (append (car (spilll 0 (nfix (nth pc dmap)) st))
                          (list (list :calld (nfix (cadr ins)) (nfix (nth pc dmap)))))))
  :hints (("Goal" :in-theory (e/d (lstep) (spilll nth)))))

(defthm vm-callv-step
  (implies (and (bshape s) (natp (car s)) (equal (car (vin)) :callv) (natp (vd)) (natp (cadr (vin)))
                (<= (1+ (cadr (vin))) (vd)) (equal (caddr s) (+ (vfb) (vd))))
           (equal (vcs-step prog s)
                  (let* ((n (cadr (vin))) (c (nth (+ (vfb) (- (vd) 1)) (vstk)))
                         (ent (and (clop c) (cdr (assoc-equal (clo-f c) (cdr prog))))))
                    (if (or (not (consp ent)) (not (equal n (nfix (cadr ent)))))
                        (list :err (vfb) (caddr s) (vstk) (car (cddddr s)))
                      (list (nfix (car ent)) (+ (vfb) (- (vd) (1+ n))) (caddr s) (vstk)
                            (cons (list (1+ (car s)) (vfb)) (car (cddddr s))))))))
  :rule-classes nil :hints (("Goal" :in-theory (enable vcs-step bshape))))

; the record's pc, after the call, is entered with the frame in memory
(defthm ctl-ok3-cons
  (equal (ctl-ok3 (cons r ctl) states)
         (and (equal (nth (nfix (car r)) states) (st-mem)) (ctl-ok3 ctl states))))

(defthm emb3-ctl-cons
  (equal (emb3-ctl (cons r ctl) blocks) (cons (list (lnpc (nfix (car r)) blocks) (cadr r)) (emb3-ctl ctl blocks))))

; ---- THE CALL, over named parts ---------------------------------------------------------
;
; The bytecode state is (pc fb sp stk ctl) with sp = fb + d, d the depth
; at pc; the machine's is (npc fb nsp mem nctl x). Stating the call over
; these parts keeps its terms small.

(defmacro B3 () '(blocks3))
(defmacro SS3 () '(states3))
(defmacro pcd () '(nth pc dmap))
(defmacro cn* () '(cadr (nth pc (car prog))))
(defmacro cc* () '(nth (+ fb (- (pcd) 1)) stk))
(defmacro ent* () '(cdr (assoc-equal (clo-f (cc*)) (cdr prog))))
(defmacro cs* () '(car (spilll 0 (pcd) (nth pc (SS3)))))
(defmacro m2* () '(car (sexec (cs*) fb mem x)))

; the call's facts about the code, the depth and the entry
(defthm callv-code3
  (implies (and (dcheck prog dmap) (natp pc) (natp (pcd)) (equal (car (nth pc (car prog))) :callv))
           (and (< (1+ pc) (len (car prog)))
                (natp (cn*)) (<= (1+ (cn*)) (pcd))
                (equal (nth pc (B3)) (append (cs*) (list (list :calld (cn*) (pcd)))))
                (equal (nth (1+ pc) (SS3)) (st-mem))
                (ncode-at (car (jit3-checked prog dmap)) (lnpc pc (B3)) (append (cs*) (list (list :calld (cn*) (pcd)))))
                (equal (lnpc (1+ pc) (B3)) (+ (lnpc pc (B3)) (len (cs*)) 1))
                (equal (cdr (assoc-equal name (cdr (jit3-checked prog dmap))))
                       (if (consp (assoc-equal name (cdr prog)))
                           (cons (lnpc (nfix (cadr (assoc-equal name (cdr prog)))) (B3)) (cddr (assoc-equal name (cdr prog))))
                         nil))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (dok jit3-checked)
                                  (lblocks lstates lstep jblockl spilll nth dcheck lfix lcode lnpc lfntab boundaries
                                   (:e st-mem) dcheck-at lblocks-nth lstates-succ lstep-callv lstep-exit-mem lcode-layout
                                   lfix-straight lfix-append lfix-other lnpc-succ lfntab-lookup spill-all-sem dcheck-facts))
                  :use ((:instance dcheck-at)
                        (:instance dcheck-facts)
                        (:instance lblocks-nth (p pc) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstates-succ (p pc) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstep-exit-mem (ins (nth pc (car prog))) (bnd (bnd3)) (st (nth pc (SS3))))
                        (:instance lstep-callv (ins (nth pc (car prog))) (bnd (bnd3)) (st (nth pc (SS3))))
                        (:instance lcode-layout (p pc) (bs (B3)) (blocks (B3)))
                        (:instance lfix-straight (blk (cs*)) (blocks (B3)))
                        (:instance lfix-append (a (cs*)) (b (list (list :calld (cn*) (pcd)))) (blocks (B3)))
                        (:instance lfix-other (ins (list :calld (cn*) (pcd))) (blocks (B3)))
                        (:instance spilll-straight (j 0) (b (pcd)) (st (nth pc (SS3))))
                        (:instance spilll-true-listp (j 0) (b (pcd)) (st (nth pc (SS3))))
                        (:instance lnpc-succ (p pc) (bs (B3)))
                        (:instance lfntab-lookup (ft (cdr prog)) (blocks (B3)))))))

(defmacro cassoc* () '(assoc-equal (clo-f (cc*)) (cdr prog)))
(defmacro fb2* () '(+ fb (- (pcd) (1+ (cn*)))))

; a block of straight code ending in a call that goes through, over plain
; variables: what the call reads and where it lands given as facts
(defthm calld-run-abs
  (implies (and (natp npc) (natp fb) (natp sp) (natp n) (natp d) (<= (1+ n) d) (natp e)
                (equal blk (append pre (list (list :calld n d))))
                (ncode-at (car np) npc blk) (straightp pre) (fb-only pre) (true-listp pre)
                (equal (cdr (sexec pre fb mem x)) x)
                (equal (nth (+ fb (- d 1)) (car (sexec pre fb mem x))) c) (clop c)
                (equal (cdr (assoc-equal (clo-f c) (cdr np))) (cons e rest)) (equal n (nfix (car rest)))
                (equal npc2 (+ npc (len pre) 1)))
           (equal (nrun np (list npc fb sp mem ctl x) (len blk))
                  (list e (+ fb (- d (1+ n))) sp (car (sexec pre fb mem x)) (cons (list npc2 fb) ctl) x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable run-pre-calld nrun sexec clop) :use run-pre-calld)))

; THE CALL'S BLOCK, run: the spills, then the call into the callee's entry
(defthm callv-run
  (implies (and (dcheck prog dmap) (natp pc) (natp fb) (natp nsp) (natp (pcd))
                (equal (car (nth pc (car prog))) :callv)
                (slots-ok (pcd) (nth pc (SS3)) fb stk mem x)
                (clop (cc*)) (consp (ent*)) (equal (cn*) (nfix (cadr (ent*)))))
           (equal (nrun (jit3-checked prog dmap) (list (lnpc pc (B3)) fb nsp mem (emb3-ctl ctl (B3)) x) (len (nth pc (B3))))
                  (list (lnpc (cadr (cassoc*)) (B3)) (fb2*) nsp (m2*)
                        (cons (list (lnpc (1+ pc) (B3)) fb) (emb3-ctl ctl (B3))) x)))
  :hints (("Goal" :in-theory (theory 'ground-zero) :do-not-induct t
                  :use ((:instance callv-code3 (name (clo-f (cc*))))
                        (:instance dcheck-facts)
                        (:instance dcheck-entries-at (ft (cdr prog)) (name (clo-f (cc*))))
                        (:instance spill-all-sem (d (pcd)) (st (nth pc (SS3))))
                        (:instance mem-ok-nth (d (pcd)) (mem (m2*)) (j (- (pcd) 1)))
                        (:instance calld-run-abs (np (jit3-checked prog dmap)) (npc (lnpc pc (B3))) (sp nsp)
                                   (ctl (emb3-ctl ctl (B3))) (pre (cs*)) (n (cn*)) (d (pcd)) (blk (nth pc (B3)))
                                   (c (cc*)) (e (lnpc (cadr (cassoc*)) (B3))) (rest (cddr (cassoc*)))
                                   (npc2 (lnpc (1+ pc) (B3))))
                        (:instance natp-lnpc (p (cadr (cassoc*))) (bs (B3)))))))

; and the callee's state it arrives in is related to the bytecode's
(defthm l3-callv-parts
  (implies (and (dcheck prog dmap) (natp pc) (natp fb) (natp nsp) (natp (pcd))
                (equal (car (nth pc (car prog))) :callv)
                (slots-ok (pcd) (nth pc (SS3)) fb stk mem x) (below-ok fb stk mem) (ctl-ok3 ctl (SS3))
                (clop (cc*)) (consp (ent*)) (equal (cn*) (nfix (cadr (ent*)))))
           (l3 prog dmap
               (list (nfix (car (ent*))) (fb2*) (+ fb (pcd)) stk (cons (list (1+ pc) fb) ctl))
               (nrun (jit3-checked prog dmap) (list (lnpc pc (B3)) fb nsp mem (emb3-ctl ctl (B3)) x) (len (nth pc (B3))))))
  :hints (("Goal" :in-theory (theory 'ground-zero) :do-not-induct t
                  :use ((:instance callv-run)
                        (:instance callv-code3 (name (clo-f (cc*))))
                        (:instance dcheck-facts)
                        (:instance spill-all-sem (d (pcd)) (st (nth pc (SS3))))
                        (:instance dcheck-entries-at (ft (cdr prog)) (name (clo-f (cc*))))
                        (:instance entry-boundary (name (clo-f (cc*))))
                        (:instance dcheck-at (pc (cadr (cassoc*))))
                        (:instance ctl-ok3-cons (r (list (1+ pc) fb)) (states (SS3)))
                        (:instance emb3-ctl-cons (r (list (1+ pc) fb)) (blocks (B3)))
                        (:instance mem-ok-shift (d (pcd)) (mem (m2*)) (a (- (pcd) (1+ (cn*)))) (m (1+ (cn*))))
                        (:instance below-ok-shift (d (pcd)) (mem (m2*)) (a (- (pcd) (1+ (cn*)))))
                        (:instance l3-arrive (p (cadr (cassoc*))) (fb (fb2*)) (mem (m2*)) (sp nsp) (sp2 (+ fb (pcd)))
                                   (ctl (cons (list (1+ pc) fb) ctl)))))))

; a call that does not go through: the machine stops at :err, as the bytecode does
(defthm calld-err-abs
  (implies (and (natp npc) (natp fb) (natp sp) (natp n) (natp d) (<= (1+ n) d)
                (equal blk (append pre (list (list :calld n d))))
                (ncode-at (car np) npc blk) (straightp pre) (fb-only pre) (true-listp pre)
                (equal (nth (+ fb (- d 1)) (car (sexec pre fb mem x))) c)
                (not (and (clop c) (consp (cdr (assoc-equal (clo-f c) (cdr np))))
                          (equal n (nfix (cadr (cdr (assoc-equal (clo-f c) (cdr np)))))))))
           (equal (nrun np (list npc fb sp mem ctl x) (len blk))
                  (list :err fb sp (car (sexec pre fb mem x)) ctl (cdr (sexec pre fb mem x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable run-pre-calld nrun sexec clop) :use run-pre-calld)))

(defthm callv-run-err
  (implies (and (dcheck prog dmap) (natp pc) (natp fb) (natp nsp) (natp (pcd))
                (equal (car (nth pc (car prog))) :callv)
                (slots-ok (pcd) (nth pc (SS3)) fb stk mem x)
                (not (and (clop (cc*)) (consp (ent*)) (equal (cn*) (nfix (cadr (ent*)))))))
           (equal (nrun (jit3-checked prog dmap) (list (lnpc pc (B3)) fb nsp mem (emb3-ctl ctl (B3)) x) (len (nth pc (B3))))
                  (list :err fb nsp (m2*) (emb3-ctl ctl (B3)) x)))
  :hints (("Goal" :in-theory (theory 'ground-zero) :do-not-induct t
                  :use ((:instance callv-code3 (name (clo-f (cc*))))
                        (:instance dcheck-facts)
                        (:instance dcheck-entries-at (ft (cdr prog)) (name (clo-f (cc*))))
                        (:instance spill-all-sem (d (pcd)) (st (nth pc (SS3))))
                        (:instance mem-ok-nth (d (pcd)) (mem (m2*)) (j (- (pcd) 1)))
                        (:instance calld-err-abs (np (jit3-checked prog dmap)) (npc (lnpc pc (B3))) (sp nsp)
                                   (ctl (emb3-ctl ctl (B3))) (pre (cs*)) (n (cn*)) (d (pcd)) (blk (nth pc (B3)))
                                   (c (cc*)))))))

; THE CALL KEEPS THE INVARIANT
(defthm l3-callv
  (implies (sh3 :callv)
           (l3 prog dmap (vcs-step prog s) (nrun (jit3-checked prog dmap) ns (len (nth (car s) (blocks3))))))
  :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(nshape bshape l3))
                  :do-not-induct t
                  :use ((:instance dinv-normal)
                        (:instance l3-facts)
                        (:instance l3-shape)
                        (:instance six-list (r ns))
                        (:instance vm-callv-step)
                        (:instance dcheck-at (pc (car s)))
                        (:instance callv-code3 (pc (car s)) (name nil))
                        (:instance l3-callv-parts (pc (car s)) (fb (cadr s)) (stk (cadddr s)) (nsp (caddr ns))
                                   (mem (cadddr ns)) (ctl (car (cddddr s))) (x (cadr (cddddr ns))))
                        (:instance callv-run-err (pc (car s)) (fb (cadr s)) (stk (cadddr s)) (nsp (caddr ns))
                                   (mem (cadddr ns)) (ctl (car (cddddr s))) (x (cadr (cddddr ns))))))))

; ---- THE CLOSURE ----------------------------------------------------------------------------

; fewer slots, still related
(defthm slots-ok-mono
  (implies (and (slots-ok d st fb stk mem x) (<= (nfix d2) (nfix d)))
           (slots-ok d2 st fb stk mem x))
  :hints (("Goal" :expand ((slots-ok d2 st fb stk mem x))
                  :use ((:instance slots-ok-necc (j (slots-ok-witness d2 st fb stk mem x)))))))

; a write at or above the frame's base leaves what is below it
(defthm below-ok-update-above
  (implies (and (below-ok fb stk mem) (natp fb) (natp i) (<= fb i))
           (below-ok fb (update-nth i v stk) (update-nth i w mem)))
  :hints (("Goal" :expand ((below-ok fb (update-nth i v stk) (update-nth i w mem)))
                  :use ((:instance below-ok-necc (a (below-ok-witness fb (update-nth i v stk) (update-nth i w mem))))))))

; a block of straight code, one instruction making a closure, and straight code
(defthm mkclo-run-abs
  (implies (and (natp npc) (natp fb) (natp sp) (natp k) (natp d) (<= k d)
                (equal blk (append (append pre (list (list :mkclod f k d))) post))
                (ncode-at (car np) npc blk)
                (straightp pre) (fb-only pre) (true-listp pre) (straightp post) (fb-only post))
           (equal (nrun np (list npc fb sp mem ctl x) (len blk))
                  (let* ((m1 (car (sexec pre fb mem x))) (x1 (cdr (sexec pre fb mem x)))
                         (m2 (update-nth (+ fb (- d k)) (clo f (stk-from (+ fb (- d k)) k m1)) m1)))
                    (list (+ npc (len blk)) fb sp (car (sexec post fb m2 x1)) ctl (cdr (sexec post fb m2 x1))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (ssetreg) (nrun nrun-plus nstep run-straight xseq-is-sexec sexec nrun-step))
                  :use ((:instance nrun-plus (p np) (ns (list npc fb sp mem ctl x)) (a (+ 1 (len pre))) (b (len post)))
                        (:instance run-pre-one (ins (list :mkclod f k d)))
                        (:instance nstep-mkclod (ins (list :mkclod f k d))
                                   (ns (list (+ npc (len pre)) fb sp (car (sexec pre fb mem x)) ctl (cdr (sexec pre fb mem x)))))
                        (:instance run-straight (seq post)
                                   (ns (list (+ 1 npc (len pre)) fb sp
                                             (update-nth (+ fb (- d k)) (clo f (stk-from (+ fb (- d k)) k (car (sexec pre fb mem x))))
                                                         (car (sexec pre fb mem x)))
                                             ctl (cdr (sexec pre fb mem x)))))
                        (:instance xseq-is-sexec (seq post) (pc (+ 1 npc (len pre))) (ctl ctl) (x (cdr (sexec pre fb mem x)))
                                   (mem (update-nth (+ fb (- d k)) (clo f (stk-from (+ fb (- d k)) k (car (sexec pre fb mem x))))
                                                    (car (sexec pre fb mem x)))))))))

; the frame after the closure is made: the spilled state, the closure's slot in memory, the slots above it dead
(defthm mkclo-rel
  (implies (and (slots-ok d st fb stk mem x) (below-ok fb stk mem) (natp fb) (natp d) (natp k) (<= k d))
           (let* ((m1 (car (sexec (car (spilll 0 d st)) fb mem x)))
                  (st2 (dropl 0 (+ 1 (- d k)) (st-set (- d k) :m (mv-nth 1 (spilll 0 d st))))))
             (and (slots-ok (+ 1 (- d k)) st2 fb
                            (update-nth (+ fb (- d k)) (clo f (stk-from (+ fb (- d k)) k stk)) stk)
                            (update-nth (+ fb (- d k)) (clo f (stk-from (+ fb (- d k)) k m1)) m1) x)
                  (below-ok fb (update-nth (+ fb (- d k)) (clo f (stk-from (+ fb (- d k)) k stk)) stk)
                            (update-nth (+ fb (- d k)) (clo f (stk-from (+ fb (- d k)) k m1)) m1)))))
  :hints (("Goal" :in-theory (disable spilll sexec spilll-sem spill-all-sem stk-from-mem-ok wr-mem slots-ok-dropl
                                      slots-ok-mono below-ok-update-above dropl st-set)
                  :use ((:instance spilll-sem (j 0) (b d))
                        (:instance spill-all-sem)
                        (:instance stk-from-mem-ok (mem (car (sexec (car (spilll 0 d st)) fb mem x))) (a (- d k)))
                        (:instance slots-ok-mono (d2 (- d k)) (st (mv-nth 1 (spilll 0 d st)))
                                   (mem (car (sexec (car (spilll 0 d st)) fb mem x))))
                        (:instance wr-mem (j (- d k)) (st (mv-nth 1 (spilll 0 d st)))
                                   (v (clo f (stk-from (+ fb (- d k)) k stk)))
                                   (mem (car (sexec (car (spilll 0 d st)) fb mem x))))
                        (:instance slots-ok-dropl (d2 (+ 1 (- d k))) (d (+ 1 (- d k))) (j 0)
                                   (st (st-set (- d k) :m (mv-nth 1 (spilll 0 d st))))
                                   (stk (update-nth (+ fb (- d k)) (clo f (stk-from (+ fb (- d k)) k stk)) stk))
                                   (mem (update-nth (+ fb (- d k)) (clo f (stk-from (+ fb (- d k)) k stk))
                                                    (car (sexec (car (spilll 0 d st)) fb mem x)))))
                        (:instance below-ok-update-above (i (+ fb (- d k))) (stk stk)
                                   (mem (car (sexec (car (spilll 0 d st)) fb mem x)))
                                   (v (clo f (stk-from (+ fb (- d k)) k stk)))
                                   (w (clo f (stk-from (+ fb (- d k)) k stk))))))))

(defthm lstep-mkclo
  (implies (equal (car ins) :mkclo)
           (let* ((d (nfix (nth pc dmap))) (k (nfix (caddr ins)))
                  (xst (dropl 0 (+ 1 (- d k)) (st-set (- d k) :m (mv-nth 1 (spilll 0 d st)))))
                  (sr (if (member-equal (1+ pc) bnd) (spilll 0 (nfix (nth (1+ pc) dmap)) xst) (mv nil xst))))
             (and (equal (car (lstep ins pc dmap bnd st))
                         (append (append (car (spilll 0 d st)) (list (list :mkclod (cadr ins) k d))) (mv-nth 0 sr)))
                  (equal (cdr (lstep ins pc dmap bnd st))
                         (if (member-equal (1+ pc) bnd) (st-mem) (mv-nth 1 sr))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (lstep) (spilll dropl st-set nth (:e st-mem))))))

(defmacro mK () '(caddr (nth pc (car prog))))
(defmacro mF () '(cadr (nth pc (car prog))))
(defmacro mx* () '(dropl 0 (+ 1 (- (pcd) (mK))) (st-set (- (pcd) (mK)) :m (mv-nth 1 (spilll 0 (pcd) (nth pc (SS3)))))))
(defmacro msr* () '(if (member-equal (1+ pc) (bnd3)) (spilll 0 (+ 1 (- (pcd) (mK))) (mx*)) (mv nil (mx*))))
(defmacro mpost* () '(mv-nth 0 (msr*)))
(defmacro mm2* () '(update-nth (+ fb (- (pcd) (mK))) (clo (mF) (stk-from (+ fb (- (pcd) (mK))) (mK) (m2*))) (m2*)))
(defmacro mstk* () '(update-nth (+ fb (- (pcd) (mK))) (clo (mF) (stk-from (+ fb (- (pcd) (mK))) (mK) stk)) stk))

; the closure's facts about the code and the depths
(defthm mkclo-code
  (implies (and (dcheck prog dmap) (natp pc) (natp (pcd)) (equal (car (nth pc (car prog))) :mkclo))
           (and (< (1+ pc) (len (car prog)))
                (natp (mK)) (<= (mK) (pcd))
                (equal (nth (1+ pc) dmap) (+ 1 (- (pcd) (mK))))
                (equal (nth pc (B3)) (append (append (cs*) (list (list :mkclod (mF) (mK) (pcd)))) (mpost*)))
                (equal (nth (1+ pc) (SS3))
                       (lentry (1+ pc) (bnd3) (if (member-equal (1+ pc) (bnd3)) (st-mem) (mv-nth 1 (msr*)))))
                (ncode-at (car (jit3-checked prog dmap)) (lnpc pc (B3)) (nth pc (B3)))
                (equal (lnpc (1+ pc) (B3)) (+ (lnpc pc (B3)) (len (nth pc (B3)))))
                (straightp (mpost*)) (fb-only (mpost*)) (true-listp (mpost*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (dok jit3-checked)
                                  (lblocks lstates lstep jblockl spilll nth dcheck lfix lcode lnpc lfntab boundaries dropl st-set
                                   (:e st-mem) dcheck-at lblocks-nth lstates-succ lstep-exit-mem lcode-layout lentry
                                   lfix-straight lfix-append lfix-other lnpc-succ lfntab-lookup spill-all-sem dcheck-facts))
                  :use ((:instance dcheck-at)
                        (:instance lblocks-nth (p pc) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstates-succ (p pc) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstep-mkclo (ins (nth pc (car prog))) (bnd (bnd3)) (st (nth pc (SS3))))
                        (:instance lcode-layout (p pc) (bs (B3)) (blocks (B3)))
                        (:instance lfix-straight (blk (cs*)) (blocks (B3)))
                        (:instance lfix-straight (blk (mpost*)) (blocks (B3)))
                        (:instance lfix-append (a (append (cs*) (list (list :mkclod (mF) (mK) (pcd))))) (b (mpost*)) (blocks (B3)))
                        (:instance lfix-append (a (cs*)) (b (list (list :mkclod (mF) (mK) (pcd)))) (blocks (B3)))
                        (:instance lfix-other (ins (list :mkclod (mF) (mK) (pcd))) (blocks (B3)))
                        (:instance spilll-straight (j 0) (b (pcd)) (st (nth pc (SS3))))
                        (:instance spilll-true-listp (j 0) (b (pcd)) (st (nth pc (SS3))))
                        (:instance spilll-straight (j 0) (b (+ 1 (- (pcd) (mK)))) (st (mx*)))
                        (:instance spilll-true-listp (j 0) (b (+ 1 (- (pcd) (mK)))) (st (mx*)))
                        (:instance lnpc-succ (p pc) (bs (B3)))))))

; THE CLOSURE'S BLOCK, run
(defthm mkclo-run
  (implies (and (dcheck prog dmap) (natp pc) (natp fb) (natp nsp) (natp (pcd))
                (equal (car (nth pc (car prog))) :mkclo)
                (slots-ok (pcd) (nth pc (SS3)) fb stk mem x))
           (equal (nrun (jit3-checked prog dmap) (list (lnpc pc (B3)) fb nsp mem (emb3-ctl ctl (B3)) x) (len (nth pc (B3))))
                  (list (lnpc (1+ pc) (B3)) fb nsp (car (sexec (mpost*) fb (mm2*) x)) (emb3-ctl ctl (B3))
                        (cdr (sexec (mpost*) fb (mm2*) x)))))
  :hints (("Goal" :in-theory (theory 'ground-zero) :do-not-induct t
                  :use ((:instance mkclo-code)
                        (:instance spill-all-sem (d (pcd)) (st (nth pc (SS3))))
                        (:instance mkclo-run-abs (np (jit3-checked prog dmap)) (npc (lnpc pc (B3))) (sp nsp)
                                   (ctl (emb3-ctl ctl (B3))) (pre (cs*)) (post (mpost*)) (f (mF)) (k (mK)) (d (pcd))
                                   (blk (nth pc (B3))))))))

; and the state it leaves is related to the bytecode's
(defthm l3-mkclo-parts
  (implies (and (dcheck prog dmap) (natp pc) (natp fb) (natp nsp) (natp (pcd))
                (equal (car (nth pc (car prog))) :mkclo)
                (slots-ok (pcd) (nth pc (SS3)) fb stk mem x) (below-ok fb stk mem) (ctl-ok3 ctl (SS3)))
           (l3 prog dmap (list (1+ pc) fb (+ fb (+ 1 (- (pcd) (mK)))) (mstk*) ctl)
               (nrun (jit3-checked prog dmap) (list (lnpc pc (B3)) fb nsp mem (emb3-ctl ctl (B3)) x) (len (nth pc (B3))))))
  :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(l3 nshape)) :do-not-induct t
                  :use ((:instance mkclo-run)
                        (:instance mkclo-code)
                        (:instance mkclo-rel (d (pcd)) (st (nth pc (SS3))) (k (mK)) (f (mF)))
                        (:instance suffix-sem (d2 (+ 1 (- (pcd) (mK)))) (st2 (mx*)) (stk2 (mstk*)) (m1 (mm2*)) (x1 x)
                                   (bnd (bnd3)))))))

(defthm vm-mkclo-step
  (implies (and (vm-hyps) (equal (car (vin)) :mkclo) (natp (caddr (vin))) (<= (caddr (vin)) (vd)))
           (vstep (+ (vfb) (+ 1 (- (vd) (caddr (vin)))))
                  (update-nth (+ (vfb) (- (vd) (caddr (vin))))
                              (clo (cadr (vin)) (stk-from (+ (vfb) (- (vd) (caddr (vin)))) (caddr (vin)) (vstk))) (vstk))))
  :rule-classes nil :hints (("Goal" :in-theory (enable vcs-step bshape ssetreg))))

; THE CLOSURE KEEPS THE INVARIANT
(defthm l3-mkclo
  (implies (sh3 :mkclo)
           (l3 prog dmap (vcs-step prog s) (nrun (jit3-checked prog dmap) ns (len (nth (car s) (blocks3))))))
  :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(nshape bshape)) :do-not-induct t
                  :use ((:instance dinv-normal)
                        (:instance l3-facts)
                        (:instance l3-shape)
                        (:instance six-list (r ns))
                        (:instance mkclo-code (pc (car s)))
                        (:instance vm-mkclo-step)
                        (:instance l3-mkclo-parts (pc (car s)) (fb (cadr s)) (stk (cadddr s)) (nsp (caddr ns))
                                   (mem (cadddr ns)) (ctl (car (cddddr s))) (x (cadr (cddddr ns))))))))

; ---- RETURNS ------------------------------------------------------------------------------

; the same value written to the same address of memory and the stack
(defthm mem-ok-update-same
  (implies (and (mem-ok d fb stk mem) (natp a))
           (mem-ok d fb (update-nth a v stk) (update-nth a v mem)))
  :hints (("Goal" :expand ((mem-ok d fb (update-nth a v stk) (update-nth a v mem)))
                  :use ((:instance mem-ok-necc (j (mem-ok-witness d fb (update-nth a v stk) (update-nth a v mem))))))))

(defthm mem-ok-of-st-mem
  (implies (slots-ok d (st-mem) fb stk mem x) (mem-ok d fb stk mem))
  :hints (("Goal" :in-theory (disable (:e st-mem)) :expand ((mem-ok d fb stk mem))
                  :use ((:instance slots-ok-necc (st (st-mem)) (j (mem-ok-witness d fb stk mem)))))))

; a return's caller frame, its base at most one past the callee's
(defthm mem-ok-zero (implies (zp d) (mem-ok d fb stk mem)) :hints (("Goal" :in-theory (enable mem-ok))))

(defthm ret-mem-ok1
  (implies (and (below-ok fb stk mem) (natp rfb) (natp fb) (<= rfb (1+ fb)))
           (mem-ok (- (1+ fb) rfb) rfb (update-nth fb v stk) (update-nth fb v mem)))
  :hints (("Goal" :cases ((<= rfb fb)) :in-theory (disable ret-mem-ok) :use ((:instance ret-mem-ok)))))

(defthm ret-below-ok1
  (implies (and (below-ok fb stk mem) (natp rfb) (natp fb) (<= rfb (1+ fb)))
           (below-ok rfb (update-nth fb v stk) (update-nth fb v mem)))
  :hints (("Goal" :in-theory (disable update-nth) :expand ((below-ok rfb (update-nth fb v stk) (update-nth fb v mem)))
                  :use ((:instance below-ok-necc (a (below-ok-witness rfb (update-nth fb v stk) (update-nth fb v mem))))))))

(defthm lstep-ret
  (implies (equal (car ins) :ret)
           (equal (car (lstep ins pc dmap bnd (st-mem))) (list (list :retd (nfix (nth pc dmap))))))
  :hints (("Goal" :in-theory (e/d (lstep) (nth)))))

(defthm below-ok-update-same
  (implies (below-ok fb stk mem)
           (below-ok fb (update-nth a v stk) (update-nth a v mem)))
  :hints (("Goal" :expand ((below-ok fb (update-nth a v stk) (update-nth a v mem)))
                  :use ((:instance below-ok-necc (a (below-ok-witness fb (update-nth a v stk) (update-nth a v mem))))))))

; the return's facts: a boundary, so its frame is in memory and its block is the return alone
(defthm ret-code
  (implies (and (dcheck prog dmap) (natp pc) (natp (pcd)) (equal (car (nth pc (car prog))) :ret))
           (and (<= 1 (pcd)) (< pc (len (car prog)))
                (equal (nth pc (SS3)) (st-mem))
                (equal (nth pc (B3)) (list (list :retd (pcd))))
                (equal (nth (lnpc pc (B3)) (car (jit3-checked prog dmap))) (list :retd (pcd)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (dok jit3-checked ncode-at)
                                  (lblocks lstates lstep jblockl spilll nth dcheck lfix lcode lnpc lfntab boundaries
                                   (:e st-mem) dcheck-at lblocks-nth lstates-at-boundary lstep-ret lcode-layout
                                   lfix-other ret-boundary dcheck-facts))
                  :use ((:instance dcheck-at)
                        (:instance ret-boundary)
                        (:instance lstates-at-boundary (p pc) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lblocks-nth (p pc) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstep-ret (ins (nth pc (car prog))) (bnd (bnd3)))
                        (:instance lcode-layout (p pc) (bs (B3)) (blocks (B3)))
                        (:instance lfix-other (ins (list :retd (pcd))) (blocks (B3)))))))

; THE RETURN'S BLOCK, run
(defthm ret-run
  (implies (and (dcheck prog dmap) (natp pc) (natp fb) (natp (pcd)) (equal (car (nth pc (car prog))) :ret))
           (equal (nrun (jit3-checked prog dmap) (list (lnpc pc (B3)) fb nsp mem nctl x) (len (nth pc (B3))))
                  (let ((v (nth (+ fb (- (pcd) 1)) mem)))
                    (if (atom nctl)
                        (list (lnpc pc (B3)) fb (nfix nsp) (update-nth 0 v mem) nctl x)
                      (list (nfix (car (car nctl))) (nfix (cadr (car nctl))) (nfix nsp) (update-nth fb v mem) (cdr nctl) x)))))
  :hints (("Goal" :in-theory (e/d (sreg ssetreg) (nstep jit3-checked lnpc lblocks lstates nth (:e st-mem)))
                  :expand ((:free (ns) (nrun (jit3-checked prog dmap) ns 1)) (:free (ns) (nrun (jit3-checked prog dmap) ns 0)))
                  :use ((:instance ret-code)
                        (:instance nstep-retd (np (jit3-checked prog dmap)) (ins (list :retd (pcd)))
                                   (ns (list (lnpc pc (B3)) fb nsp mem nctl x)))))))

; the caller's depth at its return pc, as the depth check records it
(defthm ret-mem-ok-d
  (implies (and (below-ok fb stk mem) (natp rfb) (natp fb) (natp d) (equal (+ 1 fb) (+ rfb d)))
           (mem-ok d rfb (update-nth fb v stk) (update-nth fb v mem)))
  :hints (("Goal" :in-theory (disable ret-mem-ok1) :use ((:instance ret-mem-ok1)))))

; returning to a caller
(defthm l3-ret-cons-parts
  (implies (and (dcheck prog dmap) (natp pc) (natp fb) (natp nsp) (natp (pcd)) (equal (car (nth pc (car prog))) :ret)
                (slots-ok (pcd) (nth pc (SS3)) fb stk mem x) (below-ok fb stk mem) (ctl-ok3 ctl (SS3))
                (consp ctl) (dctl ctl fb dmap))
           (l3 prog dmap
               (list (nfix (car (car ctl))) (nfix (cadr (car ctl))) (1+ fb) (update-nth fb (nth (+ fb (- (pcd) 1)) stk) stk) (cdr ctl))
               (nrun (jit3-checked prog dmap) (list (lnpc pc (B3)) fb nsp mem (emb3-ctl ctl (B3)) x) (len (nth pc (B3))))))
  :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(l3 nshape dctl emb3-ctl ctl-ok3)) :do-not-induct t
                  :use ((:instance ret-run (nctl (emb3-ctl ctl (B3))))
                        (:instance ret-code)
                        (:instance mem-ok-of-st-mem (d (pcd)))
                        (:instance mem-ok-nth (d (pcd)) (j (- (pcd) 1)))
                        (:instance ret-mem-ok-d (rfb (cadr (car ctl))) (d (nth (car (car ctl)) dmap)) (v (nth (+ fb (- (pcd) 1)) stk)))
                        (:instance ret-below-ok1 (rfb (cadr (car ctl))) (v (nth (+ fb (- (pcd) 1)) stk)))
                        (:instance slots-ok-st-mem (d (nth (car (car ctl)) dmap)) (fb (cadr (car ctl)))
                                   (stk (update-nth fb (nth (+ fb (- (pcd) 1)) stk) stk))
                                   (mem (update-nth fb (nth (+ fb (- (pcd) 1)) stk) mem)))))))

; returning with no caller: the answer at the stack's bottom, the machine where it stands
(defthm l3-ret-atom-parts
  (implies (and (dcheck prog dmap) (natp pc) (natp fb) (natp nsp) (natp (pcd)) (equal (car (nth pc (car prog))) :ret)
                (slots-ok (pcd) (nth pc (SS3)) fb stk mem x) (below-ok fb stk mem) (ctl-ok3 ctl (SS3))
                (atom ctl))
           (l3 prog dmap
               (list pc fb 1 (update-nth 0 (nth (+ fb (- (pcd) 1)) stk) stk) ctl)
               (nrun (jit3-checked prog dmap) (list (lnpc pc (B3)) fb nsp mem (emb3-ctl ctl (B3)) x) (len (nth pc (B3))))))
  :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(l3 nshape emb3-ctl)) :do-not-induct t
                  :use ((:instance ret-run (nctl (emb3-ctl ctl (B3))))
                        (:instance ret-code)
                        (:instance mem-ok-of-st-mem (d (pcd)))
                        (:instance mem-ok-nth (d (pcd)) (j (- (pcd) 1)))
                        (:instance mem-ok-update-same (d (pcd)) (a 0) (v (nth (+ fb (- (pcd) 1)) stk)))
                        (:instance below-ok-update-same (a 0) (v (nth (+ fb (- (pcd) 1)) stk)))
                        (:instance slots-ok-st-mem (d (pcd))
                                   (stk (update-nth 0 (nth (+ fb (- (pcd) 1)) stk) stk))
                                   (mem (update-nth 0 (nth (+ fb (- (pcd) 1)) stk) mem)))))))

(defthm vm-ret-step
  (implies (and (bshape s) (natp (car s)) (equal (car (vin)) :ret) (not (zp (caddr s))))
           (equal (vcs-step prog s)
                  (let ((v (nth (1- (caddr s)) (vstk))) (ctl (car (cddddr s))))
                    (if (atom ctl)
                        (list (car s) (vfb) 1 (update-nth 0 v (vstk)) ctl)
                      (list (nfix (car (car ctl))) (nfix (cadr (car ctl))) (1+ (vfb)) (update-nth (vfb) v (vstk)) (cdr ctl))))))
  :rule-classes nil :hints (("Goal" :in-theory (enable vcs-step bshape sreg ssetreg))))

; THE RETURN KEEPS THE INVARIANT
(defthm l3-ret
  (implies (sh3 :ret)
           (l3 prog dmap (vcs-step prog s) (nrun (jit3-checked prog dmap) ns (len (nth (car s) (blocks3))))))
  :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(nshape bshape dinv dctl))
                  :do-not-induct t
                  :use ((:instance l3-facts)
                        (:instance l3-shape)
                        (:instance six-list (r ns))
                        (:instance vm-ret-step)
                        (:instance ret-code (pc (car s)))
                        (:instance l3-ret-cons-parts (pc (car s)) (fb (cadr s)) (stk (cadddr s)) (nsp (caddr ns))
                                   (mem (cadddr ns)) (ctl (car (cddddr s))) (x (cadr (cddddr ns))))
                        (:instance l3-ret-atom-parts (pc (car s)) (fb (cadr s)) (stk (cadddr s)) (nsp (caddr ns))
                                   (mem (cadddr ns)) (ctl (car (cddddr s))) (x (cadr (cddddr ns))))))))

; ---- ANY OTHER INSTRUCTION, AND NO PC ------------------------------------------------------

; a machine state its step leaves where it is stays there
(defthm nrun-fixed
  (implies (equal (nstep np ns) ns) (equal (nrun np ns n) ns))
  :hints (("Goal" :in-theory (e/d (nrun) (nstep nrun-step nrun-plus)) :induct (nrun np ns n))))

(defmacro ops3 () ''(:push :load :add :lt :slide :jmpf :jmp :mkclo :capt :callv :ret))

(defthm lstep-other
  (implies (not (member-equal (car ins) (ops3)))
           (equal (car (car (lstep ins pc dmap bnd st))) (list :stuck)))
  :hints (("Goal" :in-theory (e/d (lstep) (spilll nth)))))

(defthm car-lfix-stuck
  (implies (equal (car blk) '(:stuck)) (equal (car (lfix blk blocks)) '(:stuck))))

(defthm ncode-at-car
  (implies (and (ncode-at code a blk) (consp blk)) (equal (nth a code) (car blk)))
  :rule-classes nil)

(defthm other-code
  (implies (and (dcheck prog dmap) (natp pc) (natp (pcd)) (not (member-equal (car (nth pc (car prog))) (ops3))))
           (equal (nth (lnpc pc (B3)) (car (jit3-checked prog dmap))) (list :stuck)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (jit3-checked ncode-at)
                                  (lblocks lstates lstep jblockl spilll nth dcheck lfix lcode lnpc lfntab boundaries
                                   (:e st-mem) dcheck-at lblocks-nth lstep-other lcode-layout car-lfix-stuck))
                  :use ((:instance dcheck-at)
                        (:instance lblocks-nth (p pc) (rest (car prog)) (pc 0) (bnd (bnd3)) (st (st-mem)))
                        (:instance lstep-other (ins (nth pc (car prog))) (bnd (bnd3)) (st (nth pc (SS3))))
                        (:instance lcode-layout (p pc) (bs (B3)) (blocks (B3)))
                        (:instance car-lfix-stuck (blk (nth pc (B3))) (blocks (B3)))
                        (:instance ncode-at-car (code (car (jit3-checked prog dmap))) (a (lnpc pc (B3)))
                                   (blk (lfix (nth pc (B3)) (B3))))))))

; an instruction the bytecode does not have: both stand still
(defthm l3-other
  (implies (and (dcheck prog dmap) (bshape s) (dinv prog dmap s) (natp (car s)) (l3 prog dmap s ns)
                (not (member-equal (car (nth (car s) (car prog))) (ops3))))
           (l3 prog dmap (vcs-step prog s) (nrun (jit3-checked prog dmap) ns (len (nth (car s) (blocks3))))))
  :hints (("Goal" :in-theory (e/d (vcs-step nstep) (l3 nrun jit3-checked lblocks lstates nth dcheck dinv nrun-fixed lnpc))
                  :use ((:instance l3-shape)
                        (:instance dinv-normal)
                        (:instance other-code (pc (car s)))
                        (:instance nrun-fixed (np (jit3-checked prog dmap)) (n (len (nth (car s) (blocks3)))))))))

(defthm l3-nopc
  (implies (and (bshape s) (not (natp (car s))) (l3 prog dmap s ns))
           (l3 prog dmap (vcs-step prog s) (nrun np ns 1)))
  :hints (("Goal" :in-theory (enable vcs-step nstep) :expand ((nrun np ns 1)))))

; ---- ANY STEP, THEN THE SIMULATION ---------------------------------------------------------

(defun b3steps (prog dmap s)
  (if (natp (car s)) (len (nth (car s) (blocks3))) 1))

(defthm l3-any
  (implies (and (dcheck prog dmap) (bshape s) (dinv prog dmap s) (l3 prog dmap s ns))
           (l3 prog dmap (vcs-step prog s) (nrun (jit3-checked prog dmap) ns (b3steps prog dmap s))))
  :hints (("Goal" :in-theory (e/d (b3steps)
                                  (l3-push l3-load l3-add l3-lt l3-slide l3-jmpf l3-jmp l3-mkclo l3-capt l3-callv l3-ret
                                   l3-other l3-nopc l3 nrun vcs-step dinv dcheck bshape jit3-checked lblocks lstates nth))
                  :cases ((not (natp (car s))))
                  :use (l3-push l3-load l3-add l3-lt l3-slide l3-jmpf l3-jmp l3-mkclo l3-capt l3-callv l3-ret l3-other
                        (:instance l3-nopc (np (jit3-checked prog dmap)))))))

; the machine steps the stage-2b code takes for n bytecode steps
(defun j3clk (prog dmap s n)
  (if (zp n) 0 (+ (b3steps prog dmap s) (j3clk prog dmap (vcs-step prog s) (1- n)))))

(defun jsim3-ind (prog dmap s ns n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list s ns)
    (jsim3-ind prog dmap (vcs-step prog s) (nrun (jit3-checked prog dmap) ns (b3steps prog dmap s)) (1- n))))

(defthm natp-b3steps (natp (b3steps prog dmap s)) :rule-classes :type-prescription)
(defthm natp-j3clk (natp (j3clk prog dmap s n)) :rule-classes :type-prescription)

; THE REGISTER-ALLOCATED CODE IS THE BYTECODE: from any state the
; invariant holds in, after the blocks of n steps the machine is where
; the bytecode is, its slots in registers or memory as the allocator says
(defthm jit3-sim
  (implies (and (dcheck prog dmap) (bshape s) (dinv prog dmap s) (l3 prog dmap s ns))
           (l3 prog dmap (vcs-run prog s n) (nrun (jit3-checked prog dmap) ns (j3clk prog dmap s n))))
  :hints (("Goal" :induct (jsim3-ind prog dmap s ns n)
                  :in-theory (disable l3 b3steps l3-any vcs-step nstep jit3-checked nrun-step nrun-plus bshape dinv dcheck
                                      lblocks lstates)
                  :expand ((vcs-run prog s n) (j3clk prog dmap s n)))
          ("Subgoal *1/2" :use ((:instance l3-any)
                                (:instance dinv-step)
                                (:instance bshape-step)
                                (:instance nrun-plus (p (jit3-checked prog dmap)) (a (b3steps prog dmap s))
                                           (b (j3clk prog dmap (vcs-step prog s) (1- n))))))))
