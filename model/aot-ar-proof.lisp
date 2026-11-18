; SLICE 3 of the ahead-of-time compiler (model/aot-PLAN.md): the arity and version choice.
;
; THE ARITY. compiler.cljf's fn-procedure registers a procedure with aot-arreg (model/aot.lisp,
; generated) and, below 0, writes the pick into the procedure from aot-arnf's walk and aot-arvr:
; aot-arrun is what a call of m arguments then runs -- the caller's count check for a lone fixed
; arity (Eval.f90's call_compiled), else the procedure's chain. aot-arrun-is-ex-arity: it is the
; arity exec enters (ex-arity: two ex-arfit passes, bind_closure's), or the arity error when exec
; raises one, for every count -- given the arities loaded as the template has them (aot-arok)
; and at most one variadic (aot-ar1v: clj's FnExpr refuses a second, "Can't have more than 1
; variadic overload").
;
; THE VERSION. A version is an alist (slot . type code): compiler.cljf's hints, :long 2 :double 3
; :doubles 5 :longs 6. The procedure tries them in order, each behind its guard (guard-code: the
; slot's tag, or an array view of its kind -- aot-hguard, the value fitting the code); the first
; that passes runs its typed body, none the untyped one (aot-vsel; nil the untyped). aot-vsel-ffr:
; the frame then fits the env that body was typed in (aot-henv: the version's codes, the rest
; any) -- exactly aot-ty-sound-m's hypothesis, so aot-version-sound: the chosen body's value has
; the type aot-ty gives it.
;
; COST: aot-arnf and aot-arvr take at most n - i + 1 calls (aot-arnf-cost, aot-arvr-cost).

(in-package "ACL2")
(include-book "aot-ty-sound")

; ---- THE WALKS -----------------------------------------------------------------------------

(defthm aot-arnf-range
  (implies (<= 0 (aot-arnf i s))
           (and (natp (aot-arnf i s)) (<= (nfix i) (aot-arnf i s)) (< (aot-arnf i s) (aot-tv-length s))
                (equal (aot-arv (aot-arnf i s) s) 0)))
  :rule-classes ((:rewrite) (:linear :corollary (implies (<= 0 (aot-arnf i s)) (and (<= (nfix i) (aot-arnf i s)) (< (aot-arnf i s) (aot-tv-length s)))))))
(defthm aot-arnf-int (integerp (aot-arnf i s)) :rule-classes :type-prescription)
(defthm aot-arvr-range
  (implies (<= 0 (aot-arvr i s))
           (and (natp (aot-arvr i s)) (<= (nfix i) (aot-arvr i s)) (< (aot-arvr i s) (aot-tv-length s))
                (equal (aot-arv (aot-arvr i s) s) 1)))
  :rule-classes ((:rewrite) (:linear :corollary (implies (<= 0 (aot-arvr i s)) (and (<= (nfix i) (aot-arvr i s)) (< (aot-arvr i s) (aot-tv-length s)))))))
(defthm aot-arvr-int (integerp (aot-arvr i s)) :rule-classes :type-prescription)
(defthm aot-arf-nat (natp (aot-arf i s)) :rule-classes :type-prescription)

; the fixed part of the chain from i: the first fixed arity whose count is m, -1 none
(defun-nx aot-chfx (i m s)
  (declare (xargs :measure (nfix (- (aot-tv-length s) (nfix i)))))
  (let ((j (aot-arnf i s)))
    (if (< j 0) -1 (if (equal (aot-arf j s) m) j (aot-chfx (+ 1 j) m s)))))

(defthm aot-chfx-range
  (implies (<= 0 (aot-chfx i m s))
           (and (natp (aot-chfx i m s)) (<= (nfix i) (aot-chfx i m s)) (< (aot-chfx i m s) (aot-tv-length s))))
  :rule-classes ((:rewrite) (:linear :corollary (implies (<= 0 (aot-chfx i m s)) (and (<= (nfix i) (aot-chfx i m s)) (< (aot-chfx i m s) (aot-tv-length s)))))))
(defthm aot-chfx-int (integerp (aot-chfx i m s)) :rule-classes :type-prescription)

; what a call of m arguments runs: the arity's index, -1 the arity error
(defun-nx aot-arrun (m s)
  (let ((r (aot-arreg s)))
    (if (<= 0 r)
        (if (equal r m) 0 -1)
      (let ((j (aot-chfx 0 m s)))
        (if (<= 0 j) j
          (let ((v (aot-arvr 0 s))) (if (and (<= 0 v) (<= (aot-arf v s) m)) v -1)))))))

; the arities as the template holds them (nfixed variadic start body), loaded from i on
(defun-nx aot-arok (ars i s)
  (if (atom ars)
      (equal (nfix i) (aot-tv-length s))
    (and (consp (car ars))
         (equal (nth 0 (car ars)) (aot-arf i s))
         (iff (truthy (nth 1 (car ars))) (equal (aot-arv i s) 1))
         (aot-arok (cdr ars) (+ 1 i) s))))
(defun-nx aot-ar1v (s) (< (aot-arvr (+ 1 (aot-arvr 0 s)) s) 0))

(defthm aot-arok-len (implies (and (aot-arok ars i s) (natp i)) (equal (aot-tv-length s) (+ i (len ars))))
  :rule-classes nil)
(defthm aot-arok-le (implies (and (aot-arok ars i s) (natp i)) (<= i (aot-tv-length s)))
  :hints (("Goal" :use aot-arok-len)) :rule-classes :forward-chaining)
(defthm aot-arok-lt (implies (and (aot-arok ars i s) (consp ars) (natp i)) (< i (aot-tv-length s)))
  :hints (("Goal" :use aot-arok-len)) :rule-classes :forward-chaining)

; one step of each walk past arity i
(defthm aot-arnf-step
  (implies (and (syntaxp (variablep i)) (natp i) (< i (aot-tv-length s)))
           (equal (aot-arnf i s) (if (equal (aot-arv i s) 1) (aot-arnf (+ 1 i) s) i))))
(defthm aot-arvr-step
  (implies (and (syntaxp (variablep i)) (natp i) (< i (aot-tv-length s)))
           (equal (aot-arvr i s) (if (equal (aot-arv i s) 1) i (aot-arvr (+ 1 i) s)))))
(defthm aot-chfx-step
  (implies (and (syntaxp (variablep i)) (natp i) (< i (aot-tv-length s)))
           (equal (aot-chfx i m s)
                  (cond ((equal (aot-arv i s) 1) (aot-chfx (+ 1 i) m s))
                        ((equal (aot-arf i s) m) i)
                        (t (aot-chfx (+ 1 i) m s)))))
  :hints (("Goal" :expand ((aot-chfx i m s) (aot-chfx (+ 1 i) m s))
           :in-theory (disable aot-arnf aot-arf aot-arv))))
(in-theory (disable aot-arnf aot-arvr aot-arf aot-arv aot-arreg))
; the steps again, the bound read off the rest's load (a free ars2: the hypothesis an induction
; on aot-arok leaves)
(defthm aot-chfx-step2
  (implies (and (syntaxp (variablep i)) (aot-arok ars2 (+ 1 i) s) (natp i))
           (equal (aot-chfx i m s)
                  (cond ((equal (aot-arv i s) 1) (aot-chfx (+ 1 i) m s))
                        ((equal (aot-arf i s) m) i)
                        (t (aot-chfx (+ 1 i) m s)))))
  :hints (("Goal" :use ((:instance aot-arok-len (ars ars2) (i (+ 1 i))) aot-chfx-step) :in-theory (disable aot-chfx-step))))
(defthm aot-arvr-step2
  (implies (and (syntaxp (variablep i)) (aot-arok ars2 (+ 1 i) s) (natp i))
           (equal (aot-arvr i s) (if (equal (aot-arv i s) 1) i (aot-arvr (+ 1 i) s))))
  :hints (("Goal" :use ((:instance aot-arok-len (ars ars2) (i (+ 1 i))) aot-arvr-step) :in-theory (disable aot-arvr-step))))
(defun aot-ak-ind (ars i k) (if (or (zp k) (atom ars)) (list ars i) (aot-ak-ind (cdr ars) (+ 1 i) (- k 1))))
(defthm aot-arok-consp
  (implies (and (aot-arok ars i s) (natp k) (< k (len ars))) (consp (nth k ars)))
  :hints (("Goal" :induct (aot-ak-ind ars i k) :expand ((nth k ars) (aot-arok ars i s)) :in-theory (disable aot-arf aot-arv))))

(defthm aot-nth-cdr (implies (and (natp k) (natp i) (< i k)) (equal (nth (+ -1 (- i) k) (cdr ars)) (nth (+ (- i) k) ars)))
  :hints (("Goal" :expand ((nth (+ (- i) k) ars)))))

; ex-arity's first pass is the chain's fixed part
(defthm aot-chfx-pass0
  (implies (and (aot-arok ars i s) (natp i))
           (equal (ex-arity-pass ars m 0)
                  (if (<= 0 (aot-chfx i m s)) (nth (- (aot-chfx i m s) i) ars) nil)))
  :hints (("Goal" :induct (aot-arok ars i s) :in-theory (enable ex-arfit))))

; and its second, given one variadic, the first variadic of at most m
(defthm aot-arvr-pass1-none
  (implies (and (aot-arok ars i s) (natp i) (< (aot-arvr i s) 0)) (equal (ex-arity-pass ars m 1) nil))
  :hints (("Goal" :induct (aot-arok ars i s) :in-theory (enable ex-arfit))))
(defthm aot-arvr-pass1
  (implies (and (aot-arok ars i s) (natp i) (natp m) (<= 0 (aot-arvr i s)) (< (aot-arvr (+ 1 (aot-arvr i s)) s) 0))
           (equal (ex-arity-pass ars m 1)
                  (if (<= (aot-arf (aot-arvr i s) s) m) (nth (- (aot-arvr i s) i) ars) nil)))
  :hints (("Goal" :induct (aot-arok ars i s) :in-theory (enable ex-arfit))))

(defthm aot-arreg-lone
  (implies (<= 0 (aot-arreg s))
           (and (equal (aot-tv-length s) 1) (equal (aot-arv 0 s) 0) (equal (aot-arreg s) (aot-arf 0 s))))
  :hints (("Goal" :in-theory (enable aot-arreg))))

; a lone fixed arity: the caller's check
(defthm aot-arrun-lone
  (implies (and (aot-arok ars 0 s) (<= 0 (aot-arreg s)))
           (and (iff (<= 0 (aot-arrun m s)) (ex-arity ars m))
                (implies (<= 0 (aot-arrun m s)) (equal (nth (aot-arrun m s) ars) (ex-arity ars m)))))
  :hints (("Goal" :use ((:instance aot-arok-len (i 0)))
           :expand ((aot-arok ars 0 s) (ex-arity-pass ars m 0) (ex-arity-pass ars m 1)
                    (ex-arity-pass (cdr ars) m 0) (ex-arity-pass (cdr ars) m 1))
           :in-theory (enable aot-arrun ex-arfit))))

; else the procedure's chain
(defthm aot-arrun-chain
  (implies (and (aot-arok ars 0 s) (aot-ar1v s) (natp m) (< (aot-arreg s) 0))
           (and (iff (<= 0 (aot-arrun m s)) (ex-arity ars m))
                (implies (<= 0 (aot-arrun m s)) (equal (nth (aot-arrun m s) ars) (ex-arity ars m)))))
  :hints (("Goal" :use ((:instance aot-arok-len (i 0)) (:instance aot-chfx-pass0 (i 0))
                        (:instance aot-arvr-pass1-none (i 0)) (:instance aot-arvr-pass1 (i 0))
                        (:instance aot-arok-consp (i 0) (k (aot-chfx 0 m s)))
                        (:instance aot-arok-consp (i 0) (k (aot-arvr 0 s))))
           :in-theory (e/d (aot-arrun aot-ar1v) (aot-chfx-pass0 aot-arvr-pass1-none aot-arvr-pass1 aot-arok-consp)))))

; THE ARITY CHOICE IS EXEC'S
(defthm aot-arrun-is-ex-arity
  (implies (and (aot-arok ars 0 s) (aot-ar1v s) (natp m))
           (and (iff (<= 0 (aot-arrun m s)) (ex-arity ars m))
                (implies (<= 0 (aot-arrun m s)) (equal (nth (aot-arrun m s) ars) (ex-arity ars m)))))
  :hints (("Goal" :use (aot-arrun-lone aot-arrun-chain) :in-theory (disable aot-arrun ex-arity aot-arrun-lone aot-arrun-chain))))

; ---- COST ----------------------------------------------------------------------------------

(defun-nx aot-arnf-cnt (i s)
  (declare (xargs :measure (nfix (- (aot-tv-length s) (nfix i)))))
  (if (and (natp i) (< i (aot-tv-length s)))
      (if (equal (aot-arv i s) 1) (+ 1 (aot-arnf-cnt (+ 1 i) s)) 1)
    1))
(defun-nx aot-arvr-cnt (i s)
  (declare (xargs :measure (nfix (- (aot-tv-length s) (nfix i)))))
  (if (and (natp i) (< i (aot-tv-length s)))
      (if (equal (aot-arv i s) 1) 1 (+ 1 (aot-arvr-cnt (+ 1 i) s)))
    1))
(defthm aot-arnf-cost (<= (aot-arnf-cnt i s) (+ 1 (nfix (- (aot-tv-length s) (nfix i))))) :rule-classes :linear)
(defthm aot-arvr-cost (<= (aot-arvr-cnt i s) (+ 1 (nfix (- (aot-tv-length s) (nfix i))))) :rule-classes :linear)

; ---- THE VERSION CHOICE --------------------------------------------------------------------

(defun aot-hguard (h fr)
  (if (atom h) t (and (consp (car h)) (aot-fits (nth (nfix (caar h)) fr) (cdar h)) (aot-hguard (cdr h) fr))))
(defun aot-vsel (vs fr) (cond ((atom vs) nil) ((aot-hguard (car vs) fr) (car vs)) (t (aot-vsel (cdr vs) fr))))
(defun aot-hty (s h) (cond ((atom h) 1) ((and (consp (car h)) (equal (nfix (caar h)) s)) (cdar h)) (t (aot-hty s (cdr h)))))
(defun aot-henv (h i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n)) (cons (aot-hty i h) (aot-henv h (+ 1 i) n)) nil))

(defthm aot-vsel-guard (aot-hguard (aot-vsel vs fr) fr))
(defthm aot-fits-code (implies (aot-fits v ty) (aot-fits v (aot-code ty)))
  :hints (("Goal" :in-theory (enable aot-fits aot-code))))
(defthm aot-hguard-hty (implies (and (aot-hguard h fr) (natp s)) (aot-fits (nth s fr) (aot-code (aot-hty s h)))))
(defthm aot-henv-len (equal (len (aot-henv h i n)) (if (and (natp i) (natp n) (< i n)) (- n i) 0)))
(defun aot-hk-ind (i k) (if (zp k) (list i k) (aot-hk-ind (+ 1 i) (- k 1))))
(defthm aot-henv-nth
  (implies (and (natp i) (natp n) (natp k) (< (+ i k) n)) (equal (nth k (aot-henv h i n)) (aot-hty (+ i k) h)))
  :hints (("Goal" :induct (aot-hk-ind i k) :expand ((aot-henv h i n) (nth k (cons (aot-hty i h) (aot-henv h (+ 1 i) n)))))))

(defthm aot-henv0-nth
  (implies (and (natp n) (natp k) (< k n)) (equal (nth k (aot-henv h 0 n)) (aot-hty k h)))
  :hints (("Goal" :use ((:instance aot-henv-nth (i 0))))))

(defthm aot-hguard-ffr-l
  (implies (and (aot-hguard h fr) (natp n) (equal l (aot-henv h 0 n)))
           (aot-ffr fr l nil 0 0 nil 0 0 i n))
  :hints (("Goal" :induct (aot-ffr fr l nil 0 0 nil 0 0 i n) :in-theory (enable aot-ffr (:induction aot-ffr) aot-slt tvg)))
  :rule-classes nil)
(defthm aot-hguard-ffr
  (implies (and (aot-hguard h fr) (natp n))
           (aot-ffr fr (aot-henv h 0 n) nil 0 0 nil 0 0 i n))
  :hints (("Goal" :use ((:instance aot-hguard-ffr-l (l (aot-henv h 0 n)))))))

(defthm aot-vsel-ffr
  (implies (natp n) (aot-ffr fr (aot-henv (aot-vsel vs fr) 0 n) nil 0 0 nil 0 0 0 n)))

; the body the guards chose answers a value of the type aot-ty gives it
(defthm aot-version-sound
  (let ((r (ex-ev :m e 0 nil fr fuel)) (w (aot-ty 0 e 0 0 0 s)))
    (implies (and (equal (nth 0 s) (aot-henv (aot-vsel vs fr) 0 n)) (natp n)
                  (aot-sub 0 e 0) (natp (nth 3 s)) (natp (nth 4 s)) (<= n (len (nth 1 s)))
                  (equal (mv-nth 1 w) 1) (valp (car r)))
             (aot-fits (val (car r)) (mv-nth 0 w))))
  :hints (("Goal" :use (aot-ty-sound-m (:instance aot-vsel-ffr))
           :in-theory (disable aot-ty-sound-m aot-vsel-ffr))))
