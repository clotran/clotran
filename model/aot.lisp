; THE AHEAD-OF-TIME COMPILER'S ELIGIBILITY SCAN (src/clj/clotran/compiler.cljf,
; decline-reason's recur clause), at the level the Fortran is GENERATED from
; (src/f/gen/aot_gen.inc, scripts/acl2-fortran -b aot), guard-verified.
; model/aot-PLAN.md is the plan this is the first slice of.
;
; The compiler emits code for the node kinds compiler.cljf's compiled-ops
; names (aot-cop); a node of any other kind is pooled and run WHOLE by the
; interpreter. A recur under such a node that is not inside a loop, fn or
; lazy seq below it targets the compiled code around it -- the interpreter
; would hand its recur back as a value and the compiled loop would never go
; round. The compiler declines such a fn (rather than compile it wrong).
;
; THE TREE is anpass's (model/anpass.lisp: a node (:ast id kind i2 kids s3
; caps alts rfn), read through its ten shims), with one more element and two
; more reads: (:ast id kind i2 kids s3 caps alts rfn bods), bods a fn's or a
; lazy seq's arity bodies, in its template's order (aot-nbods / aot-bod,
; Eval.f90's shims on the OBJ_AST: an arity whose body is a flat or VM form
; answers no node, as clotran-ast exports it).
;
;   aot-fr   a recur under the node, not past a loop, fn or lazy seq
;   aot-sc   the scan: some node of a kind not emitted, anywhere under the
;            body -- children, a def's metadata, a case's branches, a try's
;            catches, a deftype's methods, a fn's or lazy seq's bodies --
;            has aot-fr. nil: the fn may be compiled.
;
; model/aot-proof.lisp proves what it means (aot-sc-sound, aot-handed-norec)
; and counts it (aot-sc-steps-bound).

(in-package "ACL2")

(include-book "anpass")

; ---- THE BODIES' READS ----------------------------------------------------------------------

(defun aot-nbods (x) (declare (xargs :guard t)) (if (ast-p x) (anp-sat (anp-len (anp-nth 9 x))) 0))
(defun aot-bod (x i)
  (declare (xargs :guard t))
  (if (and (ast-p x) (natp i) (< i (aot-nbods x))) (anp-nth i (anp-nth 9 x)) nil))

(defthm aot-nbods-sb64 (and (anp40p (aot-nbods x)) (natp (aot-nbods x)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (aot-nbods x)))))

(defthm aot-bod-count
  (implies (not (equal (ast-kind x) 0)) (< (acl2-count (aot-bod x i)) (acl2-count x)))
  :hints (("Goal" :in-theory (enable ast-kind ast-p anp-nth)
           :use ((:instance anp-nth-count (l (anp-nth 9 x)))
                 (:instance anp-nth-count (i 8) (l (cdr x))))))
  :rule-classes :linear)

(in-theory (disable aot-nbods aot-bod))

; the children a sequence walks: 3 the alternatives, 5 the bodies, else the children
(defun aot-ch (fl x i)
  (declare (xargs :guard t))
  (cond ((equal fl 3) (ast-alt x i)) ((equal fl 5) (aot-bod x i)) (t (ast-kid x i))))

(defthm aot-ch-count (implies (not (equal (ast-kind x) 0)) (< (acl2-count (aot-ch fl x i)) (acl2-count x)))
  :rule-classes :linear)

; compiler.cljf's compiled-ops: const local var if do call let loop recur fn lazy new dot
(defun aot-cop (k)
  (declare (xargs :guard t))
  (or (equal k 1) (equal k 2) (equal k 3) (equal k 4) (equal k 5) (equal k 6) (equal k 11) (equal k 12)
      (equal k 14) (equal k 15) (equal k 16) (equal k 21) (equal k 22)))

; ---- A RECUR UNDER A NODE --------------------------------------------------------------------

(defun aot-fr (fl x j m)
  (declare (xargs :guard (and (natp fl) (signed-byte-p 64 fl) (natp j) (signed-byte-p 64 j) (signed-byte-p 64 m))
                  :measure (anp-meas fl x j m nil)
                  :verify-guards nil))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (cond ((equal k *n-recur*) t)
              ((or (equal k 0) (equal k *n-loop*) (equal k *n-fn*) (equal k *n-lazy*) (equal k *n-deftype*)) nil)
              ((equal k *n-try*)
               (if (aot-fr 0 (ast-kid x 0) 0 0) t (if (aot-fr 3 x 0 (ast-nalts x)) t (aot-fr 0 (ast-kid x 1) 0 0))))
              ((equal k *n-case*) (if (aot-fr 3 x 0 (ast-nalts x)) t (aot-fr 1 x 0 (ast-nkids x))))
              ((equal k *n-def*) (if (aot-fr 0 (ast-s3 x) 0 0) t (aot-fr 1 x 0 (ast-nkids x))))
              (t (aot-fr 1 x 0 (ast-nkids x)))))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (if (aot-fr 0 (aot-ch fl x j) 0 0) t (aot-fr fl x (+ 1 j) m))
      nil)))

(verify-guards aot-fr)

; ---- THE SCAN --------------------------------------------------------------------------------

(defun aot-sc (fl x j m)
  (declare (xargs :guard (and (natp fl) (signed-byte-p 64 fl) (natp j) (signed-byte-p 64 j) (signed-byte-p 64 m))
                  :measure (anp-meas fl x j m nil)
                  :verify-guards nil))
  (if (equal fl 0)
      (let ((k (ast-kind x)))
        (cond ((equal k 0) nil)
              ((and (not (aot-cop k)) (aot-fr 0 x 0 0)) t)
              ((aot-sc 1 x 0 (ast-nkids x)) t)
              ((equal k *n-def*) (aot-sc 0 (ast-s3 x) 0 0))
              ((or (equal k *n-try*) (equal k *n-case*) (equal k *n-deftype*)) (aot-sc 3 x 0 (ast-nalts x)))
              ((or (equal k *n-fn*) (equal k *n-lazy*)) (aot-sc 5 x 0 (aot-nbods x)))
              (t nil)))
    (if (and (not (equal (ast-kind x) 0)) (natp j) (integerp m) (< j m))
        (if (aot-sc 0 (aot-ch fl x j) 0 0) t (aot-sc fl x (+ 1 j) m))
      nil)))

(verify-guards aot-sc)

; =============================================================================================
; SLICE 2: THE TYPES (compiler.cljf's infer, call-type, bind-types, loop-env), generated into the
; same aot_gen.inc. A type is a code: 0 none (a recur's: nothing reaches its surroundings),
; 1 any (boxed), 2 long, 3 double, 4 bool, 5 doubles, 6 longs.
;
; THE TREE here is exec.lisp's (the one ex-ev runs: (kind i2 kids c s2 mark rstart rn rfn ...)),
; with three more fields, the host's reads of a node that the inference asks and the tree
; semantics does not: 9 a constant's type as compiler.cljf's const-type gives it (int? and
; spellable a long, a finite double a double, true/false a bool), 10 a call's op (head-op's
; kind: the folded builtin's name, or the head Var's identity against clojure.core), 11 a
; constant :doubles/:longs keyword (an array cast's hint). Eval.f90's aot_* shims answer them
; on the OBJ_AST; aot-ty-proof.lisp names what it assumes of them.
;
; THE ENVIRONMENT is the stobj aots: tv a slot's type (1 past the array), rc what the recurs to
; the current loop (slots cb .. cb+cn-1) have carried there, joined, lo a loop's settled types
; (what gen's loop-env asks), a0 a1 a2 ad the current call's first three operand types and
; whether the first is an array cast's operand, ns a count of nodes visited (the cost).
; compiler.cljf's env is a map rebuilt per scope; here a let's slot is written, the body typed,
; and the old word written back, so every flag leaves tv, cb, cn and a0..ad as it found them.
;
;   aot-ty fl e j m k   0 a node: (mv type ok aots)
;                       1 a do's children j..m-1, the last one's type
;                       2 a let's bindings j..m-1, then its body
;                       3 a recur's arguments j..m-1, joined into rc
;                       4 a call's arguments j..m-1, the first three's types kept
;                       5 a loop's round k: its body typed; settled, or (k > 4) every
;                         slot boxed (8), or each slot widened by its recurs (7) and again
;                       6 a loop's bindings j..m-1, then its rounds
;
; ok (1) is no part of the answer: it says the tree is one aot-ty-proof's theorem covers --
; each let's and loop's slots untyped where they are bound, a loop's slots above the current
; loop's, every recur to the current loop with its count of arguments -- in every round of
; every loop (a round's ok and the next's are joined, so a loop inside one round never zeroes
; the recur types of the loop around it). The answer is the same either way.

(defun aot-n40 (v) (declare (xargs :guard t)) (if (and (natp v) (< v *anp40*)) v 0))
(defthm aot-n40-p (and (natp (aot-n40 v)) (< (aot-n40 v) *anp40*))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (aot-n40 v))) (:linear :corollary (< (aot-n40 v) *anp40*))))

(defun aot-k (e) (declare (xargs :guard t)) (aot-n40 (anp-nth 0 e)))
(defun aot-i2 (e) (declare (xargs :guard t)) (aot-n40 (anp-nth 1 e)))
(defun aot-nk (e) (declare (xargs :guard t)) (anp-sat (anp-len (anp-nth 2 e))))
(defun aot-kid (e j) (declare (xargs :guard t)) (if (and (natp j) (< j (aot-nk e))) (anp-nth j (anp-nth 2 e)) nil))
(defun aot-s2 (e) (declare (xargs :guard t)) (aot-n40 (anp-nth 4 e)))
(defun aot-rs (e) (declare (xargs :guard t)) (aot-n40 (anp-nth 6 e)))
(defun aot-rn (e) (declare (xargs :guard t)) (aot-n40 (anp-nth 7 e)))
(defun aot-cty (e) (declare (xargs :guard t)) (let ((v (anp-nth 9 e))) (if (or (equal v 2) (equal v 3) (equal v 4)) v 1)))
(defun aot-hop (e) (declare (xargs :guard t)) (aot-n40 (anp-nth 10 e)))
(defun aot-kw (e) (declare (xargs :guard t)) (let ((v (anp-nth 11 e))) (if (or (equal v 5) (equal v 6)) v 0)))

(defthm aot-reads-p
  (and (anp40p (aot-k e)) (anp40p (aot-i2 e)) (anp40p (aot-nk e)) (anp40p (aot-s2 e)) (anp40p (aot-rs e))
       (anp40p (aot-rn e)) (anp40p (aot-hop e)) (natp (aot-cty e)) (<= (aot-cty e) 6) (natp (aot-kw e)) (<= (aot-kw e) 6))
  :hints (("Goal" :in-theory (enable anp-sat))))

(defthm aot-k-consp (implies (not (equal (aot-k e) 0)) (consp e)) :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable anp-nth))))

(defthm aot-kid-count
  (and (<= (acl2-count (aot-kid e j)) (acl2-count e))
       (implies (not (equal (aot-k e) 0)) (< (acl2-count (aot-kid e j)) (acl2-count e))))
  :hints (("Goal" :in-theory (enable anp-nth aot-k aot-n40)
           :use ((:instance anp-nth-count (i j) (l (anp-nth 2 e)))
                 (:instance anp-nth-count (i 1) (l (cdr e))))))
  :rule-classes :linear)

(in-theory (disable aot-k aot-i2 aot-nk aot-kid aot-s2 aot-rs aot-rn aot-cty aot-hop aot-kw))

(defun aot-code (v) (declare (xargs :guard t)) (if (and (natp v) (<= v 6)) v 1))
(defun aot-jn (a b) (declare (xargs :guard t)) (cond ((equal a 0) b) ((equal b 0) a) ((equal a b) a) (t 1)))
(defun aot-and (a b) (declare (xargs :guard t)) (if (and (equal a 1) (equal b 1)) 1 0))
(defun aot-num (a) (declare (xargs :guard t)) (or (equal a 2) (equal a 3)))
(defun aot-arr (a) (declare (xargs :guard t)) (or (equal a 5) (equal a 6)))

(defthm aot-jn-code (implies (and (natp a) (<= a 6) (natp b) (<= b 6)) (and (natp (aot-jn a b)) (<= (aot-jn a b) 6))))

; call-type: the op's kind k (1 + - *, 2 /, 3 inc dec, 4 < > <= >= ==, 5 =, 6 zero? pos? neg?,
; 7 aget, 8 aset, 9 alength, 10 int long, 11 double, 12 a Math/ member of one, 13 of two), n
; operands, the first three's types
(defun aot-optab (k n t0 t1 t2)
  (declare (xargs :guard t))
  (cond ((equal k 1) (if (and (equal n 2) (aot-num t0) (aot-num t1)) (if (and (equal t0 2) (equal t1 2)) 2 3) 1))
        ((equal k 2) (if (and (equal n 2) (aot-num t0) (aot-num t1) (or (equal t0 3) (equal t1 3))) 3 1))
        ((equal k 3) (if (and (equal n 1) (aot-num t0)) t0 1))
        ((equal k 4) (if (and (equal n 2) (or (aot-num t0) (aot-num t1)) (or (aot-num t0) (equal t0 1)) (or (aot-num t1) (equal t1 1))) 4 1))
        ((equal k 5) (if (and (equal n 2) (aot-num t0) (equal t0 t1)) 4 1))
        ((equal k 6) (if (and (equal n 1) (aot-num t0)) 4 1))
        ((equal k 7) (if (and (equal n 2) (aot-arr t0) (equal t1 2)) (if (equal t0 5) 3 2) 1))
        ((equal k 8) (if (and (equal n 3) (aot-arr t0) (equal t1 2) (if (equal t0 5) (aot-num t2) (equal t2 2))) (if (equal t0 5) 3 2) 1))
        ((equal k 9) (if (and (equal n 1) (aot-arr t0)) 2 1))
        ((equal k 10) (if (and (equal n 1) (aot-num t0)) 2 1))
        ((equal k 11) (if (and (equal n 1) (aot-num t0)) 3 1))
        ((equal k 12) (if (and (equal n 1) (aot-num t0)) 3 1))
        ((equal k 13) (if (and (equal n 2) (aot-num t0) (aot-num t1)) 3 1))
        (t 1)))

(defthm aot-optab-code (and (natp (aot-optab k n t0 t1 t2)) (<= (aot-optab k n t0 t1 t2) 6)))

; ---- THE ENVIRONMENT ------------------------------------------------------------------------

(defstobj aots
  (aot-tv :type (array (signed-byte 64) (0)) :initially 1 :resizable t)
  (aot-rc :type (array (signed-byte 64) (0)) :initially 0 :resizable t)
  (aot-lo :type (array (signed-byte 64) (0)) :initially 1 :resizable t)
  (aot-cb :type (signed-byte 64) :initially 0)
  (aot-cn :type (signed-byte 64) :initially 0)
  (aot-a0 :type (signed-byte 64) :initially 1)
  (aot-a1 :type (signed-byte 64) :initially 1)
  (aot-a2 :type (signed-byte 64) :initially 1)
  (aot-ad :type (signed-byte 64) :initially 0)
  (aot-ns :type (signed-byte 64) :initially 0))

(defun aot-get (s aots)
  (declare (xargs :stobjs aots :guard t))
  (if (and (natp s) (< s (aot-tv-length aots))) (aot-code (aot-tvi s aots)) 1))
(defun aot-raw (s aots)
  (declare (xargs :stobjs aots :guard t))
  (if (and (natp s) (< s (aot-tv-length aots))) (aot-tvi s aots) 1))
(defun aot-put (s v aots)
  (declare (xargs :stobjs aots :guard (signed-byte-p 64 v)))
  (if (and (natp s) (< s (aot-tv-length aots))) (update-aot-tvi s v aots) aots))
(defun aot-rget (s aots)
  (declare (xargs :stobjs aots :guard t))
  (if (and (natp s) (< s (aot-rc-length aots))) (aot-code (aot-rci s aots)) 0))
(defun aot-rjn (s v aots)
  (declare (xargs :stobjs aots :guard t))
  (if (and (natp s) (< s (aot-rc-length aots))) (update-aot-rci s (aot-jn (aot-rget s aots) (aot-code v)) aots) aots))
(defun aot-rz (s aots)
  (declare (xargs :stobjs aots :guard t))
  (if (and (natp s) (< s (aot-rc-length aots))) (update-aot-rci s 0 aots) aots))
(defun aot-lput (s v aots)
  (declare (xargs :stobjs aots :guard (signed-byte-p 64 v)))
  (if (and (natp s) (< s (aot-lo-length aots))) (update-aot-loi s v aots) aots))
(defun aot-tick (aots)
  (declare (xargs :stobjs aots))
  (let ((n (aot-ns aots))) (if (and (natp n) (< n *anp40*)) (update-aot-ns (+ 1 n) aots) aots)))

(defthm aot-get-code (and (natp (aot-get s aots)) (<= (aot-get s aots) 6)))
(defthm aot-rget-code (and (natp (aot-rget s aots)) (<= (aot-rget s aots) 6)))
(defthm aot-40-sb64 (implies (and (natp x) (< x *anp40*)) (signed-byte-p 64 x)))
(defthm aot-small-sb64 (implies (and (natp x) (<= x 6)) (signed-byte-p 64 x)))
(defthm aot-get-sb64 (and (signed-byte-p 64 (aot-get s aots)) (signed-byte-p 64 (aot-rget s aots))))
(defthm aot-tvp-nth
  (implies (and (aot-tvp l) (natp i) (< i (len l)))
           (and (integerp (nth i l)) (<= -9223372036854775808 (nth i l)) (< (nth i l) 9223372036854775808))))
(defthm aot-raw-sb64 (implies (aotsp aots) (signed-byte-p 64 (aot-raw s aots)))
  :hints (("Goal" :in-theory (enable aotsp aot-tvi aot-tv-length))))

(defthm aot-tvp-update (implies (and (aot-tvp l) (natp i) (< i (len l)) (signed-byte-p 64 v)) (aot-tvp (update-nth i v l))))
(defthm aot-rcp-update (implies (and (aot-rcp l) (natp i) (< i (len l)) (signed-byte-p 64 v)) (aot-rcp (update-nth i v l))))
(defthm aot-lop-update (implies (and (aot-lop l) (natp i) (< i (len l)) (signed-byte-p 64 v)) (aot-lop (update-nth i v l))))
(defthm aot-put-p (implies (and (aotsp aots) (signed-byte-p 64 v)) (aotsp (aot-put s v aots))))
(defthm aot-rjn-p (implies (aotsp aots) (aotsp (aot-rjn s v aots)))
  :hints (("Goal" :use ((:instance aot-jn-code (a (aot-rget s aots)) (b (aot-code v)))))))
(defthm aot-rz-p (implies (aotsp aots) (aotsp (aot-rz s aots))))
(defthm aot-lput-p (implies (and (aotsp aots) (signed-byte-p 64 v)) (aotsp (aot-lput s v aots))))
(defthm aot-tick-p (implies (aotsp aots) (aotsp (aot-tick aots))))
(in-theory (disable aot-get aot-raw aot-put aot-rget aot-rjn aot-rz aot-lput aot-tick))

(defun aot-rzero (b i m aots)
  (declare (xargs :stobjs aots :measure (nfix (- (nfix m) (nfix i))) :guard (and (anp40p b) (anp40p i) (anp40p m))))
  (if (and (natp i) (natp m) (< i m)) (let ((aots (aot-rz (+ b i) aots))) (aot-rzero b (+ 1 i) m aots)) aots))
(defun aot-settled (b i m aots)
  (declare (xargs :stobjs aots :measure (nfix (- (nfix m) (nfix i))) :guard (and (anp40p b) (anp40p i) (anp40p m))))
  (if (and (natp i) (natp m) (< i m))
      (and (equal (aot-jn (aot-get (+ b i) aots) (aot-rget (+ b i) aots)) (aot-get (+ b i) aots))
           (aot-settled b (+ 1 i) m aots))
    t))
(defun aot-lcopy (b i m aots)
  (declare (xargs :stobjs aots :measure (nfix (- (nfix m) (nfix i))) :guard (and (anp40p b) (anp40p i) (anp40p m))))
  (if (and (natp i) (natp m) (< i m)) (let ((aots (aot-lput (+ b i) (aot-get (+ b i) aots) aots))) (aot-lcopy b (+ 1 i) m aots)) aots))

(defthm aot-scalars-p
  (implies (aotsp x) (and (signed-byte-p 64 (aot-cb x)) (signed-byte-p 64 (aot-cn x)) (signed-byte-p 64 (aot-a0 x)) (signed-byte-p 64 (aot-a1 x)) (signed-byte-p 64 (aot-a2 x)) (signed-byte-p 64 (aot-ad x)) (signed-byte-p 64 (aot-ns x)) ))
  :hints (("Goal" :in-theory (enable aotsp))))
(defthm aot-scalars-int
  (implies (aotsp x) (and (integerp (aot-cb x)) (<= -9223372036854775808 (aot-cb x)) (< (aot-cb x) 9223372036854775808) (integerp (aot-cn x)) (<= -9223372036854775808 (aot-cn x)) (< (aot-cn x) 9223372036854775808) (integerp (aot-a0 x)) (<= -9223372036854775808 (aot-a0 x)) (< (aot-a0 x) 9223372036854775808) (integerp (aot-a1 x)) (<= -9223372036854775808 (aot-a1 x)) (< (aot-a1 x) 9223372036854775808) (integerp (aot-a2 x)) (<= -9223372036854775808 (aot-a2 x)) (< (aot-a2 x) 9223372036854775808) (integerp (aot-ad x)) (<= -9223372036854775808 (aot-ad x)) (< (aot-ad x) 9223372036854775808) (integerp (aot-ns x)) (<= -9223372036854775808 (aot-ns x)) (< (aot-ns x) 9223372036854775808) ))
  :hints (("Goal" :in-theory (enable aotsp))))
(defthm aot-updates-p
  (implies (and (aotsp x) (signed-byte-p 64 v)) (and (aotsp (update-aot-cb v x)) (aotsp (update-aot-cn v x)) (aotsp (update-aot-a0 v x)) (aotsp (update-aot-a1 v x)) (aotsp (update-aot-a2 v x)) (aotsp (update-aot-ad v x)) (aotsp (update-aot-ns v x)) ))
  :hints (("Goal" :in-theory (enable aotsp))))
(defthm aot-rzero-p (implies (aotsp aots) (aotsp (aot-rzero b i m aots))))
(defthm aot-lcopy-p (implies (aotsp aots) (aotsp (aot-lcopy b i m aots))))
(in-theory (disable aotsp aot-rzero aot-lcopy aot-settled aot-cb update-aot-cb aot-cn update-aot-cn aot-a0 update-aot-a0 aot-a1 update-aot-a1 aot-a2 update-aot-a2 aot-ad update-aot-ad aot-ns update-aot-ns ))

(defun aot-meas (fl e j m k)
  (declare (xargs :guard t))
  (make-ord 2 (+ 1 (acl2-count e))
            (cond ((equal fl 0) (make-ord 1 100 0))
                  ((equal fl 6) (make-ord 1 50 (nfix (- (nfix m) (nfix j)))))
                  ((equal fl 5) (make-ord 1 (+ 2 (* 2 (nfix (- 7 (nfix k))))) 0))
                  ((equal fl 7) (make-ord 1 (+ 1 (* 2 (nfix (- 7 (nfix k))))) (nfix (- (nfix m) (nfix j)))))
                  (t (make-ord 1 1 (nfix (- (nfix m) (nfix j))))))))

(defthm aot-meas-o-p (o-p (aot-meas fl e j m k)))

; ---- THE INFERENCE --------------------------------------------------------------------------

(defun aot-ty (fl e j m k aots)
  (declare (xargs :stobjs aots :measure (aot-meas fl e j m k) :verify-guards nil
                  :guard (and (natp fl) (signed-byte-p 64 fl) (anp40p j) (anp40p m) (natp k) (signed-byte-p 64 k))))
  (let ((aots (aot-tick aots)))
    (cond
     ((or (equal (aot-k e) 0) (not (natp j)) (not (natp m)) (not (natp k))) (mv 1 1 aots))
     ((equal fl 0)
      (let ((kd (aot-k e)))
        (cond
         ((equal kd 1) (mv (aot-cty e) 1 aots))
         ((equal kd 2) (mv (aot-get (aot-i2 e) aots) 1 aots))
         ((equal kd 5) (if (equal (aot-nk e) 0) (mv 1 1 aots) (aot-ty 1 e 0 (aot-nk e) 0 aots)))
         ((equal kd 4)
          (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e 0) 0 0 0 aots)
            (declare (ignore t0))
            (mv-let (t1 o1 aots) (aot-ty 0 (aot-kid e 1) 0 0 0 aots)
              (mv-let (t2 o2 aots) (aot-ty 0 (aot-kid e 2) 0 0 0 aots)
                (mv (aot-jn t1 t2) (aot-and o0 (aot-and o1 o2)) aots)))))
         ((equal kd 11) (aot-ty 2 e 0 (aot-i2 e) 0 aots))
         ((equal kd 12) (aot-ty 6 e 0 (aot-i2 e) 0 aots))
         ((equal kd 16)
          (let* ((nk (aot-nk e)) (cb (aot-cb aots)) (cn (aot-cn aots)) (hit (equal (aot-rs e) cb))
                 (mm (if (and hit (anp40p cn) (< nk cn)) cn nk)))
            (mv-let (t0 o0 aots) (aot-ty 3 e 0 mm 0 aots)
              (declare (ignore t0))
              (mv 0 (if (and (equal o0 1) hit (equal nk cn) (equal (aot-rn e) cn)) 1 0) aots))))
         ((equal kd 6)
          (let ((s0 (aot-a0 aots)) (s1 (aot-a1 aots)) (s2 (aot-a2 aots)) (sd (aot-ad aots)))
            (let* ((aots (update-aot-a0 1 aots)) (aots (update-aot-a1 1 aots))
                   (aots (update-aot-a2 1 aots)) (aots (update-aot-ad 0 aots)))
              (mv-let (th oh aots) (aot-ty 0 (aot-kid e 0) 0 0 0 aots)
                (declare (ignore th))
                (mv-let (tw ow aots) (aot-ty 4 e 1 (aot-nk e) 0 aots)
                  (declare (ignore tw))
                  (let* ((tc (aot-optab (aot-hop e) (if (< 0 (aot-nk e)) (- (aot-nk e) 1) 0)
                                        (aot-a0 aots) (aot-a1 aots) (aot-a2 aots)))
                         (aots (update-aot-a0 s0 aots)) (aots (update-aot-a1 s1 aots))
                         (aots (update-aot-a2 s2 aots)) (aots (update-aot-ad sd aots)))
                    (mv tc (aot-and oh ow) aots)))))))
         (t (mv 1 1 aots)))))
     ((equal fl 1)
      (if (< j m)
          (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e j) 0 0 0 aots)
            (if (< (+ 1 j) m)
                (mv-let (t1 o1 aots) (aot-ty 1 e (+ 1 j) m 0 aots) (mv t1 (aot-and o0 o1) aots))
              (mv t0 o0 aots)))
        (mv 1 1 aots)))
     ((or (equal fl 2) (equal fl 6))
      (if (< j m)
          (let* ((s (+ (aot-s2 e) j)) (old (aot-raw s aots)) (fresh (equal (aot-get s aots) 1)))
            (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e j) 0 0 0 aots)
              (let ((aots (aot-put s t0 aots)))
                (mv-let (t1 o1 aots) (aot-ty fl e (+ 1 j) m 0 aots)
                  (let ((aots (aot-put s old aots)))
                    (mv t1 (if (and fresh (equal o0 1) (equal o1 1)) 1 0) aots))))))
        (if (equal fl 2)
            (aot-ty 0 (aot-kid e m) 0 0 0 aots)
          (let* ((b (aot-s2 e)) (ocb (aot-cb aots)) (ocn (aot-cn aots))
                 (dj (and (anp40p ocb) (anp40p ocn) (<= (+ ocb ocn) b)))
                 (aots (aot-rzero b 0 m aots))
                 (aots (update-aot-cb b aots)) (aots (update-aot-cn m aots)))
            (mv-let (t1 o1 aots) (aot-ty 5 e 0 m 0 aots)
              (let* ((aots (update-aot-cb ocb aots)) (aots (update-aot-cn ocn aots)))
                (mv t1 (if (and dj (equal o1 1)) 1 0) aots)))))))
     ((equal fl 5)
      (let ((b (aot-s2 e)))
        (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e m) 0 0 0 aots)
          (cond ((aot-settled b 0 m aots) (let ((aots (aot-lcopy b 0 m aots))) (mv t0 o0 aots)))
                ((< 4 k) (mv-let (t1 o1 aots) (aot-ty 8 e 0 m k aots) (mv t1 (aot-and o0 o1) aots)))
                (t (mv-let (t1 o1 aots) (aot-ty 7 e 0 m k aots) (mv t1 (aot-and o0 o1) aots)))))))
     ((equal fl 7)
      (if (< j m)
          (let* ((s (+ (aot-s2 e) j)) (old (aot-raw s aots))
                 (aots (aot-put s (aot-jn (aot-get s aots) (aot-rget s aots)) aots)))
            (mv-let (t1 o1 aots) (aot-ty 7 e (+ 1 j) m k aots)
              (let ((aots (aot-put s old aots))) (mv t1 o1 aots))))
        (if (< k 5) (aot-ty 5 e 0 m (+ 1 k) aots) (mv 1 1 aots))))
     ((equal fl 8)
      (if (< j m)
          (let* ((s (+ (aot-s2 e) j)) (old (aot-raw s aots)) (aots (aot-put s 1 aots)))
            (mv-let (t1 o1 aots) (aot-ty 8 e (+ 1 j) m k aots)
              (let ((aots (aot-put s old aots))) (mv t1 o1 aots))))
        (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e m) 0 0 0 aots)
          (let ((aots (aot-lcopy (aot-s2 e) 0 m aots))) (mv t0 o0 aots)))))
     ((equal fl 3)
      (if (< j m)
          (mv-let (t0 o0 aots) (aot-ty 0 (aot-kid e j) 0 0 0 aots)
            (let ((aots (if (and (equal (aot-rs e) (aot-cb aots)) (< j (aot-cn aots)))
                            (aot-rjn (+ (aot-rs e) j) t0 aots)
                          aots)))
              (mv-let (t1 o1 aots) (aot-ty 3 e (+ 1 j) m 0 aots)
                (declare (ignore t1))
                (mv 0 (aot-and o0 o1) aots))))
        (mv 0 1 aots)))
     ((equal fl 4)
      (if (< j m)
          (let* ((a (aot-kid e j)) (h (aot-hop e))
                 (cast (and (equal j 1) (or (equal h 7) (equal h 8) (equal h 9)) (equal (aot-k a) 6)
                            (equal (aot-hop a) 20) (not (equal (aot-kw (aot-kid a 2)) 0)))))
            (mv-let (t0 o0 aots) (aot-ty 0 a 0 0 0 aots)
              (mv-let (ti oi aots) (aot-ty 0 (aot-kid a (if cast 1 -1)) 0 0 0 aots)
                (let* ((d (and cast (equal ti (aot-kw (aot-kid a 2)))))
                       (aots (cond ((equal j 1) (let ((aots (update-aot-a0 (if d ti t0) aots)))
                                                  (update-aot-ad (if d 1 0) aots)))
                                   ((equal j 2) (update-aot-a1 t0 aots))
                                   ((equal j 3) (update-aot-a2 t0 aots))
                                   (t aots))))
                  (mv-let (t1 o1 aots) (aot-ty 4 e (+ 1 j) m 0 aots)
                    (declare (ignore t1))
                    (mv 0 (aot-and o0 (aot-and oi o1)) aots))))))
        (mv 0 1 aots)))
     (t (mv 1 1 aots)))))

(defthm aot-ty-code
  (and (natp (mv-nth 0 (aot-ty fl e j m k aots))) (<= (mv-nth 0 (aot-ty fl e j m k aots)) 6)
       (natp (mv-nth 1 (aot-ty fl e j m k aots))) (<= (mv-nth 1 (aot-ty fl e j m k aots)) 1))
  :hints (("Goal" :induct (aot-ty fl e j m k aots) :in-theory (disable aot-get aot-optab aot-jn aot-rzero aot-settled aot-lcopy aot-put aot-raw aot-rjn aot-tick))))

(defthm aot-ty-sb64 (and (signed-byte-p 64 (car (aot-ty fl e j m k aots))) (signed-byte-p 64 (mv-nth 1 (aot-ty fl e j m k aots)))
                         (natp (car (aot-ty fl e j m k aots))) (<= (car (aot-ty fl e j m k aots)) 6))
  :hints (("Goal" :use aot-ty-code :in-theory (disable aot-ty aot-ty-code)))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (car (aot-ty fl e j m k aots))) :hints (("Goal" :use aot-ty-code :in-theory (disable aot-ty aot-ty-code))))
                 (:linear :corollary (<= (car (aot-ty fl e j m k aots)) 6) :hints (("Goal" :use aot-ty-code :in-theory (disable aot-ty aot-ty-code))))))

(defthm aot-ty-aotsp
  (implies (and (aotsp aots) (anp40p m)) (aotsp (mv-nth 2 (aot-ty fl e j m k aots))))
  :hints (("Goal" :induct (aot-ty fl e j m k aots))))

(verify-guards aot-ty)
