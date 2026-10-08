; clotran's VM, formally (PLAN step 30): THE IMPLEMENTATION-LEVEL
; COMPILER IS vcs2-compile. A program vmic-program compiles without an
; error or an overflow leaves the machine vmi-load-prog leaves for
; vcs2-program's lists -- in shape, in its invariant, reading back as
; exactly that program, at the start -- so vmi-correct's argument holds
; for it word for word (vmic-correct).
;
; The method: an instruction is "placed" at j when its four code words
; and its pool slot are the encoder's (ins-at); a range of them when each
; is (code-at). Writes elsewhere leave a placed instruction placed, so
; the backpatched jumps, written after the code between them, are
; harmless. An error or an overflow is sticky, so a compile that ends
; without one had none at any step.

(in-package "ACL2")

(include-book "vmic")
(include-book "vmi-proof")

(in-theory (disable nth update-nth))

; ---- THE RUNTIME'S OPERATIONS ARE car AND cdr ----------------------------------------------

(defthm rt-car-is (equal (rt-car x) (car x)))
(defthm rt-cdr-is (equal (rt-cdr x) (cdr x)))
(defthm rt-consp-is (equal (rt-consp x) (consp x)))
(defthm rt-is-is (equal (rt-is x k) (equal x k)))
(defthm rt-len-is (equal (rt-len x) (len x)))
(in-theory (disable rt-car rt-cdr rt-consp rt-is rt-len))

(defun size-ind (flg e)
  (declare (xargs :measure (acl2-count e)))
  (if (eq flg :args)
      (if (atom e) nil (list (size-ind :m (car e)) (size-ind :args (cdr e))))
    (if (atom e) nil (list (size-ind :m (cadr e)) (size-ind :m (caddr e)) (size-ind :m (cadddr e))
          (size-ind :args (cddr e)) (size-ind :args (cadr e)) (size-ind :args (cdr e))))))

(defthm vmic-size-flag
  (if (eq flg :args) (equal (vmic-size-args e) (s2code-len-args e)) (equal (vmic-size e) (s2code-len e)))
  :rule-classes nil
  :hints (("Goal" :induct (size-ind flg e))))

(defthm vmic-size-is (equal (vmic-size e) (s2code-len e)) :hints (("Goal" :use ((:instance vmic-size-flag (flg :m))))))
(defthm vmic-size-args-is (equal (vmic-size-args es) (s2code-len-args es))
  :hints (("Goal" :use ((:instance vmic-size-flag (flg :args) (e es))))))

; ---- ONE INSTRUCTION, PLACED -----------------------------------------------------------------

(defun pool-const (ins) (case (car ins) (:push (cadr ins)) (:prim (cadr ins)) (otherwise nil)))

; instruction j's word w
(defun ins-w (j w vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (v-codei (+ (* 4 (nfix j)) w) vmi))

(defun ins-at (j ins vmi)
  (declare (xargs :stobjs vmi :verify-guards nil))
  (let ((w (enc-words ins j)))
    (and (< (+ (* 4 (nfix j)) 3) (v-code-length vmi)) (< (nfix j) (v-pool-length vmi))
         (equal (ins-w j 0 vmi) (nth 0 w)) (equal (ins-w j 1 vmi) (nth 1 w))
         (equal (ins-w j 2 vmi) (nth 2 w)) (equal (ins-w j 3 vmi) (nth 3 w))
         (equal (v-pooli (nfix j) vmi) (pool-const ins)))))

(defun code-at (j code vmi)
  (declare (xargs :stobjs vmi :measure (acl2-count code) :verify-guards nil))
  (if (atom code) t (and (ins-at j (car code) vmi) (code-at (1+ (nfix j)) (cdr code) vmi))))

(defthm code-at-append
  (implies (natp j)
           (equal (code-at j (append a b) vmi) (and (code-at j a vmi) (code-at (+ j (len a)) b vmi)))))

; a placed instruction decodes as itself
(defthm ins-at-decodes
  (implies (and (natp j) (enc-ok-ins ins) (ins-at j ins vmi)) (equal (vmi-ins j vmi) ins))
  :hints (("Goal" :in-theory (enable vmi-ins vmi-w vmi-poolv ins-w))))

(defthm code-at-decodes
  (implies (and (natp j) (enc-ok-code code) (code-at j code vmi)) (equal (vmi-code-list j (len code) vmi) code))
  :hints (("Goal" :induct (code-at j code vmi) :in-theory (e/d (vmi-code-list) (ins-at vmi-ins enc-ok-ins)))))

; ---- vmic-put ------------------------------------------------------------------------------

(defthm vmic-put-fields
  (implies (not (member k '(3 6 7))) (equal (nth k (vmic-put pc op a b c v vmi)) (nth k vmi))))

(defthm vmic-put-lens
  (and (equal (len (nth 6 (vmic-put pc op a b c v vmi))) (len (nth 6 vmi)))
       (equal (len (nth 7 (vmic-put pc op a b c v vmi))) (len (nth 7 vmi)))))

(defthm vmic-put-status
  (implies (equal (nth 3 vmi) 2) (equal (nth 3 (vmic-put pc op a b c v vmi)) 2)))

(defthm vmic-put-ok-before
  (implies (not (equal (nth 3 (vmic-put pc op a b c v vmi)) 2)) (not (equal (nth 3 vmi) 2)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 3 (vmic-put pc op a b c v vmi))))))

(defthm vmic-put-ins-w
  (implies (and (natp j) (natp p) (not (equal j p)) (natp w) (< w 4))
           (equal (ins-w j w (vmic-put p op a b c v vmi)) (ins-w j w vmi)))
  :hints (("Goal" :cases ((< j p)))))

(defthm vmic-put-pool
  (implies (and (natp j) (natp p) (not (equal j p)))
           (equal (nth j (nth 7 (vmic-put p op a b c v vmi))) (nth j (nth 7 vmi)))))

(defthm vmic-put-elsewhere
  (implies (and (natp j) (natp p) (not (equal j p)))
           (equal (ins-at j ins (vmic-put p op a b c v vmi)) (ins-at j ins vmi)))
  :hints (("Goal" :in-theory (disable enc-words pool-const ins-w vmic-put))))

(defthm vmic-put-here
  (implies (and (natp p) (not (equal (nth 3 (vmic-put p op a b c v vmi)) 2)) (not (equal (nth 3 vmi) 2))
                (equal (nth 0 (enc-words ins p)) op) (equal (nth 1 (enc-words ins p)) a)
                (equal (nth 2 (enc-words ins p)) b) (equal (nth 3 (enc-words ins p)) c) (equal (pool-const ins) v))
           (ins-at p ins (vmic-put p op a b c v vmi)))
  :hints (("Goal" :in-theory (disable enc-words pool-const))))

(in-theory (disable ins-w))

(in-theory (disable vmic-put ins-at))

; ---- THE ENVIRONMENT -----------------------------------------------------------------------

(defthm vce-fields
  (and (equal (nth 0 (vce-fail vce)) (nth 0 vce))
       (equal (len (nth 0 (vce-fail vce))) (len (nth 0 vce)))
       (equal (len (nth 0 (vce-set n x vce))) (len (nth 0 vce)))
       (equal (len (nth 0 (vce-count n d k vce))) (len (nth 0 vce)))))

(defmacro failed (vce) `(not (equal (nth 1 ,vce) 0)))

(defthm vce-sticky
  (and (failed (vce-fail vce))
       (implies (failed vce) (failed (vce-set n x vce)))
       (implies (failed vce) (failed (vce-count n d k vce)))))

(defthm vce-set-below
  (implies (and (natp j) (natp n) (< j n)) (equal (nth j (nth 0 (vce-set n x vce))) (nth j (nth 0 vce)))))

(defthm vce-count-below
  (implies (and (natp j) (natp n) (< j n)) (equal (nth j (nth 0 (vce-count n d k vce))) (nth j (nth 0 vce)))))

(in-theory (disable vce-fail vce-set vce-count))

; ---- THE COMPILER'S INDUCTION ----------------------------------------------------------------

(defun vmic-call (flg e depth n self pc lch lcb lck vmi vce)
  (declare (xargs :stobjs (vmi vce) :verify-guards nil))
  (if (eq flg :args) (vmic-compile-args e depth n self pc vmi vce) (vmic-compile e depth n self pc lch lcb lck vmi vce)))

(defun-nx vmic-ind (flg e depth n self pc lch lcb lck vmi vce)
  (declare (xargs :measure (acl2-count e) :verify-guards nil))
  (if (eq flg :args)
      (if (consp e)
          (mv-let (pa vmi2 vce2) (vmic-compile (car e) depth n self pc -1 0 0 vmi vce)
            (list (vmic-ind :m (car e) depth n self pc -1 0 0 vmi vce)
                  (vmic-ind :args (cdr e) (1+ (nfix depth)) n self pa lch lcb lck vmi2 vce2)))
        nil)
    (let ((op (car e)) (pc (nfix pc)) (depth (nfix depth)) (n (nfix n)))
      (cond
       ((equal op :if)
        (mv-let (pa vmi2 vce2) (vmic-compile (cadr e) depth n self pc -1 0 0 vmi vce)
          (mv-let (pb vmi3 vce3) (vmic-compile (caddr e) depth n self (1+ pa) lch lcb lck vmi2 vce2)
            (list (vmic-ind :m (cadr e) depth n self pc -1 0 0 vmi vce)
                  (vmic-ind :m (caddr e) depth n self (1+ pa) lch lcb lck vmi2 vce2)
                  (vmic-ind :m (cadddr e) depth n self (1+ pb) lch lcb lck vmi3 vce3)))))
       ((equal op :let)
        (mv-let (pa vmi2 vce2) (vmic-compile (cadr e) depth n self pc -1 0 0 vmi vce)
          (list (vmic-ind :m (cadr e) depth n self pc -1 0 0 vmi vce)
                (vmic-ind :m (caddr e) (1+ depth) (1+ n) self pa lch lcb lck vmi2 (vce-set n depth vce2)))))
       ((or (equal op :add) (equal op :lt))
        (mv-let (pa vmi2 vce2) (vmic-compile (cadr e) depth n self pc -1 0 0 vmi vce)
          (list (vmic-ind :m (cadr e) depth n self pc -1 0 0 vmi vce)
                (vmic-ind :m (caddr e) (1+ depth) n self pa -1 0 0 vmi2 vce2))))
       ((or (equal op :mkclo) (equal op :prim)) (vmic-ind :args (cddr e) depth n self pc lch lcb lck vmi vce))
       ((equal op :callv)
        (mv-let (pa vmi2 vce2) (vmic-compile-args (cddr e) depth n self pc vmi vce)
          (list (vmic-ind :args (cddr e) depth n self pc lch lcb lck vmi vce)
                (vmic-ind :m (cadr e) (+ depth (len (cddr e))) n self pa -1 0 0 vmi2 vce2))))
       ((equal op :loop)
        (let ((k (len (cadr e))))
          (mv-let (head vmi2 vce2) (vmic-compile-args (cadr e) depth n self pc vmi vce)
            (list (vmic-ind :args (cadr e) depth n self pc lch lcb lck vmi vce)
                  (vmic-ind :m (caddr e) (+ depth k) (+ n k) self head head depth k vmi2 (vce-count n depth k vce2))))))
       ((equal op :recur) (vmic-ind :args (cdr e) depth n self pc lch lcb lck vmi vce))
       ((equal op :throw) (vmic-ind :m (cadr e) depth n self pc -1 0 0 vmi vce))
       ((equal op :try)
        (mv-let (pb vmi2 vce2) (vmic-compile (cadr e) depth n self (1+ pc) -1 0 0 vmi vce)
          (list (vmic-ind :m (cadr e) depth n self (1+ pc) -1 0 0 vmi vce)
                (vmic-ind :m (caddr e) (1+ depth) (1+ n) self (+ pb 2) -1 0 0 vmi2 (vce-set n depth vce2)))))
       (t (list depth n self pc lch lcb lck vmi vce))))))

; slides: k :slide instructions from pc
(defun vslides-ind (pc i vmi)
  (declare (xargs :stobjs vmi :measure (nfix i) :verify-guards nil))
  (if (zp i) vmi (let ((vmi (vmic-put pc 5 0 0 0 nil vmi))) (vslides-ind (1+ (nfix pc)) (1- i) vmi))))

(defthm vmic-slides-facts
  (and (implies (not (member k '(3 6 7))) (equal (nth k (vmic-slides pc i vmi)) (nth k vmi)))
       (equal (len (nth 6 (vmic-slides pc i vmi))) (len (nth 6 vmi)))
       (equal (len (nth 7 (vmic-slides pc i vmi))) (len (nth 7 vmi)))
       (implies (equal (nth 3 vmi) 2) (equal (nth 3 (vmic-slides pc i vmi)) 2)))
  :hints (("Goal" :induct (vslides-ind pc i vmi))))

(defthm vmic-slides-ok-before
  (implies (not (equal (nth 3 (vmic-slides pc i vmi)) 2)) (not (equal (nth 3 vmi) 2)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 3 (vmic-slides pc i vmi)))))
  :hints (("Goal" :use vmic-slides-facts :in-theory (disable vmic-slides-facts))))

(defthm vmic-slides-elsewhere
  (implies (and (natp j) (natp pc) (or (< j pc) (<= (+ pc (nfix i)) j)))
           (equal (ins-at j ins (vmic-slides pc i vmi)) (ins-at j ins vmi)))
  :hints (("Goal" :induct (vslides-ind pc i vmi))))

(defthm vmic-slides-code
  (implies (and (natp pc) (not (equal (nth 3 (vmic-slides pc i vmi)) 2)))
           (code-at pc (slides i) (vmic-slides pc i vmi)))
  :hints (("Goal" :induct (vslides-ind pc i vmi) :in-theory (enable slides))))

; the cursor: e's code is s2code-len long
(defthm vmic-pc-flag
  (equal (mv-nth 0 (vmic-call flg e depth n self pc lch lcb lck vmi vce))
         (+ (nfix pc) (if (eq flg :args) (s2code-len-args e) (s2code-len e))))
  :rule-classes nil
  :hints (("Goal" :induct (vmic-ind flg e depth n self pc lch lcb lck vmi vce) :in-theory (disable vmic-compile vmic-compile-args)
                  :expand ((vmic-compile e depth n self pc lch lcb lck vmi vce) (vmic-compile-args e depth n self pc vmi vce)))))

(defthm vmic-compile-pc
  (equal (mv-nth 0 (vmic-compile e depth n self pc lch lcb lck vmi vce)) (+ (nfix pc) (s2code-len e)))
  :hints (("Goal" :use ((:instance vmic-pc-flag (flg :m))))))

(defthm vmic-compile-args-pc
  (equal (mv-nth 0 (vmic-compile-args es depth n self pc vmi vce)) (+ (nfix pc) (s2code-len-args es)))
  :hints (("Goal" :use ((:instance vmic-pc-flag (flg :args) (e es))))))

(defmacro vmic-flag-lemma (name concl &key hyp)
  ; concl over (vmi2 vce2), the call's result
  `(progn
     (defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-FLAG") name)
       (let ((vmi2 (mv-nth 1 (vmic-call flg e depth n self pc lch lcb lck vmi vce)))
             (vce2 (mv-nth 2 (vmic-call flg e depth n self pc lch lcb lck vmi vce)))
             (pc2 (+ (nfix pc) (if (eq flg :args) (s2code-len-args e) (s2code-len e)))))
         (declare (ignorable vmi2 vce2 pc2))
         (implies (and ,@(or hyp '(t))) ,concl))
       :rule-classes nil
       :hints (("Goal" :induct (vmic-ind flg e depth n self pc lch lcb lck vmi vce) :in-theory (disable vmic-compile vmic-compile-args)
                :expand ((vmic-compile e depth n self pc lch lcb lck vmi vce) (vmic-compile-args e depth n self pc vmi vce)))))
     (defthm ,name
       (let ((vmi2 (mv-nth 1 (vmic-compile e depth n self pc lch lcb lck vmi vce)))
             (vce2 (mv-nth 2 (vmic-compile e depth n self pc lch lcb lck vmi vce)))
             (pc2 (+ (nfix pc) (s2code-len e))))
         (declare (ignorable vmi2 vce2 pc2))
         (implies (and ,@(or hyp '(t))) ,concl))
       :hints (("Goal" :use ((:instance ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-FLAG") name) (flg :m)))
                       :in-theory (disable vmic-compile vmic-compile-args))))
     (defthm ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-ARGS") name)
       (let ((vmi2 (mv-nth 1 (vmic-compile-args e depth n self pc vmi vce)))
             (vce2 (mv-nth 2 (vmic-compile-args e depth n self pc vmi vce)))
             (pc2 (+ (nfix pc) (s2code-len-args e))))
         (declare (ignorable vmi2 vce2 pc2))
         (implies (and ,@(or hyp '(t))) ,concl))
       :hints (("Goal" :use ((:instance ,(intern-in-package-of-symbol (concatenate 'string (symbol-name name) "-FLAG") name) (flg :args)))
                       :in-theory (disable vmic-compile vmic-compile-args))))))

(vmic-flag-lemma vmic-fields (equal (nth k vmi2) (nth k vmi)) :hyp ((not (member k '(3 6 7)))))
(vmic-flag-lemma vmic-lens (and (equal (len (nth 6 vmi2)) (len (nth 6 vmi))) (equal (len (nth 7 vmi2)) (len (nth 7 vmi)))
                                (equal (len (nth 0 vce2)) (len (nth 0 vce)))))
(vmic-flag-lemma vmic-status-sticky (equal (nth 3 vmi2) 2) :hyp ((equal (nth 3 vmi) 2)))
(vmic-flag-lemma vmic-err-sticky (failed vce2) :hyp ((failed vce)))

; a run that ends without an overflow or an error had none before
(defthm vmic-ok-before
  (and (implies (not (equal (nth 3 (mv-nth 1 (vmic-compile e depth n self pc lch lcb lck vmi vce))) 2))
                (not (equal (nth 3 vmi) 2)))
       (implies (not (failed (mv-nth 2 (vmic-compile e depth n self pc lch lcb lck vmi vce)))) (not (failed vce))))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 3 (mv-nth 1 (vmic-compile e depth n self pc lch lcb lck vmi vce)))))
                 (:forward-chaining :trigger-terms ((nth 1 (mv-nth 2 (vmic-compile e depth n self pc lch lcb lck vmi vce))))))
  :hints (("Goal" :use (vmic-status-sticky vmic-err-sticky) :in-theory (disable vmic-status-sticky vmic-err-sticky vmic-compile))))

(defthm vmic-args-ok-before
  (and (implies (not (equal (nth 3 (mv-nth 1 (vmic-compile-args e depth n self pc vmi vce))) 2))
                (not (equal (nth 3 vmi) 2)))
       (implies (not (failed (mv-nth 2 (vmic-compile-args e depth n self pc vmi vce)))) (not (failed vce))))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 3 (mv-nth 1 (vmic-compile-args e depth n self pc vmi vce)))))
                 (:forward-chaining :trigger-terms ((nth 1 (mv-nth 2 (vmic-compile-args e depth n self pc vmi vce))))))
  :hints (("Goal" :use (vmic-status-sticky-args vmic-err-sticky-args)
                  :in-theory (disable vmic-status-sticky-args vmic-err-sticky-args vmic-compile-args))))

(defthm vce-set-ok-before
  (implies (not (failed (vce-set n x vce))) (not (failed vce)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 1 (vce-set n x vce)))))
  :hints (("Goal" :use (vce-sticky) :in-theory (disable vce-sticky))))

(defthm vce-count-ok-before
  (implies (not (failed (vce-count n d k vce))) (not (failed vce)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 1 (vce-count n d k vce)))))
  :hints (("Goal" :use (vce-sticky) :in-theory (disable vce-sticky))))

; ---- WRITES ELSEWHERE LEAVE CODE PLACED -------------------------------------------------------

(defthm code-at-put-elsewhere
  (implies (and (natp a) (natp p) (or (< p a) (<= (+ a (len c)) p)))
           (equal (code-at a c (vmic-put p op x y z v vmi)) (code-at a c vmi)))
  :hints (("Goal" :induct (code-at a c vmi))))

(defthm code-at-slides-elsewhere
  (implies (and (natp a) (natp p) (or (<= (+ p (nfix i)) a) (<= (+ a (len c)) p)))
           (equal (code-at a c (vmic-slides p i vmi)) (code-at a c vmi)))
  :hints (("Goal" :induct (code-at a c vmi))))

(vmic-flag-lemma vmic-code-elsewhere (equal (code-at a c vmi2) (code-at a c vmi))
                 :hyp ((natp a) (or (<= (+ a (len c)) (nfix pc)) (<= pc2 a))))

; ---- THE ENVIRONMENT: cenv is a prefix of the array ----------------------------------------------

(defun pfx (a b) (if (atom a) t (and (consp b) (equal (car a) (car b)) (pfx (cdr a) (cdr b)))))

(defthm pfx-nth
  (implies (and (pfx c env) (natp i) (< i (len c))) (equal (nth i env) (nth i c)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm pfx-len (implies (pfx c env) (<= (len c) (len env))) :rule-classes :linear)

(defthm pfx-update-past
  (implies (and (pfx c env) (natp j) (<= (len c) j)) (pfx c (update-nth j x env)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm pfx-update-at
  (implies (and (pfx c env) (equal (len c) j) (< j (len env))) (pfx (append c (list x)) (update-nth j x env)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm pfx-update-0
  (implies (< 0 (len env)) (pfx (list x) (update-nth 0 x env)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm vce-set-pfx
  (and (implies (and (pfx c (nth 0 vce)) (<= (len c) (nfix n))) (pfx c (nth 0 (vce-set n x vce))))
       (implies (and (pfx c (nth 0 vce)) (equal (len c) (nfix n)) (not (failed (vce-set n x vce))) (not (failed vce)))
                (pfx (append c (list x)) (nth 0 (vce-set n x vce)))))
  :hints (("Goal" :in-theory (e/d (vce-set vce-fail) (pfx)))))

(defthm vce-set-pfx-0
  (implies (and (equal (nfix n) 0) (not (failed (vce-set n x vce))) (not (failed vce))) (pfx (list x) (nth 0 (vce-set n x vce))))
  :hints (("Goal" :in-theory (e/d (vce-set vce-fail) (pfx)))))

(defthm append-count-from-step
  (implies (and (natp d) (natp k) (< 0 k))
           (equal (append c (count-from d (+ d k))) (append (append c (list d)) (count-from (+ 1 d) (+ 1 d (1- k)))))))

(defthm vce-count-pfx-below
  (implies (and (pfx c (nth 0 vce)) (<= (len c) (nfix n))) (pfx c (nth 0 (vce-count n d k vce))))
  :hints (("Goal" :induct (vce-count n d k vce) :in-theory (enable vce-count))))

(defthm count-from-empty (equal (count-from d d) nil))
(defthm len-count-from-i (implies (and (natp i) (natp n)) (equal (len (count-from i n)) (nfix (- n i))))
  :hints (("Goal" :induct (count-from i n))))
(defthm len-count-from-k (implies (and (natp d) (natp k)) (equal (len (count-from d (+ d k))) k)))
(defthm pfx-atom (implies (atom a) (pfx a b)))
(defthm pfx-append-nil (equal (pfx (append c nil) env) (pfx c env)))

(defun-nx vcp-ind (c n d k vce)
  (declare (xargs :measure (nfix k) :verify-guards nil))
  (if (zp k) (list c n d vce)
    (let ((vce (vce-set n d vce))) (vcp-ind (append c (list d)) (1+ (nfix n)) (1+ (nfix d)) (1- k) vce))))

(defthm vce-count-pfx
  (implies (and (pfx c (nth 0 vce)) (equal (len c) (nfix n)) (natp d) (natp k) (not (failed (vce-count n d k vce))) (not (failed vce)))
           (pfx (append c (count-from d (+ d k))) (nth 0 (vce-count n d k vce))))
  :hints (("Goal" :induct (vcp-ind c n d k vce) :in-theory (disable append-count-from-step pfx count-from)
                  :expand ((vce-count n d k vce)))
          ("Subgoal *1/2" :use ((:instance append-count-from-step (k (nfix k)))))))

(vmic-flag-lemma vmic-env-frame (pfx c (nth 0 vce2)) :hyp ((pfx c (nth 0 vce)) (<= (len c) (nfix n))))

; ---- THE CODE: vcs2-compile's, placed from pc ------------------------------------------------

; vmic-ind, carrying vcs2's environment as the scopes extend it
(defun-nx vmic-indc (flg e depth n self pc lch lcb lck vmi vce cenv)
  (declare (xargs :measure (acl2-count e) :verify-guards nil))
  (if (eq flg :args)
      (if (consp e)
          (mv-let (pa vmi2 vce2) (vmic-compile (car e) depth n self pc -1 0 0 vmi vce)
            (list (vmic-indc :m (car e) depth n self pc -1 0 0 vmi vce cenv)
                  (vmic-indc :args (cdr e) (1+ (nfix depth)) n self pa lch lcb lck vmi2 vce2 cenv)))
        nil)
    (let ((op (car e)) (pc (nfix pc)) (depth (nfix depth)) (n (nfix n)))
      (cond
       ((equal op :if)
        (mv-let (pa vmi2 vce2) (vmic-compile (cadr e) depth n self pc -1 0 0 vmi vce)
          (mv-let (pb vmi3 vce3) (vmic-compile (caddr e) depth n self (1+ pa) lch lcb lck vmi2 vce2)
            (list (vmic-indc :m (cadr e) depth n self pc -1 0 0 vmi vce cenv)
                  (vmic-indc :m (caddr e) depth n self (1+ pa) lch lcb lck vmi2 vce2 cenv)
                  (vmic-indc :m (cadddr e) depth n self (1+ pb) lch lcb lck vmi3 vce3 cenv)))))
       ((equal op :let)
        (mv-let (pa vmi2 vce2) (vmic-compile (cadr e) depth n self pc -1 0 0 vmi vce)
          (list (vmic-indc :m (cadr e) depth n self pc -1 0 0 vmi vce cenv)
                (vmic-indc :m (caddr e) (1+ depth) (1+ n) self pa lch lcb lck vmi2 (vce-set n depth vce2)
                           (append cenv (list depth))))))
       ((or (equal op :add) (equal op :lt))
        (mv-let (pa vmi2 vce2) (vmic-compile (cadr e) depth n self pc -1 0 0 vmi vce)
          (list (vmic-indc :m (cadr e) depth n self pc -1 0 0 vmi vce cenv)
                (vmic-indc :m (caddr e) (1+ depth) n self pa -1 0 0 vmi2 vce2 cenv))))
       ((or (equal op :mkclo) (equal op :prim)) (vmic-indc :args (cddr e) depth n self pc lch lcb lck vmi vce cenv))
       ((equal op :callv)
        (mv-let (pa vmi2 vce2) (vmic-compile-args (cddr e) depth n self pc vmi vce)
          (list (vmic-indc :args (cddr e) depth n self pc lch lcb lck vmi vce cenv)
                (vmic-indc :m (cadr e) (+ depth (len (cddr e))) n self pa -1 0 0 vmi2 vce2 cenv))))
       ((equal op :loop)
        (let ((k (len (cadr e))))
          (mv-let (head vmi2 vce2) (vmic-compile-args (cadr e) depth n self pc vmi vce)
            (list (vmic-indc :args (cadr e) depth n self pc lch lcb lck vmi vce cenv)
                  (vmic-indc :m (caddr e) (+ depth k) (+ n k) self head head depth k vmi2 (vce-count n depth k vce2)
                             (append cenv (count-from depth (+ depth k))))))))
       ((equal op :recur) (vmic-indc :args (cdr e) depth n self pc lch lcb lck vmi vce cenv))
       ((equal op :throw) (vmic-indc :m (cadr e) depth n self pc -1 0 0 vmi vce cenv))
       ((equal op :try)
        (mv-let (pb vmi2 vce2) (vmic-compile (cadr e) depth n self (1+ pc) -1 0 0 vmi vce)
          (list (vmic-indc :m (cadr e) depth n self (1+ pc) -1 0 0 vmi vce cenv)
                (vmic-indc :m (caddr e) (1+ depth) (1+ n) self (+ pb 2) -1 0 0 vmi2 (vce-set n depth vce2)
                           (append cenv (list depth))))))
       (t (list depth n self pc lch lcb lck vmi vce cenv))))))

(defthm vmic-code-flag
  (let ((vmi2 (mv-nth 1 (vmic-call flg e depth n self pc lch lcb lck vmi vce)))
        (vce2 (mv-nth 2 (vmic-call flg e depth n self pc lch lcb lck vmi vce))))
    (implies (and (natp pc) (natp depth) (natp n) (integerp self) (integerp lch)
                  (pfx cenv (nth 0 vce)) (equal (len cenv) n)
                  (not (equal (nth 3 vmi2) 2)) (not (failed vce2)))
             (code-at pc (if (eq flg :args)
                             (vcs2-compile-args e depth cenv (if (< self 0) nil self) pc)
                           (vcs2-compile e depth cenv (if (< self 0) nil self) pc (if (< lch 0) nil (list lch lcb lck))))
                      vmi2)))
  :rule-classes nil
  :hints (("Goal" :induct (vmic-indc flg e depth n self pc lch lcb lck vmi vce cenv)
                  :in-theory (disable vmic-compile vmic-compile-args vcs2-compile vcs2-compile-args pfx count-from)
                  :expand ((:free (depth n self pc lch lcb lck vmi vce) (vmic-compile e depth n self pc lch lcb lck vmi vce))
                           (:free (depth n self pc vmi vce) (vmic-compile-args e depth n self pc vmi vce))
                           (:free (depth cenv self pc lc) (vcs2-compile e depth cenv self pc lc))
                           (:free (depth cenv self pc) (vcs2-compile-args e depth cenv self pc))))))

(defthm vmic-code
  (implies (and (natp pc) (natp depth) (natp n) (integerp self) (integerp lch)
                (pfx cenv (nth 0 vce)) (equal (len cenv) n)
                (not (equal (nth 3 (mv-nth 1 (vmic-compile e depth n self pc lch lcb lck vmi vce))) 2))
                (not (failed (mv-nth 2 (vmic-compile e depth n self pc lch lcb lck vmi vce))))
                (equal sv (if (< self 0) nil self)) (equal lc (if (< lch 0) nil (list lch lcb lck))))
           (code-at pc (vcs2-compile e depth cenv sv pc lc) (mv-nth 1 (vmic-compile e depth n self pc lch lcb lck vmi vce))))
  :hints (("Goal" :use ((:instance vmic-code-flag (flg :m))) :in-theory (disable vmic-compile vcs2-compile))))

(in-theory (disable vmic-compile vmic-compile-args vmic-slides))

; ---- A CLAUSE'S BODY -------------------------------------------------------------------------

; a clause's arity as the table holds it, and its rest flag
(defun cl-n (cl) (nfix (rt-nat (car cl))))
(defun cl-rest (cl) (if (equal (caddr cl) :rest) 1 0))
(defthm cl-rest-value (and (implies (equal (caddr cl) :rest) (equal (cl-rest cl) 1)) (implies (not (equal (caddr cl) :rest)) (equal (cl-rest cl) 0))))
(defthm cl-rest-1 (equal (equal (cl-rest cl) 1) (equal (caddr cl) :rest)))
(defthm len-vcs2-body (equal (len (vcs2-body cl pc)) (+ 1 (s2code-len (cadr cl)))) :hints (("Goal" :in-theory (enable vcs2-body))))

(defthm vmic-body-facts
  (and (implies (not (member k '(3 6 7))) (equal (nth k (mv-nth 1 (vmic-body cl pc vmi vce))) (nth k vmi)))
       (equal (len (nth 6 (mv-nth 1 (vmic-body cl pc vmi vce)))) (len (nth 6 vmi)))
       (equal (len (nth 7 (mv-nth 1 (vmic-body cl pc vmi vce)))) (len (nth 7 vmi)))
       (implies (equal (nth 3 vmi) 2) (equal (nth 3 (mv-nth 1 (vmic-body cl pc vmi vce))) 2))
       (implies (failed vce) (failed (mv-nth 2 (vmic-body cl pc vmi vce))))
       (natp (mv-nth 0 (vmic-body cl pc vmi vce)))
       (<= (nfix pc) (mv-nth 0 (vmic-body cl pc vmi vce)))))

(defthm vmic-body-pc
  (implies (not (failed (mv-nth 2 (vmic-body cl pc vmi vce))))
           (equal (mv-nth 0 (vmic-body cl pc vmi vce)) (+ (nfix pc) 1 (s2code-len (cadr cl))))))

(defthm vmic-body-pc-car
  (and (natp (car (vmic-body cl pc vmi vce)))
       (implies (not (failed (mv-nth 2 (vmic-body cl pc vmi vce))))
                (equal (car (vmic-body cl pc vmi vce)) (+ (nfix pc) 1 (s2code-len (cadr cl))))))
  :hints (("Goal" :use (vmic-body-pc vmic-body-facts) :in-theory (disable vmic-body-pc vmic-body-facts vmic-body))))

(defthm vmic-body-pc-car-linear
  (<= (nfix pc) (car (vmic-body cl pc vmi vce))) :rule-classes :linear
  :hints (("Goal" :use (vmic-body-facts) :in-theory (disable vmic-body-facts vmic-body))))

(defthm vmic-body-pc-car-natp
  (natp (car (vmic-body cl pc vmi vce))) :rule-classes :type-prescription
  :hints (("Goal" :use (vmic-body-facts) :in-theory (disable vmic-body-facts vmic-body))))

(defthm vmic-body-ok-before
  (and (implies (not (equal (nth 3 (mv-nth 1 (vmic-body cl pc vmi vce))) 2)) (not (equal (nth 3 vmi) 2)))
       (implies (not (failed (mv-nth 2 (vmic-body cl pc vmi vce)))) (not (failed vce))))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 3 (mv-nth 1 (vmic-body cl pc vmi vce)))))
                 (:forward-chaining :trigger-terms ((nth 1 (mv-nth 2 (vmic-body cl pc vmi vce))))))
  :hints (("Goal" :use (vmic-body-facts) :in-theory (disable vmic-body-facts vmic-body))))

(defthm vmic-body-elsewhere
  (implies (and (natp a) (natp pc) (<= (+ a (len c)) pc))
           (equal (code-at a c (mv-nth 1 (vmic-body cl pc vmi vce))) (code-at a c vmi))))

(defthm vmic-body-ok
  (implies (and (natp pc) (not (equal (nth 3 (mv-nth 1 (vmic-body cl pc vmi vce))) 2))
                (not (failed (mv-nth 2 (vmic-body cl pc vmi vce)))))
           (code-at pc (vcs2-body cl pc) (mv-nth 1 (vmic-body cl pc vmi vce))))
  :hints (("Goal" :in-theory (e/d (vcs2-body) (vcs2-compile))
                  :use ((:instance vce-count-pfx (c nil) (n 0) (d 0)
                                   (k (if (equal (caddr cl) :rest) (1+ (car cl)) (car cl))))))))

; a body compiled without an error had a natural arity
(defthm vmic-body-arity
  (implies (not (failed (mv-nth 2 (vmic-body cl pc vmi vce)))) (and (natp (car cl)) (< (car cl) 2147483648)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 1 (mv-nth 2 (vmic-body cl pc vmi vce)))))))

(defthm cl-n-is (implies (and (natp (car cl)) (< (car cl) 2147483648)) (equal (cl-n cl) (car cl))))

(in-theory (disable vmic-body vcs2-body cl-n cl-rest cl-n-is))

; ---- THE TABLE'S ENTRIES -----------------------------------------------------------------------

(defthm vmic-clause-entry-facts
  (let ((g (vmic-clause-entry ci n pc rest vmi)))
    (and (implies (not (member k '(3 16 17 18))) (equal (nth k g) (nth k vmi)))
         (equal (len (nth 16 g)) (len (nth 16 vmi))) (equal (len (nth 17 g)) (len (nth 17 vmi)))
         (equal (len (nth 18 g)) (len (nth 18 vmi)))
         (implies (equal (nth 3 vmi) 2) (equal (nth 3 g) 2))
         (implies (and (natp j) (natp ci) (not (equal j ci)) (member k '(16 17 18))) (equal (nth j (nth k g)) (nth j (nth k vmi))))
         (implies (and (natp ci) (not (equal (nth 3 g) 2)))
                  (and (equal (nth ci (nth 16 g)) n) (equal (nth ci (nth 17 g)) pc)
                       (equal (nth ci (nth 18 g)) rest))))))

(defthm vmic-clause-entry-ok-before
  (implies (not (equal (nth 3 (vmic-clause-entry ci n pc rest vmi)) 2)) (not (equal (nth 3 vmi) 2)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 3 (vmic-clause-entry ci n pc rest vmi))))))

(defthm vmic-fn-entry-facts
  (let ((g (vmic-fn-entry f ci count vmi)))
    (and (implies (not (member k '(3 14 15))) (equal (nth k g) (nth k vmi)))
         (implies (equal (nth 3 vmi) 2) (equal (nth 3 g) 2))
         (implies (and (natp j) (natp f) (not (equal j f)) (member k '(14 15))) (equal (nth j (nth k g)) (nth j (nth k vmi))))
         (implies (and (natp f) (not (equal (nth 3 g) 2)))
                  (and (equal (nth f (nth 14 g)) ci) (equal (nth f (nth 15 g)) count))))))

(defthm vmic-fn-entry-ok-before
  (implies (not (equal (nth 3 (vmic-fn-entry f ci count vmi)) 2)) (not (equal (nth 3 vmi) 2)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 3 (vmic-fn-entry f ci count vmi))))))

(defthm ins-at-entries
  (and (equal (ins-at j ins (vmic-clause-entry ci n pc rest vmi)) (ins-at j ins vmi))
       (equal (ins-at j ins (vmic-fn-entry f ci count vmi)) (ins-at j ins vmi)))
  :hints (("Goal" :in-theory (e/d (ins-at ins-w) (vmic-clause-entry vmic-fn-entry enc-words pool-const)))))

(defthm code-at-entries
  (and (equal (code-at a c (vmic-clause-entry ci n pc rest vmi)) (code-at a c vmi))
       (equal (code-at a c (vmic-fn-entry f ci count vmi)) (code-at a c vmi)))
  :hints (("Goal" :induct (code-at a c vmi) :in-theory (disable vmic-clause-entry vmic-fn-entry))))

(in-theory (disable vmic-clause-entry vmic-fn-entry))

; ---- THE CLAUSES -----------------------------------------------------------------------------

(defmacro vcl-b () '(vmic-body (car cls) pc (vmic-clause-entry ci (cl-n (car cls)) (nfix pc) (cl-rest (car cls)) vmi) vce))

(defthm vmic-clauses-step
  (equal (vmic-clauses cls ci pc vmi vce)
         (if (consp cls)
             (vmic-clauses (cdr cls) (1+ (nfix ci)) (mv-nth 0 (vcl-b)) (mv-nth 1 (vcl-b)) (mv-nth 2 (vcl-b)))
           (list (nfix pc) vmi vce)))
  :rule-classes ((:definition :controller-alist ((vmic-clauses t nil nil nil nil))))
  :hints (("Goal" :in-theory (enable cl-n cl-rest))))

(defun-nx vcl-ind (cls ci pc vmi vce)
  (declare (xargs :measure (acl2-count cls)))
  (if (consp cls) (vcl-ind (cdr cls) (1+ (nfix ci)) (mv-nth 0 (vcl-b)) (mv-nth 1 (vcl-b)) (mv-nth 2 (vcl-b))) nil))

(defmacro vcl () '(vmic-clauses cls ci pc vmi vce))
(defthm vmic-clauses-fields (implies (not (member k '(3 6 7 16 17 18))) (equal (nth k (mv-nth 1 (vcl))) (nth k vmi)))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))
(defthm vmic-clauses-len-6 (equal (len (nth 6 (mv-nth 1 (vcl)))) (len (nth 6 vmi)))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))
(defthm vmic-clauses-len-7 (equal (len (nth 7 (mv-nth 1 (vcl)))) (len (nth 7 vmi)))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))
(defthm vmic-clauses-len-16 (equal (len (nth 16 (mv-nth 1 (vcl)))) (len (nth 16 vmi)))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))
(defthm vmic-clauses-len-17 (equal (len (nth 17 (mv-nth 1 (vcl)))) (len (nth 17 vmi)))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))
(defthm vmic-clauses-len-18 (equal (len (nth 18 (mv-nth 1 (vcl)))) (len (nth 18 vmi)))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))
(defthm vmic-clauses-status-sticky (implies (equal (nth 3 vmi) 2) (equal (nth 3 (mv-nth 1 (vcl))) 2))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))
(defthm vmic-clauses-err-sticky (implies (failed vce) (failed (mv-nth 2 (vcl))))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))
(defthm vmic-clauses-pc-natp (natp (mv-nth 0 (vcl))) :rule-classes :type-prescription
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))

(defthm vmic-clauses-ok-before
  (and (implies (not (equal (nth 3 (mv-nth 1 (vcl))) 2)) (not (equal (nth 3 vmi) 2)))
       (implies (not (failed (mv-nth 2 (vcl)))) (not (failed vce))))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 3 (mv-nth 1 (vcl)))))
                 (:forward-chaining :trigger-terms ((nth 1 (mv-nth 2 (vcl))))))
  :hints (("Goal" :use (vmic-clauses-status-sticky vmic-clauses-err-sticky)
                  :in-theory (disable vmic-clauses-status-sticky vmic-clauses-err-sticky vmic-clauses))))

(defthm vmic-clauses-pc
  (implies (and (natp pc) (not (failed (mv-nth 2 (vcl)))))
           (equal (mv-nth 0 (vcl)) (+ pc (len (car (vcs2-clauses cls pc))))))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))

(defthm vmic-clauses-pc-car
  (and (natp (car (vcl)))
       (implies (and (natp pc) (not (failed (mv-nth 2 (vcl))))) (equal (car (vcl)) (+ pc (len (car (vcs2-clauses cls pc)))))))
  :hints (("Goal" :use (vmic-clauses-pc vmic-clauses-pc-natp) :in-theory (disable vmic-clauses-pc vmic-clauses-pc-natp vmic-clauses))))

(defthm vmic-clauses-pc-car-natp (natp (car (vcl))) :rule-classes :type-prescription
  :hints (("Goal" :use (vmic-clauses-pc-natp) :in-theory (disable vmic-clauses-pc-natp vmic-clauses))))

(defthm vmic-clauses-pc-linear
  (<= (nfix pc) (car (vcl))) :rule-classes :linear
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))

(defthm vmic-clauses-elsewhere
  (implies (and (natp a) (natp pc) (<= (+ a (len c)) pc)) (equal (code-at a c (mv-nth 1 (vcl))) (code-at a c vmi)))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))

(defthm vmic-clauses-below
  (implies (and (natp j) (natp ci) (< j ci) (member k '(16 17 18)))
           (equal (nth j (nth k (mv-nth 1 (vcl)))) (nth j (nth k vmi))))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))

(defthm vmic-clauses-code
  (implies (and (natp pc) (not (equal (nth 3 (mv-nth 1 (vcl))) 2)) (not (failed (mv-nth 2 (vcl)))))
           (code-at pc (car (vcs2-clauses cls pc)) (mv-nth 1 (vcl))))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (disable vmic-clauses) :expand ((vcl)))))

; the table's fields as lists: each entry's component written at its index
(defun ent-rest (ent) (if (eq (caddr ent) :rest) 1 0))
(defun ent-at (k ent) (case k (16 (car ent)) (17 (cadr ent)) (otherwise (ent-rest ent))))
(defun cl-fld (k ents ci l)
  (if (atom ents) l (cl-fld k (cdr ents) (1+ (nfix ci)) (update-nth (nfix ci) (ent-at k (car ents)) l))))

(defthm ent-rest-vcs2 (equal (ent-rest (if (equal (caddr cl) :rest) (list a b :rest) (list a b))) (cl-rest cl))
  :hints (("Goal" :in-theory (enable cl-rest))))

(defthm enc-clauses-field
  (implies (and (member k '(16 17 18)) (natp ci)) (equal (nth k (enc-clauses ents ci vmi)) (cl-fld k ents ci (nth k vmi))))
  :hints (("Goal" :induct (enc-clauses ents ci vmi) :expand ((cl-fld k ents ci (nth k vmi))))))

(defthm vmic-clause-entry-field
  (implies (and (natp ci) (not (equal (nth 3 (vmic-clause-entry ci n pc rest vmi)) 2)))
           (and (equal (nth 16 (vmic-clause-entry ci n pc rest vmi)) (update-nth ci n (nth 16 vmi)))
                (equal (nth 17 (vmic-clause-entry ci n pc rest vmi)) (update-nth ci pc (nth 17 vmi)))
                (equal (nth 18 (vmic-clause-entry ci n pc rest vmi)) (update-nth ci rest (nth 18 vmi)))))
  :hints (("Goal" :in-theory (enable vmic-clause-entry))))

(defthm nfix-car-cl-n (implies (and (natp (car cl)) (< (car cl) 2147483648)) (equal (nfix (car cl)) (cl-n cl)))
  :hints (("Goal" :in-theory (enable cl-n))))
(in-theory (disable nfix-car-cl-n))

(defthm vmic-clauses-field
  (implies (and (member k '(16 17 18)) (natp pc) (natp ci) (not (equal (nth 3 (mv-nth 1 (vcl))) 2)) (not (failed (mv-nth 2 (vcl)))))
           (equal (nth k (mv-nth 1 (vcl))) (cl-fld k (cdr (vcs2-clauses cls pc)) ci (nth k vmi))))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :in-theory (e/d (nfix-car-cl-n) (vmic-clauses)) :expand ((vcl)))))

(in-theory (disable vmic-clauses))

; ---- THE FUNCTIONS ---------------------------------------------------------------------------

; the name check: a function's name is its id
(defun def-vce (d f vce)
  (declare (xargs :stobjs vce :verify-guards nil))
  (if (equal (rt-nat (car d)) (nfix f)) vce (vce-fail vce)))

(defthm def-vce-facts
  (and (equal (nth 0 (def-vce d f vce)) (nth 0 vce))
       (implies (failed vce) (failed (def-vce d f vce)))))

(defthm def-vce-ok-before
  (implies (not (failed (def-vce d f vce))) (not (failed vce)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 1 (def-vce d f vce))))))

(in-theory (disable def-vce))

(defmacro vdf-c () '(vmic-clauses (cdr (car defs)) ci pc (vmic-fn-entry f (nfix ci) (len (cdr (car defs))) vmi)
                                  (def-vce (car defs) f vce)))

(defthm vmic-defs-step
  (equal (vmic-defs defs f ci pc vmi vce)
         (if (consp defs)
             (vmic-defs (cdr defs) (1+ (nfix f)) (+ (nfix ci) (len (cdr (car defs))))
                        (mv-nth 0 (vdf-c)) (mv-nth 1 (vdf-c)) (mv-nth 2 (vdf-c)))
           (list (nfix pc) vmi vce)))
  :rule-classes ((:definition :controller-alist ((vmic-defs t nil nil nil nil nil))))
  :hints (("Goal" :in-theory (enable def-vce))))

(defun-nx vdf-ind (defs f ci pc vmi vce)
  (declare (xargs :measure (acl2-count defs)))
  (if (consp defs)
      (vdf-ind (cdr defs) (1+ (nfix f)) (+ (nfix ci) (len (cdr (car defs)))) (mv-nth 0 (vdf-c)) (mv-nth 1 (vdf-c)) (mv-nth 2 (vdf-c)))
    nil))

(defmacro vdf () '(vmic-defs defs f ci pc vmi vce))
(defthm vmic-defs-fields (implies (not (member k '(3 6 7 14 15 16 17 18))) (equal (nth k (mv-nth 1 (vdf))) (nth k vmi)))
  :hints (("Goal" :induct (vdf-ind defs f ci pc vmi vce) :in-theory (disable vmic-defs) :expand ((vdf)))))

(defthm vmic-defs-len-6 (equal (len (nth 6 (mv-nth 1 (vdf)))) (len (nth 6 vmi)))
  :hints (("Goal" :induct (vdf-ind defs f ci pc vmi vce) :in-theory (disable vmic-defs) :expand ((vdf)))))

(defthm vmic-defs-len-7 (equal (len (nth 7 (mv-nth 1 (vdf)))) (len (nth 7 vmi)))
  :hints (("Goal" :induct (vdf-ind defs f ci pc vmi vce) :in-theory (disable vmic-defs) :expand ((vdf)))))

(defthm vmic-defs-status-sticky (implies (equal (nth 3 vmi) 2) (equal (nth 3 (mv-nth 1 (vdf))) 2))
  :hints (("Goal" :induct (vdf-ind defs f ci pc vmi vce) :in-theory (disable vmic-defs) :expand ((vdf)))))

(defthm vmic-defs-err-sticky (implies (failed vce) (failed (mv-nth 2 (vdf))))
  :hints (("Goal" :induct (vdf-ind defs f ci pc vmi vce) :in-theory (disable vmic-defs) :expand ((vdf)))))

(defthm vmic-defs-ok-before
  (and (implies (not (equal (nth 3 (mv-nth 1 (vdf))) 2)) (not (equal (nth 3 vmi) 2)))
       (implies (not (failed (mv-nth 2 (vdf)))) (not (failed vce))))
  :rule-classes ((:forward-chaining :trigger-terms ((nth 3 (mv-nth 1 (vdf)))))
                 (:forward-chaining :trigger-terms ((nth 1 (mv-nth 2 (vdf))))))
  :hints (("Goal" :use (vmic-defs-status-sticky vmic-defs-err-sticky)
                  :in-theory (disable vmic-defs-status-sticky vmic-defs-err-sticky vmic-defs))))

(defthm vmic-defs-pc (implies (and (natp pc) (not (failed (mv-nth 2 (vdf))))) (equal (mv-nth 0 (vdf)) (+ pc (len (car (vcs2-defs defs pc))))))
  :hints (("Goal" :induct (vdf-ind defs f ci pc vmi vce) :in-theory (disable vmic-defs) :expand ((vdf)))))

(defthm vmic-defs-elsewhere (implies (and (natp a) (natp pc) (<= (+ a (len c)) pc)) (equal (code-at a c (mv-nth 1 (vdf))) (code-at a c vmi)))
  :hints (("Goal" :induct (vdf-ind defs f ci pc vmi vce) :in-theory (disable vmic-defs) :expand ((vdf)))))

(defthm vmic-defs-code (implies (and (natp pc) (not (equal (nth 3 (mv-nth 1 (vdf))) 2)) (not (failed (mv-nth 2 (vdf))))) (code-at pc (car (vcs2-defs defs pc)) (mv-nth 1 (vdf))))
  :hints (("Goal" :induct (vdf-ind defs f ci pc vmi vce) :in-theory (disable vmic-defs) :expand ((vdf)))))

; the function table's fields as lists
(defthm len-vcs2-clauses-entries (equal (len (cdr (vcs2-clauses cls pc))) (len cls)))

(defun fn-fld (k tab f ci l)
  (if (atom tab) l
    (fn-fld k (cdr tab) (1+ (nfix f)) (+ (nfix ci) (len (cdar tab)))
            (case k (14 (update-nth (nfix f) (nfix ci) l)) (15 (update-nth (nfix f) (len (cdar tab)) l))
              (otherwise (cl-fld k (cdar tab) ci l))))))

(defthm enc-fntab-field
  (implies (and (member k '(14 15 16 17 18)) (natp f) (natp ci))
           (equal (nth k (enc-fntab tab f ci vmi)) (fn-fld k tab f ci (nth k vmi))))
  :hints (("Goal" :induct (enc-fntab tab f ci vmi) :in-theory (disable enc-clauses) :expand ((fn-fld k tab f ci (nth k vmi))))))

(defthm vmic-fn-entry-field
  (implies (and (natp f) (not (equal (nth 3 (vmic-fn-entry f ci count vmi)) 2)))
           (and (equal (nth 14 (vmic-fn-entry f ci count vmi)) (update-nth f ci (nth 14 vmi)))
                (equal (nth 15 (vmic-fn-entry f ci count vmi)) (update-nth f count (nth 15 vmi)))))
  :hints (("Goal" :in-theory (enable vmic-fn-entry))))

(defthm vmic-defs-field
  (implies (and (member k '(14 15 16 17 18)) (natp pc) (natp f) (natp ci)
                (not (equal (nth 3 (mv-nth 1 (vdf))) 2)) (not (failed (mv-nth 2 (vdf)))))
           (equal (nth k (mv-nth 1 (vdf))) (fn-fld k (cdr (vcs2-defs defs pc)) f ci (nth k vmi))))
  :hints (("Goal" :induct (vdf-ind defs f ci pc vmi vce) :in-theory (disable vmic-defs) :expand ((vdf)))))

(in-theory (disable vmic-defs))

; ---- THE MACHINE'S SHAPE: every write lands inside the 19 fields --------------------------------

(defmacro shape19 (x) `(and (true-listp ,x) (equal (len ,x) 19)))

(defthm vmic-put-shape (implies (shape19 vmi) (shape19 (vmic-put pc op a b c v vmi))) :hints (("Goal" :in-theory (enable vmic-put))))
(defthm vmic-slides-shape (implies (shape19 vmi) (shape19 (vmic-slides pc i vmi)))
  :hints (("Goal" :induct (vslides-ind pc i vmi) :in-theory (enable vmic-slides))))
(defthm vmic-entries-shape
  (and (implies (shape19 vmi) (shape19 (vmic-clause-entry ci n pc rest vmi)))
       (implies (shape19 vmi) (shape19 (vmic-fn-entry f ci count vmi))))
  :hints (("Goal" :in-theory (enable vmic-clause-entry vmic-fn-entry))))

(vmic-flag-lemma vmic-shape (shape19 vmi2) :hyp ((shape19 vmi)))

(defthm vmic-body-shape (implies (shape19 vmi) (shape19 (mv-nth 1 (vmic-body cl pc vmi vce))))
  :hints (("Goal" :in-theory (enable vmic-body))))
(defthm vmic-clauses-shape (implies (shape19 vmi) (shape19 (mv-nth 1 (vcl))))
  :hints (("Goal" :induct (vcl-ind cls ci pc vmi vce) :expand ((vcl)))))
(defthm vmic-defs-shape (implies (shape19 vmi) (shape19 (mv-nth 1 (vdf))))
  :hints (("Goal" :induct (vdf-ind defs f ci pc vmi vce) :expand ((vdf)))))

