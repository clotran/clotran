; clotran's persistent vector, formally (PLAN step 28).
;
; The model is OURS, not clj's: src/f/PersistentVector.f90's 32-way
; trie with no tail -- every node 32 slots, elements at level 0 -- and a
; VIEW for subvec, the trie shared and an offset and the trie's length
; kept beside it. A vector is (root count level off tlen); the Fortran's
; shift is 5 * level. Each function mirrors one there:
;
;   t-get     gcv_nth's walk           t-set    node_assoc
;   t-pop     node_pop                 v-nth    gcv_nth
;   v-conj    gcv_conj                 v-assoc  gcv_assoc
;   v-pop     gcv_pop                  v-subvec gcv_subvec
;
; and it proves, for every vector the operations can make:
;
;   VALUES  nth after assoc, conj, pop and subvec is what a list's would
;           be -- the element changed, appended, dropped or offset;
;   SHAPE   the trie holds its length and is never a level deeper than
;           it needs (32^level < tlen), through conj's growth and pop's
;           collapse alike;
;   COST    nth reads level+1 nodes, conj, assoc and pop copy level+1,
;           subvec none: with the shape, O(log32 n), and subvec O(1),
;           as clj's are (test/bigo.edn).

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

; ---- the trie --------------------------------------------------------

; the digit of j at level l: floor by 32 l times, then the low 5 bits --
; iand(ishft(j, -5*l), 31) in the Fortran
(defun dig (j l)
  (if (zp l) (mod (nfix j) 32) (dig (floor (nfix j) 32) (1- l))))

; how many indices a trie of level l holds: 32^(l+1)
(defun cap (l) (if (zp l) 32 (* 32 (cap (1- l)))))

(defun new-node () (make-list 32 :initial-element nil))

; gcv_nth's walk: level l down to 0, a child per 5 bits of j
(defun t-get (node l j)
  (declare (xargs :measure (nfix l)))
  (if (zp l)
      (nth (dig j 0) node)
    (t-get (nth (dig j l) node) (1- l) j)))

; node_assoc: the path to j copied, everything else shared; an unset
; (nil) child becomes a fresh node, which is how conj grows into a level
(defun t-set (node l j x)
  (declare (xargs :measure (nfix l)))
  (let ((node (if (consp node) node (new-node))))
    (if (zp l)
        (update-nth (dig j 0) x node)
      (update-nth (dig j l)
                  (t-set (nth (dig j l) node) (1- l) j x)
                  node))))

; THE KEY LEMMA: setting slot j leaves every other slot k as it was.
(defun all-nil (xs) (if (endp xs) t (and (null (car xs)) (all-nil (cdr xs)))))

(defthm nth-of-all-nil
  (implies (all-nil xs) (equal (nth i xs) nil)))

(defthm all-nil-new-node (all-nil (new-node)))

(defthm consp-new-node (consp (new-node)))

(defthm len-new-node (equal (len (new-node)) 32))

(in-theory (disable new-node (new-node)))

(defthm nth-of-new-node
  (equal (nth i (new-node)) nil))

(defthm t-get-of-nil
  (equal (t-get nil l k) nil))

(defthm t-get-of-new-node
  (equal (t-get (new-node) l k) nil))

; j and k take the same child at every level from l down
(defun same-path (j k l)
  (if (zp l)
      (equal (dig j 0) (dig k 0))
    (and (equal (dig j l) (dig k l)) (same-path j k (1- l)))))

(defun get-set-induct (node l j k)
  (declare (xargs :measure (nfix l)))
  (if (zp l)
      (list node j k)
    (get-set-induct (nth (dig j l) (if (consp node) node (new-node))) (1- l) j k)))

(defthm dig-natp (natp (dig j l)) :rule-classes :type-prescription)

(defthm dig-below-32 (< (dig j l) 32) :rule-classes :linear)

(defthm t-get-step
  (implies (not (zp l))
           (equal (t-get node l k) (t-get (nth (dig k l) node) (1- l) k))))

(defthm t-get-zero
  (implies (zp l) (equal (t-get node l k) (nth (dig k 0) node))))

(defthm t-set-step
  (implies (not (zp l))
           (equal (t-set node l j x)
                  (let ((node (if (consp node) node (new-node))))
                    (update-nth (dig j l) (t-set (nth (dig j l) node) (1- l) j x) node)))))

(defthm t-set-zero
  (implies (zp l)
           (equal (t-set node l j x)
                  (update-nth (dig j 0) x (if (consp node) node (new-node))))))

(in-theory (disable t-get t-set))

(defthm t-get-of-t-set
  (equal (t-get (t-set node l j x) l k)
         (if (same-path j k l) x (t-get node l k)))
  :hints (("Goal" :induct (get-set-induct node l j k))))

; the steps were for the lemma above; from here a trie is read through it
(in-theory (disable t-get-step t-set-step t-get-zero t-set-zero))

; Below the capacity, sharing every digit is being the same index.
(defun floor-induct (j k l)
  (if (zp l)
      (list j k)
    (floor-induct (floor j 32) (floor k 32) (1- l))))

(defthm dig-of-floor
  (implies (and (natp j) (not (zp l)))
           (equal (dig j l) (dig (floor j 32) (1- l)))))

(defthm same-path-low-first
  (implies (and (natp j) (natp k) (not (zp l)))
           (equal (same-path j k l)
                  (and (equal (mod j 32) (mod k 32))
                       (same-path (floor j 32) (floor k 32) (1- l)))))
  :hints (("Goal" :induct (same-path j k l)
                  :expand ((same-path (floor j 32) (floor k 32) (+ -1 l))))))

(defthm cap-integer (integerp (cap l)) :rule-classes :type-prescription)

(defthm cap-at-least-32 (<= 32 (cap l)) :rule-classes :linear)

(defthm floor-below-cap
  (implies (and (natp j) (not (zp l)) (< j (cap l)))
           (< (floor j 32) (cap (1- l))))
  :rule-classes :linear)

(defthm same-path-is-equal
  (implies (and (natp j) (natp k) (< j (cap l)) (< k (cap l)))
           (equal (same-path j k l) (equal j k)))
  :hints (("Goal" :induct (floor-induct j k l))
          ("Subgoal *1/2" :use ((:instance floor-mod-elim (x j) (y 32))
                                 (:instance floor-mod-elim (x k) (y 32))))))

(in-theory (disable same-path same-path-low-first dig-of-floor))

; An index below 32^l has 0 as its digit at level l: the top level's
; first child is all of it. conj's growth puts the old root there, and
; pop's collapse takes it back out.
(defthm dig-zero-below-cap
  (implies (and (natp m) (natp l) (< m (cap l)))
           (equal (dig m (1+ l)) 0))
  :hints (("Goal" :induct (floor-induct m m l) :in-theory (enable dig-of-floor))))

; conj's growth: the old root as the new root's first child keeps
; every old index where it was
(defthm t-get-under-new-root
  (implies (and (natp m) (natp l) (< m (cap l)))
           (equal (t-get (cons r rest) (1+ l) m) (t-get r l m)))
  :hints (("Goal" :in-theory (enable t-get-step)
                  :use ((:instance dig-zero-below-cap (m m) (l l))))))

; ---- pop: node_pop ----------------------------------------------------
;
; element i let go; a node left empty (i first in it) becomes nil
(defun t-pop (node l i)
  (declare (xargs :measure (nfix l)))
  (if (zp l)
      (if (equal (dig i 0) 0) nil (update-nth (dig i 0) nil node))
    (let ((sub (t-pop (nth (dig i l) node) (1- l) i)))
      (if (and (null sub) (equal (dig i l) 0))
          nil
        (update-nth (dig i l) sub node)))))

; k before i, digit by digit from the top
(defun lex-less (k i l)
  (if (zp l)
      (< (dig k 0) (dig i 0))
    (or (< (dig k l) (dig i l))
        (and (equal (dig k l) (dig i l)) (lex-less k i (1- l))))))

(defun pop-induct (node l i)
  (declare (xargs :measure (nfix l)))
  (if (zp l)
      (list node i)
    (pop-induct (nth (dig i l) node) (1- l) i)))

; Popping i leaves every element before it as it was.
(defthm t-get-of-t-pop
  (implies (lex-less k i l)
           (equal (t-get (t-pop node l i) l k) (t-get node l k)))
  :hints (("Goal" :induct (pop-induct node l i)
                  :in-theory (enable t-get-step t-get-zero))))

(defthm lex-less-low-first
  (implies (and (natp k) (natp i) (not (zp l)))
           (equal (lex-less k i l)
                  (or (lex-less (floor k 32) (floor i 32) (1- l))
                      (and (same-path (floor k 32) (floor i 32) (1- l))
                           (< (mod k 32) (mod i 32))))))
  :hints (("Goal" :induct (lex-less k i l)
                  :in-theory (enable same-path dig-of-floor)
                  :expand ((lex-less (floor k 32) (floor i 32) (+ -1 l))
                           (same-path (floor k 32) (floor i 32) (+ -1 l))))))

; numeric order is digit order, below the capacity
(defthm floor-monotone
  (implies (and (natp k) (natp i) (< k i))
           (<= (floor k 32) (floor i 32)))
  :rule-classes :linear)

(defthm same-floor-mod-less
  (implies (and (natp k) (natp i) (< k i) (equal (floor k 32) (floor i 32)))
           (< (mod k 32) (mod i 32)))
  :hints (("Goal" :use ((:instance floor-mod-elim (x k) (y 32))
                        (:instance floor-mod-elim (x i) (y 32))))))

(defthm less-is-lex-less
  (implies (and (natp k) (natp i) (< k i) (< i (cap l)))
           (lex-less k i l))
  :hints (("Goal" :induct (floor-induct k i l)
                  :in-theory (e/d (same-path-low-first) (lex-less)))
          ("Subgoal *1/2" :cases ((< (floor k 32) (floor i 32)))
                          :expand ((lex-less k i 0)))
          ("Subgoal *1/1" :expand ((lex-less k i l)))))

(in-theory (disable dig t-pop lex-less))

; ---- the vector ----------------------------------------------------------
;
; (root count level off tlen): gc_slot 1, i1, i2/5, v_off, v_tlen

(defun v-root (v) (nth 0 v))
(defun v-count (v) (nth 1 v))
(defun v-level (v) (nth 2 v))
(defun v-off (v) (nth 3 v))
(defun v-tlen (v) (nth 4 v))

; THE SHAPE: the view inside the trie, the trie inside its capacity,
; and no level more than it needs -- 32^level < tlen
(defun v-ok (v)
  (and (natp (v-count v)) (natp (v-level v)) (natp (v-off v)) (natp (v-tlen v))
       (<= (+ (v-off v) (v-count v)) (v-tlen v))
       (<= (v-tlen v) (cap (v-level v)))
       (or (zp (v-level v)) (< (cap (1- (v-level v))) (v-tlen v)))))

(defun v-empty () (list nil 0 0 0 0))

(defun v-nth (v i) (t-get (v-root v) (v-level v) (+ (v-off v) i)))

(defun v-assoc (v i x)
  (list (t-set (v-root v) (v-level v) (+ (v-off v) i) x)
        (v-count v) (v-level v) (v-off v) (v-tlen v)))

; gcv_conj: at off + count; past the capacity, a level more first
(defun v-conj (v x)
  (let* ((j (+ (v-off v) (v-count v)))
         (tl (max (v-tlen v) (1+ j))))
    (if (<= (cap (v-level v)) j)
        (list (t-set (update-nth 0 (v-root v) (new-node)) (1+ (v-level v)) j x)
              (1+ (v-count v)) (1+ (v-level v)) (v-off v) tl)
      (list (t-set (v-root v) (v-level v) j x)
            (1+ (v-count v)) (v-level v) (v-off v) tl))))

; pop's collapse: while the rest fits under the first child
(defun collapse (root l n)
  (declare (xargs :measure (nfix l)))
  (if (and (not (zp l)) (<= n (cap (1- l))))
      (collapse (nth 0 root) (1- l) n)
    (list root l)))

(defun v-pop (v)
  (cond ((<= (v-count v) 1) (v-empty))
        ((or (not (equal (v-off v) 0)) (not (equal (v-count v) (v-tlen v))))
         (list (v-root v) (1- (v-count v)) (v-level v) (v-off v) (v-tlen v)))
        (t (let ((c (collapse (t-pop (v-root v) (v-level v) (1- (v-count v)))
                              (v-level v) (1- (v-count v)))))
             (list (car c) (1- (v-count v)) (cadr c) 0 (1- (v-count v)))))))

(defun v-subvec (v lo hi)
  (if (<= hi lo)
      (v-empty)
    (list (v-root v) (- hi lo) (v-level v) (+ (v-off v) lo) (v-tlen v))))

; ---- VALUES: nth after each operation, as a list's ---------------------

(defthm v-nth-of-v-assoc
  (implies (and (v-ok v) (natp i) (natp k) (< i (v-count v)) (< k (v-count v)))
           (equal (v-nth (v-assoc v i x) k)
                  (if (equal i k) x (v-nth v k))))
  :hints (("Goal" :use ((:instance same-path-is-equal
                         (j (+ (v-off v) i)) (k (+ (v-off v) k)) (l (v-level v)))))))

(defthm v-nth-of-v-subvec
  (implies (and (< lo hi) (natp k))
           (equal (v-nth (v-subvec v lo hi) k) (v-nth v (+ lo k)))))

(defthm cap-of-1+ (implies (natp l) (equal (cap (1+ l)) (* 32 (cap l)))) :rule-classes nil)

(defthm v-nth-of-v-conj
  (implies (and (v-ok v) (natp k) (<= k (v-count v)))
           (equal (v-nth (v-conj v x) k)
                  (if (equal k (v-count v)) x (v-nth v k))))
  :hints (("Goal" :use ((:instance same-path-is-equal
                         (j (+ (v-off v) (v-count v))) (k (+ (v-off v) k)) (l (v-level v)))
                        (:instance same-path-is-equal
                         (j (+ (v-off v) (v-count v))) (k (+ (v-off v) k)) (l (1+ (v-level v))))
                        (:instance dig-zero-below-cap (m (+ (v-off v) k)) (l (v-level v)))
                        (:instance cap-of-1+ (l (v-level v)))))))

; collapse keeps every element below n where it was
(defthm t-get-of-collapse
  (implies (and (natp m) (< m n))
           (equal (t-get (car (collapse root l n)) (cadr (collapse root l n)) m)
                  (t-get root l m)))
  :hints (("Goal" :induct (collapse root l n) :in-theory (enable t-get-step))
          ("Subgoal *1/1" :use ((:instance dig-zero-below-cap (m m) (l (1- l)))))))

(defthm v-nth-of-v-pop
  (implies (and (v-ok v) (natp k) (< k (1- (v-count v))))
           (equal (v-nth (v-pop v) k) (v-nth v k)))
  :hints (("Goal" :use ((:instance less-is-lex-less (k k) (i (1- (v-count v))) (l (v-level v)))))))

; ---- SHAPE: every operation keeps it -------------------------------------

(defthm cap-monotone
  (implies (and (natp a) (natp b) (<= a b)) (<= (cap a) (cap b)))
  :rule-classes :linear
  :hints (("Goal" :induct (cap b))))

(defthm v-ok-of-v-empty (v-ok (v-empty)))

(defthm v-ok-of-v-assoc
  (implies (v-ok v) (v-ok (v-assoc v i x))))

(defthm v-ok-of-v-subvec
  (implies (and (v-ok v) (natp lo) (natp hi) (<= lo hi) (<= hi (v-count v)))
           (v-ok (v-subvec v lo hi))))

(defthm v-ok-of-v-conj
  (implies (v-ok v) (v-ok (v-conj v x)))
  :hints (("Goal" :use ((:instance cap-of-1+ (l (v-level v)))))))

(defthm collapse-shape
  (implies (and (natp l) (natp n) (<= n (cap l)))
           (let ((l2 (cadr (collapse root l n))))
             (and (natp l2) (<= n (cap l2))
                  (or (zp l2) (< (cap (1- l2)) n)))))
  :hints (("Goal" :induct (collapse root l n))))

(defthm v-ok-of-v-pop
  (implies (v-ok v) (v-ok (v-pop v)))
  :hints (("Goal" :use ((:instance collapse-shape
                         (root (t-pop (v-root v) (v-level v) (1- (v-count v))))
                         (l (v-level v)) (n (1- (v-count v))))))))

; ---- COST: nodes read or copied, as the Fortran's loops do -------------

; nth reads one node per level; conj, assoc and pop copy one per level
; (conj one more when it grows a level); subvec copies none
(defun nth-cost (v) (1+ (v-level v)))
(defun assoc-copies (v) (1+ (v-level v)))
(defun conj-copies (v)
  (if (<= (cap (v-level v)) (+ (v-off v) (v-count v))) (+ 2 (v-level v)) (1+ (v-level v))))
(defun pop-copies (v)
  (if (or (not (equal (v-off v) 0)) (not (equal (v-count v) (v-tlen v)))) 0 (1+ (v-level v))))
(defun subvec-copies (v) (declare (ignore v)) 0)

; THE LOG BOUND: a vector's level is at most any level that holds its
; trie -- level = the least l with tlen <= 32^(l+1), ceiling(log32 tlen)
; less one -- so every cost above is O(log32 n), and subvec O(1).
(defthm level-is-least
  (implies (and (v-ok v) (natp m) (<= (v-tlen v) (cap m)))
           (<= (v-level v) m))
  :hints (("Goal" :cases ((< m (v-level v))))
          ("Subgoal 1" :use ((:instance cap-monotone (a m) (b (1- (v-level v))))))))

; concretely: a trie of fewer than 2^35 elements (a 32-bit count is
; 2^31) is read in at most 7 nodes, and copied in at most 8
(defthm cap-6 (equal (cap 6) (expt 2 35)))

(defthm nth-cost-at-most-7
  (implies (and (v-ok v) (<= (v-tlen v) (expt 2 35)))
           (<= (nth-cost v) 7))
  :hints (("Goal" :use ((:instance level-is-least (m 6))))))

(defthm conj-copies-at-most-8
  (implies (and (v-ok v) (< (v-tlen v) (expt 2 35)))
           (<= (conj-copies v) 8))
  :hints (("Goal" :use ((:instance level-is-least (m 6))))))
