; clotran's array map and persistent list, formally (docs/model-coverage.md).
;
; src/f/PersistentArrayMap.f90 keeps a small map as two runs, keys and
; values, and a count (i1): index_of scans the keys in order for the
; first equal one (gc_equal; here `equal`), gcm_get answers its value or
; nil, gcm_assoc replaces the value in place or appends the pair,
; gcm_dissoc closes the hole up in order (PersistentArrayMap.without) or,
; for a transient (swap), moves the last entry into it
; (TransientArrayMap.doWithout); gcm_insert_at, gcm_replace_at and
; gcm_remove_at are the positional edits the sorted map (Assoc.f90)
; makes. Every one builds new runs: copy_run's first min(oldn, newn)
; values, then the loops below, modelled as the loops they are.
;
; src/f/PersistentList.f90 keeps a list as cons cells carrying their
; count (gcl_cons, gcl_first, gcl_rest, gcl_count): consing onto
; anything not a list starts a fresh one, the rest of a one-element or
; empty list is the empty list.
;
; What it proves:
;
;   ARRAY MAP  for a map whose runs are each `count` long and whose
;              keys are distinct (am-wf, which assoc and dissoc keep; the
;              positional edits are the sorted map's, which keeps it):
;              after assoc k is v and every other key what it was; after
;              dissoc, either way, k is gone and every other key what it
;              was; the count is the entries' number, up by one exactly
;              when assoc added a key, down by one exactly when dissoc
;              found one; dissoc without swap keeps the other keys' order
;              (the loop is remove-the-one); insert_at, replace_at and
;              remove_at do the positional edits, and remove_at undoes
;              insert_at
;   LIST       the count every cell carries is the chain's length (gl-wf,
;              which cons keeps); first of (cons x l) is x and its rest
;              is l when l is a list, else the empty list
;   COST       counting a step a key compared and a value copied or set:
;              index_of n, get n + 1, assoc 3n + 2, dissoc 5n, insert_at
;              2n + 2, remove_at 2n, replace_at 2n + 1; the list's count
;              1 step, where walking the chain is its length + 1
;
; Not modelled: the rooting (the roots(:) lists), and the heap's objects
; -- a run is the list it holds.

(in-package "ACL2")

; ---- lists, the few facts needed ------------------------------------------

(defun am-take (n l) (if (zp n) nil (cons (car l) (am-take (1- n) (cdr l)))))

(defthm len-am-take (equal (len (am-take n l)) (nfix n)))

(defthm len-update-nth-am
  (implies (< (nfix i) (len l)) (equal (len (update-nth i v l)) (len l))))

(defthm len-append-am (equal (len (append a b)) (+ (len a) (len b))))

(defthm nth-append-am
  (equal (nth i (append a b))
         (if (< (nfix i) (len a)) (nth i a) (nth (- (nfix i) (len a)) b))))

(defthm nth-update-nth-am
  (equal (nth i (update-nth j v l))
         (if (equal (nfix i) (nfix j)) v (nth i l))))

(defthm nth-am-take
  (implies (< (nfix i) (nfix n)) (equal (nth i (am-take n l)) (nth i l))))

; ---- the array map ----------------------------------------------------------
;
; a map: (count keys vals)

(defun am-count (m) (nfix (car m)))
(defun am-keys (m) (cadr m))
(defun am-vals (m) (caddr m))
(defun am-make (n ks vs) (list n ks vs))

(defun am-wf (m)
  (and (natp (car m))
       (true-listp (am-keys m)) (true-listp (am-vals m))
       (equal (len (am-keys m)) (car m)) (equal (len (am-vals m)) (car m))
       (no-duplicatesp-equal (am-keys m))))

; index_of: the 1-based place of the first key equal to k, or 0
(defun am-index-from (ks k i)
  (cond ((atom ks) 0) ((equal (car ks) k) i) (t (am-index-from (cdr ks) k (1+ i)))))

(defun am-index (m k) (am-index-from (am-keys m) k 1))

(defun am-contains (m k) (not (equal (am-index m k) 0)))

(defun am-get (m k)
  (let ((at (am-index m k))) (if (equal at 0) nil (nth (1- at) (am-vals m)))))

(defthm am-index-from-natp
  (implies (natp i) (natp (am-index-from ks k i)))
  :rule-classes :type-prescription)

(defthm am-index-from-member
  (implies (posp i)
           (iff (equal (am-index-from ks k i) 0) (not (member-equal k ks)))))

(defthm am-index-from-range
  (implies (and (posp i) (member-equal k ks))
           (and (<= i (am-index-from ks k i))
                (< (am-index-from ks k i) (+ i (len ks)))))
  :rule-classes :linear)

(defthm am-index-from-nth
  (implies (and (posp i) (member-equal k ks))
           (equal (nth (- (am-index-from ks k i) i) ks) k)))

; two keys present at one place are one key
(defthm am-index-from-injective
  (implies (and (posp i) (member-equal k ks) (member-equal k2 ks)
                (equal (am-index-from ks k i) (am-index-from ks k2 i)))
           (equal (equal k k2) t))
  :rule-classes nil
  :hints (("Goal" :use ((:instance am-index-from-nth) (:instance am-index-from-nth (k k2))) :in-theory (disable am-index-from-nth))))

(defthm am-index-from-append
  (implies (posp i)
           (equal (am-index-from (append ks (list x)) k i)
                  (if (member-equal k ks) (am-index-from ks k i)
                    (if (equal x k) (+ i (len ks)) 0)))))

(defthm member-append-am
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))

(defthm am-contains-is-member
  (iff (am-contains m k) (member-equal k (am-keys m))))

; gcm_assoc: copy_run of n (or n + 1) of each run, the value set in place
; or the pair appended
(defun am-assoc (m k v)
  (let ((n (am-count m)) (at (am-index m k)))
    (if (not (equal at 0))
        (am-make n (am-keys m) (update-nth (1- at) v (am-vals m)))
      (am-make (1+ n) (append (am-keys m) (list k)) (append (am-vals m) (list v))))))

(defthm am-assoc-get
  (implies (am-wf m)
           (equal (am-get (am-assoc m k v) k2) (if (equal k2 k) v (am-get m k2))))
  :hints (("Goal" :use ((:instance am-index-from-injective (ks (am-keys m)) (i 1))))))

(defthm am-assoc-contains
  (equal (am-contains (am-assoc m k v) k2) (or (equal k2 k) (am-contains m k2))))

(defthm am-assoc-count
  (implies (am-wf m)
           (equal (am-count (am-assoc m k v)) (if (am-contains m k) (am-count m) (+ 1 (am-count m))))))

(defthm no-dups-append-am
  (implies (and (no-duplicatesp-equal l) (not (member-equal k l)))
           (no-duplicatesp-equal (append l (list k)))))

(defthm true-listp-update-nth-am
  (implies (true-listp l) (true-listp (update-nth i v l))))

(defthm am-assoc-wf (implies (am-wf m) (am-wf (am-assoc m k v))))

; gcm_dissoc's close-up loop: do i = at, n - 1: new(i) = old(i + 1),
; over copy_run's first n - 1 of old
(defun shift-loop (i n new old)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (zp i) (zp n) (>= i n)) new
    (shift-loop (1+ i) n (update-nth (1- i) (nth i old) new) old)))

; the swap: copy_run's first n - 1, the last entry into the hole
(defun swap-fill (at n run)
  (if (equal at n) (am-take (1- n) run) (update-nth (1- at) (nth (1- n) run) (am-take (1- n) run))))

(defun am-dissoc (m k swap)
  (let ((n (am-count m)) (at (am-index m k)))
    (cond ((equal at 0) m)
          (swap (am-make (1- n) (swap-fill at n (am-keys m)) (swap-fill at n (am-vals m))))
          (t (am-make (1- n)
                      (shift-loop at n (am-take (1- n) (am-keys m)) (am-keys m))
                      (shift-loop at n (am-take (1- n) (am-vals m)) (am-vals m)))))))

; what the loop computes: the list without its at-th element
(defun remove-at (at l) (append (am-take (1- at) l) (nthcdr at l)))

(defthm am-take-update-nth-past
  (implies (<= (nfix n) (nfix j)) (equal (am-take n (update-nth j v l)) (am-take n l))))

(defthm am-take-of-update-nth-at-end
  (implies (and (posp i) (<= i (len l)))
           (equal (am-take i (update-nth (+ -1 i) v l)) (append (am-take (+ -1 i) l) (list v))))
  :hints (("Goal" :induct (am-take i l))))

(defthm append-assoc-am
  (equal (append (append a b) c) (append a (append b c))))

(defthm nthcdr-cons-nth
  (implies (and (natp i) (< i (len l)))
           (equal (cons (nth i l) (nthcdr (1+ i) l)) (nthcdr i l))))

(defthm am-take-len (implies (true-listp l) (equal (am-take (len l) l) l)))

(defthm nthcdr-len-am (implies (true-listp l) (equal (nthcdr (len l) l) nil)))

(defthm shift-loop-is
  (implies (and (posp i) (natp n) (<= i n) (equal (len new) (1- n)) (equal (len old) n)
                (true-listp new) (true-listp old))
           (equal (shift-loop i n new old)
                  (append (am-take (1- i) new) (nthcdr i old))))
  :hints (("Goal" :induct (shift-loop i n new old) :in-theory (disable nth nthcdr) :do-not (quote (eliminate-destructors generalize)))))

(defthm member-len-pos
  (implies (member-equal k l) (< 0 (len l)))
  :rule-classes :linear)

(defthm am-take-am-take
  (implies (<= (nfix a) (nfix b)) (equal (am-take a (am-take b l)) (am-take a l))))

(defthm true-listp-am-take (true-listp (am-take n l)))

(defthm am-dissoc-shift-keys
  (implies (and (am-wf m) (am-contains m k))
           (equal (am-keys (am-dissoc m k nil)) (remove-at (am-index m k) (am-keys m))))
  :hints (("Goal" :use ((:instance shift-loop-is (i (am-index m k)) (n (am-count m))
                                   (new (am-take (1- (am-count m)) (am-keys m))) (old (am-keys m)))
                        (:instance am-index-from-range (ks (am-keys m)) (i 1)))
                  :in-theory (disable shift-loop-is am-index-from-range))))

; remove-at of the place k is at: k's first occurrence gone, the rest in order
(defun remove1-am (k l) (cond ((atom l) nil) ((equal (car l) k) (cdr l)) (t (cons (car l) (remove1-am k (cdr l))))))

(defthm remove-at-index-from
  (implies (and (posp i) (member-equal k ks))
           (equal (remove-at (+ 1 (- (am-index-from ks k i) i)) ks) (remove1-am k ks))))

(defthm am-dissoc-absent
  (implies (not (member-equal k (am-keys m))) (equal (am-dissoc m k swap) m)))

; ORDER: dissoc without swap is "remove the one", in order
(defthm am-dissoc-order
  (implies (am-wf m)
           (equal (am-keys (am-dissoc m k nil))
                  (if (am-contains m k) (remove1-am k (am-keys m)) (am-keys m))))
  :hints (("Goal" :use ((:instance am-dissoc-shift-keys) (:instance remove-at-index-from (ks (am-keys m)) (i 1)))
                  :in-theory (disable am-dissoc-shift-keys remove-at-index-from am-dissoc remove-at))))

; ---- dissoc: what get and contains answer, both ways ------------------------
;
; get as a walk of the two runs side by side
(defun am-lookup (ks vs k)
  (cond ((atom ks) nil) ((equal (car ks) k) (car vs)) (t (am-lookup (cdr ks) (cdr vs) k))))

(defthm am-index-from-lookup
  (implies (posp i)
           (equal (if (equal (am-index-from ks k i) 0) nil (nth (- (am-index-from ks k i) i) vs))
                  (am-lookup ks vs k)))
  :rule-classes nil)

(defthm am-get-is-lookup
  (equal (am-get m k) (am-lookup (am-keys m) (am-vals m) k))
  :hints (("Goal" :use ((:instance am-index-from-lookup (ks (am-keys m)) (vs (am-vals m)) (i 1))))))

(in-theory (disable am-get))

(defthm am-lookup-append
  (implies (equal (len a) (len c))
           (equal (am-lookup (append a b) (append c d) k)
                  (if (member-equal k a) (am-lookup a c k) (am-lookup b d k)))))

(defthm am-lookup-absent
  (implies (not (member-equal k ks)) (equal (am-lookup ks vs k) nil)))

; the place-p entry removed, recursively
(defun rm-pos (p l) (if (or (zp p) (equal p 1) (atom l)) (cdr l) (cons (car l) (rm-pos (1- p) (cdr l)))))

(defthm remove-at-is-rm-pos
  (implies (and (posp p) (<= p (len l)))
           (equal (remove-at p l) (rm-pos p l)))
  :hints (("Goal" :induct (rm-pos p l))))

(defthm len-rm-pos
  (implies (and (posp p) (<= p (len l))) (equal (len (rm-pos p l)) (1- (len l)))))

(defthm true-listp-rm-pos (implies (true-listp l) (true-listp (rm-pos p l))))

(defthm member-rm-pos-sub
  (implies (member-equal x (rm-pos p l)) (member-equal x l)))

(defthm no-dups-rm-pos
  (implies (no-duplicatesp-equal l) (no-duplicatesp-equal (rm-pos p l))))

(defthm member-nth-am
  (implies (< (nfix i) (len l)) (member-equal (nth i l) l)))

(defthm car-not-later-nth
  (implies (and (not (member-equal (car l) (cdr l))) (posp i) (< i (len l)))
           (not (equal (car l) (nth i l))))
  :hints (("Goal" :use ((:instance member-nth-am (i (1- i)) (l (cdr l)))) :in-theory (disable member-nth-am))))

(defthm member-rm-pos
  (implies (and (posp p) (<= p (len l)) (no-duplicatesp-equal l))
           (iff (member-equal x (rm-pos p l))
                (and (member-equal x l) (not (equal x (nth (1- p) l)))))))

(defthm lookup-rm-pos
  (implies (and (posp p) (<= p (len ks)) (equal (len ks) (len vs)) (no-duplicatesp-equal ks))
           (equal (am-lookup (rm-pos p ks) (rm-pos p vs) k2)
                  (if (equal k2 (nth (1- p) ks)) nil (am-lookup ks vs k2)))))

; ---- the swap: the list's shape ---------------------------------------------

(defun dec2-am (at l) (if (or (zp at) (atom l)) nil (dec2-am (1- at) (cdr l))))

(defthm nth-nthcdr-am
  (equal (nth i (nthcdr j l)) (nth (+ (nfix i) (nfix j)) l)))

(defthm len-nthcdr-am
  (implies (<= (nfix j) (len l)) (equal (len (nthcdr j l)) (- (len l) (nfix j)))))

(defthm true-listp-nthcdr-am (implies (true-listp l) (true-listp (nthcdr j l))))

; a true list not empty: all but its last, then its last
(defthm butlast-last-shape
  (implies (and (true-listp x) (consp x))
           (equal (append (am-take (1- (len x)) x) (list (nth (1- (len x)) x))) x)))

; the first m, cut at place at
(defthm take-shape
  (implies (and (posp at) (<= at (nfix m)) (<= (nfix m) (len l)))
           (equal (am-take m l)
                  (append (am-take (1- at) l) (cons (nth (1- at) l) (am-take (- (nfix m) at) (nthcdr at l))))))
  :rule-classes nil
  :hints (("Goal" :induct (list (dec2-am at l) (am-take m l)))))

(defthm update-nth-at-cut
  (equal (update-nth (len a) x (append a (cons y z))) (append a (cons x z))))

(defthm at-shape
  (implies (and (posp at) (<= at (len l)) (true-listp l))
           (equal (append (am-take (1- at) l) (cons (nth (1- at) l) (nthcdr at l))) l))
  :hints (("Goal" :induct (dec2-am at l))))

(defthm plus-minus-cancel-am (equal (+ a (+ (- a) b)) (fix b)))

(defthm consp-nthcdr-am
  (implies (< (nfix at) (len l)) (consp (nthcdr at l))))

(defthm nthcdr-butlast-shape
  (implies (and (true-listp l) (natp at) (< at (len l)))
           (equal (append (am-take (- (len l) (1+ at)) (nthcdr at l)) (list (nth (1- (len l)) l)))
                  (nthcdr at l)))
  :hints (("Goal" :use ((:instance butlast-last-shape (x (nthcdr at l)))) :do-not-induct t :in-theory (disable butlast-last-shape))))

(defthm list-shape
  (implies (and (true-listp l) (posp at) (< at (len l)))
           (equal (append (am-take (1- at) l)
                          (cons (nth (1- at) l)
                                (append (am-take (- (len l) (1+ at)) (nthcdr at l)) (list (nth (1- (len l)) l)))))
                  l))
  :rule-classes nil
  :hints (("Goal" :use ((:instance nthcdr-butlast-shape) (:instance at-shape)) :do-not-induct t
                  :in-theory (disable butlast-last-shape nthcdr-butlast-shape at-shape))))

(defthm swap-shape
  (implies (and (true-listp l) (posp at) (< at (len l)))
           (equal (swap-fill at (len l) l)
                  (append (am-take (1- at) l)
                          (cons (nth (1- (len l)) l) (am-take (- (len l) (1+ at)) (nthcdr at l))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance take-shape (m (1- (len l)))))
                  :in-theory (disable update-nth-at-cut)
                  :expand ((swap-fill at (len l) l)))
          ("Goal'" :use ((:instance update-nth-at-cut (a (am-take (1- at) l)) (x (nth (1- (len l)) l))
                                    (y (nth (1- at) l)) (z (am-take (- (len l) (1+ at)) (nthcdr at l))))))))

; over the shape: a ++ k :: (b ++ [kl]) becomes a ++ kl :: b
(defthm no-dups-append-cons
  (implies (no-duplicatesp-equal (append a (cons x y)))
           (and (not (member-equal x a)) (not (member-equal x y))
                (no-duplicatesp-equal (append a y)))))

(defthm member-append-list
  (iff (member-equal x (append a (list y))) (or (member-equal x a) (equal x y))))

(defthm no-dups-shape-ends-differ
  (implies (no-duplicatesp-equal (append a (cons k (append b (list kl)))))
           (and (not (equal k kl)) (not (member-equal k a)) (not (member-equal k b))
                (not (member-equal kl a)) (not (member-equal kl b))))
  :rule-classes :forward-chaining
  :hints (("Goal" :use ((:instance no-dups-append-cons (x k) (y (append b (list kl))))) :in-theory (disable no-dups-append-cons))))

(defthm no-dups-append-shuffle
  (implies (no-duplicatesp-equal (append a (cons k (append b (list kl)))))
           (no-duplicatesp-equal (append a (cons kl b)))))

(defthm swap-lookup-generic
  (implies (and (no-duplicatesp-equal (append a (cons k (append b (list kl)))))
                (equal (len a) (len c)) (equal (len b) (len d)))
           (equal (am-lookup (append a (cons kl b)) (append c (cons vl d)) k2)
                  (if (equal k2 k) nil
                    (am-lookup (append a (cons k (append b (list kl)))) (append c (cons vk (append d (list vl)))) k2))))
  :hints (("Goal" :do-not-induct t)))

(defthm swap-member-generic
  (implies (no-duplicatesp-equal (append a (cons k (append b (list kl)))))
           (iff (member-equal k2 (append a (cons kl b)))
                (and (not (equal k2 k)) (member-equal k2 (append a (cons k (append b (list kl)))))))))

(defthm len-swap-fill
  (implies (and (posp at) (<= at n) (equal (len l) n))
           (equal (len (swap-fill at n l)) (1- n))))

(defthm true-listp-swap-fill (true-listp (swap-fill at n l)))

(defthm swap-facts-generic
  (implies (and (equal ks (append a (cons k (append b (list kl)))))
                (equal vs (append c (cons vk (append d (list vl)))))
                (equal sk (append a (cons kl b)))
                (equal sv (append c (cons vl d)))
                (no-duplicatesp-equal ks) (equal (len a) (len c)) (equal (len b) (len d)))
           (and (equal (am-lookup sk sv k2) (if (equal k2 k) nil (am-lookup ks vs k2)))
                (iff (member-equal k2 sk) (and (not (equal k2 k)) (member-equal k2 ks)))
                (no-duplicatesp-equal sk)))
  :rule-classes nil)

; the swap on the runs themselves
(defthm swap-facts
  (implies (and (equal n (len ks)) (true-listp ks) (true-listp vs) (equal (len vs) (len ks)) (no-duplicatesp-equal ks)
                (posp at) (< at (len ks)))
           (and (equal (am-lookup (swap-fill at n ks) (swap-fill at n vs) k2)
                       (if (equal k2 (nth (1- at) ks)) nil (am-lookup ks vs k2)))
                (iff (member-equal k2 (swap-fill at n ks))
                     (and (not (equal k2 (nth (1- at) ks))) (member-equal k2 ks)))
                (no-duplicatesp-equal (swap-fill at n ks))))
  :hints (("Goal" :use ((:instance swap-shape (l ks)) (:instance swap-shape (l vs))
                        (:instance list-shape (l ks)) (:instance list-shape (l vs))
                        (:instance swap-facts-generic
                                   (a (am-take (1- at) ks)) (k (nth (1- at) ks))
                                   (b (am-take (- (len ks) (1+ at)) (nthcdr at ks))) (kl (nth (1- (len ks)) ks))
                                   (c (am-take (1- at) vs)) (vk (nth (1- at) vs))
                                   (d (am-take (- (len ks) (1+ at)) (nthcdr at vs))) (vl (nth (1- (len ks)) vs))
                                   (sk (swap-fill at (len ks) ks)) (sv (swap-fill at (len ks) vs))))
                  :do-not-induct t
                  :in-theory (disable swap-fill at-shape nthcdr-butlast-shape))))

; at the last place, the swap is the close-up
(defthm swap-fill-last
  (implies (and (true-listp l) (posp n) (equal (len l) n))
           (equal (swap-fill n n l) (rm-pos n l)))
  :hints (("Goal" :use ((:instance remove-at-is-rm-pos (p n))) :in-theory (disable remove-at-is-rm-pos))))

(defthm am-dissoc-shift-vals
  (implies (and (am-wf m) (am-contains m k))
           (equal (am-vals (am-dissoc m k nil)) (remove-at (am-index m k) (am-vals m))))
  :hints (("Goal" :use ((:instance shift-loop-is (i (am-index m k)) (n (am-count m))
                                   (new (am-take (1- (am-count m)) (am-vals m))) (old (am-vals m)))
                        (:instance am-index-from-range (ks (am-keys m)) (i 1)))
                  :in-theory (disable shift-loop-is am-index-from-range))))

(defthm am-index-nth
  (implies (member-equal k (am-keys m)) (equal (nth (1- (am-index m k)) (am-keys m)) k))
  :hints (("Goal" :use ((:instance am-index-from-nth (ks (am-keys m)) (i 1))) :in-theory (disable am-index-from-nth))))

(defthm am-index-range
  (implies (member-equal k (am-keys m))
           (and (<= 1 (am-index m k)) (<= (am-index m k) (len (am-keys m)))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance am-index-from-range (ks (am-keys m)) (i 1))) :in-theory (disable am-index-from-range))))

(defthm am-index-natp (natp (am-index m k)) :rule-classes :type-prescription)

(in-theory (disable am-index swap-fill remove-at))

; the close-up loop over copy_run is the place removed
(defthm shift-loop-rm-pos
  (implies (and (equal n (len l)) (posp at) (true-listp l) (<= at (len l)))
           (equal (shift-loop at n (am-take (1- n) l) l) (rm-pos at l)))
  :hints (("Goal" :use ((:instance shift-loop-is (i at) (n (len l)) (new (am-take (1- (len l)) l)) (old l))
                        (:instance remove-at-is-rm-pos (p at)))
                  :in-theory (e/d (remove-at) (shift-loop-is remove-at-is-rm-pos)))))

(in-theory (disable shift-loop-is))

; GET after dissoc, either way: k is gone, the rest is what it was
(defthm am-dissoc-get
  (implies (am-wf m)
           (equal (am-get (am-dissoc m k swap) k2) (if (equal k2 k) nil (am-get m k2))))
  :hints (("Goal" :cases ((not (am-contains m k)) (equal (am-index m k) (am-count m)))
                  :use ((:instance am-index-nth) (:instance am-index-range)))))

(in-theory (disable am-contains))

(defthm am-dissoc-contains
  (implies (am-wf m)
           (iff (am-contains (am-dissoc m k swap) k2) (and (not (equal k2 k)) (am-contains m k2))))
  :hints (("Goal" :cases ((not (am-contains m k)) (equal (am-index m k) (am-count m)))
                  :use ((:instance am-index-nth) (:instance am-index-range)))))

(defthm am-dissoc-count
  (implies (am-wf m)
           (equal (am-count (am-dissoc m k swap)) (if (am-contains m k) (1- (am-count m)) (am-count m))))
  :hints (("Goal" :in-theory (enable am-index am-contains))))

(defthm am-dissoc-wf
  (implies (am-wf m) (am-wf (am-dissoc m k swap)))
  :hints (("Goal" :cases ((not (am-contains m k)) (equal (am-index m k) (am-count m)))
                  :use ((:instance am-index-nth) (:instance am-index-range)))))

; ---- the positional edits: gcm_insert_at, gcm_replace_at, gcm_remove_at -------
;
; old(a+1 .. b), 0-based a <= b: the run's slice
(defun am-range (a b l) (am-take (- (nfix b) (nfix a)) (nthcdr a l)))

; do i = i0, hi: new(i + off) = old(i), the Fortran's 1-based places
(defun copy-up (i hi off new old)
  (declare (xargs :measure (nfix (- (1+ (nfix hi)) (nfix i)))))
  (if (or (zp i) (> i (nfix hi))) new
    (copy-up (1+ i) hi off (update-nth (+ i (nfix off) -1) (nth (1- i) old) new) old)))

(defthm nthcdr-update-nth-before
  (implies (and (natp j) (natp k) (< j k)) (equal (nthcdr k (update-nth j v l)) (nthcdr k l))))

(defthm nthcdr-1+-am
  (implies (natp a) (equal (nthcdr (+ 1 a) l) (cdr (nthcdr a l)))))

(defthm nth-as-nthcdr-am
  (implies (natp a) (equal (car (nthcdr a l)) (nth a l))))

(defthm am-range-open
  (implies (and (natp a) (natp b) (< a b))
           (equal (am-range a b l) (cons (nth a l) (am-range (1+ a) b l))))
  :hints (("Goal" :in-theory (disable nthcdr-cons-nth nth nthcdr) :expand ((am-take (- b a) (nthcdr a l))))))

(defthm am-range-empty (equal (am-range a a l) nil))

(in-theory (disable am-range nthcdr-1+-am))

(defthm am-take-append-nthcdr
  (implies (and (true-listp l) (<= (nfix k) (len l))) (equal (append (am-take k l) (nthcdr k l)) l)))

(defthm copy-up-is
  (implies (and (posp i) (natp hi) (natp off) (<= i (1+ hi)) (<= (+ hi off) (len new)) (true-listp new))
           (equal (copy-up i hi off new old)
                  (append (am-take (+ i off -1) new)
                          (append (am-range (1- i) hi old) (nthcdr (+ hi off) new)))))
  :hints (("Goal" :induct (copy-up i hi off new old))))

; gc_vec(n): a run of n nils
(defun am-nils (n) (if (zp n) nil (cons nil (am-nils (1- n)))))

(defthm len-am-nils (equal (len (am-nils n)) (nfix n)))
(defthm true-listp-am-nils (true-listp (am-nils n)))

(defthm am-take-append-am
  (equal (am-take k (append a b))
         (if (<= (nfix k) (len a)) (am-take k a) (append a (am-take (- (nfix k) (len a)) b)))))

(defthm am-range-0 (equal (am-range 0 b l) (am-take b l)) :hints (("Goal" :in-theory (enable am-range))))

(defthm am-range-to-end
  (implies (and (true-listp l) (natp a) (<= a (len l)))
           (equal (am-range a (len l) l) (nthcdr a l)))
  :hints (("Goal" :in-theory (enable am-range))))

(defthm consp-nthcdr-nils
  (implies (< (nfix a) (nfix n)) (consp (nthcdr a (am-nils n)))))

(defthm true-listp-append-am (implies (true-listp b) (true-listp (append a b))))

(defthm nthcdr-past-end-am
  (implies (and (true-listp l) (<= (len l) (nfix k))) (equal (nthcdr k l) nil)))

(defthm len-cdr-am
  (implies (consp x) (equal (len (cdr x)) (1- (len x)))))

(defthm true-listp-nthcdr-nils (true-listp (nthcdr a (am-nils n))))

; gcm_insert_at's runs: gc_vec(n + 1), the places before at, at, the rest moved up one
(defun ins-run (at x n old)
  (copy-up at n 1 (update-nth (1- at) x (copy-up 1 (1- at) 0 (am-nils (1+ n)) old)) old))

(defthm ins-run-is
  (implies (and (posp at) (true-listp old) (<= at (1+ (len old))) (equal n (len old)))
           (equal (ins-run at x n old)
                  (append (am-take (1- at) old) (cons x (nthcdr (1- at) old)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable update-nth-at-cut)
                  :use ((:instance update-nth-at-cut (a (am-take (1- at) old)) (x x)
                                   (y (car (nthcdr (1- at) (am-nils (1+ n)))))
                                   (z (cdr (nthcdr (1- at) (am-nils (1+ n))))))))))

; gcm_remove_at's loop: do i = 1, n; if (i == at) cycle; j = j + 1; new(j) = old(i)
(defun rm-loop (i n at j new old)
  (declare (xargs :measure (nfix (- (1+ (nfix n)) (nfix i)))))
  (cond ((or (zp i) (> i (nfix n))) new)
        ((equal i at) (rm-loop (1+ i) n at j new old))
        (t (rm-loop (1+ i) n at (1+ (nfix j)) (update-nth (nfix j) (nth (1- i) old) new) old))))

(defthm am-take-update-nth-last
  (implies (and (equal j (+ -1 i)) (posp i) (<= i (len l)))
           (equal (am-take i (update-nth j v l)) (append (am-take j l) (list v)))))

(defthm nthcdr-cons-nth-free
  (implies (and (equal j (+ 1 i)) (natp i) (< i (len l)))
           (equal (cons (nth i l) (nthcdr j l)) (nthcdr i l))))

(defthm cdr-nthcdr-am
  (implies (natp a) (equal (cdr (nthcdr a l)) (nthcdr (+ 1 a) l))))

(defthm nthcdr-last-am
  (implies (and (true-listp l) (natp k) (equal (len l) (+ 1 k)))
           (equal (nthcdr k l) (list (nth k l)))))

; past the hole: the rest, each one place down
(defthm rm-loop-after
  (implies (and (equal j (- i 2)) (posp at) (< at i) (posp i) (<= i (1+ n)) (equal n (len old)) (true-listp old)
                (true-listp new) (equal (len new) (1- n)) (posp n))
           (equal (rm-loop i n at j new old)
                  (append (am-take (- i 2) new) (nthcdr (1- i) old))))
  :hints (("Goal" :induct (rm-loop i n at j new old))))

; before it: the places as they were, then the place removed from the rest
(defthm rm-loop-before
  (implies (and (posp i) (integerp at) (<= i at) (<= at n) (equal n (len old)) (true-listp old)
                (true-listp new) (equal (len new) (1- n)))
           (equal (rm-loop i n at (1- i) new old)
                  (append (am-take (1- i) new) (rm-pos (+ 1 (- at i)) (nthcdr (1- i) old)))))
  :hints (("Goal" :induct (rm-loop i n at (1- i) new old))))

(defun rm-run (at n old) (rm-loop 1 n at 0 (am-nils (1- n)) old))

(defthm rm-run-is
  (implies (and (posp at) (<= at n) (equal n (len old)) (true-listp old))
           (equal (rm-run at n old) (rm-pos at old)))
  :hints (("Goal" :use ((:instance rm-loop-before (i 1) (new (am-nils (1- n))))) :in-theory (disable rm-loop-before))))

(in-theory (disable ins-run rm-run))

(defun am-insert-at (m at k v)
  (let ((n (am-count m)))
    (am-make (1+ n) (ins-run at k n (am-keys m)) (ins-run at v n (am-vals m)))))

(defun am-replace-at (m at v)
  (let ((n (am-count m)))
    (am-make n (am-take n (am-keys m)) (update-nth (1- at) v (am-take n (am-vals m))))))

(defun am-remove-at (m at)
  (let ((n (am-count m)))
    (am-make (1- n) (rm-run at n (am-keys m)) (rm-run at n (am-vals m)))))

; INSERT keeps the order: k at place at, the rest around it
(defthm am-insert-at-keys
  (implies (and (am-wf m) (posp at) (<= at (1+ (am-count m))))
           (and (equal (am-keys (am-insert-at m at k v))
                       (append (am-take (1- at) (am-keys m)) (cons k (nthcdr (1- at) (am-keys m)))))
                (equal (am-vals (am-insert-at m at k v))
                       (append (am-take (1- at) (am-vals m)) (cons v (nthcdr (1- at) (am-vals m)))))
                (equal (am-count (am-insert-at m at k v)) (1+ (am-count m))))))

(defthm am-replace-at-is
  (implies (and (am-wf m) (posp at) (<= at (am-count m)))
           (and (equal (am-keys (am-replace-at m at v)) (am-keys m))
                (equal (am-vals (am-replace-at m at v)) (update-nth (1- at) v (am-vals m)))
                (equal (am-count (am-replace-at m at v)) (am-count m)))))

(defun dec-pl (p l) (if (or (zp p) (equal p 1)) l (dec-pl (1- p) (cdr l))))

(defthm rm-pos-at-cut
  (implies (posp p) (equal (rm-pos p (append (am-take (1- p) l) (cons x z))) (append (am-take (1- p) l) z)))
  :hints (("Goal" :induct (dec-pl p l))))

; REMOVE undoes INSERT
(defthm am-remove-at-insert-at
  (implies (and (am-wf m) (posp at) (<= at (1+ (am-count m))))
           (let ((m2 (am-remove-at (am-insert-at m at k v) at)))
             (and (equal (am-keys m2) (am-keys m)) (equal (am-vals m2) (am-vals m))
                  (equal (am-count m2) (am-count m))))))

; ---- COST: steps counted as the code runs ------------------------------------
;
; a step a key compared (index_of's loop) and a value copied or set
; (copy_run's loop, gc_vec_set, the edits' loops)

(defun am-index-steps (ks k)
  (cond ((atom ks) 0) ((equal (car ks) k) 1) (t (1+ (am-index-steps (cdr ks) k)))))

(defthm am-index-steps-bound (<= (am-index-steps ks k) (len ks)) :rule-classes :linear)

(defun am-get-steps (m k) (+ 1 (am-index-steps (am-keys m) k)))

; index_of, then copy_run of each run (n values each), then one or two sets
(defun am-assoc-steps (m k)
  (let ((n (am-count m)))
    (+ (am-index-steps (am-keys m) k) n n (if (am-contains m k) 1 2))))

; index_of, copy_run of n - 1 each, then the swap's two sets or the close-up's
; two a place from at to n - 1
(defun am-dissoc-steps (m k swap)
  (let ((n (am-count m)) (at (am-index m k)))
    (if (equal at 0) (am-index-steps (am-keys m) k)
      (+ (am-index-steps (am-keys m) k) (1- n) (1- n)
         (if swap 2 (+ (nfix (- n at)) (nfix (- n at))))))))

(defun am-insert-steps (m) (* 2 (1+ (am-count m))))
(defun am-remove-steps (m) (* 2 (nfix (1- (am-count m)))))
(defun am-replace-steps (m) (+ 1 (* 2 (am-count m))))

(defthm am-cost
  (implies (am-wf m)
           (and (<= (am-index-steps (am-keys m) k) (am-count m))
                (<= (am-get-steps m k) (+ 1 (am-count m)))
                (<= (am-assoc-steps m k) (+ 2 (* 3 (am-count m))))
                (<= (am-dissoc-steps m k swap) (* 5 (am-count m)))
                (<= (am-insert-steps m) (+ 2 (* 2 (am-count m))))
                (<= (am-remove-steps m) (* 2 (am-count m)))
                (<= (am-replace-steps m) (+ 1 (* 2 (am-count m))))))
  :hints (("Goal" :in-theory (enable am-index)
                  :use ((:instance am-index-from-range (ks (am-keys m)) (i 1))
                        (:instance am-index-steps-bound (ks (am-keys m)))))))

; ---- the persistent list: gcl_cons, gcl_first, gcl_rest, gcl_count ------------
;
; a cell (:cons first rest count); the empty list the one cell of count 0
; (gcl_empty's singleton)

(defconst *gl-empty* '(:cons nil nil 0))

(defun gl-is (v) (and (consp v) (eq (car v) :cons)))
(defun gl-count (v) (if (gl-is v) (nfix (cadddr v)) 0))

(defun gl-cons (x l)
  (if (gl-is l) (list :cons x l (1+ (gl-count l))) (list :cons x *gl-empty* 1)))

(defun gl-first (v) (if (or (not (gl-is v)) (zp (cadddr v))) nil (cadr v)))

(defun gl-rest (v)
  (if (or (not (gl-is v)) (<= (nfix (cadddr v)) 1)) *gl-empty* (caddr v)))

; what cons builds: the empty cell, or a cell whose count is one more than its rest's
(defun gl-wf (v)
  (declare (xargs :measure (acl2-count v)))
  (and (gl-is v) (true-listp v) (equal (len v) 4) (natp (cadddr v))
       (if (equal (cadddr v) 0) (equal v *gl-empty*)
         (and (gl-wf (caddr v)) (equal (cadddr v) (1+ (gl-count (caddr v))))))))

; the chain's length, walked
(defun gl-len (v)
  (declare (xargs :measure (acl2-count v)))
  (if (or (not (gl-is v)) (zp (cadddr v))) 0 (1+ (gl-len (caddr v)))))

(defthm gl-cons-wf
  (implies (or (gl-wf l) (not (gl-is l))) (gl-wf (gl-cons x l))))

; COUNT: the count a cell carries is the chain's length
(defthm gl-count-is-len
  (implies (gl-wf v) (equal (gl-count v) (gl-len v))))

(defthm gl-first-cons (equal (gl-first (gl-cons x l)) x))

(defthm gl-rest-cons
  (implies (or (gl-wf l) (not (gl-is l)))
           (equal (gl-rest (gl-cons x l)) (if (gl-is l) l *gl-empty*))))

(defthm gl-rest-wf (implies (gl-wf v) (gl-wf (gl-rest v))))

(defthm gl-rest-count
  (implies (gl-wf v) (equal (gl-count (gl-rest v)) (nfix (1- (gl-count v))))))

(defthm gl-empty-rest (equal (gl-rest *gl-empty*) *gl-empty*))

; COST: count reads the cell, 1 step, where walking the chain is its length
(defun gl-count-steps (v) (declare (ignore v)) 1)
(defun gl-len-steps (v)
  (declare (xargs :measure (acl2-count v)))
  (if (or (not (gl-is v)) (zp (cadddr v))) 1 (1+ (gl-len-steps (caddr v)))))

(defthm gl-cost
  (implies (gl-wf v)
           (and (equal (gl-count-steps v) 1)
                (equal (gl-len-steps v) (1+ (gl-count v))))))
