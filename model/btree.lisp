; clotran's sorted map, formally: why it stays O(log n) (PLAN step 28).
;
; src/f/Assoc.f90 keeps a sorted map as a counted B+-tree: leaves of up
; to ST_MAX = 32 entries, internal nodes of up to 32 children. Insertion
; splits a node that would hold 33 into two (st_ins); deletion, when a
; child is left with fewer than ST_MIN = 16, takes the neighbour with
; it -- one node when the two fit in 32, else two sharing them evenly
; (st_rebalance). Before that rebalance a node could thin to one entry,
; and a map that had held 10^5 entries kept height 3 at 100 (measured);
; clj's red-black tree is O(log n) whatever was deleted.
;
; What this book proves:
;
;   SIZES   every node a split or a rebalance makes holds between 16
;           and 32 -- so every node but the root keeps at least 16;
;   HEIGHT  a tree whose nodes but the root hold at least 16 holds at
;           least 2 * 16^h entries at height h >= 1: h <= log16(n/2),
;           so find, insert and remove read O(log n) nodes;
;   WALK    such a tree has at most n/16 + 1 leaves, so a seq's walk,
;           which descends once per leaf, is O(n).

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

(defconst *st-max* 32)
(defconst *st-min* 16)

; ---- SIZES --------------------------------------------------------------

; st_ins: a node of ST_MAX + 1 splits at (n+1)/2
(defthm split-sizes
  (let ((half (floor (1+ *st-max*) 2)))
    (and (<= *st-min* half) (<= half *st-max*)
         (<= *st-min* (- (1+ *st-max*) half)) (<= (- (1+ *st-max*) half) *st-max*))))

; st_rebalance: an underfull node u (it lost one: ST_MIN - 1) with a
; neighbour s at least ST_MIN and at most ST_MAX
(defun rebalance-sizes (u s)
  (let ((tot (+ u s)))
    (if (<= tot *st-max*)
        (list tot)
      (list (floor tot 2) (- tot (floor tot 2))))))

(defun all-between (xs lo hi)
  (if (endp xs) t (and (<= lo (car xs)) (<= (car xs) hi) (all-between (cdr xs) lo hi))))

(defthm rebalance-keeps-half-full
  (implies (and (natp s) (<= *st-min* s) (<= s *st-max*))
           (all-between (rebalance-sizes (1- *st-min*) s) *st-min* *st-max*)))

; and nothing is lost: the sizes made add up to what the two held
(defun sum (xs) (if (endp xs) 0 (+ (car xs) (sum (cdr xs)))))

(defthm rebalance-keeps-entries
  (implies (and (natp u) (natp s))
           (equal (sum (rebalance-sizes u s)) (+ u s))))

; ---- HEIGHT ---------------------------------------------------------------
;
; a tree: (:leaf n) with n entries, or (:node kids) with its children

(mutual-recursion
 (defun tcount (tr)
   (declare (xargs :measure (acl2-count tr)))
   (cond ((atom tr) 0)
         ((eq (car tr) :leaf) (nfix (cadr tr)))
         (t (tcount-list (cadr tr)))))
 (defun tcount-list (ts)
   (declare (xargs :measure (acl2-count ts)))
   (if (atom ts) 0 (+ (tcount (car ts)) (tcount-list (cdr ts))))))

; every node of height h, its children of height h - 1, at least ST_MIN
; of whatever it holds -- the invariant st_ins and st_del keep for every
; node but the root
(mutual-recursion
 (defun half-full (tr h)
   (declare (xargs :measure (acl2-count tr)))
   (cond ((atom tr) nil)
         ((zp h) (and (eq (car tr) :leaf) (<= *st-min* (nfix (cadr tr)))))
         (t (and (eq (car tr) :node) (<= *st-min* (len (cadr tr)))
                 (half-full-list (cadr tr) (1- h))))))
 (defun half-full-list (ts h)
   (declare (xargs :measure (acl2-count ts)))
   (if (atom ts) t (and (half-full (car ts) h) (half-full-list (cdr ts) h)))))

(defun sixteen-to (h) (if (zp h) 1 (* 16 (sixteen-to (1- h)))))

(defthm sixteen-to-positive (< 0 (sixteen-to h)) :rule-classes :linear)

; trees and their child lists at once (a flag induction): a half-full
; subtree of height h holds at least 16 * 16^h entries, a list of them
; that many times its length
(defun hf-induct (flg x h)
  (declare (xargs :measure (acl2-count x)))
  (if (eq flg :tree)
      (if (or (atom x) (zp h)) nil (hf-induct :list (cadr x) (1- h)))
    (if (atom x) nil (list (hf-induct :tree (car x) h) (hf-induct :list (cdr x) h)))))

(defthm half-full-holds-many-flag
  (implies (natp h)
           (if (eq flg :tree)
               (implies (half-full x h) (<= (* *st-min* (sixteen-to h)) (tcount x)))
             (implies (half-full-list x h) (<= (* (len x) *st-min* (sixteen-to h)) (tcount-list x)))))
  :rule-classes nil
  :hints (("Goal" :induct (hf-induct flg x h) :nonlinearp t)))

(defthm half-full-holds-many
  (implies (and (natp h) (half-full tr h))
           (<= (* *st-min* (sixteen-to h)) (tcount tr)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance half-full-holds-many-flag (flg :tree) (x tr))))))

; THE ROOT may be under half full, but a root of height h >= 1 has at
; least two children (st_dissoc lifts a root of one child), each a
; half-full subtree: the map holds at least 2 * 16^h entries, so
;   h <= log16(n / 2)   -- find, insert and remove read O(log n) nodes
(defun root-ok (tr h)
  (and (consp tr) (posp h) (eq (car tr) :node)
       (<= 2 (len (cadr tr)))
       (half-full-list (cadr tr) (1- h))))

(defthm height-is-log16
  (implies (root-ok tr h)
           (<= (* 2 (sixteen-to h)) (tcount tr)))
  :hints (("Goal" :use ((:instance half-full-holds-many-flag (flg :list) (x (cadr tr)) (h (1- h))))
                  :nonlinearp t)))

; THE WALK: a seq descends once per leaf (Eval.f90 cursor_seq, kinds 3
; and 4), and a half-full tree has a leaf per 16 entries at most
(mutual-recursion
 (defun leaf-count (tr)
   (declare (xargs :measure (acl2-count tr)))
   (cond ((atom tr) 0)
         ((eq (car tr) :leaf) 1)
         (t (leaf-count-list (cadr tr)))))
 (defun leaf-count-list (ts)
   (declare (xargs :measure (acl2-count ts)))
   (if (atom ts) 0 (+ (leaf-count (car ts)) (leaf-count-list (cdr ts))))))

(defthm leaves-flag
  (implies (natp h)
           (if (eq flg :tree)
               (implies (half-full x h) (<= (* *st-min* (leaf-count x)) (tcount x)))
             (implies (half-full-list x h) (<= (* *st-min* (leaf-count-list x)) (tcount-list x)))))
  :rule-classes nil
  :hints (("Goal" :induct (hf-induct flg x h))))

(defthm walk-is-linear
  (implies (and (natp h) (half-full tr h))
           (<= (* *st-min* (leaf-count tr)) (tcount tr)))
  :hints (("Goal" :use ((:instance leaves-flag (flg :tree) (x tr))))))
