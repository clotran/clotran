; clotran's seq over a hash map, formally (PLAN step 28).
;
; src/f/PersistentHashMap.f90's cursor: a FRAME (node slot parent), the
; entry where the seq stands being slot `slot` of `node` -- a trie node
; of 32 slots, or a collision bucket and its entry's position -- and
; `parent` the frame of the slot that led into node. Frames are only
; ever made, never changed. scan finds the first entry from a slot on;
; next steps past the current one, climbing when a node is spent.
;
; What it proves: what a cursor has LEFT to walk (remaining) is exactly the
; trie's entries after it in the order gch_entries walks them --
;
;   (remaining (first t)) = (entries t)       the seq holds every entry
;   (remaining (next f))  = (cdr (remaining f))     next drops exactly one
;   (current f)     = (car (remaining f))     and reads the one it stands on
;
; so seq, keys and vals all walk the one order, and the seq never
; copies an entry it has not reached. Cost: next scans within the
; current node and climbs only out of spent ones, each node entered and
; left once in a walk -- O(1) amortized, first O(log32 n).
;
; A node is a list of slots; a slot is (:leaf k v), (:node child),
; (:bucket entries) with entries a list of (k . v), or nil.

(in-package "ACL2")

; ---- the trie's entries, as gch_entries walks them -------------------

(mutual-recursion
 (defun slot-entries (s)
   (declare (xargs :measure (acl2-count s)))
   (cond ((and (consp s) (eq (car s) :leaf)) (list (cons (cadr s) (caddr s))))
         ((and (consp s) (eq (car s) :bucket)) (true-list-fix (cadr s)))
         ((and (consp s) (eq (car s) :node)) (node-entries (cadr s)))
         (t nil)))
 (defun node-entries (node)
   (declare (xargs :measure (acl2-count node)))
   (if (atom node)
       nil
     (append (slot-entries (car node)) (node-entries (cdr node))))))

; the entries from slot i on (0-based here; the Fortran counts from 1)
(defun entries-from (node i)
  (node-entries (nthcdr i node)))

; ---- the cursor --------------------------------------------------------
;
; a frame: (list :trie node i parent) standing on a leaf in slot i, or
; (list :bucket entries j parent) standing on entry j of a bucket; the
; parent stands on the slot that holds what this frame walks

(defun f-kind (f) (nth 0 f))
(defun f-node (f) (nth 1 f))
(defun f-i (f) (nfix (nth 2 f)))
(defun f-parent (f) (nth 3 f))

; a frame's parent is part of it: what lets the climb end
(defthm acl2-count-nth-less
  (implies (consp l) (< (acl2-count (nth n l)) (acl2-count l)))
  :rule-classes :linear)

; what is left after the slot the frame stands on, in its node and up
; the chain -- gch_cursor_next's climb
(defun after (f)
  (declare (xargs :measure (acl2-count f)))
  (if (atom f)
      nil
    (append (if (eq (f-kind f) :bucket)
                (nthcdr (1+ (f-i f)) (true-list-fix (f-node f)))
              (entries-from (f-node f) (1+ (f-i f))))
            (after (f-parent f)))))

; what is left from where the frame stands, its own entry first
(defun remaining (f)
  (if (atom f)
      nil
    (if (eq (f-kind f) :bucket)
        (append (nthcdr (f-i f) (true-list-fix (f-node f))) (after (f-parent f)))
      (append (slot-entries (nth (f-i f) (f-node f))) (after f)))))

; ---- scan and next: gch_cursor_first and gch_cursor_next ---------------

(defun leaf-slot-p (s) (and (consp s) (eq (car s) :leaf)))
(defun bucket-slot-p (s) (and (consp s) (eq (car s) :bucket) (consp (cadr s))))
(defun node-slot-p (s) (and (consp s) (eq (car s) :node)))

; scan: the first entry in xs (slots s, s+1, ... of node) or below it,
; under parent; nil when there is none
(defun scan-slots (xs s node parent)
  (declare (xargs :measure (acl2-count xs)))
  (cond ((atom xs) nil)
        ((leaf-slot-p (car xs)) (list :trie node s parent))
        ((bucket-slot-p (car xs))
         (list :bucket (cadr (car xs)) 0 (list :trie node s parent)))
        ((node-slot-p (car xs))
         (or (scan-slots (cadr (car xs)) 0 (cadr (car xs)) (list :trie node s parent))
             (scan-slots (cdr xs) (1+ (nfix s)) node parent)))
        (t (scan-slots (cdr xs) (1+ (nfix s)) node parent))))

(defun cursor-first (root) (scan-slots root 0 root nil))

; next: the bucket's next entry, else past this slot in its node, else
; the same one level up
(defun cursor-next (f)
  (declare (xargs :measure (acl2-count f)))
  (cond ((atom f) nil)
        ((eq (f-kind f) :bucket)
         (if (< (1+ (f-i f)) (len (f-node f)))
             (list :bucket (f-node f) (1+ (f-i f)) (f-parent f))
           (cursor-next (f-parent f))))
        (t (or (scan-slots (nthcdr (1+ (f-i f)) (f-node f)) (1+ (f-i f)) (f-node f) (f-parent f))
               (cursor-next (f-parent f))))))

(defun rem* (r p) (if r (remaining r) (after p)))

; what a built frame has left, so the definitions need not open on a
; frame scan made
(defthm after-of-nil (equal (after nil) nil))
(defthm after-of-trie
  (equal (after (list :trie node s p))
         (append (node-entries (nthcdr (1+ (nfix s)) node)) (after p))))
(defthm after-of-bucket
  (equal (after (list :bucket es j p))
         (append (nthcdr (1+ (nfix j)) (true-list-fix es)) (after p))))
(defthm remaining-of-trie
  (equal (remaining (list :trie node s p))
         (append (slot-entries (nth (nfix s) node))
                 (node-entries (nthcdr (1+ (nfix s)) node)) (after p))))
(defthm remaining-of-bucket
  (equal (remaining (list :bucket es j p))
         (append (nthcdr (nfix j) (true-list-fix es)) (after p))))
(defthm nth-as-car-nthcdr
  (implies (natp s) (equal (nth s l) (car (nthcdr s l)))))
(in-theory (disable remaining after entries-from))

(defthm append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defthm len-of-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm len-positive-when-consp
  (implies (consp a) (< 0 (len a)))
  :rule-classes :linear)

(defthm append-nil-means-empty
  (implies (equal (append a b) b) (not (consp a)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance len-of-append))
                  :in-theory (disable len-of-append append))))

(defthm append-equal-tail
  (equal (equal (append a b) b) (atom a))
  :hints (("Goal" :use ((:instance append-nil-means-empty)))))

(defthm node-entries-true-listp (true-listp (node-entries x))
  :hints (("Goal" :induct (len x))))

(defthm cdr-of-nthcdr
  (implies (natp s) (equal (cdr (nthcdr s l)) (nthcdr (+ 1 s) l))))

; SCAN finds exactly the entries from slot s on, and nothing only when
; there are none
(defthm scan-slots-rem
  (implies (and (natp s) (equal xs (nthcdr s node)))
           (equal (rem* (scan-slots xs s node parent) parent)
                  (append (node-entries xs) (after parent))))
  :hints (("Goal" :induct (scan-slots xs s node parent))))

(defthm scan-none-means-empty
  (implies (and (natp s) (not (scan-slots (nthcdr s node) s node parent)))
           (equal (node-entries (nthcdr s node)) nil))
  :hints (("Goal" :use ((:instance scan-slots-rem (xs (nthcdr s node))))
                  :in-theory (e/d (rem*) (scan-slots-rem scan-slots nthcdr)))))

(defthm scan-found-remaining
  (implies (and (natp s) (scan-slots (nthcdr s node) s node parent))
           (equal (remaining (scan-slots (nthcdr s node) s node parent))
                  (append (node-entries (nthcdr s node)) (after parent))))
  :hints (("Goal" :use ((:instance scan-slots-rem (xs (nthcdr s node))))
                  :in-theory (e/d (rem*) (scan-slots-rem scan-slots nthcdr)))))

(defthm nthcdr-past-end
  (implies (and (natp n) (<= (len l) n))
           (equal (nthcdr n (true-list-fix l)) nil))
  :hints (("Goal" :induct (nthcdr n l))))

; NEXT leaves exactly what came after the entry it stood on
(defthm cursor-next-rem
  (equal (rem* (cursor-next f) nil) (after f))
  :hints (("Goal" :induct (cursor-next f) :in-theory (e/d (after entries-from) (nthcdr)))))

; and the first cursor holds every entry, in gch_entries' order
(defthm cursor-first-rem
  (equal (rem* (cursor-first root) nil) (node-entries root)))

(defthm cdr-of-append-consp
  (implies (consp a) (equal (cdr (append a b)) (append (cdr a) b))))

(defthm nthcdr-before-end-consp
  (implies (and (natp j) (< j (len l)))
           (consp (nthcdr j (true-list-fix l))))
  :hints (("Goal" :induct (nthcdr j l))))

(defthm nthcdr-of-1 (equal (nthcdr 1 l) (cdr l)))

(defthm consp-of-true-list-fix (equal (consp (true-list-fix l)) (consp l)))

(defthm consp-when-len-positive
  (implies (< 0 (len l)) (consp l))
  :rule-classes :forward-chaining)

; a frame on an entry: rem is that entry, then what is after it
(defthm rem-is-current-then-after
  (implies (or (and (eq (f-kind f) :trie) (leaf-slot-p (nth (f-i f) (f-node f))))
               (and (eq (f-kind f) :bucket) (< (f-i f) (len (f-node f)))))
           (equal (cdr (remaining f)) (after f)))
  :hints (("Goal" :in-theory (e/d (remaining after) (nth-as-car-nthcdr)))))
