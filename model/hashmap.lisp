; clotran's hash map trie, formally (PLAN step 28; docs/model-coverage.md).
;
; src/f/PersistentHashMap.f90 keeps a hash map as a 32-way trie on the
; key's 32-bit hash, five bits a level (node_get, node_assoc, split,
; node_dissoc): a node is 32 slots, each empty, a leaf (key, value), a
; child node one level deeper, or a collision bucket -- a small linear
; map. Two keys wanting one leaf's slot are pushed down a level until
; their indices part (split); keys with one hash, or still together at
; shift 30 (the seventh level, depth 6 here), share a bucket. Assoc and
; dissoc copy the path and share the rest; dissoc never collapses a node.
;
; A slot is as in model/hashseq.lisp: nil, (:leaf k v), (:node child) or
; (:bucket entries), entries a list of (k . v); a node a list of slots,
; its index 0-based (the Fortran's is 1-based). The hash is `hk`, any
; function: nothing below depends on what it answers, only that one key
; always answers the same -- so the theorems hold whatever gc_hash is,
; and a hash that collides everywhere only makes the buckets long.
;
; What it proves, for a slot at depth d (the root's slots are depth 0):
;
;   GET     after (assoc k v), get k is v and every other key's get is
;           what it was; after (dissoc k), k is absent and every other
;           key's get is what it was (k's absence needs each bucket to
;           hold a key once, which assoc, split and dissoc keep: hm-wf);
;   COUNT   assoc's `added` is exactly "k was absent" and dissoc's
;           `removed` exactly "k was present" -- the count gch_assoc and
;           gch_dissoc keep in i1 without walking the trie is right;
;   DEPTH   no node is deeper than depth 6 in anything assoc and dissoc
;           build from the empty map: the seven levels of the header;
;   COST    so, counting a step a slot visited and an entry scanned, get
;           takes at most 7 - d hops, assoc 2 (7 - d) + 1 (the path, then
;           a split's descent) and node_dissoc 7 - d, plus scans of the
;           one bucket on k's path: at the root 7, 15 and (gch_dissoc,
;           its gch_contains and node_dissoc) 14 -- O(1) for a hash that
;           spreads, a bucket's length for one that collides.
;
; Not modelled: the rooting (vs_enter), and the bucket's own code
; (PersistentArrayMap.f90), taken as the alist it behaves as.

(in-package "ACL2")

(defstub hk (*) => *)

(defconst *maxd* 6)

; the slot a hash picks at depth d: (iand (ishft h, -shift), 31), shift 5d
;; (nfix is a no-op: a logand with 31 is in 0..31; it gives the type)
(defun hidx (h d) (nfix (logand (ash (ifix h) (* -5 (nfix d))) 31)))
(in-theory (disable hidx))

(defun hm-leafp (s) (and (consp s) (eq (car s) :leaf)))
(defun hm-bucketp (s) (and (consp s) (eq (car s) :bucket)))
(defun hm-nodep (s) (and (consp s) (eq (car s) :node)))

(defthm acl2-count-of-nth-le
  (<= (acl2-count (nth i l)) (acl2-count l))
  :rule-classes :linear)

(defthm acl2-count-of-nth-child
  (implies (hm-nodep s)
           (< (acl2-count (nth i (cadr s))) (acl2-count s)))
  :rule-classes :linear)

; ---- get and contains: node_get, node_find ------------------------------

(defun hm-get-slot (s k d)
  (declare (xargs :measure (acl2-count s)))
  (cond ((hm-leafp s) (if (equal (cadr s) k) (caddr s) nil))
        ((hm-bucketp s) (cdr (assoc-equal k (cadr s))))
        ((hm-nodep s) (hm-get-slot (nth (hidx (hk k) (1+ (nfix d))) (cadr s)) k (1+ (nfix d))))
        (t nil)))

(defun hm-has-slot (s k d)
  (declare (xargs :measure (acl2-count s)))
  (cond ((hm-leafp s) (equal (cadr s) k))
        ((hm-bucketp s) (consp (assoc-equal k (cadr s))))
        ((hm-nodep s) (hm-has-slot (nth (hidx (hk k) (1+ (nfix d))) (cadr s)) k (1+ (nfix d))))
        (t nil)))

(defun hm-get (node k) (hm-get-slot (nth (hidx (hk k) 0) node) k 0))
(defun hm-has (node k) (hm-has-slot (nth (hidx (hk k) 0) node) k 0))

; ---- split: two different keys wanting one slot at depth d --------------

(defun hm-split (k1 v1 k v d)
  (declare (xargs :measure (nfix (- *maxd* (nfix d)))))
  (if (or (equal (hk k1) (hk k)) (<= *maxd* (nfix d)))
      (list :bucket (list (cons k1 v1) (cons k v)))
    (let* ((d1 (1+ (nfix d))) (i1 (hidx (hk k1) d1)) (i2 (hidx (hk k) d1)))
      (if (equal i1 i2)
          (list :node (update-nth i1 (hm-split k1 v1 k v d1) nil))
        (list :node (update-nth i2 (list :leaf k v) (update-nth i1 (list :leaf k1 v1) nil)))))))

; ---- assoc: node_assoc, the new slot and `added` --------------------------

(defun hm-assoc-slot (s k v d)
  (declare (xargs :measure (acl2-count s)))
  (cond ((hm-leafp s) (if (equal (cadr s) k)
                       (mv (list :leaf (cadr s) v) nil)
                     (mv (hm-split (cadr s) (caddr s) k v d) t)))
        ((hm-bucketp s) (mv (list :bucket (put-assoc-equal k v (cadr s)))
                         (not (consp (assoc-equal k (cadr s))))))
        ((hm-nodep s) (let ((i (hidx (hk k) (1+ (nfix d)))))
                     (mv-let (c added)
                       (hm-assoc-slot (nth i (cadr s)) k v (1+ (nfix d)))
                       (mv (list :node (update-nth i c (cadr s))) added))))
        (t (mv (list :leaf k v) t))))

(defun hm-assoc (node k v)
  (let ((i (hidx (hk k) 0)))
    (mv-let (s added) (hm-assoc-slot (nth i node) k v 0)
      (mv (update-nth i s node) added))))

; ---- dissoc: node_dissoc, the new slot and `removed` ----------------------

(defun hm-dissoc-slot (s k d)
  (declare (xargs :measure (acl2-count s)))
  (cond ((hm-leafp s) (if (equal (cadr s) k) (mv nil t) (mv s nil)))
        ((hm-bucketp s) (if (consp (assoc-equal k (cadr s)))
                         (mv (list :bucket (remove1-assoc-equal k (cadr s))) t)
                       (mv s nil)))
        ((hm-nodep s) (let ((i (hidx (hk k) (1+ (nfix d)))))
                     (mv-let (c removed)
                       (hm-dissoc-slot (nth i (cadr s)) k (1+ (nfix d)))
                       (mv (list :node (update-nth i c (cadr s))) removed))))
        (t (mv s nil))))

(defun hm-dissoc (node k)
  (let ((i (hidx (hk k) 0)))
    (mv-let (s removed) (hm-dissoc-slot (nth i node) k 0)
      (mv (update-nth i s node) removed))))

; ---- GET -----------------------------------------------------------------

(defthm assoc-equal-put-assoc-equal
  (equal (assoc-equal k2 (put-assoc-equal k v es))
         (if (equal k2 k) (cons k v) (assoc-equal k2 es))))

(defthm assoc-equal-remove1-assoc-equal-other
  (implies (not (equal k2 k))
           (equal (assoc-equal k2 (remove1-assoc-equal k es))
                  (assoc-equal k2 es))))

; what a split slot answers: the two keys, and nothing else
(defthm split-get
  (implies (not (equal k1 k))
           (equal (hm-get-slot (hm-split k1 v1 k v d) k2 d)
                  (cond ((equal k2 k) v) ((equal k2 k1) v1) (t nil)))))

(defthm split-has
  (implies (not (equal k1 k))
           (equal (hm-has-slot (hm-split k1 v1 k v d) k2 d)
                  (or (equal k2 k) (equal k2 k1)))))

(defthm assoc-get-same
  (equal (hm-get-slot (car (hm-assoc-slot s k v d)) k d) v))

(defthm assoc-get-other
  (implies (not (equal k2 k))
           (equal (hm-get-slot (car (hm-assoc-slot s k v d)) k2 d)
                  (hm-get-slot s k2 d))))

(defthm assoc-has
  (equal (hm-has-slot (car (hm-assoc-slot s k v d)) k2 d)
         (or (equal k2 k) (hm-has-slot s k2 d))))

(defthm dissoc-get-other
  (implies (not (equal k2 k))
           (equal (hm-get-slot (car (hm-dissoc-slot s k d)) k2 d)
                  (hm-get-slot s k2 d))))

(defthm dissoc-has-other
  (implies (not (equal k2 k))
           (equal (hm-has-slot (car (hm-dissoc-slot s k d)) k2 d)
                  (hm-has-slot s k2 d))))

; dissoc's own key: gone, given what assoc keeps true -- a bucket holds
; each key once (gcm_dissoc removes the one entry it finds)
(mutual-recursion
 (defun hm-wf (s)
   (declare (xargs :measure (acl2-count s)))
   (cond ((hm-bucketp s) (and (alistp (cadr s)) (no-duplicatesp-equal (strip-cars (cadr s)))))
         ((hm-nodep s) (hm-wf-list (cadr s)))
         (t t)))
 (defun hm-wf-list (l)
   (declare (xargs :measure (acl2-count l)))
   (if (atom l) t (and (hm-wf (car l)) (hm-wf-list (cdr l))))))

(defthm hm-wf-list-nth
  (implies (hm-wf-list l) (hm-wf (nth i l))))

(defthm hm-wf-list-update-nth
  (implies (and (hm-wf-list l) (hm-wf x)) (hm-wf-list (update-nth i x l))))

(defthm hm-wf-list-nil (hm-wf-list nil))

(defthm strip-cars-put-assoc-equal-member
  (implies (consp (assoc-equal k es))
           (equal (strip-cars (put-assoc-equal k v es)) (strip-cars es))))

(defthm alistp-put-assoc-equal-hm
  (implies (alistp es) (alistp (put-assoc-equal k v es))))

(defthm alistp-remove1-assoc-equal-hm
  (implies (alistp es) (alistp (remove1-assoc-equal k es))))

(defthm member-strip-cars-is-assoc
  (implies (alistp es) (iff (member-equal k (strip-cars es)) (assoc-equal k es))))

(defthm strip-cars-put-assoc-equal-new
  (implies (and (alistp es) (not (assoc-equal k es)))
           (equal (strip-cars (put-assoc-equal k v es)) (append (strip-cars es) (list k)))))

(defthm member-equal-append-hm
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))

(defthm no-duplicates-append-one
  (implies (and (no-duplicatesp-equal l) (not (member-equal k l)))
           (no-duplicatesp-equal (append l (list k)))))

(defthm member-strip-cars-remove1
  (implies (and (alistp es) (not (member-equal k2 (strip-cars es))))
           (not (member-equal k2 (strip-cars (remove1-assoc-equal k es))))))

(defthm no-duplicates-remove1-assoc
  (implies (and (alistp es) (no-duplicatesp-equal (strip-cars es)))
           (no-duplicatesp-equal (strip-cars (remove1-assoc-equal k es)))))

(defthm remove1-assoc-gone
  (implies (and (alistp es) (no-duplicatesp-equal (strip-cars es)))
           (not (assoc-equal k (remove1-assoc-equal k es)))))

(defthm split-wf
  (implies (not (equal k1 k)) (hm-wf (hm-split k1 v1 k v d))))

(defthm assoc-wf
  (implies (hm-wf s) (hm-wf (car (hm-assoc-slot s k v d)))))

(defthm dissoc-wf
  (implies (hm-wf s) (hm-wf (car (hm-dissoc-slot s k d)))))

(defthm dissoc-has-same
  (implies (hm-wf s) (not (hm-has-slot (car (hm-dissoc-slot s k d)) k d))))

; ---- COUNT -----------------------------------------------------------------

(defthm assoc-added
  (equal (mv-nth 1 (hm-assoc-slot s k v d)) (not (hm-has-slot s k d))))

(defthm dissoc-removed
  (equal (mv-nth 1 (hm-dissoc-slot s k d)) (hm-has-slot s k d)))

; ---- the root: the same, through the root node's slot ---------------------

(defthm hm-assoc-get
  (equal (hm-get (car (hm-assoc node k v)) k2)
         (if (equal k2 k) v (hm-get node k2))))

(defthm hm-assoc-has
  (equal (hm-has (car (hm-assoc node k v)) k2)
         (or (equal k2 k) (hm-has node k2))))

(defthm hm-assoc-added
  (equal (mv-nth 1 (hm-assoc node k v)) (not (hm-has node k))))

(defthm hm-dissoc-get-other
  (implies (not (equal k2 k))
           (equal (hm-get (car (hm-dissoc node k)) k2) (hm-get node k2))))

(defthm hm-dissoc-has-other
  (implies (not (equal k2 k))
           (equal (hm-has (car (hm-dissoc node k)) k2) (hm-has node k2))))

(defthm hm-dissoc-removed
  (equal (mv-nth 1 (hm-dissoc node k)) (hm-has node k)))

(defthm hm-assoc-wf
  (implies (hm-wf-list node) (hm-wf-list (car (hm-assoc node k v)))))

(defthm hm-dissoc-wf
  (implies (hm-wf-list node) (hm-wf-list (car (hm-dissoc node k)))))

(defthm hm-dissoc-has-same
  (implies (hm-wf-list node) (not (hm-has (car (hm-dissoc node k)) k))))

; ---- DEPTH -------------------------------------------------------------------

; a slot at depth d holds a node only when d < 6, and so on down
(mutual-recursion
 (defun hm-depth-ok (s d)
   (declare (xargs :measure (acl2-count s)))
   (if (hm-nodep s)
       (and (< (nfix d) *maxd*) (hm-depth-ok-list (cadr s) (1+ (nfix d))))
     t))
 (defun hm-depth-ok-list (l d)
   (declare (xargs :measure (acl2-count l)))
   (if (atom l) t (and (hm-depth-ok (car l) d) (hm-depth-ok-list (cdr l) d)))))

(defthm depth-ok-list-nth
  (implies (hm-depth-ok-list l d) (hm-depth-ok (nth i l) d)))

(defthm depth-ok-list-update-nth
  (implies (and (hm-depth-ok-list l d) (hm-depth-ok x d))
           (hm-depth-ok-list (update-nth i x l) d)))

(defthm depth-ok-list-nil (hm-depth-ok-list nil d))

(defthm split-depth-ok (hm-depth-ok (hm-split k1 v1 k v d) d))

(defthm assoc-depth-ok
  (implies (hm-depth-ok s d) (hm-depth-ok (car (hm-assoc-slot s k v d)) d)))

(defthm dissoc-depth-ok
  (implies (hm-depth-ok s d) (hm-depth-ok (car (hm-dissoc-slot s k d)) d)))

(defthm hm-assoc-depth-ok
  (implies (hm-depth-ok-list node 0) (hm-depth-ok-list (car (hm-assoc node k v)) 0)))

(defthm hm-dissoc-depth-ok
  (implies (hm-depth-ok-list node 0) (hm-depth-ok-list (car (hm-dissoc node k)) 0)))

; ---- COST: steps counted as the functions run ------------------------------
;
; one step a slot visited, and one an entry a bucket scan reads

(defun get-steps (s k d)
  (declare (xargs :measure (acl2-count s)))
  (cond ((hm-bucketp s) (+ 1 (len (cadr s))))
        ((hm-nodep s) (+ 1 (get-steps (nth (hidx (hk k) (1+ (nfix d))) (cadr s)) k (1+ (nfix d)))))
        (t 1)))

; the bucket k's path ends at, if it ends at one: what a scan can read
(defun path-bucket-len (s k d)
  (declare (xargs :measure (acl2-count s)))
  (cond ((hm-bucketp s) (len (cadr s)))
        ((hm-nodep s) (path-bucket-len (nth (hidx (hk k) (1+ (nfix d))) (cadr s)) k (1+ (nfix d))))
        (t 0)))

(defthm get-steps-bound
  (implies (and (hm-depth-ok s d) (natp d) (<= d *maxd*))
           (<= (get-steps s k d) (+ (- (1+ *maxd*) d) (path-bucket-len s k d))))
  :rule-classes :linear)

(defun split-steps (k1 k d)
  (declare (xargs :measure (nfix (- *maxd* (nfix d)))))
  (if (or (equal (hk k1) (hk k)) (<= *maxd* (nfix d)))
      2
    (let* ((d1 (1+ (nfix d))))
      (if (equal (hidx (hk k1) d1) (hidx (hk k) d1))
          (+ 1 (split-steps k1 k d1))
        1))))

(defthm split-steps-bound
  (implies (and (natp d) (<= d *maxd*))
           (<= (split-steps k1 k d) (+ 2 (- *maxd* d))))
  :rule-classes :linear)

(defun assoc-steps (s k d)
  (declare (xargs :measure (acl2-count s)))
  (cond ((hm-leafp s) (if (equal (cadr s) k) 1 (+ 1 (split-steps (cadr s) k d))))
        ; gcm_contains, then gcm_assoc: two scans
        ((hm-bucketp s) (+ 1 (len (cadr s)) (len (cadr s))))
        ((hm-nodep s) (+ 1 (assoc-steps (nth (hidx (hk k) (1+ (nfix d))) (cadr s)) k (1+ (nfix d)))))
        (t 1)))

(defthm assoc-steps-bound
  (implies (and (hm-depth-ok s d) (natp d) (<= d *maxd*))
           (<= (assoc-steps s k d) (+ (- (1+ *maxd*) d) (- (1+ *maxd*) d) 1
                                      (path-bucket-len s k d) (path-bucket-len s k d))))
  :rule-classes :linear)

; node_dissoc's walk: get's path, and in a bucket gcm_contains then gcm_dissoc
(defun dissoc-steps (s k d)
  (declare (xargs :measure (acl2-count s)))
  (cond ((hm-bucketp s) (+ 1 (len (cadr s)) (len (cadr s))))
        ((hm-nodep s) (+ 1 (dissoc-steps (nth (hidx (hk k) (1+ (nfix d))) (cadr s)) k (1+ (nfix d)))))
        (t 1)))

(defthm dissoc-steps-bound
  (implies (and (hm-depth-ok s d) (natp d) (<= d *maxd*))
           (<= (dissoc-steps s k d) (+ (- (1+ *maxd*) d) (path-bucket-len s k d) (path-bucket-len s k d))))
  :rule-classes :linear)

; at the root, d = 0: seven hops for a get, fifteen for an assoc that
; splits to the bottom, fourteen for gch_dissoc (gch_contains' walk,
; then node_dissoc's), and at most three scans of the one bucket on
; k's path
(defthm hm-get-steps
  (implies (hm-depth-ok-list node 0)
           (<= (get-steps (nth (hidx (hk k) 0) node) k 0)
               (+ 7 (path-bucket-len (nth (hidx (hk k) 0) node) k 0))))
  :rule-classes nil)

(defthm hm-assoc-steps
  (implies (hm-depth-ok-list node 0)
           (<= (assoc-steps (nth (hidx (hk k) 0) node) k 0)
               (+ 15 (path-bucket-len (nth (hidx (hk k) 0) node) k 0)
                  (path-bucket-len (nth (hidx (hk k) 0) node) k 0))))
  :rule-classes nil)

(defthm hm-dissoc-steps
  (implies (hm-depth-ok-list node 0)
           (<= (+ (get-steps (nth (hidx (hk k) 0) node) k 0)
                  (dissoc-steps (nth (hidx (hk k) 0) node) k 0))
               (+ 14 (path-bucket-len (nth (hidx (hk k) 0) node) k 0)
                  (path-bucket-len (nth (hidx (hk k) 0) node) k 0)
                  (path-bucket-len (nth (hidx (hk k) 0) node) k 0))))
  :rule-classes nil)
