; The sweep (model/heapsw.lisp) proved: it frees exactly the slots that are
; neither marked nor free, and leaves what is marked as it was -- every
; object's five slots (the sweep never writes one), a marked object's
; kind, a marked run's place and length -- and writes no arena word but
; the first word of a run it frees. With the marking's hpg-drain-closed,
; that is alloc-old.lisp's old-gc-invisible for this heap: what the roots
; reach is marked, and the sweep changes none of it.

(in-package "ACL2")

(include-book "heapsw")

(in-theory (disable nth update-nth hpgp hpg-ok hpg-sw-ok))

; ---- WHAT A FREE WRITES ----------------------------------------------------------------

(defthm hpg-free-obj-fields
  (and (equal (nth *h-otagi* (hpg-free-obj i hpg)) (nth *h-otagi* hpg))
       (equal (nth *h-orefi* (hpg-free-obj i hpg)) (nth *h-orefi* hpg))
       (equal (nth *h-omarki* (hpg-free-obj i hpg)) (nth *h-omarki* hpg))
       (equal (nth *h-voffi* (hpg-free-obj i hpg)) (nth *h-voffi* hpg))
       (equal (nth *h-vleni* (hpg-free-obj i hpg)) (nth *h-vleni* hpg))
       (equal (nth *h-vmarki* (hpg-free-obj i hpg)) (nth *h-vmarki* hpg))
       (equal (nth *h-vfreei* (hpg-free-obj i hpg)) (nth *h-vfreei* hpg))
       (equal (nth *h-atagi* (hpg-free-obj i hpg)) (nth *h-atagi* hpg))
       (equal (nth *h-arefi* (hpg-free-obj i hpg)) (nth *h-arefi* hpg))
       (equal (nth *h-aivali* (hpg-free-obj i hpg)) (nth *h-aivali* hpg))
       (equal (nth *h-smarki* (hpg-free-obj i hpg)) (nth *h-smarki* hpg))
       (equal (nth *h-sfreei* (hpg-free-obj i hpg)) (nth *h-sfreei* hpg)))
  :hints (("Goal" :in-theory (enable hpg-free-obj))))

(defthm hpg-free-obj-slot
  (and (equal (nth j (nth *h-okindi* (hpg-free-obj i hpg)))
              (if (equal (nfix j) (nfix i)) 0 (nth j (nth *h-okindi* hpg))))
       (equal (nth j (nth *h-ofreei* (hpg-free-obj i hpg)))
              (if (equal (nfix j) (nfix i)) 1 (nth j (nth *h-ofreei* hpg))))
       (equal (len (nth *h-ofreei* (hpg-free-obj i hpg)))
              (if (< (nfix i) (len (nth *h-ofreei* hpg))) (len (nth *h-ofreei* hpg)) (+ 1 (nfix i))))
       (equal (len (nth *h-okindi* (hpg-free-obj i hpg)))
              (if (< (nfix i) (len (nth *h-okindi* hpg))) (len (nth *h-okindi* hpg)) (+ 1 (nfix i)))))
  :hints (("Goal" :in-theory (enable hpg-free-obj nth update-nth))))

; a free in range keeps every array's length
(defthm hpg-free-obj-lens
  (implies (and (natp i) (< i (len (nth *h-okindi* hpg))) (< i (len (nth *h-ofreei* hpg)))
                (< i (len (nth *h-onexti* hpg))) (< i (len (nth *h-ofini* hpg))))
           (and (equal (len (nth *h-okindi* (hpg-free-obj i hpg))) (len (nth *h-okindi* hpg)))
                (equal (len (nth *h-ofreei* (hpg-free-obj i hpg))) (len (nth *h-ofreei* hpg)))
                (equal (len (nth *h-onexti* (hpg-free-obj i hpg))) (len (nth *h-onexti* hpg)))
                (equal (len (nth *h-ofini* (hpg-free-obj i hpg))) (len (nth *h-ofini* hpg)))))
  :hints (("Goal" :in-theory (enable hpg-free-obj))))

(in-theory (disable hpg-free-obj))

; ---- THE OBJECTS' SWEEP -------------------------------------------------------------------

(defmacro obj-in (j h)
  `(and (< ,j (len (nth *h-omarki* ,h))) (< ,j (len (nth *h-ofreei* ,h))) (< ,j (len (nth *h-okindi* ,h)))
        (< ,j (len (nth *h-onexti* ,h))) (< ,j (len (nth *h-ofini* ,h)))))

(defthm hpg-sweep-objs-keeps
  (and (equal (nth *h-otagi* (hpg-sweep-objs i n h)) (nth *h-otagi* h))
       (equal (nth *h-orefi* (hpg-sweep-objs i n h)) (nth *h-orefi* h))
       (equal (nth *h-omarki* (hpg-sweep-objs i n h)) (nth *h-omarki* h)))
  :hints (("Goal" :in-theory (enable hpg-sweep-objs))))

; a slot the sweep is past or has not reached is as it was
(defthm hpg-sweep-objs-outside
  (implies (and (natp j) (natp i) (< j i))
           (and (equal (nth j (nth *h-okindi* (hpg-sweep-objs i n h))) (nth j (nth *h-okindi* h)))
                (equal (nth j (nth *h-ofreei* (hpg-sweep-objs i n h))) (nth j (nth *h-ofreei* h)))))
  :hints (("Goal" :in-theory (enable hpg-sweep-objs) :induct (hpg-sweep-objs i n h))))

; THE SWEEP FREES EXACTLY THE UNMARKED: a slot in the range, both its marks
; read, is free after if it was free before or unmarked; its kind cleared
; exactly when it is freed
(defthm hpg-sweep-objs-frees
  (implies (and (natp i) (natp n) (natp j) (<= i j) (<= j n) (obj-in j h))
           (and (equal (nth j (nth *h-ofreei* (hpg-sweep-objs i n h)))
                       (if (and (equal (nth j (nth *h-omarki* h)) 0) (equal (nth j (nth *h-ofreei* h)) 0))
                           1
                         (nth j (nth *h-ofreei* h))))
                (equal (nth j (nth *h-okindi* (hpg-sweep-objs i n h)))
                       (if (and (equal (nth j (nth *h-omarki* h)) 0) (equal (nth j (nth *h-ofreei* h)) 0))
                           0
                         (nth j (nth *h-okindi* h))))))
  :hints (("Goal" :in-theory (enable hpg-sweep-objs) :induct (hpg-sweep-objs i n h))))

; ---- THE RUNS' SWEEP -----------------------------------------------------------------------

(defthm hpg-slab-free-fields
  (and (equal (nth *h-vmarki* (hpg-slab-free i hpg)) (nth *h-vmarki* hpg))
       (equal (nth *h-vfreei* (hpg-slab-free i hpg)) (nth *h-vfreei* hpg))
       (equal (nth *h-vnexti* (hpg-slab-free i hpg)) (nth *h-vnexti* hpg))
       (equal (nth *h-otagi* (hpg-slab-free i hpg)) (nth *h-otagi* hpg))
       (equal (nth *h-orefi* (hpg-slab-free i hpg)) (nth *h-orefi* hpg))
       (equal (nth *h-omarki* (hpg-slab-free i hpg)) (nth *h-omarki* hpg))
       (equal (nth *h-okindi* (hpg-slab-free i hpg)) (nth *h-okindi* hpg))
       (equal (nth *h-ofreei* (hpg-slab-free i hpg)) (nth *h-ofreei* hpg))
       (equal (nth *h-smarki* (hpg-slab-free i hpg)) (nth *h-smarki* hpg))
       (equal (nth *h-sfreei* (hpg-slab-free i hpg)) (nth *h-sfreei* hpg))
       (equal (nth *h-vhead* (hpg-slab-free i hpg)) (nth *h-vhead* hpg))
       (equal (nth *h-nswv* (hpg-slab-free i hpg)) (nth *h-nswv* hpg)))
  :hints (("Goal" :in-theory (enable hpg-slab-free))))

(defthm hpg-slab-free-others
  (implies (and (natp j) (not (equal j (nfix i))))
           (and (equal (nth j (nth *h-voffi* (hpg-slab-free i hpg))) (nth j (nth *h-voffi* hpg)))
                (equal (nth j (nth *h-vleni* (hpg-slab-free i hpg))) (nth j (nth *h-vleni* hpg)))))
  :hints (("Goal" :in-theory (enable hpg-slab-free nth update-nth))))

; an arena word other than the run's first is untouched
(defthm hpg-slab-free-words
  (implies (and (natp w) (not (equal w (hpg-n40 (nth i (nth *h-voffi* hpg))))))
           (and (equal (nth w (nth *h-atagi* (hpg-slab-free i hpg))) (nth w (nth *h-atagi* hpg)))
                (equal (nth w (nth *h-arefi* (hpg-slab-free i hpg))) (nth w (nth *h-arefi* hpg)))
                (equal (nth w (nth *h-aivali* (hpg-slab-free i hpg))) (nth w (nth *h-aivali* hpg)))))
  :hints (("Goal" :in-theory (enable hpg-slab-free nth update-nth))))

(defthm hpg-slab-free-lens
  (implies (and (natp i) (< i (len (nth *h-voffi* hpg))) (< i (len (nth *h-vleni* hpg))))
           (and (equal (len (nth *h-voffi* (hpg-slab-free i hpg))) (len (nth *h-voffi* hpg)))
                (equal (len (nth *h-vleni* (hpg-slab-free i hpg))) (len (nth *h-vleni* hpg)))))
  :hints (("Goal" :in-theory (enable hpg-slab-free))))

(in-theory (disable hpg-slab-free))

(defthm hpg-free-vec-fields
  (and (equal (nth *h-vmarki* (hpg-free-vec i hpg)) (nth *h-vmarki* hpg))
       (equal (nth *h-otagi* (hpg-free-vec i hpg)) (nth *h-otagi* hpg))
       (equal (nth *h-orefi* (hpg-free-vec i hpg)) (nth *h-orefi* hpg))
       (equal (nth *h-omarki* (hpg-free-vec i hpg)) (nth *h-omarki* hpg))
       (equal (nth *h-okindi* (hpg-free-vec i hpg)) (nth *h-okindi* hpg))
       (equal (nth *h-ofreei* (hpg-free-vec i hpg)) (nth *h-ofreei* hpg))
       (equal (nth *h-smarki* (hpg-free-vec i hpg)) (nth *h-smarki* hpg))
       (equal (nth *h-sfreei* (hpg-free-vec i hpg)) (nth *h-sfreei* hpg)))
  :hints (("Goal" :in-theory (enable hpg-free-vec))))

(defthm hpg-free-vec-slot
  (implies (natp j)
           (and (equal (nth j (nth *h-vfreei* (hpg-free-vec i hpg)))
                       (if (equal j (nfix i)) 1 (nth j (nth *h-vfreei* hpg))))
                (implies (not (equal j (nfix i)))
                         (and (equal (nth j (nth *h-voffi* (hpg-free-vec i hpg))) (nth j (nth *h-voffi* hpg)))
                              (equal (nth j (nth *h-vleni* (hpg-free-vec i hpg))) (nth j (nth *h-vleni* hpg)))))))
  :hints (("Goal" :in-theory (enable hpg-free-vec nth update-nth))))

(defthm hpg-free-vec-words
  (implies (and (natp w) (not (equal w (hpg-n40 (nth i (nth *h-voffi* hpg))))))
           (and (equal (nth w (nth *h-atagi* (hpg-free-vec i hpg))) (nth w (nth *h-atagi* hpg)))
                (equal (nth w (nth *h-arefi* (hpg-free-vec i hpg))) (nth w (nth *h-arefi* hpg)))))
  :hints (("Goal" :in-theory (enable hpg-free-vec))))

(defthm hpg-free-vec-lens
  (implies (and (natp i) (< i (len (nth *h-voffi* hpg))) (< i (len (nth *h-vleni* hpg)))
                (< i (len (nth *h-vfreei* hpg))) (< i (len (nth *h-vnexti* hpg))))
           (and (equal (len (nth *h-voffi* (hpg-free-vec i hpg))) (len (nth *h-voffi* hpg)))
                (equal (len (nth *h-vleni* (hpg-free-vec i hpg))) (len (nth *h-vleni* hpg)))
                (equal (len (nth *h-vfreei* (hpg-free-vec i hpg))) (len (nth *h-vfreei* hpg)))
                (equal (len (nth *h-vnexti* (hpg-free-vec i hpg))) (len (nth *h-vnexti* hpg)))))
  :hints (("Goal" :in-theory (enable hpg-free-vec))))

(in-theory (disable hpg-free-vec))

(defmacro vec-in (j h)
  `(and (< ,j (len (nth *h-vmarki* ,h))) (< ,j (len (nth *h-vfreei* ,h))) (< ,j (len (nth *h-voffi* ,h)))
        (< ,j (len (nth *h-vleni* ,h))) (< ,j (len (nth *h-vnexti* ,h)))))

(defthm hpg-sweep-vecs-keeps
  (equal (nth *h-vmarki* (hpg-sweep-vecs i n h)) (nth *h-vmarki* h))
  :hints (("Goal" :in-theory (enable hpg-sweep-vecs))))

(defthm hpg-sweep-vecs-outside
  (implies (and (natp j) (natp i) (< j i))
           (and (equal (nth j (nth *h-vfreei* (hpg-sweep-vecs i n h))) (nth j (nth *h-vfreei* h)))
                (equal (nth j (nth *h-voffi* (hpg-sweep-vecs i n h))) (nth j (nth *h-voffi* h)))
                (equal (nth j (nth *h-vleni* (hpg-sweep-vecs i n h))) (nth j (nth *h-vleni* h)))))
  :hints (("Goal" :in-theory (enable hpg-sweep-vecs) :induct (hpg-sweep-vecs i n h))))

; THE SWEEP FREES EXACTLY THE UNMARKED RUNS, and a run it does not free
; keeps its place and length
(defthm hpg-sweep-vecs-frees
  (implies (and (natp i) (natp n) (natp j) (<= i j) (<= j n) (vec-in j h))
           (and (equal (nth j (nth *h-vfreei* (hpg-sweep-vecs i n h)))
                       (if (and (equal (nth j (nth *h-vmarki* h)) 0) (equal (nth j (nth *h-vfreei* h)) 0))
                           1
                         (nth j (nth *h-vfreei* h))))
                (implies (not (and (equal (nth j (nth *h-vmarki* h)) 0) (equal (nth j (nth *h-vfreei* h)) 0)))
                         (and (equal (nth j (nth *h-voffi* (hpg-sweep-vecs i n h))) (nth j (nth *h-voffi* h)))
                              (equal (nth j (nth *h-vleni* (hpg-sweep-vecs i n h))) (nth j (nth *h-vleni* h)))))))
  :hints (("Goal" :in-theory (enable hpg-sweep-vecs) :induct (hpg-sweep-vecs i n h))))

; no run the sweep frees, from i to n, starts at arena word w
(defun no-start (w i n h)
  (declare (xargs :measure (nfix (- (+ 1 (nfix n)) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (< n i))
      t
    (and (implies (and (vec-in i h) (equal (nth i (nth *h-vmarki* h)) 0) (equal (nth i (nth *h-vfreei* h)) 0))
                  (not (equal w (hpg-n40 (nth i (nth *h-voffi* h))))))
         (no-start w (+ 1 i) n h))))

; a free at run i leaves the runs after it as they were
(defthm no-start-free-vec
  (implies (and (natp i) (natp k) (< i k) (vec-in i h))
           (equal (no-start w k n (hpg-free-vec i h)) (no-start w k n h)))
  :hints (("Goal" :induct (no-start w k n h) :expand ((:free (w) (no-start w k n (hpg-free-vec i h)))))))

; the arena words no freed run starts at are as they were: a marked run's
; words, where runs do not overlap
(defthm hpg-sweep-vecs-words
  (implies (and (natp w) (no-start w i n h))
           (and (equal (nth w (nth *h-atagi* (hpg-sweep-vecs i n h))) (nth w (nth *h-atagi* h)))
                (equal (nth w (nth *h-arefi* (hpg-sweep-vecs i n h))) (nth w (nth *h-arefi* h)))))
  :hints (("Goal" :in-theory (enable hpg-sweep-vecs) :induct (hpg-sweep-vecs i n h))))

; ---- THE TEXTS' SWEEP ----------------------------------------------------------------------

(defthm hpg-free-str-slot
  (implies (natp j)
           (equal (nth j (nth *h-sfreei* (hpg-free-str i hpg)))
                  (if (equal j (nfix i)) 1 (nth j (nth *h-sfreei* hpg)))))
  :hints (("Goal" :in-theory (enable hpg-free-str nth update-nth))))

(defthm hpg-free-str-fields
  (equal (nth *h-smarki* (hpg-free-str i hpg)) (nth *h-smarki* hpg))
  :hints (("Goal" :in-theory (enable hpg-free-str))))

(defthm hpg-free-str-lens
  (implies (and (natp i) (< i (len (nth *h-sreli* hpg))) (< i (len (nth *h-sfreei* hpg))) (< i (len (nth *h-snexti* hpg))))
           (and (equal (len (nth *h-sreli* (hpg-free-str i hpg))) (len (nth *h-sreli* hpg)))
                (equal (len (nth *h-sfreei* (hpg-free-str i hpg))) (len (nth *h-sfreei* hpg)))
                (equal (len (nth *h-snexti* (hpg-free-str i hpg))) (len (nth *h-snexti* hpg)))))
  :hints (("Goal" :in-theory (enable hpg-free-str))))

(in-theory (disable hpg-free-str))

(defmacro str-in (j h)
  `(and (< ,j (len (nth *h-smarki* ,h))) (< ,j (len (nth *h-sfreei* ,h))) (< ,j (len (nth *h-sreli* ,h)))
        (< ,j (len (nth *h-snexti* ,h)))))

(defthm hpg-sweep-strs-outside
  (implies (and (natp j) (natp i) (< j i))
           (equal (nth j (nth *h-sfreei* (hpg-sweep-strs i n h))) (nth j (nth *h-sfreei* h))))
  :hints (("Goal" :in-theory (enable hpg-sweep-strs) :induct (hpg-sweep-strs i n h))))

(defthm hpg-sweep-strs-frees
  (implies (and (natp i) (natp n) (natp j) (<= i j) (<= j n) (str-in j h))
           (equal (nth j (nth *h-sfreei* (hpg-sweep-strs i n h)))
                  (if (and (equal (nth j (nth *h-smarki* h)) 0) (equal (nth j (nth *h-sfreei* h)) 0))
                      1
                    (nth j (nth *h-sfreei* h)))))
  :hints (("Goal" :in-theory (enable hpg-sweep-strs) :induct (hpg-sweep-strs i n h))))
