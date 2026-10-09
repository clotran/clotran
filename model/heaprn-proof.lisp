; The arena's allocation (model/heaprn.lisp) proved: no run handed out
; overlaps a run still free or batched.
;
; A run is (off . len), the words off .. off+len-1. THE INVARIANT, for a
; size class c of run length l, over a ghost list L -- the class's free
; list's offsets in order -- and a ghost list R of runs that must be kept
; apart from the class's (every other class's free and batched runs):
; L runs from the class's head through the first words' links to 0; the
; class's batch is in range; every run of L, of the batch and of R lies
; inside the used arena; and all of them together are pairwise apart.
; Then:
;   hpg-run-new-safe   a run taken is L's head (the list its rest) or the
;                      run just past the used end, apart from all that is
;                      left, or 0
;   hpg-run-push-safe  a run apart from all of them onto the batch
;   hpg-run-pop-safe   the batch's last, apart from all that is left
;   hpg-runs-fill-safe a fill moves runs from L's front, or from past the
;                      used end, onto the batch
;   hpg-run-take-safe  what run_take hands out: in the arena, apart from
;                      all that is left
; Allocation never writes a run's words or another class's head, so these
; keep every other class's invariant too (hpg-run-take-other).

(in-package "ACL2")

(include-book "heaprn")

(in-theory (disable nth update-nth hpgp hpg-ok hpg-sw-ok hpg-al-ok hpg-rn-ok))

(defmacro aused (h) `(nth *h-aused* ,h))
(defmacro aival (h) `(nth *h-aivali* ,h))
(defmacro chead (h) `(nth *h-cheadi* ,h))
(defmacro rb (h) `(nth *h-rbi* ,h))
(defmacro nrb (h) `(nth *h-nrbi* ,h))

; a batch count or entry read in range is an integer, said forward so that
; type reasoning sees it
(defthm nrb-elem-fc
  (implies (and (hpgp h) (natp c) (< c (len (nrb h)))) (integerp (nth c (nrb h))))
  :rule-classes ((:forward-chaining :trigger-terms ((nth c (nrb h))))))
(defthm rb-elem-fc
  (implies (and (hpgp h) (natp j) (< j (len (rb h)))) (integerp (nth j (rb h))))
  :rule-classes ((:forward-chaining :trigger-terms ((nth j (rb h))))))

; ---- RUNS AND APARTNESS -------------------------------------------------------------------

; a run inside the used arena, its first word's link in range
(defun run-at (off l h)
  (and (natp off) (< 0 off) (posp l) (integerp (aused h)) (<= (+ off l) (+ 1 (aused h)))
       (< off (len (aival h)))))

(defun runs (offs l) (if (endp offs) nil (cons (cons (car offs) l) (runs (cdr offs) l))))

(defun r-in (rs h)
  (if (endp rs) t (and (consp (car rs)) (run-at (caar rs) (cdar rs) h) (r-in (cdr rs) h))))

(defun apart (a b) (or (<= (+ (car a) (cdr a)) (car b)) (<= (+ (car b) (cdr b)) (car a))))
(defun apart-all (a l) (if (endp l) t (and (apart a (car l)) (apart-all a (cdr l)))))
(defun all-apart (l) (if (endp l) t (and (apart-all (car l) (cdr l)) (all-apart (cdr l)))))

; ---- THE CLASS'S LIST AND BATCH -----------------------------------------------------------

(defun rn-fl (offs head l h)
  (if (endp offs)
      (equal head 0)
    (and (equal head (car offs)) (run-at (car offs) l h)
         (rn-fl (cdr offs) (nth (car offs) (aival h)) l h))))

(defun c-head (c h) (if (< c (len (chead h))) (nth c (chead h)) 0))

; the batch's offsets, last first
(defun b-offs (c k h) (if (zp k) nil (cons (nth (rb-at c k) (rb h)) (b-offs c (1- k) h))))

(defun c-batched (c h) (and (<= 1 c) (<= c *run-classes*) (< c (len (nrb h)))))

(defun batch-ok (c h)
  (or (not (c-batched c h))
      (and (natp (nth c (nrb h))) (<= (nth c (nrb h)) *run-batch*)
           (< (rb-at c (nth c (nrb h))) (len (rb h))))))

(defun c-batch (c h) (if (c-batched c h) (b-offs c (nfix (nth c (nrb h))) h) nil))

(defun rn-inv (c l fl r h)
  (and (true-listp fl) (natp c) (posp l)
       (integerp (nth *h-acap* h)) (< (nth *h-acap* h) (len (aival h)))
       (rn-fl fl (c-head c h) l h)
       (<= 0 (c-head c h)) (< (c-head c h) (len (aival h)))
       (batch-ok c h)
       (r-in (runs (c-batch c h) l) h) (r-in r h)
       (all-apart (append (runs fl l) (append (runs (c-batch c h) l) r)))))

; ---- APARTNESS LEMMAS ---------------------------------------------------------------------

(defthm apart-sym (equal (apart a b) (apart b a)))
(in-theory (disable apart-sym))

(defthm apart-all-append
  (equal (apart-all a (append x y)) (and (apart-all a x) (apart-all a y))))

(defthm all-apart-append-cons
  (equal (all-apart (append (cons a x) y))
         (and (apart-all a (append x y)) (all-apart (append x y)))))

(defthm apart-all-sym-member
  (implies (and (apart-all a l) (member b l)) (apart b a))
  :hints (("Goal" :in-theory (enable apart-sym))))

(defun apart-all-each (l a) (if (endp l) t (and (apart (car l) a) (apart-all-each (cdr l) a))))

(defthm apart-all-each-is
  (equal (apart-all-each l a) (apart-all a l))
  :hints (("Goal" :in-theory (enable apart-sym))))

; an element in the middle of an appended list: apart from the rest, and
; the rest apart
(defthm all-apart-middle
  (equal (all-apart (append x (cons a y)))
         (and (apart-all a (append x y)) (all-apart (append x y))))
  :hints (("Goal" :induct (len x) :in-theory (enable apart-sym))))

; every run of a list inside the arena, with the arena's end before o: o's
; run is apart from them all
(defthm r-in-below
  (implies (and (r-in rs h) (integerp (aused h)) (integerp o) (< (aused h) o))
           (apart-all (cons o l) rs)))

(defthm r-in-append (equal (r-in (append x y) h) (and (r-in x h) (r-in y h))))

(defthm rn-fl-r-in (implies (rn-fl offs head l h) (r-in (runs offs l) h)))

; ---- FRAMES -------------------------------------------------------------------------------

; the arena's used end raised: what was inside it still is
(defthm run-at-used-up
  (implies (and (run-at off l h) (integerp u) (<= (aused h) u)) (run-at off l (update-nth *h-aused* u h))))
(defthm r-in-used-up
  (implies (and (r-in rs h) (integerp u) (<= (aused h) u)) (r-in rs (update-nth *h-aused* u h))))
(defthm rn-fl-used-up
  (implies (and (rn-fl offs head l h) (integerp u) (<= (aused h) u)) (rn-fl offs head l (update-nth *h-aused* u h))))

; fields the class's view does not read
(defmacro rn-not-read (name fld)
  `(defthm ,name
     (and (equal (run-at off l (update-nth ,fld v h)) (run-at off l h))
          (equal (r-in rs (update-nth ,fld v h)) (r-in rs h))
          (equal (rn-fl offs head l (update-nth ,fld v h)) (rn-fl offs head l h)))
     :hints (("Goal" :induct (rn-fl offs head l h)))))
(rn-not-read areu-not-read *h-areu*) (rn-not-read afre-not-read *h-afre*) (rn-not-read asince-not-read *h-asince*)
(rn-not-read chead-not-read *h-cheadi*) (rn-not-read rb-not-read *h-rbi*) (rn-not-read nrb-not-read *h-nrbi*)
(defthm r-in-not-read-areu (equal (r-in rs (update-nth *h-areu* v h)) (r-in rs h)))

(defthm b-offs-frame
  (implies (and (natp fld) (not (equal fld *h-rbi*))) (equal (b-offs c k (update-nth fld v h)) (b-offs c k h))))

; a batch slot written outside the first k: they are as they were
(defthm b-offs-write-above
  (implies (and (equal x (rb h)) (natp c) (<= 1 c) (natp k) (natp j) (< (rb-at c k) j))
           (equal (b-offs c k (update-nth *h-rbi* (update-nth j v x) h)) (b-offs c k h))))
(defthm b-offs-write-below
  (implies (and (equal x (rb h)) (natp c) (<= 1 c) (natp k) (natp j) (< j (rb-at c 1)))
           (equal (b-offs c k (update-nth *h-rbi* (update-nth j v x) h)) (b-offs c k h))))

(defthm b-offs-step
  (implies (natp k) (equal (b-offs c (+ 1 k) h) (cons (nth (rb-at c (+ 1 k)) (rb h)) (b-offs c k h)))))

(defthm c-head-other
  (implies (and (equal x (chead h)) (natp c) (natp d) (< d (len x)) (not (equal d c)))
           (equal (c-head c (update-nth *h-cheadi* (update-nth d v x) h)) (c-head c h))))

(defthm c-head-self
  (implies (and (equal x (chead h)) (natp c) (< c (len x)))
           (equal (c-head c (update-nth *h-cheadi* (update-nth c v x) h)) v)))

(defthm c-head-frame
  (implies (and (natp fld) (not (equal fld *h-cheadi*))) (equal (c-head c (update-nth fld v h)) (c-head c h))))
(defthm c-batched-frame
  (implies (and (natp fld) (not (equal fld *h-nrbi*))) (equal (c-batched c (update-nth fld v h)) (c-batched c h))))
(defthm batch-ok-frame
  (implies (and (natp fld) (not (equal fld *h-nrbi*)) (not (equal fld *h-rbi*)))
           (equal (batch-ok c (update-nth fld v h)) (batch-ok c h))))
(defthm c-batch-frame
  (implies (and (natp fld) (not (equal fld *h-nrbi*)) (not (equal fld *h-rbi*)))
           (equal (c-batch c (update-nth fld v h)) (c-batch c h))))

(defthm rn-fl-head-consp (implies (and (rn-fl offs head l h) (not (equal head 0))) (consp offs)))

; a list's head, said forward: a nonzero head is the list's first run,
; inside the arena; a zero head, an empty list
(defthm rn-fl-head-facts
  (implies (and (rn-fl offs head l h) (not (equal head 0)))
           (and (consp offs) (equal (car offs) head) (integerp head) (< 0 head) (< head (len (aival h)))
                (integerp (aused h)) (<= (+ head l) (+ 1 (aused h)))))
  :rule-classes :forward-chaining)
(defthm rn-fl-head-range
  (implies (and (rn-fl offs head l h) (< 0 (len (aival h))))
           (and (<= 0 head) (< head (len (aival h)))))
  :rule-classes :rewrite)
(defthm rn-fl-zero-head
  (implies (and (rn-fl offs head l h) (equal head 0)) (not (consp offs)))
  :rule-classes :forward-chaining)

(defthm hpg-s64-is (implies (sb64ip x) (equal (hpg-s64 x) x)) :hints (("Goal" :in-theory (enable hpg-s64))))

(defthm aival-elem-sb64
  (implies (and (hpgp h) (< (nfix i) (len (aival h))))
           (sb64ip (nth i (aival h))))
  :hints (("Goal" :use ((:instance hpg-aival-elem (hpg h) (j i))))))

(defthm hpg-s64-aival
  (implies (and (hpgp h) (< (nfix i) (len (aival h))))
           (equal (hpg-s64 (nth i (aival h))) (nth i (aival h))))
  :hints (("Goal" :in-theory (disable aival-elem-sb64 hpg-s64-is)
           :use ((:instance aival-elem-sb64) (:instance hpg-s64-is (x (nth i (aival h))))))))


(defmacro rest-of (fl c h) `(append (runs ,fl l) (append (runs (c-batch ,c ,h) l) r)))

; A RUN TAKEN: the list's head, the list its rest; or the run past the
; used end, apart from every run there is; or 0
(defthm hpg-run-new-safe
  (implies (and (hpgp h) (hpg-rn-ok h) (natp c) (posp l) (<= l *hb40*) (rn-inv c l fl r h))
           (let ((off (car (hpg-run-new c l h))) (h2 (mv-nth 1 (hpg-run-new c l h))))
             (if (consp fl)
                 (and (equal off (car fl)) (rn-inv c l (cdr fl) r h2) (run-at off l h2)
                      (apart-all (cons off l) (rest-of (cdr fl) c h2)))
               (and (rn-inv c l fl r h2)
                    (or (equal off 0)
                        (and (run-at off l h2) (apart-all (cons off l) (rest-of fl c h2))))))))
  :hints (("Goal" :in-theory (enable hpg-run-new) :expand ((rn-fl fl (nth c (chead h)) l h)))))

; the same, as three rules: the list left is always the list's rest (an
; empty list's rest is itself), the run taken is the list's head when there
; is one, and a run taken is in the arena and apart from all that is left
(defthm hpg-run-new-inv
  (implies (and (hpgp h) (hpg-rn-ok h) (natp c) (posp l) (<= l *hb40*) (rn-inv c l fl r h))
           (rn-inv c l (cdr fl) r (mv-nth 1 (hpg-run-new c l h))))
  :hints (("Goal" :use hpg-run-new-safe :in-theory (disable hpg-run-new-safe))))
(defthm hpg-run-new-head
  (implies (and (hpgp h) (hpg-rn-ok h) (natp c) (posp l) (<= l *hb40*) (rn-inv c l fl r h) (consp fl))
           (equal (car (hpg-run-new c l h)) (car fl)))
  :hints (("Goal" :use hpg-run-new-safe :in-theory (disable hpg-run-new-safe))))
(defthm hpg-run-new-apart
  (implies (and (hpgp h) (hpg-rn-ok h) (natp c) (posp l) (<= l *hb40*) (rn-inv c l fl r h)
                (not (equal (car (hpg-run-new c l h)) 0)))
           (and (run-at (car (hpg-run-new c l h)) l (mv-nth 1 (hpg-run-new c l h)))
                (apart-all (cons (car (hpg-run-new c l h)) l) (rest-of (cdr fl) c (mv-nth 1 (hpg-run-new c l h))))))
  :hints (("Goal" :use hpg-run-new-safe :in-theory (disable hpg-run-new-safe))))

; A RUN PUSHED onto the batch, apart from all there is: the batch has it
; on top
(defthm hpg-run-push-safe
  (implies (and (hpgp h) (hpg-rn-ok h) (rn-inv c l fl r h) (c-batched c h)
                (equal n (nth c (nrb h))) (natp n) (< n *run-batch*) (< (rb-at c (+ 1 n)) (len (rb h)))
                (run-at off l h) (apart-all (cons off l) (rest-of fl c h)))
           (and (rn-inv c l fl r (hpg-run-push c n off h))
                (equal (c-batch c (hpg-run-push c n off h)) (cons off (c-batch c h)))))
  :hints (("Goal" :in-theory (e/d (hpg-run-push) (hpg-nrb-elem)) :do-not-induct t
           :use ((:instance hpg-nrb-elem (hpg h) (j c))))))

; A RUN POPPED: the batch's last, apart from all that is left
(defthm hpg-run-pop-safe
  (implies (and (hpgp h) (hpg-rn-ok h) (rn-inv c l fl r h) (consp (c-batch c h)))
           (let ((off (car (hpg-run-pop c h))) (h2 (mv-nth 1 (hpg-run-pop c h))))
             (and (equal off (car (c-batch c h)))
                  (equal (c-batch c h2) (cdr (c-batch c h)))
                  (rn-inv c l fl r h2) (run-at off l h2)
                  (apart-all (cons off l) (rest-of fl c h2)))))
  :hints (("Goal" :in-theory (enable hpg-run-pop) :do-not-induct t :expand ((b-offs c (nth c (nrb h)) h)))))

(defthm rn-inv-facts
  (implies (rn-inv c l fl r h) (and (natp c) (posp l) (true-listp fl)))
  :rule-classes :forward-chaining)

(defthm c-batch-unbatched
  (implies (not (c-batched c h)) (equal (c-batch c h) nil)))

(in-theory (disable rn-inv hpg-run-push c-batch))

; no run taken, nothing changed
(defthm hpg-run-new-none
  (implies (and (hpgp h) (hpg-rn-ok h) (equal (car (hpg-run-new c l h)) 0))
           (equal (mv-nth 1 (hpg-run-new c l h)) h))
  :hints (("Goal" :in-theory (enable hpg-run-new))))

; a run taken is apart from each part of what is left
(defthm hpg-run-new-apart-parts
  (implies (and (hpgp h) (hpg-rn-ok h) (natp c) (posp l) (<= l *hb40*) (rn-inv c l fl r h)
                (not (equal (car (hpg-run-new c l h)) 0)))
           (and (apart-all (cons (car (hpg-run-new c l h)) l) (runs (cdr fl) l))
                (apart-all (cons (car (hpg-run-new c l h)) l) (runs (c-batch c (mv-nth 1 (hpg-run-new c l h))) l))
                (apart-all (cons (car (hpg-run-new c l h)) l) r)))
  :hints (("Goal" :use hpg-run-new-apart :in-theory (disable hpg-run-new-apart hpg-run-new hpg-run-new-safe))))

; what is left of the list as a fill takes from it: its rest, for each run
; the fill takes
(defun-nx rn-fill-rest (fl c l fuel h)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (not (and (<= 1 c) (<= c *run-classes*) (< c (len (nrb h))))))
      fl
    (let ((n (nth c (nrb h))))
      (if (not (and (<= 0 n) (< n *run-batch*) (< (rb-at c (+ 1 n)) (len (rb h)))))
          fl
        (let ((off (car (hpg-run-new c l h))) (h1 (mv-nth 1 (hpg-run-new c l h))))
          (if (equal off 0)
              fl
            (rn-fill-rest (cdr fl) c l (- fuel 1) (hpg-run-push c n off h1))))))))

; A FILL keeps the invariant
(defthm hpg-runs-fill-safe
  (implies (and (hpgp h) (hpg-rn-ok h) (natp c) (posp l) (<= l *hb40*) (rn-inv c l fl r h))
           (rn-inv c l (rn-fill-rest fl c l fuel h) r (hpg-runs-fill c l fuel h)))
  :hints (("Goal" :induct (rn-fill-rest fl c l fuel h)
           :in-theory (e/d (hpg-runs-fill) (hpg-run-new hpg-run-new-safe)))))

; an empty batch pops 0 and changes nothing; a batch with runs pops one
(defthm hpg-run-pop-empty
  (implies (and (hpgp h) (hpg-rn-ok h) (rn-inv c l fl r h) (not (consp (c-batch c h))))
           (and (equal (car (hpg-run-pop c h)) 0) (equal (mv-nth 1 (hpg-run-pop c h)) h)))
  :hints (("Goal" :in-theory (enable hpg-run-pop c-batch rn-inv) :expand ((b-offs c (nth c (nrb h)) h)))))
(defthm r-in-runs-car
  (implies (and (r-in (runs offs l) h) (consp offs))
           (and (integerp (car offs)) (< 0 (car offs)))))
(defthm c-batch-car
  (implies (and (rn-inv c l fl r h) (consp (c-batch c h)))
           (and (integerp (car (c-batch c h))) (< 0 (car (c-batch c h)))))
  :hints (("Goal" :in-theory (enable rn-inv))))
(defthm hpg-run-pop-none
  (implies (equal (car (hpg-run-pop c h)) 0) (equal (mv-nth 1 (hpg-run-pop c h)) h))
  :hints (("Goal" :in-theory (enable hpg-run-pop))))
(defthm hpg-run-pop-had-runs
  (implies (and (hpgp h) (hpg-rn-ok h) (rn-inv c l fl r h) (not (equal (car (hpg-run-pop c h)) 0)))
           (consp (c-batch c h)))
  :hints (("Goal" :use hpg-run-pop-empty :in-theory (disable hpg-run-pop-empty))))
(defthm hpg-run-pop-nonzero
  (implies (and (hpgp h) (hpg-rn-ok h) (rn-inv c l fl r h) (consp (c-batch c h)))
           (and (integerp (car (hpg-run-pop c h))) (< 0 (car (hpg-run-pop c h)))))
  :hints (("Goal" :use hpg-run-pop-safe :in-theory (disable hpg-run-pop-safe))))

(in-theory (disable hpg-run-pop hpg-runs-fill))

; a pop after a fill (or with no fill): the run is the batch's, apart from
; all that is left
(defthm hpg-pop-after-safe
  (implies (and (hpgp h) (hpg-rn-ok h) (natp c) (posp l) (<= l *hb40*) (rn-inv c l fl r h)
                (not (equal (car (hpg-run-pop c h)) 0)))
           (let ((off (car (hpg-run-pop c h))) (h2 (mv-nth 1 (hpg-run-pop c h))))
             (and (rn-inv c l fl r h2) (run-at off l h2) (apart-all (cons off l) (rest-of fl c h2)))))
  :hints (("Goal" :do-not-induct t :in-theory (disable hpg-run-pop-safe hpg-run-pop-had-runs)
           :use (hpg-run-pop-had-runs hpg-run-pop-safe))))

(defthm hpg-fill-ok-instance
  (implies (and (hpgp h) (hpg-rn-ok h) (natp c) (posp l) (<= l *hb40*))
           (and (hpgp (hpg-runs-fill c l fuel h)) (hpg-rn-ok (hpg-runs-fill c l fuel h))))
  :hints (("Goal" :use ((:instance hpg-runs-fill-ok (hpg h))) :in-theory (disable hpg-runs-fill-ok))))

(defmacro took-safe (off h2 fl2)
  `(and (rn-inv c l ,fl2 r ,h2)
        (implies (not (equal ,off 0)) (and (run-at ,off l ,h2) (apart-all (cons ,off l) (rest-of ,fl2 c ,h2))))))

; FROM THE BATCH, or else from the list or the end
(defun-nx rn-fb-rest (fl c h) (if (< 0 (car (hpg-run-pop c h))) fl (cdr fl)))

(defthm hpg-run-from-batch-safe
  (implies (and (hpgp h) (hpg-rn-ok h) (natp c) (posp l) (<= l *hb40*) (rn-inv c l fl r h))
           (took-safe (car (hpg-run-from-batch c l h)) (mv-nth 1 (hpg-run-from-batch c l h)) (rn-fb-rest fl c h)))
  :hints (("Goal" :in-theory (e/d (hpg-run-from-batch)
                                  (hpg-run-new hpg-run-new-safe hpg-pop-after-safe hpg-run-new-apart hpg-run-new-inv))
           :do-not-induct t :use (hpg-pop-after-safe hpg-run-new-apart hpg-run-new-inv))))

; A CLASS'S RUN: through the batch, filled first if empty, or not
(defun-nx rn-tc-rest (fl c l batching h)
  (if (and (not (equal batching 0)) (<= c *run-classes*))
      (if (and (< c (len (nrb h))) (equal (nth c (nrb h)) 0))
          (rn-fb-rest (rn-fill-rest fl c l *run-batch* h) c (hpg-runs-fill c l *run-batch* h))
        (rn-fb-rest fl c h))
    (cdr fl)))

(defthm hpg-run-take-c-safe
  (implies (and (hpgp h) (hpg-rn-ok h) (natp c) (posp l) (<= l *hb40*) (rn-inv c l fl r h))
           (took-safe (car (hpg-run-take-c c l batching h)) (mv-nth 1 (hpg-run-take-c c l batching h))
                      (rn-tc-rest fl c l batching h)))
  :hints (("Goal" :in-theory (e/d (hpg-run-take-c)
                                  (hpg-run-new hpg-run-from-batch hpg-run-from-batch-safe hpg-runs-fill-safe
                                   hpg-run-new-safe hpg-run-new-apart hpg-run-new-inv hpg-fill-ok-instance
                                   rn-fb-rest rn-fill-rest rn-tc-rest))
           :expand ((rn-tc-rest fl c l batching h))
           :do-not-induct t
           :use (hpg-run-from-batch-safe hpg-run-new-apart hpg-run-new-inv
                 (:instance hpg-runs-fill-safe (fuel 64))
                 (:instance hpg-fill-ok-instance (fuel 64))
                 (:instance hpg-run-from-batch-safe (h (hpg-runs-fill c l 64 h)) (fl (rn-fill-rest fl c l 64 h)))))))

; WHAT run_take HANDS OUT is in the arena and apart from every run still
; free or batched, here or in R; and the invariant holds of what is left
(defun-nx rn-take-rest (fl n batching h)
  (if (not (< 0 n)) fl (rn-tc-rest fl (hpg-size-class n 1 1) (hpg-class-len (hpg-size-class n 1 1) 1 1) batching h)))

(defthm hpg-run-take-safe
  (implies (and (hpgp h) (hpg-rn-ok h) (natp n) (<= n *hb40*)
                (equal c (hpg-size-class n 1 1)) (equal l (hpg-class-len c 1 1)) (rn-inv c l fl r h))
           (took-safe (car (hpg-run-take n batching h)) (mv-nth 1 (hpg-run-take n batching h))
                      (rn-take-rest fl n batching h)))
  :hints (("Goal" :in-theory (e/d (hpg-run-take) (hpg-run-take-c hpg-run-take-c-safe rn-tc-rest))
           :do-not-induct t :use hpg-run-take-c-safe)))

; ---- EVERY OTHER CLASS ----------------------------------------------------------------------

; class d's view the same in h2 as in h: its head, its batch, the arena's
; links and size, and the used end no lower
(defun d-kept (d h h2)
  (and (equal (c-head d h2) (c-head d h)) (equal (c-batch d h2) (c-batch d h)) (equal (batch-ok d h2) (batch-ok d h))
       (equal (aival h2) (aival h)) (equal (nth *h-acap* h2) (nth *h-acap* h))
       (integerp (aused h)) (integerp (aused h2)) (<= (aused h) (aused h2))))

(defthm run-at-kept
  (implies (and (run-at off l h) (equal (aival h2) (aival h)) (integerp (aused h2)) (<= (aused h) (aused h2)))
           (run-at off l h2)))
(defthm r-in-kept
  (implies (and (r-in rs h) (equal (aival h2) (aival h)) (integerp (aused h2)) (<= (aused h) (aused h2)))
           (r-in rs h2))
  :hints (("Goal" :in-theory (disable run-at))))
(defthm rn-fl-kept
  (implies (and (rn-fl offs head l h) (equal (aival h2) (aival h)) (integerp (aused h2)) (<= (aused h) (aused h2)))
           (rn-fl offs head l h2))
  :hints (("Goal" :in-theory (disable run-at))))

(defthm rn-inv-kept
  (implies (and (rn-inv d l fl r h) (d-kept d h h2)) (rn-inv d l fl r h2))
  :hints (("Goal" :in-theory (e/d (rn-inv) (run-at)))))

; (the later step first, so that an induction hypothesis names the state
; between)
(defthm d-kept-trans
  (implies (and (d-kept d h1 h2) (d-kept d h h1)) (d-kept d h h2)))
(defthm d-kept-refl
  (implies (integerp (aused h)) (d-kept d h h)))

; class c's batch count or a slot of its batch written: class d's batch as
; it was
(defthm c-batch-other-nrb
  (implies (and (equal x (nrb h)) (natp c) (natp d) (not (equal c d)) (< c (len x)))
           (and (equal (c-batch d (update-nth *h-nrbi* (update-nth c v x) h)) (c-batch d h))
                (equal (batch-ok d (update-nth *h-nrbi* (update-nth c v x) h)) (batch-ok d h))
                (equal (c-head d (update-nth *h-nrbi* (update-nth c v x) h)) (c-head d h))))
  :hints (("Goal" :in-theory (enable c-batch))))

(defthm c-batch-other-rb
  (implies (and (equal x (rb h)) (natp c) (<= 1 c) (natp d) (not (equal c d)) (batch-ok d h)
                (natp j) (< (rb-at c 0) j) (<= j (rb-at c *run-batch*)) (< j (len x)))
           (and (equal (c-batch d (update-nth *h-rbi* (update-nth j v x) h)) (c-batch d h))
                (equal (batch-ok d (update-nth *h-rbi* (update-nth j v x) h)) (batch-ok d h))
                (equal (c-head d (update-nth *h-rbi* (update-nth j v x) h)) (c-head d h))))
  :hints (("Goal" :in-theory (enable c-batch) :cases ((< d c)))))

(defthm rn-inv-batch-ok (implies (rn-inv c l fl r h) (batch-ok c h))
  :hints (("Goal" :in-theory (enable rn-inv))) :rule-classes :forward-chaining)

(defthm d-kept-batch-ok (implies (d-kept d h h2) (equal (batch-ok d h2) (batch-ok d h))))

(in-theory (disable d-kept))

(defmacro other (op) `(implies (and (hpgp h) (hpg-rn-ok h) (natp c) (natp d) (not (equal c d)) (batch-ok d h)) (d-kept d h ,op)))

(defthm hpg-run-new-kept (implies (and (natp l) (<= l *hb40*)) (other (mv-nth 1 (hpg-run-new c l h))))
  :hints (("Goal" :in-theory (enable hpg-run-new d-kept hpgp hpg-rn-ok))))

(defthm hpg-run-push-kept
  (implies (and (<= 1 c) (< c (len (nrb h))) (natp n) (< n *run-batch*) (< (rb-at c (+ 1 n)) (len (rb h))))
           (other (hpg-run-push c n off h)))
  :hints (("Goal" :in-theory (enable hpg-run-push d-kept))))

(defthm hpg-run-pop-kept (other (mv-nth 1 (hpg-run-pop c h)))
  :hints (("Goal" :in-theory (enable hpg-run-pop d-kept))))

; class d's batch bounds through each step, said directly
(defthm hpg-run-new-batch-ok
  (equal (batch-ok d (mv-nth 1 (hpg-run-new c l h))) (batch-ok d h))
  :hints (("Goal" :in-theory (enable hpg-run-new))))
(defthm hpg-run-push-batch-ok
  (implies (and (hpgp h) (hpg-rn-ok h) (natp c) (natp d) (not (equal c d)) (batch-ok d h)
                (<= 1 c) (< c (len (nrb h))) (natp n) (< n *run-batch*) (< (rb-at c (+ 1 n)) (len (rb h))))
           (batch-ok d (hpg-run-push c n off h)))
  :hints (("Goal" :in-theory (enable hpg-run-push))))
(defthm hpg-run-pop-batch-ok
  (implies (and (natp c) (natp d) (not (equal c d))) (equal (batch-ok d (mv-nth 1 (hpg-run-pop c h))) (batch-ok d h)))
  :hints (("Goal" :in-theory (enable hpg-run-pop))))

(in-theory (disable batch-ok))

; one step of the fill
(defthm hpg-fill-step-kept
  (implies (and (natp l) (<= l *hb40*) (<= 1 c) (< c (len (nrb h))) (equal n (nth c (nrb h))) (natp n) (< n *run-batch*)
                (< (rb-at c (+ 1 n)) (len (rb h))))
           (other (hpg-run-push c n (car (hpg-run-new c l h)) (mv-nth 1 (hpg-run-new c l h)))))
  :hints (("Goal" :in-theory (disable hpg-run-new hpg-run-push d-kept-trans hpg-run-push-kept hpg-run-new-kept)
           :use ((:instance d-kept-trans (h1 (mv-nth 1 (hpg-run-new c l h)))
                            (h2 (hpg-run-push c n (car (hpg-run-new c l h)) (mv-nth 1 (hpg-run-new c l h)))))
                 hpg-run-new-kept
                 (:instance hpg-run-push-kept (off (car (hpg-run-new c l h))) (h (mv-nth 1 (hpg-run-new c l h))))))))

(defthm hpg-runs-fill-kept (implies (and (natp l) (<= l *hb40*)) (other (hpg-runs-fill c l fuel h)))
  :hints (("Goal" :induct (hpg-runs-fill c l fuel h)
           :in-theory (e/d (hpg-runs-fill) (hpg-run-new hpg-run-push hpg-run-new-safe hpg-run-push-kept hpg-run-new-kept)))))

(defthm hpg-run-from-batch-kept (implies (and (natp l) (<= l *hb40*)) (other (mv-nth 1 (hpg-run-from-batch c l h))))
  :hints (("Goal" :in-theory (e/d (hpg-run-from-batch) (hpg-run-new hpg-run-pop d-kept-trans))
           :use ((:instance d-kept-trans (h1 (mv-nth 1 (hpg-run-pop c h))) (h2 (mv-nth 1 (hpg-run-new c l (mv-nth 1 (hpg-run-pop c h))))))
                 (:instance hpg-run-new-kept (h (mv-nth 1 (hpg-run-pop c h))))))))

(defthm hpg-run-take-c-kept (implies (and (natp l) (<= l *hb40*)) (other (mv-nth 1 (hpg-run-take-c c l batching h))))
  :hints (("Goal" :in-theory (e/d (hpg-run-take-c) (hpg-run-new hpg-runs-fill hpg-run-from-batch d-kept-trans))
           :use ((:instance d-kept-trans (h1 (hpg-runs-fill c l 64 h)) (h2 (mv-nth 1 (hpg-run-from-batch c l (hpg-runs-fill c l 64 h)))))
                 (:instance hpg-run-from-batch-kept (h (hpg-runs-fill c l 64 h)))
                 (:instance hpg-runs-fill-kept (fuel 64))
                 (:instance d-kept-batch-ok (h2 (hpg-runs-fill c l 64 h)))
                 (:instance hpg-fill-ok-instance (fuel 64))))))

; TAKING A RUN OF ONE CLASS KEEPS EVERY OTHER CLASS'S INVARIANT, with its
; own ghosts
(defthm hpg-run-take-other
  (implies (and (hpgp h) (hpg-rn-ok h) (natp n) (<= n *hb40*) (natp d) (not (equal d (hpg-size-class n 1 1)))
                (rn-inv d ld fld rd h))
           (rn-inv d ld fld rd (mv-nth 1 (hpg-run-take n batching h))))
  :hints (("Goal" :in-theory (e/d (hpg-run-take) (hpg-run-take-c rn-inv-kept hpg-run-take-c-kept))
           :use ((:instance rn-inv-kept (l ld) (fl fld) (r rd) (h2 (mv-nth 1 (hpg-run-take n batching h))))
                 (:instance hpg-run-take-c-kept (c (hpg-size-class n 1 1)) (l (hpg-class-len (hpg-size-class n 1 1) 1 1)))
                 (:instance d-kept-refl)))))

; ---- THE SWEEP'S FREE ----------------------------------------------------------------------

; a run apart from a list's runs starts at none of them
(defthm apart-all-not-member
  (implies (and (apart-all (cons off l) (runs offs l2)) (posp l) (posp l2)) (not (member off offs))))

; a link written at a word no run of the list starts at: the list as it was
(defthm rn-fl-aival-other
  (implies (and (equal x (aival h)) (natp j) (< j (len x)) (not (member j offs)))
           (equal (rn-fl offs head l (update-nth *h-aivali* (update-nth j v x) h)) (rn-fl offs head l h)))
  :hints (("Goal" :induct (rn-fl offs head l h))))
(defthm r-in-aival
  (implies (and (equal x (aival h)) (natp j) (< j (len x)))
           (equal (r-in rs (update-nth *h-aivali* (update-nth j v x) h)) (r-in rs h))))

(rn-not-read atag-not-read *h-atagi*) (rn-not-read aref-not-read *h-arefi*)
(rn-not-read voff-not-read *h-voffi*) (rn-not-read vlen-not-read *h-vleni*)

(defthm hpg-s64-chead
  (implies (and (hpgp h) (< (nfix c) (len (chead h))))
           (equal (hpg-s64 (nth c (chead h))) (nth c (chead h))))
  :hints (("Goal" :in-theory (disable hpg-s64-is) :use ((:instance hpg-s64-is (x (nth c (chead h))))
                                                       (:instance hpg-chead-elem (hpg h) (j c))))))

(defmacro freed (h)
  `(hpg-slab-free i ,h))
(defmacro free-hyps (c l)
  `(and (hpgp h) (natp i) (< i (len (nth *h-voffi* h))) (< i (len (nth *h-vleni* h)))
        (equal len (hpg-n40 (nth i (nth *h-vleni* h)))) (< 0 len) (equal off (hpg-n40 (nth i (nth *h-voffi* h))))
        (equal ,c (hpg-size-class len 1 1)) (equal ,l (hpg-class-len ,c 1 1))
        (< off (len (nth *h-atagi* h))) (< off (len (nth *h-arefi* h))) (< ,c (len (chead h)))))

; THE SWEEP'S FREE of a run apart from every run free or batched puts it on
; its class's list
(defthm hpg-slab-free-safe
  (implies (and (free-hyps c l) (rn-inv c l fl r h) (run-at off l h) (apart-all (cons off l) (rest-of fl c h)))
           (rn-inv c l (cons off fl) r (freed h)))
  :hints (("Goal" :in-theory (e/d (hpg-slab-free rn-inv c-batch batch-ok) (hpg-n40)) :do-not-induct t)))

; ...and keeps every other class's invariant, the run apart from its runs
(defthm hpg-slab-free-other
  (implies (and (free-hyps c l) (natp d) (not (equal d c)) (rn-inv d ld fld rd h) (posp l)
                (run-at off l h) (apart-all (cons off l) (runs fld ld)))
           (rn-inv d ld fld rd (freed h)))
  :hints (("Goal" :in-theory (e/d (hpg-slab-free rn-inv c-batch batch-ok) (hpg-n40)) :do-not-induct t)))
