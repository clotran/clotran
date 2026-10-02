; clotran's string index, formally (PLAN step 28).
;
; A string is UTF-8 bytes in the pool, indexed by CODE POINT (DEVIATIONS
; 41). Character i starts at the i-th LEAD byte -- any byte that is not
; 10xxxxxx. GC.f90 used to find it by walking the bytes from the start
; (u8_off, O(n)); str_index now records, when the text is made, how many
; characters it holds and the byte where every 32nd starts, and
; str_byte goes to the mark at or before i and walks the rest.
;
; This book proves the index answers what the walk from the start did,
; for every i, and that what it walks is at most 31 characters: with
; the count a field, count is O(1) and nth, get and a slice's ends
; O(1), as clj's charAt is (test/bigo.edn).
;
; Bytes are a list of naturals; positions are 0-based here (the Fortran
; adds one).

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

; a byte that starts a character: not 10xxxxxx (GC.f90 u8_lead)
(defun lead-p (b) (or (< (nfix b) 128) (<= 192 (nfix b))))

; the position of the i-th lead byte of bs, counting positions from p;
; p + (len bs) when there are fewer -- u8_off, the walk from the start
(defun nth-lead (bs i p)
  (cond ((endp bs) (+ (nfix p) (len bs)))
        ((lead-p (car bs))
         (if (zp i) (nfix p) (nth-lead (cdr bs) (1- i) (1+ (nfix p)))))
        (t (nth-lead (cdr bs) i (1+ (nfix p))))))

; how many lead bytes: u8_count, which str_index stores as ncp
(defun leads (bs)
  (cond ((endp bs) 0)
        ((lead-p (car bs)) (1+ (leads (cdr bs))))
        (t (leads (cdr bs)))))

; ---- skipping ahead -------------------------------------------------
;
; Going to lead a, then b leads further on from there, is going to lead
; a + b: what lets a walk start at a mark instead of at the start.

(defthm nth-lead-at-least-p
  (<= (nfix p) (nth-lead bs i p))
  :rule-classes :linear)

(defthm nth-lead-shift-general
  (implies (and (natp p) (natp q))
           (equal (nth-lead bs i (+ p q)) (+ p (nth-lead bs i q))))
  :hints (("Goal" :induct (nth-lead bs i q))))

(defthm nth-lead-shift
  (implies (natp p)
           (equal (nth-lead bs i p) (+ p (nth-lead bs i 0))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance nth-lead-shift-general (p p) (q 0)))
                  :in-theory (disable nth-lead-shift-general))))

(defun skip-induct (bs a p)
  (cond ((endp bs) (list bs a p))
        ((lead-p (car bs))
         (if (zp a) (list bs a p) (skip-induct (cdr bs) (1- a) (1+ p))))
        (t (skip-induct (cdr bs) a (1+ p)))))

(defthm nth-lead-skip-general
  (implies (and (natp a) (natp b) (natp p) (< a (leads bs)))
           (equal (nth-lead bs (+ a b) p)
                  (let ((m (nth-lead bs a p)))
                    (nth-lead (nthcdr (- m p) bs) b m))))
  :hints (("Goal" :induct (skip-induct bs a p)
                  :in-theory (disable nth-lead-shift-general))))

(defthm nth-lead-skip
  (implies (and (natp a) (natp b) (< a (leads bs)))
           (equal (nth-lead bs (+ a b) 0)
                  (let ((m (nth-lead bs a 0)))
                    (+ m (nth-lead (nthcdr m bs) b 0)))))
  :hints (("Goal" :use ((:instance nth-lead-skip-general (p 0))
                        (:instance nth-lead-shift (bs (nthcdr (nth-lead bs a 0) bs)) (i b) (p (nth-lead bs a 0))))
                  :in-theory (disable nth-lead-skip-general))))

; ---- the index --------------------------------------------------------
;
; mark q: where character 32q starts, as str_index records it
(defun mark (bs q) (nth-lead bs (* 32 q) 0))

; str_byte: from the mark at or before i, (mod i 32) leads on
(defun str-byte (bs i)
  (let ((m (mark bs (floor i 32))))
    (+ m (nth-lead (nthcdr m bs) (mod i 32) 0))))

; THE INDEX IS THE WALK: for every character, str_byte finds the byte
; u8_off's walk from the start did.
(defthm str-byte-is-walk
  (implies (and (natp i) (< i (leads bs)))
           (equal (str-byte bs i) (nth-lead bs i 0)))
  :hints (("Goal" :use ((:instance nth-lead-skip (a (* 32 (floor i 32))) (b (mod i 32)))
                        (:instance floor-mod-elim (x i) (y 32)))
                  :in-theory (disable nth-lead-skip nth-lead-shift-general))))

; ---- cost ---------------------------------------------------------------
;
; characters walked past the mark: (mod i 32), at most 31, whatever the
; length -- O(1)
(defun walk-chars (i) (mod (nfix i) 32))

(defthm walk-at-most-31
  (<= (walk-chars i) 31)
  :rule-classes :linear)

; and the marks str_index keeps: one per 32 characters
(defun marks-kept (n) (if (zp n) 0 (1+ (floor (1- n) 32))))

(defthm marks-kept-bound
  (implies (natp n) (<= (marks-kept n) (1+ (/ n 32))))
  :rule-classes :linear)
