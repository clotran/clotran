; THE PRIMITIVE KINDS' COST (model/anprim.lisp), by counting: the fold one
; step an operand, its operand's kind (the host's tree read) counted where
; it runs; every other decision a fixed number of comparisons.
(in-package "ACL2")

(include-book "anprim")

; (the fold's steps do not depend on what it has folded so far)
(defun apk-fold-steps (kids sc i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n) (< n *anl40*))
      (if (member (apk-kid kids sc i) '(0 4)) 1 (+ 1 (apk-fold-steps kids sc (+ 1 i) n)))
    1))

; at most one step an operand, and one to stop
(defthm apk-fold-steps-bound
  (<= (apk-fold-steps kids sc i n) (+ 1 (nfix (- (nfix n) (nfix i))))) :rule-classes :linear)

; a Numbers op of n - 1 operands: n steps and the promoting check
(defun apk-arith-steps (kids sc n) (+ 1 (apk-fold-steps kids sc 1 n)))
(defthm apk-arith-steps-bound (<= (apk-arith-steps kids sc n) (+ 2 (nfix n))) :rule-classes :linear
  :hints (("Goal" :use ((:instance apk-fold-steps-bound (i 1))) :in-theory (disable apk-fold-steps-bound))))

; the rest: the comparisons on each one's longest path
(defun apk-own (f)
  (case f (apk-step 6) (apk-num 3) (apk-loop 2) (apk-let 5) (apk-ret 7) (apk-recur-ok 5) (apk-elem 8) (apk-cast 4) (otherwise 0)))
(defthm apk-own-bound (<= (apk-own f) 8) :rule-classes :linear)
