;; a lazy stream: a cons of a value and a memoized thunk, as a Clojure lazy-seq is
(defstruct (cell (:constructor mk (head thunk))) head thunk (val nil) (done nil))
(defun tail (c) (if (cell-done c) (cell-val c) (let ((v (funcall (cell-thunk c)))) (setf (cell-val c) v (cell-done c) t (cell-thunk c) nil) v)))
(defun from (n) (mk n (lambda () (from (1+ n)))))
(defun take-s (n s) (if (or (zerop n) (null s)) nil (mk (cell-head s) (lambda () (take-s (1- n) (tail s))))))
(defun sum-s (s) (let ((a 0)) (loop while s do (incf a (cell-head s)) (setf s (tail s))) a))
(defun bench (label f) (funcall f) (let ((t0 (get-internal-real-time)) (r (funcall f)))
  (format t "~44a ~8,1f ms  (~a)~%" label (/ (- (get-internal-real-time) t0) (/ internal-time-units-per-second 1000.0)) r)))
(bench "sum-s (take-s n (from 0))  (hand stream)" (lambda () (sum-s (take-s 1000000 (from 0)))))
