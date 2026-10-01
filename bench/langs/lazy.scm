;; a lazy stream with R7RS delay/force: memoized, a promise per element
(import (scheme base) (scheme time) (chicken format))
(define (from n) (cons n (delay (from (+ n 1)))))
(define (take-s n s) (if (or (= n 0) (null? s)) '() (cons (car s) (delay (take-s (- n 1) (force (cdr s)))))))
(define (sum-s s) (let loop ((s s) (a 0)) (if (null? s) a (loop (force (cdr s)) (+ a (car s))))))
(define (bench label f) (f) (let* ((t0 (current-jiffy)) (r (f)))
  (printf "~a ~a ms  (~a)~%" label (/ (* 1000.0 (- (current-jiffy) t0)) (jiffies-per-second)) r)))
(bench "sum-s (take-s n (from 0))  (hand stream)          " (lambda () (sum-s (take-s 1000000 (from 0)))))
