;; lms_trace_test.clj: an uncaught error in a .lms fn, printed as the REPL
;; prints it; make check-lms greps the frame for (test/lms/proj/mix/solver.lms:13:3)
(require 'mix.solver)
(mix.solver/boom 1)
