;; An overflow caught outside a binding: the binding's finally runs as it
;; unwinds, its own calls in the reserve, so the var is unbound again
;; (review of stack_low, 2026-10-12). make check-overflow-binding runs it
;; with a small value stack: every level allocates its binding frame, and
;; at the default depth one run peaks near 2.5 GB, which the Linux gate
;; killed for memory. Not a fuzz regression: clj's finally can overflow
;; too and leave the binding in place ([:so 0] once on Linux, 2026-10-17),
;; so clj cannot judge it.
(prn (let [f (fn f [n] (binding [*print-length* n] (f (inc n))))]
       [(try (f 0) (catch clotran.host.stack_overflow_error e :so)) *print-length*]))
