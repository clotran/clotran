; THE VM RUNTIME'S FRAMES (src/f/VmRuntime.f90): rt_prim and the runtime's
; other shims that allocate, on the value stack, as model/heaprt.lisp models
; it. A book of its own: heaprt's names are not hpg's (model/vmrt.lisp).
;
; Theorems (this book):
;   vrt-prim-frame-balance  rt_prim's frame leaves the value stack as it found it
;   vrt-prim-frame-cost     n + 2 writes inside it

(in-package "ACL2")

(include-book "heaprt")

; ---- THE FRAMES: rt_prim on the value stack ----------------------------------------------
;
; rt_prim enters a frame of n+1 slots, sets slot 1 to the list and slots
; 2 .. n+1 to its elements, dispatches -- a call writing no slot of the
; frame but its own, a frame of its own inside -- and leaves to its base:
; heaprt's run, so heaprt's frame-balance gives it back the stack as found.
; rt_prim1..3, rt_cons, rt_clo, rt_list_from and vmrt_throw_of are the same
; shape: an enter, sets inside the frame, allocations, a leave.



(defun vrt-prim-sets (xs k)
  (if (atom xs) (list (list :frame 0)) (cons (list :set k (car xs)) (vrt-prim-sets (cdr xs) (+ 1 k)))))

(defun vrt-prim-frame (vals)
  (cons (+ 1 (len vals)) (cons (list :set 1 vals) (vrt-prim-sets vals 2))))

(defthm vrt-prim-frame-balance
  (implies (and (vs-ok st) (not (equal (run :frame (vrt-prim-frame vals) 0 0 st) :full)))
           (equal (run :frame (vrt-prim-frame vals) 0 0 st) st))
  :hints (("Goal" :use ((:instance frame-balance (x (vrt-prim-frame vals)))) :in-theory (disable run vrt-prim-frame))))

(defthm vrt-prim-sets-len (equal (len (vrt-prim-sets xs k)) (+ 1 (len xs))))

; and its cost: n + 2 writes, one a slot, inside its frame
(defthm vrt-prim-frame-cost
  (equal (len (cdr (vrt-prim-frame vals))) (+ 2 (len vals))))
