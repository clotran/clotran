; THE VM RUNS THE TREE (model/exec-vm.lisp with model/vmx2-proof.lisp):
; exec-vm proves a well-formed core tree's value is mx2's of its
; translation (ex-vm-agree) and the translation x2wf (ex-tr-xwf);
; vmx2-proof proves the VM's run of an x2wf program answers mx2's value
; (vcs2-correct). Together: the VM run of the translation answers the
; tree's value, or its throw (a call's head translated first, as the
; tree runs it). A book of its own so exec-cost need not carry vmx2-proof's
; arithmetic.

(in-package "ACL2")

(include-book "exec-vm")
(include-book "vmx2-proof")

; THE VM RUN OF A WELL-FORMED TREE'S TRANSLATION ANSWERS THE TREE'S VALUE OR THROW,
; the runtime's cast to IFn throwing nothing and its apply refusing what the tree's does,
; the program's defs every template's the tree can call (ex-defs-ok), its
; fns of any arities, variadic ones among them, and apply's spread call
(defthm ex-vm-runs
  (implies (and (ex-vwf :m e 0 nil nil defs) (ex-defs-ok defs defs) (ex-lzok defs) (ex-ifnok) (ex-apok) (ex-isaok) (ex-caseok) (ex-collok defs) (ex-collok defs)
                (or (valp (car (ex-ev :m e 0 nil fr fuel))) (thrownp (car (ex-ev :m e 0 nil fr fuel)))) (natp k))
           (equal (vcs2-run-program (ex-tr :m e 0 nil) defs (+ (s2clk (ex-tr :m e 0 nil) nil nil defs fuel) k))
                  (car (ex-ev :m e 0 nil fr fuel))))
  :hints (("Goal" :in-theory (disable vcs2-run-program s2clk ex-ev ex-tr ex-vwf mx2 ex-defs-ok)
                  :use ((:instance ex-vm-agree (cm nil) (env nil) (caps nil))
                        (:instance ex-tr-xwf (cm nil) (lp nil))
                        (:instance ex-defs-xdefs (ds defs))
                        (:instance vcs2-correct (e (ex-tr :m e 0 nil)))))))

; an example: (let* [y 10] ((fn [x] (if x (recur nil) y)) true)) -- a
; closure capturing y, entered, its body recurring to the fn once: the
; tree, mx2 and the VM all answer 10. The template (name arities caps
; nslots self): one arity (1 nil 0 body), the capture pair (outer 0 inner
; 1), 3 slots, the self slot 2; a node (kind i2 kids c s2 mark rstart rn)
; the checks' runtime: vmx2's prim-impl, and a call's IFn test (ex-ifn,
; prim :ifn) that a closure and apply pass -- what is callable here; and
; instance? (prim :isa) of the class :any, which every value is; and
; case*'s test (prim :case), equality; a collection the values tagged
; (prim :vector seqk's vector); a collection the values tagged
; (prim :vector seqk's vector)
(defun ex-prim-impl (op vals)
  (declare (xargs :guard t))
  (case op
    (:ifn (and (consp vals) (or (equal (car vals) :apply) (and (consp (car vals)) (eq (car (car vals)) :clo)))))
    (:isa (and (consp vals) (equal (car vals) :any)))
    (:vector (cons :vec vals))
    ((:map :set) (cons op vals))
    (:vector (cons :vec vals))
    ((:map :set) (cons op vals))
    (:case (and (consp vals) (consp (cdr vals)) (equal (car vals) (cadr vals))))
    (otherwise (prim-impl op vals))))
(local (defattach prim ex-prim-impl))
(defconst *ex-tm*
  '(f ((1 nil 0 (4 0 ((2 0 nil nil 0 nil 0 0)
                      (16 0 ((1 0 nil nil 0 nil 0 0)) nil 0 nil 0 1)
                      (2 1 nil nil 0 nil 0 0)) nil 0 nil 0 0)))
      (0 1) 3 2))
(defconst *ex-prog*
  `(11 1 ((1 0 nil 10 0 nil 0 0)
          (6 0 ((14 0 nil ,*ex-tm* 0 nil 0 0) (1 0 nil t 0 nil 0 0)) nil 0 nil 0 0))
       nil 0 nil 0 0))
; multi-arity and variadic: (fn ([x] x) ([x & r] r)), slots 0 and 1, called
; with one argument (the fixed arity wins), three (the rest a list) and
; none (no arity: the arity error)
(defconst *ex-tmv*
  '(g ((1 nil 0 (2 0 nil nil 0 nil 0 0)) (1 t 0 (2 1 nil nil 0 nil 0 0))) nil 2 nil))
(defun ex-consts (vs) (if (atom vs) nil (cons (list 1 0 nil (car vs) 0 nil 0 0) (ex-consts (cdr vs)))))
(defun ex-callg (vs) (list 6 0 (cons (list 14 0 nil *ex-tmv* 0 nil 0 0) (ex-consts vs)) nil 0 nil 0 0))
(defconst *ex-defs* (list (cons *ex-tm* (ex-def *ex-tm*)) (cons *ex-tmv* (ex-def *ex-tmv*))))
; the tree runs here with guard checking off: ex-apway reads apply's spread
; of every call's record (ex-seqp, an argument of ex-apentry), a record
; whose second value is no closure among them -- guards the logic never needs
(assert-event (ex-defs-ok *ex-defs* *ex-defs*))
(assert-event (ex-vwf :m *ex-prog* 0 nil nil *ex-defs*))
(assert-event (with-guard-checking :none (equal (car (ex-ev :m *ex-prog* 0 nil (make-list 1) 10)) '(:val . 10))))
; a call of what is no fn throws :not-fn before its arguments run
(assert-event (with-guard-checking :none (equal (car (ex-ev :m '(6 0 ((1 0 nil 3 0 nil 0 0) (17 0 ((1 0 nil 7 0 nil 0 0)) nil 0 nil 0 0)) nil 0 nil 0 0) 0 nil nil 10)) '(:thrown . :not-fn))))
(assert-event (with-guard-checking :none (equal (car (ex-ev :m (ex-callg (quote (5))) 0 nil nil 10)) '(:val . 5))))
(assert-event (with-guard-checking :none (equal (car (ex-ev :m (ex-callg (quote (5 6 7))) 0 nil nil 10)) '(:val 6 7))))
(assert-event (with-guard-checking :none (equal (car (ex-ev :m (ex-callg (quote (5))) 0 nil nil 10)) '(:val . 5))))
(assert-event (with-guard-checking :none (equal (car (ex-ev :m (ex-callg nil) 0 nil nil 10)) '(:thrown . :arity))))
(assert-event (ex-vwf :m (ex-callg (quote (5 6 7))) 0 nil nil *ex-defs*))
; mx2's lookup is assoc-equal, the VM's too: a template is its own def's
; name. vmx2's guards are not verified, so the runs on these defs are the
; logic's, evaluated by the prover
(assert-event (with-guard-checking :none (equal (mx2 (ex-tr :m *ex-prog* 0 nil) nil nil *ex-defs* 10) '(:val . 10)))) ; ex-example-mx
(assert-event (with-guard-checking :none (equal (vcs2-run-program (ex-tr :m *ex-prog* 0 nil) *ex-defs* 1000) '(:val . 10)))) ; ex-example-vm
(assert-event ; ex-example-rest
 (with-guard-checking :none (and (equal (mx2 (ex-tr :m (ex-callg (quote (5 6 7))) 0 nil) nil nil *ex-defs* 10) '(:val 6 7))
       (equal (vcs2-run-program (ex-tr :m (ex-callg (quote (5 6 7))) 0 nil) *ex-defs* 1000) '(:val 6 7)))))
; the arity error: the tree, mx2 and the VM all throw :arity
(assert-event ; ex-example-arity
 (with-guard-checking :none (and (equal (mx2 (ex-tr :m (ex-callg nil) 0 nil) nil nil *ex-defs* 10) '(:thrown . :arity))
       (equal (vcs2-run-program (ex-tr :m (ex-callg nil) 0 nil) *ex-defs* 1000) '(:thrown . :arity)))))
; letfn (milestone 5): (letfn [(h [x] (if x (h nil) 7))] (h true)) -- h's
; capture of its own slot sealed (:grp G 0) in the tree, (:const (:grp nil
; 0)) in the translation's (:mkgrp ..): the tree, mx2 and the VM all answer 7
(defconst *ex-tmlf*
  '(h ((1 nil 0 (4 0 ((2 0 nil nil 0 nil 0 0)
                      (6 0 ((2 1 nil nil 0 nil 0 0) (1 0 nil nil 0 nil 0 0)) nil 0 nil 0 0)
                      (1 0 nil 7 0 nil 0 0)) nil 0 nil 0 0)))
      (0 1) 2 nil))
(defconst *ex-lf*
  `(13 1 ((14 0 nil ,*ex-tmlf* 0 nil 0 0) (6 0 ((2 0 nil nil 0 nil 0 0) (1 0 nil t 0 nil 0 0)) nil 0 nil 0 0)) nil 0 nil 0 0))
(defconst *ex-defsl* (list (cons *ex-tmlf* (ex-def *ex-tmlf*))))
(assert-event (and (ex-defs-ok *ex-defsl* *ex-defsl*) (ex-vwf :m *ex-lf* 0 nil nil *ex-defsl*)))
(assert-event ; ex-example-letfn
 (with-guard-checking :none (and (equal (car (ex-ev :m *ex-lf* 0 nil (make-list 1) 10)) '(:val . 7))
       (equal (mx2 (ex-tr :m *ex-lf* 0 nil) nil nil *ex-defsl* 10) '(:val . 7))
       (equal (vcs2-run-program (ex-tr :m *ex-lf* 0 nil) *ex-defsl* 1000) '(:val . 7)))))
; apply (2c-iii): (apply g 5 '(6 7)) spreads to (g 5 6 7), the rest (6 7);
; (apply g nil) to (g), the arity error -- the tree, mx2 (:applyv) and the
; VM alike
(defun ex-applyg (vs l)
  (list 6 0 (list* (list 1 0 nil :apply 0 nil 0 0) (list 14 0 nil *ex-tmv* 0 nil 0 0) (ex-consts (append vs (list l))))
        nil 0 nil 0 0))
(assert-event (ex-vwf :m (ex-applyg '(5) '(6 7)) 0 nil nil *ex-defs*))
(assert-event (with-guard-checking :none (equal (car (ex-ev :m (ex-applyg '(5) '(6 7)) 0 nil nil 10)) '(:val 6 7))))
(assert-event (with-guard-checking :none (equal (car (ex-ev :m (ex-applyg nil nil) 0 nil nil 10)) '(:thrown . :arity))))
(assert-event ; ex-example-apply
 (with-guard-checking :none (and (equal (mx2 (ex-tr :m (ex-applyg '(5) '(6 7)) 0 nil) nil nil *ex-defs* 10) '(:val 6 7))
       (equal (vcs2-run-program (ex-tr :m (ex-applyg '(5) '(6 7)) 0 nil) *ex-defs* 1000) '(:val 6 7))
       (equal (mx2 (ex-tr :m (ex-applyg nil nil) 0 nil) nil nil *ex-defs* 10) '(:thrown . :arity))
       (equal (vcs2-run-program (ex-tr :m (ex-applyg nil nil) 0 nil) *ex-defs* 1000) '(:thrown . :arity)))))
; over a vector (2c-iv): (apply g 5 [6 7]) hands g the vector -- the
; translation the same call, :applyv's spread seqk's (x2-vals) -- the rest
; the vector's view from 0, the vector [6 7] (2c-vi: nothing read past
; req + 1), in the tree, mx2 and the VM alike
(assert-event (ex-vwf :m (ex-applyg '(5) '(:vec 6 7)) 0 nil nil *ex-defs*))
(assert-event (with-guard-checking :none (equal (car (ex-ev :m (ex-applyg '(5) '(:vec 6 7)) 0 nil nil 10)) '(:val :vec 6 7))))
(assert-event ; ex-example-apply-vector
 (with-guard-checking :none (and (equal (mx2 (ex-tr :m (ex-applyg '(5) '(:vec 6 7)) 0 nil) nil nil *ex-defs* 10) '(:val :vec 6 7))
       (equal (vcs2-run-program (ex-tr :m (ex-applyg '(5) '(:vec 6 7)) 0 nil) *ex-defs* 1000) '(:val :vec 6 7)))))

; a variadic fn handed apply's seq reads it only through req + 1 (2c-vi,
; RestFn.applyTo): clj's (apply (fn [& xs] (first xs)) (range)) is 0 -- here
; (apply (fn [& xs] xs) (range)) answers the seq handed over, its first 0,
; where before the infinite seq made the call the host's; (apply (fn [a &
; r] a) (range)) is 0, the walk realising 3 cells as clj's counting seq
; does; the tree, mx2 and the VM alike (range attached as seqk's sk-real
; by vmx2's checks)
(defconst *ex-tmh* '(h ((0 t 0 (2 0 nil nil 0 nil 0 0))) nil 1 nil))
(defconst *ex-tma* '(a ((1 t 0 (2 0 nil nil 0 nil 0 0))) nil 2 nil))
(defconst *ex-defsh* (list (cons *ex-tmh* (ex-def *ex-tmh*)) (cons *ex-tma* (ex-def *ex-tma*))))
(defun ex-applyt (tm l)
  (list 6 0 (list (list 1 0 nil :apply 0 nil 0 0) (list 14 0 nil tm 0 nil 0 0) (list 1 0 nil l 0 nil 0 0)) nil 0 nil 0 0))
(assert-event (ex-defs-ok *ex-defsh* *ex-defsh*))
(assert-event (ex-vwf :m (ex-applyt *ex-tmh* '(:lazy . 0)) 0 nil nil *ex-defsh*))
(assert-event (ex-vwf :m (ex-applyt *ex-tma* '(:lazy . 0)) 0 nil nil *ex-defsh*))
(assert-event (with-guard-checking :none (equal (car (ex-ev :m (ex-applyt *ex-tmh* '(:lazy . 0)) 0 nil nil 10)) '(:val :cons 0 :lazy . 1))))
(assert-event (equal (sk-first (sk-cur '(:cons 0 :lazy . 1))) 0))
(assert-event (with-guard-checking :none (equal (car (ex-ev :m (ex-applyt *ex-tma* '(:lazy . 0)) 0 nil nil 10)) '(:val . 0))))
(assert-event (equal (nth 4 (ex-apwalk (ex-varnf (nth 1 *ex-tma*)) nil (sk-cur '(:lazy . 0)))) 3))
; sk-real is constrained, its attachment (vmx2's range) run, not proved from: these are
; evaluated, as vmx2's checks are
(assert-event
 (with-guard-checking :none
  (and (equal (mx2 (ex-tr :m (ex-applyt *ex-tmh* '(:lazy . 0)) 0 nil) nil nil *ex-defsh* 10) '(:val :cons 0 :lazy . 1))
       (equal (vcs2-run-program (ex-tr :m (ex-applyt *ex-tmh* '(:lazy . 0)) 0 nil) *ex-defsh* 1000) '(:val :cons 0 :lazy . 1))
       (equal (mx2 (ex-tr :m (ex-applyt *ex-tma* '(:lazy . 0)) 0 nil) nil nil *ex-defsh* 10) '(:val . 0))
       (equal (vcs2-run-program (ex-tr :m (ex-applyt *ex-tma* '(:lazy . 0)) 0 nil) *ex-defsh* 1000) '(:val . 0)))))

; try (exec-PLAN 3b): (try (throw 7) (catch C x x) (finally 3)) -- of the
; class :any the catch takes the throw, 7; of :none it throws 7 on, the
; finally run either way; without the finally the same -- the tree, mx2
; (:try over the catch walk, the finally desugared) and the VM alike
(defun ex-tryg (cls fin)
  (list 18 0 (append (list (list 17 0 (list (list 1 0 nil 7 0 nil 0 0)) nil 0 nil 0 0))
                     (if fin (list (list 1 0 nil 3 0 nil 0 0)) nil))
        (list (list cls 0 '(2 0 nil nil 0 nil 0 0))) 0 nil 0 0))
(assert-event (and (ex-vwf :m (ex-tryg :any t) 0 nil nil *ex-defs*) (ex-vwf :m (ex-tryg :none nil) 0 nil nil *ex-defs*)))
(assert-event ; ex-example-try
 (with-guard-checking :none
  (and (equal (car (ex-ev :m (ex-tryg :any t) 0 nil (make-list 1) 10)) '(:val . 7))
       (equal (mx2 (ex-tr :m (ex-tryg :any t) 0 nil) nil nil *ex-defs* 10) '(:val . 7))
       (equal (vcs2-run-program (ex-tr :m (ex-tryg :any t) 0 nil) *ex-defs* 1000) '(:val . 7))
       (equal (car (ex-ev :m (ex-tryg :none t) 0 nil (make-list 1) 10)) '(:thrown . 7))
       (equal (mx2 (ex-tr :m (ex-tryg :none t) 0 nil) nil nil *ex-defs* 10) '(:thrown . 7))
       (equal (vcs2-run-program (ex-tr :m (ex-tryg :none t) 0 nil) *ex-defs* 1000) '(:thrown . 7))
       (equal (car (ex-ev :m (ex-tryg :any nil) 0 nil (make-list 1) 10)) '(:val . 7))
       (equal (vcs2-run-program (ex-tr :m (ex-tryg :any nil) 0 nil) *ex-defs* 1000) '(:val . 7)))))

; case* (exec-PLAN 3b): (case x 1 10 2 20 30) -- 2 takes the second entry,
; 20; 5 none, the default 30 -- the tree, mx2 (the table's walk over prim
; :case) and the VM alike, the checks' case test value equality
(defun ex-caseg (x)
  (list 19 0 (list (list 1 0 nil x 0 nil 0 0) '(1 0 nil 30 0 nil 0 0))
        '((1 (1 0 nil 10 0 nil 0 0)) (2 (1 0 nil 20 0 nil 0 0))) 0 nil 0 0))
(assert-event (ex-vwf :m (ex-caseg 2) 0 nil nil *ex-defs*))
(assert-event ; ex-example-case
 (with-guard-checking :none
  (and (equal (car (ex-ev :m (ex-caseg 2) 0 nil nil 10)) '(:val . 20))
       (equal (mx2 (ex-tr :m (ex-caseg 2) 0 nil) nil nil *ex-defs* 10) '(:val . 20))
       (equal (vcs2-run-program (ex-tr :m (ex-caseg 2) 0 nil) *ex-defs* 1000) '(:val . 20))
       (equal (car (ex-ev :m (ex-caseg 5) 0 nil nil 10)) '(:val . 30))
       (equal (mx2 (ex-tr :m (ex-caseg 5) 0 nil) nil nil *ex-defs* 10) '(:val . 30))
       (equal (vcs2-run-program (ex-tr :m (ex-caseg 5) 0 nil) *ex-defs* 1000) '(:val . 30)))))

; collections (exec-PLAN 3b): (apply g 5 [6 7]) with the vector a literal
; -- its elements run, the vector seqk's (:vec 6 7) -- and #{1 2}, the
; runtime's set: the tree, mx2 (:prim :vector, :set) and the VM alike
(defun ex-applyv (vs)
  (list 6 0 (list (list 1 0 nil :apply 0 nil 0 0) (list 14 0 nil *ex-tmv* 0 nil 0 0) '(1 0 nil 5 0 nil 0 0)
                  (list 7 0 (ex-consts vs) nil 0 nil 0 0))
        nil 0 nil 0 0))
(defconst *ex-set* (list 9 0 (ex-consts '(1 2)) nil 0 nil 0 0))
(assert-event (and (ex-vwf :m (ex-applyv '(6 7)) 0 nil nil *ex-defs*) (ex-vwf :m *ex-set* 0 nil nil *ex-defs*)))
(assert-event ; ex-example-coll
 (with-guard-checking :none
  (and (equal (car (ex-ev :m (ex-applyv '(6 7)) 0 nil nil 10)) '(:val :vec 6 7))
       (equal (mx2 (ex-tr :m (ex-applyv '(6 7)) 0 nil) nil nil *ex-defs* 10) '(:val :vec 6 7))
       (equal (vcs2-run-program (ex-tr :m (ex-applyv '(6 7)) 0 nil) *ex-defs* 1000) '(:val :vec 6 7))
       (equal (car (ex-ev :m *ex-set* 0 nil nil 10)) '(:val :set 1 2))
       (equal (mx2 (ex-tr :m *ex-set* 0 nil) nil nil *ex-defs* 10) '(:val :set 1 2))
       (equal (vcs2-run-program (ex-tr :m *ex-set* 0 nil) *ex-defs* 1000) '(:val :set 1 2)))))

; collections (exec-PLAN 3b): (apply g 5 [6 7]) with the vector a literal
; -- its elements run, the vector seqk's (:vec 6 7) -- and #{1 2}, the
; runtime's set: the tree, mx2 (:prim :vector, :set) and the VM alike
(defun ex-applyv (vs)
  (list 6 0 (list (list 1 0 nil :apply 0 nil 0 0) (list 14 0 nil *ex-tmv* 0 nil 0 0) '(1 0 nil 5 0 nil 0 0)
                  (list 7 0 (ex-consts vs) nil 0 nil 0 0))
        nil 0 nil 0 0))
(defconst *ex-set* (list 9 0 (ex-consts '(1 2)) nil 0 nil 0 0))
(assert-event (and (ex-vwf :m (ex-applyv '(6 7)) 0 nil nil *ex-defs*) (ex-vwf :m *ex-set* 0 nil nil *ex-defs*)))
(assert-event ; ex-example-coll
 (with-guard-checking :none
  (and (equal (car (ex-ev :m (ex-applyv '(6 7)) 0 nil nil 10)) '(:val :vec 6 7))
       (equal (mx2 (ex-tr :m (ex-applyv '(6 7)) 0 nil) nil nil *ex-defs* 10) '(:val :vec 6 7))
       (equal (vcs2-run-program (ex-tr :m (ex-applyv '(6 7)) 0 nil) *ex-defs* 1000) '(:val :vec 6 7))
       (equal (car (ex-ev :m *ex-set* 0 nil nil 10)) '(:val :set 1 2))
       (equal (mx2 (ex-tr :m *ex-set* 0 nil) nil nil *ex-defs* 10) '(:val :set 1 2))
       (equal (vcs2-run-program (ex-tr :m *ex-set* 0 nil) *ex-defs* 1000) '(:val :set 1 2)))))
