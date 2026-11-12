; A FN BODY'S CLEARING CONDITION FROM THE TAIL CHECK AND HAS_FN_RECUR
; (exec-PLAN milestone 4, second part): exec-vmtr's ex-arwf asks of a fn
; body either that it clears nothing of its captures or self slot, or that
; it is well formed with no loop target -- no recur to the fn. Both from
; what the analyzer checks of the body (model/anpass.lisp, on exec.lisp's
; node as exec-clrmap's ex-ast reads it):
;
;   ex-vwf-nolp   a body well formed with the fn's loop target lp, whose
;                 tail check at the fn's tail position (anp-tc at tt 1)
;                 passed and with no recur to the fn (anp-hfr nil), is well
;                 formed with none: a recur in the fn's tail has rfn
;                 nonzero, so has_fn_recur sees it
;   ex-arwf-body  so ex-arwf's last condition: when has_fn_recur holds,
;                 apply_clears marks nothing (anpass-proof's
;                 anp-clears-spec), so the body clears nothing
;
; anp-tc and anp-hfr stay closed: the node's case is opened once per kind
; (ex-ntm-*).

(in-package "ACL2")

(include-book "exec-clrlv")
(include-book "anpass-sound")

; the fn's tail position under a node holds no recur to the fn
(defun ex-ntm (e) (and (equal (anp-tc 0 (ex-ast e) 0 0 1) 0) (not (anp-hfr 0 (ex-ast e) 0 0))))

(defmacro ex-ntct (e i) `(and (equal (anp-tc 3 (ex-ast ,e) ,i (len (ex-c ,e)) 1) 0) (not (anp-hfr 3 (ex-ast ,e) ,i (len (ex-c ,e))))))

; ... under the tail places of a piece ex-vwf passes the loop target to
(defun ex-ntl (flg e i)
  (case flg
    (:do (if (zp (ex-nk e)) t (ex-ntm (ex-kid-of e (1- (ex-nk e))))))
    (:let (if (equal (ex-kind e) 11) (ex-ntm (ex-kid-of e (ex-i2 e))) t))
    (:ct (ex-ntct e i))
    (:rec nil)
    ((:call :coll :cs :fin) t)
    (otherwise (ex-ntm e))))

(in-theory (disable anp-tc anp-hfr tc-0-open hfr-0-open ex-ntm ex-kid-of))

; ---- THE NODE, ONE KIND AT A TIME ---------------------------------------------------------------

(defthm ex-ntm-if
  (implies (and (ex-nodep e) (equal (ex-kind e) 4) (ex-ntm e))
           (and (ex-ntm (ex-kid-of e 1)) (ex-ntm (ex-kid-of e 2))))
  :hints (("Goal" :in-theory (enable ex-ntm) :expand ((anp-tc 0 (ex-ast e) 0 0 1) (anp-hfr 0 (ex-ast e) 0 0))
           :use ((:instance hfr-kid (x (ex-ast e)) (i 1)) (:instance hfr-kid (x (ex-ast e)) (i 2))))))

(defthm ex-ntm-do
  (implies (and (ex-nodep e) (member (ex-kind e) '(5 11)) (ex-ntm e) (< 0 (ex-nk e)))
           (ex-ntm (ex-kid-of e (1- (ex-nk e)))))
  :hints (("Goal" :in-theory (enable ex-ntm) :expand ((anp-tc 0 (ex-ast e) 0 0 1) (anp-hfr 0 (ex-ast e) 0 0))
           :use ((:instance hfr-kid (x (ex-ast e)) (i (1- (ex-nk e))))))))

(defthm ex-ntm-recur
  (implies (and (ex-nodep e) (equal (ex-kind e) 16)) (not (ex-ntm e)))
  :hints (("Goal" :in-theory (enable ex-ntm ast-rfn ast-p) :expand ((anp-tc 0 (ex-ast e) 0 0 1) (anp-hfr 0 (ex-ast e) 0 0)))))

(defthm ex-ntm-case
  (implies (and (ex-nodep e) (equal (ex-kind e) 19) (ex-ntm e))
           (and (ex-ntm (ex-kid-of e 1)) (ex-ntct e 0)))
  :hints (("Goal" :in-theory (enable ex-ntm) :expand ((anp-tc 0 (ex-ast e) 0 0 1) (anp-hfr 0 (ex-ast e) 0 0))
           :use ((:instance hfr-kid (x (ex-ast e)) (i 1))))))

(defthm ex-ntl-ct
  (implies (and (ex-nodep e) (equal (ex-kind e) 19) (natp i) (< i (len (ex-c e))) (ex-ntct e i))
           (and (ex-ntm (ex-cthen e i)) (ex-ntct e (1+ i))))
  :hints (("Goal" :use ((:instance tc-seq-open (fl 3) (x (ex-ast e)) (j i) (m (len (ex-c e))) (tt 1))
                        (:instance hfr-seq-open (fl 3) (x (ex-ast e)) (j i) (m (len (ex-c e)))))
           :in-theory (e/d (ex-ntm) (tc-seq-open hfr-seq-open)))))


(defthm ex-ntm-let
  (implies (and (ex-nodep e) (equal (ex-kind e) 11) (ex-ntm e) (equal (ex-nk e) (1+ (ex-i2 e))))
           (ex-ntm (ex-kid-of e (ex-i2 e))))
  :hints (("Goal" :in-theory (disable ex-ntm-do) :use ex-ntm-do)))

; a letfn's body is in its tail, its fns in none
(defthm ex-ntm-letfn
  (implies (and (ex-nodep e) (equal (ex-kind e) 13) (ex-ntm e) (equal (ex-nk e) (1+ (ex-i2 e))))
           (ex-ntm (ex-kid-of e (ex-i2 e))))
  :hints (("Goal" :in-theory (enable ex-ntm anp-nn) :expand ((anp-tc 0 (ex-ast e) 0 0 1) (anp-hfr 0 (ex-ast e) 0 0))
           :use ((:instance hfr-kid (x (ex-ast e)) (i (ex-i2 e)))))))

; a call's, collection's or try's parts and a loop's inits and body take
; no loop target from outside
(defthm ex-vwf-lpfree
  (implies (and (syntaxp (not (equal lp ''nil)))
                (or (member flg '(:call :coll :cs)) (and (equal flg :let) (equal (ex-kind e) 12))))
           (equal (ex-vwf flg e i cm lp defs) (ex-vwf flg e i cm nil defs)))
  :hints (("Goal" :induct (ex-vwf flg e i cm lp defs)
           :in-theory (disable (:definition ex-vwf) ex-clr ex-astf ex-ast-open)
           :expand ((:free (flg cm lp) (ex-vwf flg e i cm lp defs))))))

; ex-vwf walks a letfn's body, not its fns, so no let's walk of one
(defthm ex-vwf-let-13 (implies (equal (ex-kind e) 13) (not (ex-vwf :let e i cm lp defs)))
  :hints (("Goal" :expand ((ex-vwf :let e i cm lp defs)))))

; ---- NO LOOP TARGET NEEDED ----------------------------------------------------------------------

(defthm ex-vwf-nolp
  (implies (and (ex-shp flg e i) (natp i) (ex-vwf flg e i cm lp defs) (ex-ntl flg e i))
           (ex-vwf flg e i cm nil defs))
  :hints (("Goal" :induct (ex-vwf flg e i cm lp defs)
           :in-theory (disable (:definition ex-vwf) ex-kid-of ex-clr ex-astf ex-ast-open)
           :expand ((:free (flg cm lp) (ex-vwf flg e i cm lp defs)) (:free (flg) (ex-shp flg e i)))))
  :rule-classes nil)

(defthm ex-nomem-atom (implies (atom ls) (ex-nomem ls cm)))

; ex-arwf's fn-body condition: the analyzer's tail check passed in the fn's
; tail, and the body's marks apply_clears' -- none when it recurs to the fn
(defthm ex-arwf-body
  (implies (and (ex-shp :m (ex-abody ar) 0)
                (ex-vwf :m (ex-abody ar) 0 (ex-fcmb tm ar) (ex-flp ar) defs)
                (equal (anp-tc 0 (ex-ast (ex-abody ar)) 0 0 1) 0)
                (implies (anp-hfr 0 (ex-ast (ex-abody ar)) 0 0) (atom (ex-clr :m (ex-abody ar) 0))))
           (or (ex-nomem (ex-clr :m (ex-abody ar) 0) (ex-fcm tm ar))
               (ex-vwf :m (ex-abody ar) 0 (ex-fcmb tm ar) nil defs)))
  :hints (("Goal" :in-theory (e/d (ex-ntm) (ex-vwf ex-clr ex-fcm ex-fcmb ex-flp))
           :use ((:instance ex-vwf-nolp (flg :m) (e (ex-abody ar)) (i 0) (cm (ex-fcmb tm ar)) (lp (ex-flp ar)))))))
