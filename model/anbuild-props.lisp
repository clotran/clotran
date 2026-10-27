; WHAT THE ANALYZER'S NODES CARRY (model/anbuild.lisp, anbuild-proof.lisp):
; a symbol bound locally is N_LOCAL of the binding its lexical meaning is;
; a def's node its metadata's node, exactly when its name has metadata or
; it has a docstring; a fn* its own name, bound in its root block to its
; self slot; and a fn node its captures, the outer slots of the capture
; records anlocal keeps for the fn -- one for each name anl-fcaps lists,
; which anlocal-proof proves exactly the free locals the fn uses, once each.
;
; Theorems:
;   anb-an-local     a symbol bound locally: N_LOCAL of anl-lookup's slot,
;                    the binding found its lexical meaning (anl-lookup-lex)
;   anb-def-node     a def's node: kind N_DEF, i2 its init flag, slot 3 its
;                    metadata's node exactly when there is metadata or a docstring
;   anb-fn-self      the fn's own name, bound in its root block to the slot
;                    reserved there first, is found there at that slot
;                    (anl-bind-lookup-own)
;   anb-fn-caps      the captures anb-fn's node lists (anb-caps after
;                    anl-caps-of) are the capture records' outer slots, oldest
;                    first; anb-capouts-names: as many as anl-fcaps's names

(in-package "ACL2")

(include-book "anbuild-proof")
(include-book "anlocal-proof")
(include-book "anlocal-frames")

; ---- A SYMBOL'S LOCAL IS ANLOCAL'S ------------------------------------------------------------------

; a symbol bound locally: N_LOCAL of the slot anl-lookup answers, and the
; binding it found the one its lexical meaning is (anl-lookup-lex), given
; anlocal's invariant
(defthm anb-an-local
  (implies (and (equal (frf-kind x) 2) (anlsp anls) (anl-ccc b anls)
                (equal (anl-err (mv-nth 2 (anl-lookup b (frm-sid x) anls))) 0)
                (<= 0 (anl-lex b (frm-sid x) anls)))
           (and (equal (car (anb-stk (mv-nth 2 (anb-an x b anls anb))))
                       (anf-node 2 (car (anl-lookup b (frm-sid x) anls)) nil nil nil))
                (equal (mv-nth 1 (anl-lookup b (frm-sid x) anls)) (anl-lex b (frm-sid x) anls))))
  :hints (("Goal" :expand ((anb-an x b anls anb))
           :use ((:instance anl-lookup-lex (s (frm-sid x))))
           :in-theory (e/d (anb-local) (anl-lookup-lex)))))

; ---- A DEF'S METADATA -------------------------------------------------------------------------------

(defthm anf-wf-consp (implies (anf-wf x) (consp x)) :rule-classes :forward-chaining)
(defthm anb-host-meta-node
  (implies (equal (car (anb-host-meta x b anls anb)) 0)
           (and (consp (anb-stk (mv-nth 2 (anb-host-meta x b anls anb)))) (car (anb-stk (mv-nth 2 (anb-host-meta x b anls anb))))))
  :hints (("Goal" :use ((:instance anb-host-meta-push)))))

; a def's node carries its metadata's node in slot 3 when its name has
; metadata or it has a docstring (DefExpr analyses the map, the docstring
; as :doc), and nothing else there; the init its one child when it has one
(defthm anb-def-node
  (implies (and (equal (car (anb-defend x b i2 anls anb)) 0) (member i2 '(0 1)))
           (let ((nd (car (anb-stk (mv-nth 2 (anb-defend x b i2 anls anb))))))
             (and (equal (nth 2 nd) 10) (equal (nth 3 nd) i2)
                  (iff (nth 5 nd) (or (equal (frf-meta (frf-nth x 1)) 1) (not (equal (anf-def x 2) 0)))))))
  :hints (("Goal" :in-theory (enable anb-defend anb-meta anb-def anb-top))))
(defthm anl-lookup-found
  (implies (<= 0 (anl-chain-find b s anls))
           (equal (car (anl-lookup b s anls)) (anl-g-xsl (anl-chain-find b s anls) anls)))
  :hints (("Goal" :expand ((anl-lookup b s anls)))))

(defthm anl-bind-new-record
  (implies (and (anlsp anls) (signed-byte-p 64 b) (signed-byte-p 64 s) (signed-byte-p 64 k)
                (equal (anl-err anls) 0) (equal (anl-err (anl-bind b s k anls)) 0))
           (let ((n (anl-nx anls)) (a (anl-bind b s k anls)))
             (and (equal (anl-g-bhead b a) n) (equal (anl-g-xnm n a) s) (equal (anl-g-xsl n a) k)
                  (natp n) (< n (anl-nx a)))))
  :hints (("Goal" :in-theory (enable anl-bind))))

(defthm anl-bind-chain-find-own
  (implies (and (anlsp anls) (signed-byte-p 64 b) (signed-byte-p 64 s) (signed-byte-p 64 k)
                (natp b) (< b (anl-nb anls)) (equal (anl-err anls) 0) (equal (anl-err (anl-bind b s k anls)) 0))
           (equal (anl-chain-find b s (anl-bind b s k anls)) (anl-nx anls)))
  :hints (("Goal" :expand ((anl-chain-find b s (anl-bind b s k anls)) (anl-xfind (anl-nx anls) s (anl-bind b s k anls)))
           :use anl-bind-new-record :in-theory (disable anl-bind-new-record))))

; a name bound in block b is found there, at the slot it was bound to
(defthm anl-bind-lookup-own
  (implies (and (anlsp anls) (signed-byte-p 64 b) (signed-byte-p 64 s) (signed-byte-p 64 k)
                (natp b) (< b (anl-nb anls)) (equal (anl-err anls) 0) (equal (anl-err (anl-bind b s k anls)) 0))
           (equal (car (anl-lookup b s (anl-bind b s k anls))) k))
  :hints (("Goal" :use anl-bind-new-record :in-theory (disable anl-bind-new-record))))

(defthm anl-new-fn-block
  (implies (and (anlsp anls) (signed-byte-p 64 o) (equal (anl-err (mv-nth 1 (anl-new-fn o anls))) 0) (equal (anl-err anls) 0))
           (and (natp (car (anl-new-fn o anls)))
                (< (car (anl-new-fn o anls)) (anl-nb (mv-nth 1 (anl-new-fn o anls))))))
  :hints (("Goal" :in-theory (enable anl-new-fn))))
(defthm anl-reserve-nb (equal (anl-nb (mv-nth 1 (anl-reserve b n anls))) (anl-nb anls)) :hints (("Goal" :in-theory (enable anl-reserve))))
(defthm anl-reserve-err (implies (equal (anl-err (mv-nth 1 (anl-reserve b n anls))) 0) (equal (anl-err anls) 0))
  :hints (("Goal" :in-theory (enable anl-reserve))) :rule-classes :forward-chaining)
(defthm anl-bind-err (implies (equal (anl-err (anl-bind b s k anls)) 0) (equal (anl-err anls) 0))
  :hints (("Goal" :in-theory (enable anl-bind))) :rule-classes :forward-chaining)

; A FN'S OWN NAME: anb-fn binds it in the fn's root block to the slot it
; reserves there first, the self slot, so a lookup of it from the root
; finds that slot (and from each method's block, a child of the root, by
; the lexical walk anl-lookup-lex proves)
(defthm anb-fn-self
  (implies (and (anlsp anls) (signed-byte-p 64 b) (signed-byte-p 64 s) (equal (anl-err anls) 0)
                (equal (anl-err (anl-bind (car (anl-new-fn b anls)) s
                                          (car (anl-reserve (car (anl-new-fn b anls)) 1 (mv-nth 1 (anl-new-fn b anls))))
                                          (mv-nth 1 (anl-reserve (car (anl-new-fn b anls)) 1 (mv-nth 1 (anl-new-fn b anls))))))
                       0))
           (equal (car (anl-lookup (car (anl-new-fn b anls)) s
                                   (anl-bind (car (anl-new-fn b anls)) s
                                             (car (anl-reserve (car (anl-new-fn b anls)) 1 (mv-nth 1 (anl-new-fn b anls))))
                                             (mv-nth 1 (anl-reserve (car (anl-new-fn b anls)) 1 (mv-nth 1 (anl-new-fn b anls)))))))
                  (car (anl-reserve (car (anl-new-fn b anls)) 1 (mv-nth 1 (anl-new-fn b anls))))))
  :hints (("Goal" :use ((:instance anl-new-fn-block (o b))))))

; ---- A FN'S CAPTURES ----------------------------------------------------------------------------------

; the outer slots of the capture records from c, newest first: the records
; anl-capnames walks, so the same in number and order as the names anl-fcaps
; lists (anlocal-proof: exactly the free locals the fn uses, once each)
(defun anb-capouts (c anls)
  (declare (xargs :stobjs anls :measure (nfix c) :ruler-extenders :all :verify-guards nil))
  (if (and (natp c) (< c (anl-nc anls)))
      (cons (anl-g-cout c anls)
            (let ((j (anl-g-cnext c anls))) (if (and (natp j) (< j c)) (anb-capouts j anls) nil)))
    nil))

(defthm anb-capouts-names (equal (len (anb-capouts c anls)) (len (anl-capnames c anls))))

(defun anb-rev (l) (if (atom l) nil (append (anb-rev (cdr l)) (list (car l)))))

; what the read-back array ev holds from i below n
(defun anb-evs (i n anls)
  (declare (xargs :stobjs anls :measure (nfix (- (nfix n) (nfix i))) :verify-guards nil))
  (if (and (natp i) (natp n) (< i n)) (cons (anl-g-ev i anls) (anb-evs (+ 1 i) n anls)) nil))

(defthm anb-caps-evs
  (implies (and (natp i) (natp (anl-nev anls))) (equal (anb-caps i anls) (anb-rev (anb-evs i (anl-nev anls) anls)))))

(defthm anl-grow-e-room-ev (implies (natp n) (< n (anl-ev-length (anl-grow-e n anls)))) :rule-classes :linear
  :hints (("Goal" :use anl-grow-e-room :in-theory (disable anl-grow-e-room))))
(defthm anl-push-e-reads
  (and (equal (anl-nc (anl-push-e s k anls)) (anl-nc anls))
       (equal (anl-g-cout j (anl-push-e s k anls)) (anl-g-cout j anls))
       (equal (anl-g-cnext j (anl-push-e s k anls)) (anl-g-cnext j anls))
       (implies (and (natp (anl-nev anls)) (< (anl-nev anls) (- *anl40* 1)))
                (and (equal (anl-nev (anl-push-e s k anls)) (+ 1 (anl-nev anls)))
                     (equal (anl-g-ev j (anl-push-e s k anls))
                            (if (equal j (anl-nev anls)) s (if (and (integerp j) (<= 0 j) (< j (anl-nev anls))) (anl-g-ev j anls) -1))))))
  :hints (("Goal" :in-theory (enable anl-push-e))))

(defthm anb-capouts-push-e (equal (anb-capouts c (anl-push-e s k anls)) (anb-capouts c anls)))

(defthm anb-evs-push-e
  (implies (and (natp i) (natp (anl-nev anls)) (<= i (anl-nev anls)) (< (anl-nev anls) (- *anl40* 1)))
           (equal (anb-evs i (+ 1 (anl-nev anls)) (anl-push-e s k anls)) (append (anb-evs i (anl-nev anls) anls) (list s)))))

(defthm anb-append-assoc (equal (append (append a b) c) (append a (append b c))))
(defthm anb-caps-c-evs
  (implies (and (natp (anl-nev anls)) (< (+ (anl-nev anls) (len (anb-capouts c anls))) (- *anl40* 1)))
           (and (equal (anl-nev (anl-caps-c c anls)) (+ (anl-nev anls) (len (anb-capouts c anls))))
                (equal (anb-evs 0 (anl-nev (anl-caps-c c anls)) (anl-caps-c c anls))
                       (append (anb-evs 0 (anl-nev anls) anls) (anb-capouts c anls)))))
  :hints (("Goal" :induct (anl-caps-c c anls) :in-theory (disable anl-push-e))))

(defthm anb-capouts-nev (equal (anb-capouts c (update-anl-nev v anls)) (anb-capouts c anls)))
(defthm anl-capnames-nev (equal (anl-capnames c (update-anl-nev v anls)) (anl-capnames c anls)))

; THE FN'S CAPTURES IN ITS NODE: anb-fn's node lists the outer slots of its
; capture records, oldest first (scope_caps), one for each name anl-fcaps
; lists -- the free locals the fn uses (anl-lookup-caps-own, -any, -nodup)
(defthm anb-fn-caps
  (implies (< (len (anb-capouts (anl-g-fcap (anl-g-bfn b anls) anls) anls)) (- *anl40* 1))
           (equal (anb-caps 0 (anl-caps-of b anls))
                  (anb-rev (anb-capouts (anl-g-fcap (anl-g-bfn b anls) anls) anls))))
  :hints (("Goal" :in-theory (enable anl-caps-of)
           :use ((:instance anb-caps-c-evs (c (anl-g-fcap (anl-g-bfn b anls) anls)) (anls (update-anl-nev 0 anls)))))))
