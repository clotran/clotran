; The REPL's line editor, formally (src/clj/clotran/lineedit.cljf).
;
; The editor is a state machine over the input -- a list of characters
; and a cursor -- and the history. Every key is a function of that
; state; the terminal only shows it. This book proves what the editor
; promises:
;
;   - the cursor stays within the text, whatever keys come
;   - an edit changes only what it says: an insert keeps the text before
;     and after the cursor, a deletion takes out exactly its span
;   - leaving the draft for the history and coming back gives the draft
;     back, however far back one went
;   - completion inserts a candidate's suffix: the word before the cursor
;     becomes the candidate, or the candidates' common prefix, which is a
;     prefix of every one
;   - COST: each key does at most 3n + m + 3 steps for an input of n
;     characters and an insert of m -- linear in the input, nothing
;     quadratic hides in a key
;
; The Clojure is the same functions over a vector: insert, cut,
; delete-back, delete-forward, move, line-start, line-end, kill-to-end,
; kill-to-start, word-left, word-right, history-back, history-forward,
; complete-with, common-prefix. The host part (src/c/tty_shim.c: raw mode,
; the bytes typed, the width) is the OS's and is not modelled; it holds
; no state the editor decides on.

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

; ---- lists ------------------------------------------------------------------

(defun lfix (l) (if (atom l) nil (cons (car l) (lfix (cdr l)))))

(defthm len-lfix (equal (len (lfix l)) (len l)))
(defthm true-listp-lfix (true-listp (lfix l)))
(defthm lfix-true-list (implies (true-listp l) (equal (lfix l) l)))
(defthm len-append (equal (len (append a b)) (+ (len a) (len b))))

(defthm len-take-le
  (implies (and (natp n) (<= n (len l))) (equal (len (take n l)) n)))

(defthm len-nthcdr-le
  (implies (and (natp n) (<= n (len l))) (equal (len (nthcdr n l)) (- (len l) n))))

(defthm take-append-first
  (implies (equal n (len a)) (equal (take n (append a b)) (lfix a))))

(defthm nthcdr-append-first
  (implies (equal n (len a)) (equal (nthcdr n (append a b)) b)))

(defun nth-ind (n a) (if (or (zp n) (atom a)) (list n a) (nth-ind (1- n) (cdr a))))

(defthm nthcdr-append-past
  (implies (and (natp n) (<= (len a) n))
           (equal (nthcdr n (append a b)) (nthcdr (- n (len a)) b)))
  :hints (("Goal" :induct (nth-ind n a))))

(defthm take-append-within
  (implies (and (natp n) (<= n (len a)))
           (equal (take n (append a b)) (take n a)))
  :hints (("Goal" :induct (nth-ind n a))))

(defthm take-of-take
  (implies (and (natp n) (<= n (len l))) (equal (take n (take n l)) (take n l))))

(defthm append-take-nthcdr
  (implies (and (natp n) (<= n (len l)) (true-listp l))
           (equal (append (take n l) (nthcdr n l)) l)))

(defthm true-listp-take (true-listp (take n l)))

(defthm true-listp-nthcdr (implies (true-listp l) (true-listp (nthcdr n l))))

(defthm append-assoc
  (equal (append (append a b) c) (append a (append b c))))

; ---- the state ----------------------------------------------------------------
;
; (buf pos hist hidx draft): the input's characters, the cursor, the
; history (oldest first), the entry shown (hidx = (len hist): the draft),
; and the draft as it was left.

(defun le (buf pos hist hidx draft) (list buf pos hist hidx draft))
(defun le-buf (st) (nth 0 st))
(defun le-pos (st) (nth 1 st))
(defun le-hist (st) (nth 2 st))
(defun le-hidx (st) (nth 3 st))
(defun le-draft (st) (nth 4 st))

(defun character-listp-list (l)
  (if (atom l) (null l) (and (character-listp (car l)) (character-listp-list (cdr l)))))

(defun le-ok (st)
  (and (true-listp (le-buf st))
       (natp (le-pos st))
       (<= (le-pos st) (len (le-buf st)))
       (true-listp (le-hist st))
       (natp (le-hidx st))
       (<= (le-hidx st) (len (le-hist st)))
       (character-listp-list (le-hist st))
       (true-listp (le-draft st))))

; ---- the edits --------------------------------------------------------------------

(defun clamp (buf p) (max 0 (min (len buf) (ifix p))))

(defun le-insert (st cs)
  (let ((buf (le-buf st)) (pos (le-pos st)))
    (le (append (take pos buf) (append (lfix cs) (nthcdr pos buf))) (+ pos (len cs))
        (le-hist st) (le-hidx st) (le-draft st))))

; the characters from a to b taken out, the cursor at a
(defun le-cut (st a b)
  (let ((buf (le-buf st)))
    (le (append (take a buf) (nthcdr b buf)) a (le-hist st) (le-hidx st) (le-draft st))))

(defun le-move (st p)
  (le (le-buf st) (clamp (le-buf st) p) (le-hist st) (le-hidx st) (le-draft st)))

(defun le-delete-back (st)
  (if (zp (le-pos st)) st (le-cut st (1- (le-pos st)) (le-pos st))))

(defun le-delete-forward (st)
  (if (< (le-pos st) (len (le-buf st))) (le-cut st (le-pos st) (1+ (le-pos st))) st))

; the line's start: back to just after a newline
(defun line-start (buf p)
  (declare (xargs :measure (nfix p)))
  (if (or (zp p) (equal (nth (1- p) buf) #\Newline)) (nfix p) (line-start buf (1- p))))

; its end: on to the next newline
(defun line-end (buf p)
  (declare (xargs :measure (nfix (- (len buf) (nfix p)))))
  (if (or (not (natp p)) (>= p (len buf)) (equal (nth p buf) #\Newline)) (nfix p) (line-end buf (1+ p))))

(defthm line-start-le (<= (line-start buf p) (nfix p)) :rule-classes :linear)
(defthm line-start-natp (natp (line-start buf p)) :rule-classes :type-prescription)
(defthm line-end-ge (implies (natp p) (<= p (line-end buf p))) :rule-classes :linear)
(defthm line-end-le (implies (and (natp p) (<= p (len buf))) (<= (line-end buf p) (len buf))) :rule-classes :linear)

(defun le-kill-to-end (st)
  (let* ((buf (le-buf st)) (pos (le-pos st)) (e (line-end buf pos)))
    (le-cut st pos (if (and (equal e pos) (< e (len buf))) (1+ e) e))))

(defun le-kill-to-start (st)
  (le-cut st (line-start (le-buf st) (le-pos st)) (le-pos st)))

; what a word is made of: not space, not a delimiter (lineedit's word-char?)
(defun word-char-p (c)
  (not (member c '(#\Space #\Tab #\Newline #\Return #\Page #\( #\) #\[ #\] #\{ #\} #\" #\' #\, #\; #\@ #\^ #\` #\~))))

(defun skip-back (buf p word)
  (declare (xargs :measure (nfix p)))
  (if (or (zp p) (not (iff (word-char-p (nth (1- p) buf)) word))) (nfix p) (skip-back buf (1- p) word)))

(defun skip-fwd (buf p word)
  (declare (xargs :measure (nfix (- (len buf) (nfix p)))))
  (if (or (not (natp p)) (>= p (len buf)) (not (iff (word-char-p (nth p buf)) word))) (nfix p) (skip-fwd buf (1+ p) word)))

(defthm skip-back-le (<= (skip-back buf p w) (nfix p)) :rule-classes :linear)
(defthm skip-fwd-ge (implies (natp p) (<= p (skip-fwd buf p w))) :rule-classes :linear)
(defthm skip-fwd-le (implies (and (natp p) (<= p (len buf))) (<= (skip-fwd buf p w) (len buf))) :rule-classes :linear)

(defun word-left (buf p) (skip-back buf (skip-back buf p nil) t))
(defun word-right (buf p) (skip-fwd buf (skip-fwd buf p nil) t))

(defun le-word-left (st) (le-move st (word-left (le-buf st) (le-pos st))))
(defun le-word-right (st) (le-move st (word-right (le-buf st) (le-pos st))))

; ---- every edit keeps the cursor within the text --------------------------------------

(defthm le-insert-ok (implies (le-ok st) (le-ok (le-insert st cs))))
(defthm le-cut-ok
  (implies (and (le-ok st) (natp a) (natp b) (<= a b) (<= b (len (le-buf st))))
           (le-ok (le-cut st a b))))
(defthm le-move-ok (implies (le-ok st) (le-ok (le-move st p))))
(defthm le-delete-back-ok (implies (le-ok st) (le-ok (le-delete-back st))))
(defthm le-delete-forward-ok (implies (le-ok st) (le-ok (le-delete-forward st))))
(defthm le-kill-to-end-ok (implies (le-ok st) (le-ok (le-kill-to-end st))))
(defthm le-kill-to-start-ok (implies (le-ok st) (le-ok (le-kill-to-start st))))
(defthm le-word-left-ok (implies (le-ok st) (le-ok (le-word-left st))))
(defthm le-word-right-ok (implies (le-ok st) (le-ok (le-word-right st))))

; ---- an edit changes only what it says -----------------------------------------------

; an insert: what was before the cursor is still before it, what was
; after it still after the inserted characters, and the cursor after them
(defthm le-insert-keeps-around
  (implies (le-ok st)
           (let ((st2 (le-insert st cs)))
             (and (equal (take (le-pos st) (le-buf st2)) (take (le-pos st) (le-buf st)))
                  (equal (nthcdr (le-pos st2) (le-buf st2)) (nthcdr (le-pos st) (le-buf st)))
                  (equal (le-pos st2) (+ (le-pos st) (len cs)))
                  (equal (len (le-buf st2)) (+ (len (le-buf st)) (len cs)))))))

; a cut from a to b: the text before a and from b on, nothing else
(defthm le-cut-keeps-around
  (implies (and (le-ok st) (natp a) (natp b) (<= a b) (<= b (len (le-buf st))))
           (let ((st2 (le-cut st a b)))
             (and (equal (take a (le-buf st2)) (take a (le-buf st)))
                  (equal (nthcdr a (le-buf st2)) (nthcdr b (le-buf st)))
                  (equal (len (le-buf st2)) (- (len (le-buf st)) (- b a)))))))

; Backspace takes out exactly the character before the cursor
(defthm le-delete-back-one
  (implies (and (le-ok st) (< 0 (le-pos st)))
           (equal (le-buf (le-delete-back st))
                  (append (take (1- (le-pos st)) (le-buf st)) (nthcdr (le-pos st) (le-buf st))))))

; a move never changes the text
(defthm le-move-keeps-text (equal (le-buf (le-move st p)) (le-buf st)))

; ---- history ---------------------------------------------------------------------------

(defun le-history-back (st)
  (if (zp (le-hidx st)) st
    (let* ((draft (if (equal (le-hidx st) (len (le-hist st))) (le-buf st) (le-draft st)))
           (e (nth (1- (le-hidx st)) (le-hist st))))
      (le e (len e) (le-hist st) (1- (le-hidx st)) draft))))

(defun le-history-forward (st)
  (if (>= (le-hidx st) (len (le-hist st))) st
    (let ((i (1+ (le-hidx st))))
      (if (equal i (len (le-hist st)))
          (le (le-draft st) (len (le-draft st)) (le-hist st) i (le-draft st))
        (let ((e (nth i (le-hist st))))
          (le e (len e) (le-hist st) i (le-draft st)))))))

(defthm character-listp-nth
  (implies (character-listp-list l) (true-listp (nth i l))))

(defthm le-history-back-ok (implies (le-ok st) (le-ok (le-history-back st))))
(defthm le-history-forward-ok (implies (le-ok st) (le-ok (le-history-forward st))))

(defun backs (n st) (if (zp n) st (backs (1- n) (le-history-back st))))
(defun fwds (n st) (if (zp n) st (fwds (1- n) (le-history-forward st))))

(defthm backs-hidx
  (implies (and (le-ok st) (natp n) (<= n (le-hidx st)))
           (equal (le-hidx (backs n st)) (- (le-hidx st) n))))

(defthm backs-ok (implies (le-ok st) (le-ok (backs n st))))

(defthm backs-hist (equal (le-hist (backs n st)) (le-hist st)))

; going back from an entry keeps the draft stored; from the draft, stores it
(defthm backs-keep-draft
  (implies (< (le-hidx st) (len (le-hist st)))
           (equal (le-draft (backs n st)) (le-draft st)))
  :hints (("Goal" :induct (backs n st))))

(defthm backs-draft
  (implies (and (le-ok st) (natp n) (< 0 n) (equal (le-hidx st) (len (le-hist st))) (< 0 (le-hidx st)))
           (equal (le-draft (backs n st)) (le-buf st)))
  :hints (("Goal" :expand ((backs n st))
                  :use ((:instance backs-keep-draft (n (1- n)) (st (le-history-back st))))
                  :in-theory (disable backs-keep-draft))))

(defthm fwds-draft (equal (le-draft (fwds n st)) (le-draft st)))

(defthm fwds-reach-draft
  (implies (and (le-ok st) (natp n) (< 0 n) (equal (+ (le-hidx st) n) (len (le-hist st))))
           (and (equal (le-buf (fwds n st)) (le-draft st))
                (equal (le-hidx (fwds n st)) (len (le-hist st))))))

; THE DRAFT COMES BACK: from the draft, n entries back (n at most the
; history's length) and n forward is the draft, the cursor at its end
(defthm history-restores-draft
  (implies (and (le-ok st) (natp n) (< 0 n) (<= n (len (le-hist st)))
                (equal (le-hidx st) (len (le-hist st))))
           (and (equal (le-buf (fwds n (backs n st))) (le-buf st))
                (equal (le-hidx (fwds n (backs n st))) (le-hidx st))))
  :hints (("Goal" :use ((:instance fwds-reach-draft (st (backs n st)))
                        (:instance backs-hidx) (:instance backs-draft) (:instance backs-ok))
                  :in-theory (disable fwds-reach-draft backs-hidx backs-draft backs-ok le-ok backs fwds))))

; ---- completion ------------------------------------------------------------------------

(defun prefixp-l (a b)
  (if (atom a) t (and (consp b) (equal (car a) (car b)) (prefixp-l (cdr a) (cdr b)))))

(defun cp2 (a b)
  (if (or (atom a) (atom b) (not (equal (car a) (car b)))) nil (cons (car a) (cp2 (cdr a) (cdr b)))))

(defun common-prefix (cands)
  (if (atom cands) nil
    (if (atom (cdr cands)) (lfix (car cands)) (cp2 (car cands) (common-prefix (cdr cands))))))

(defthm cp2-prefix-a (prefixp-l (cp2 a b) a))
(defthm cp2-prefix-b (prefixp-l (cp2 a b) b))

(defthm prefixp-l-trans
  (implies (and (prefixp-l a b) (prefixp-l b c)) (prefixp-l a c)))

(defthm cp2-prefix-when
  (implies (prefixp-l b c) (prefixp-l (cp2 a b) c))
  :hints (("Goal" :use ((:instance prefixp-l-trans (a (cp2 a b)) (b b) (c c)))
                  :in-theory (disable prefixp-l-trans))))

(defthm prefixp-l-lfix (prefixp-l (lfix a) a))

; the common prefix is a prefix of every candidate
(defthm common-prefix-of-each
  (implies (member c cands) (prefixp-l (common-prefix cands) c))
  :hints (("Goal" :induct (common-prefix cands))))

; the word before the cursor: its last k characters
(defun word-before (st k) (nthcdr (- (le-pos st) k) (take (le-pos st) (le-buf st))))

(defun le-complete (st w cand) (le-insert st (nthcdr (len w) cand)))

(defthm prefixp-l-append-nthcdr
  (implies (and (prefixp-l w c) (true-listp c)) (equal (append (lfix w) (nthcdr (len w) c)) c)))

(defthm prefixp-l-len (implies (prefixp-l w c) (<= (len w) (len c))) :rule-classes :linear)

(defun tt-ind (j p l) (if (or (zp j) (zp p) (atom l)) (list j p l) (tt-ind (1- j) (1- p) (cdr l))))

(defthm take-of-take-le
  (implies (and (natp j) (natp p) (<= j p)) (equal (take j (take p l)) (take j l)))
  :hints (("Goal" :induct (tt-ind j p l))))

; the text before the cursor is what is before the word, then the word
(defthm append-take-word
  (implies (and (natp j) (natp p) (<= j p) (<= p (len l)) (true-listp l))
           (equal (append (take p l) x) (append (take j l) (append (nthcdr j (take p l)) x))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance append-take-nthcdr (n j) (l (take p l))))
                  :in-theory (disable append-take-nthcdr))))

(defthm prefix-then-rest
  (implies (and (prefixp-l w c) (true-listp c) (true-listp w))
           (equal (append w (append (nthcdr (len w) c) r)) (append c r)))
  :hints (("Goal" :use ((:instance prefixp-l-append-nthcdr))
                  :in-theory (disable prefixp-l-append-nthcdr))))

; COMPLETION INSERTS THE SUFFIX: when the k characters before the cursor
; are a prefix of the candidate, inserting the rest of it leaves the
; candidate in their place -- the text before them and after the cursor
; as it was, the cursor after the candidate
(defthm completion-replaces-word
  (implies (and (le-ok st) (natp k) (<= k (le-pos st)) (true-listp cand)
                (prefixp-l (word-before st k) cand))
           (let ((st2 (le-complete st (word-before st k) cand)))
             (and (equal (le-buf st2)
                         (append (take (- (le-pos st) k) (le-buf st)) (append cand (nthcdr (le-pos st) (le-buf st)))))
                  (equal (le-pos st2) (+ (- (le-pos st) k) (len cand))))))
  :hints (("Goal" :use ((:instance append-take-word (j (- (le-pos st) k)) (p (le-pos st)) (l (le-buf st))
                                     (x (append (nthcdr k cand) (nthcdr (le-pos st) (le-buf st)))))
                        (:instance prefix-then-rest (w (word-before st k)) (c cand) (r (nthcdr (le-pos st) (le-buf st))))
                        (:instance prefixp-l-len (w (word-before st k)) (c cand)))
                  :in-theory (disable prefix-then-rest prefixp-l-len))))

; ---- cost ---------------------------------------------------------------------------------
;
; Steps a key takes: the characters a scan looks at and the characters
; an edit copies (lineedit's subvec and into copy the vector once).

(defun line-start-steps (buf p)
  (declare (xargs :measure (nfix p)))
  (if (or (zp p) (equal (nth (1- p) buf) #\Newline)) 1 (1+ (line-start-steps buf (1- p)))))

(defun line-end-steps (buf p)
  (declare (xargs :measure (nfix (- (len buf) (nfix p)))))
  (if (or (not (natp p)) (>= p (len buf)) (equal (nth p buf) #\Newline)) 1 (1+ (line-end-steps buf (1+ p)))))

(defthm line-start-steps-bound (<= (line-start-steps buf p) (1+ (nfix p))) :rule-classes :linear)
(defthm line-end-steps-bound
  (implies (and (natp p) (<= p (len buf))) (<= (line-end-steps buf p) (1+ (- (len buf) p))))
  :rule-classes :linear)

(defun skip-back-steps (buf p w)
  (declare (xargs :measure (nfix p)))
  (if (or (zp p) (not (iff (word-char-p (nth (1- p) buf)) w))) 1 (1+ (skip-back-steps buf (1- p) w))))

(defun skip-fwd-steps (buf p w)
  (declare (xargs :measure (nfix (- (len buf) (nfix p)))))
  (if (or (not (natp p)) (>= p (len buf)) (not (iff (word-char-p (nth p buf)) w))) 1 (1+ (skip-fwd-steps buf (1+ p) w))))

(defthm skip-back-steps-bound (<= (skip-back-steps buf p w) (1+ (nfix p))) :rule-classes :linear)
(defthm skip-fwd-steps-bound
  (implies (and (natp p) (<= p (len buf))) (<= (skip-fwd-steps buf p w) (1+ (- (len buf) p))))
  :rule-classes :linear)

; a key's steps, for the keys above; m is an insert's length
(defun key-steps (key st m)
  (let ((buf (le-buf st)) (pos (le-pos st)))
    (case key
      (:insert (+ (len buf) m))
      ((:backspace :delete) (len buf))
      ((:left :right) 1)
      (:line-start (line-start-steps buf pos))
      (:line-end (line-end-steps buf pos))
      (:kill-end (+ (line-end-steps buf pos) (len buf)))
      (:kill-start (+ (line-start-steps buf pos) (len buf)))
      (:word-left (+ (skip-back-steps buf pos nil) (skip-back-steps buf (skip-back buf pos nil) t)))
      (:word-right (+ (skip-fwd-steps buf pos nil) (skip-fwd-steps buf (skip-fwd buf pos nil) t)))
      (otherwise 1))))

; LINEAR: every key is at most 3n + m + 3 steps for an input of n characters
(defthm key-steps-linear
  (implies (and (le-ok st) (natp m))
           (<= (key-steps key st m) (+ 3 m (* 3 (len (le-buf st)))))))

