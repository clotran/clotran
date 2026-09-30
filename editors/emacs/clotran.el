;;; clotran.el --- Emacs knows clotran's files  -*- lexical-binding: t; -*-

;; A .cljf file is clotran Clojure (the extension, and the :cljf feature
;; in reader conditionals: DEVIATIONS.md 33). Its syntax is Clojure's, so
;; it opens in clojure-mode, and CIDER works in it as in any Clojure
;; buffer -- connected to a clotran nREPL server (~/jborden/clotran-nrepl).
;; A script whose first line runs clotran opens in clojure-mode too.
;;
;; In your init file:
;;
;;   (load "/path/to/clotran/editors/emacs/clotran.el")

(add-to-list 'auto-mode-alist '("\\.cljf\\'" . clojure-mode))
(add-to-list 'interpreter-mode-alist '("clotran" . clojure-mode))

(provide 'clotran)
;;; clotran.el ends here
