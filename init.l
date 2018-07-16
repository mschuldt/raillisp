
(define defmacro
  (macro (name args &rest body)
         (cons 'define
               (cons name
                     (cons (cons 'macro
                                 (cons args body))
                           nil)))))

(defmacro defun (name args &rest body)
  (cons 'define
        (cons name
              (cons (cons 'lambda
                          (cons args body))
                    nil))))

(defun list (&rest args)
  args)

(defmacro setq (var value)
  (list 'set (list 'quote var) value))

(defmacro dolist (spec &rest body)
  (list 'let (list (list '--dolist-tail-- (car (cdr spec)))
                   (list (car spec) nil))
        (list 'while '--dolist-tail--
              (list 'setq (car spec) '(car --dolist-tail--))
              (list 'setq (car spec) '(car --dolist-tail--))
              (cons 'progn body)
              '(setq --dolist-tail-- (cdr --dolist-tail--)))))

(defmacro dotimes (spec &rest body)
  (list 'let (list (list '--dotimes-limit-- (car (cdr spec)))
                   (list (car spec) 0))
        (list 'while (list '< (car spec) '--dotimes-limit--)
              (cons 'progn body)
              (list 'setq (car spec) (list '+ (car spec) 1)))))

(defun consp (obj)
  (= (lisp-type-tag obj) 0))

(defmacro when (test &rest body)
  (list 'if test (cons 'progn body) nil))

(defmacro unless (test &rest body)
  (list 'if test nil (cons 'progn body)))

(defmacro assert (form)
  (list 'unless form
        '(display 'AssertionFailed)
        (list 'display (list 'quote form))))

(defun caar (x) (car (car x)))
(defun cadr (x) (car (cdr x)))
(defun cdar (x) (cdr (car x)))
(defun cddr (x) (cdr (cdr x)))
