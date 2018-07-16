
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

(defun caar (x) (car (car x)))
(defun cadr (x) (car (cdr x)))
(defun cdar (x) (cdr (car x)))
(defun cddr (x) (cdr (cdr x)))
