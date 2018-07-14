
(define defmacro
  (macro (name args &rest body)
         (cons (quote define)
               (cons name
                     (cons (cons (quote macro)
                                 (cons args body))
                           nil)))))

(defmacro defun (name args &rest body)
  (cons (quote define)
        (cons name
              (cons (cons (quote lambda)
                          (cons args body))
                    nil))))

(define caar (lambda (x) (car (car x))))
(define cadr (lambda (x) (car (cdr x))))
(define cdar (lambda (x) (cdr (car x))))
(define cddr (lambda (x) (cdr (cdr x))))
