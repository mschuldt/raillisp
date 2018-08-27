
(set start-time (utime))
(set start-here (here))

(var raillisp-version "0.1")

(defcode if (test true &rest false)
  (compile-r test)
  (if,)
  (compile true)
  (else,)
  (compile-progn false)
  (then,))

(defcode while (test &rest body)
  (begin,)
  (compile-r test)
  (while,)
  (compile-list-nr body)
  (repeat,)
  (maybe-ret))

(defcode dotimes (spec &rest body)
  (let* ((v (car (cdr spec))))
    (if (number? v)
        (untag-lit, v)
      (compile-r v)
      (untag-num,)))
  (untag-lit, 0)
  (do,)
  (set loop-vars (cons (car spec) loop-vars))
  (compile-list-nr body)
  (set loop-vars (cdr loop-vars))
  (loop,)
  (maybe-ret))

(defmacro dolist (spec &rest body)
  (list 'let* (list (list '--tail-- (car (cdr spec)))
                    (list (car spec) 'nil))
        (list 'while '--tail--
              (list 'set (car spec) '(car --tail--))
              '(set --tail-- (cdr --tail--))
              (cons 'progn body))))

(defcode cond (&rest forms)
  (dolist (x forms)
    (compile-r (car x))
    (if,)
    (compile-progn (cdr x))
    (else,))
  (dolist (x forms)
    (then,)))

(defcode and (&rest conditions)
  (dolist (x conditions)
    (compile-r x)
    (if,))
  (return-lit t)
  (dolist (x conditions)
    (else,)
    (return-lit nil)
    (then,)))

(defcode or (&rest conditions)
  (dolist (x conditions)
    (compile-r x)
    (if,)
    (return-lit t)
    (else,))
  (return-lit nil)
  (dolist (x conditions)
    (then,)))

(defun println (obj)
  (print obj)
  (cr))

(defun repl ()
  (cr)
  (while 1
    (println (eval (read-from-input)))))

(defun mapcar (fn lst)
  (if lst
      (cons (funcall fn (list (car lst))) (mapcar fn (cdr lst)))
    lst))

(defcode when (test &rest body)
  (compile-r test)
  (if,)
  (compile-progn body)
  (then,))

(defun caar (x) (car (car x)))
(defun cadr (x) (car (cdr x)))
(defun cdar (x) (cdr (car x)))
(defun cddr (x) (cdr (cdr x)))

(defun nthcdr (n list)
  (dotimes (_ n)
    (set list (cdr list)))
  list)

(defun nth (n list)
  (car (nthcdr n list)))

(defun init ()
  (if (not (boundp '_noinit_))
      (progn
        (process-args)
        (if (= (list-length command-line-args) 0)
            (progn
              (print "// Raillisp ")
              (print raillisp-version)
              (println " \\\\")
              (repl))
          (load (car command-line-args))
          (bye))
        nil)))

(var lisp-init-time (- (utime) start-time))
(var lisp-dict-space (- (here) start-here))

(init)
