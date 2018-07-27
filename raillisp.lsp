
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
              (cons 'progn body)
              '(setq --dolist-tail-- (cdr --dolist-tail--)))))

(defmacro dotimes (spec &rest body)
  (list 'let (list (list '--dotimes-limit-- (car (cdr spec)))
                   (list (car spec) 0))
        (list 'while (list '< (car spec) '--dotimes-limit--)
              (cons 'progn body)
              (list 'setq (car spec) (list '+ (car spec) 1)))))

(defun consp (obj) (= (lisp-type-tag obj) 0))
(defun numberp (obj) (= (lisp-type-tag obj) 1))
(defun symbolp (obj) (= (lisp-type-tag obj) 3))
(defun functionp (obj) (or (= (lisp-type-tag obj) 2)
                           (= (lisp-type-tag obj) 5)))
(defun macrop (obj) (= (lisp-type-tag obj) 6))
(defun stringp (obj) (= (lisp-type-tag obj) 7))

(defun type-of (obj)
  (let ((tag (lisp-type-tag obj)))
    (cond ((= tag 0) 'cons)
          ((= tag 1) 'number)
          ((= tag 3) 'symbol)
          ((or (= tag 2) (= tag 5) 'function))
          ((= tag 6) 'macro)
          ((= tag 7) 'string))))

(defmacro when (test &rest body)
  (list 'if test (cons 'progn body) nil))

(defmacro unless (test &rest body)
  (list 'if test nil (cons 'progn body)))

(defun apply (fn &rest args)
  (let ((head args)
        (prev nil))
    (while (cdr args)
      (setq prev args)
      (setq args (cdr args)))
    (when (consp (car args))
      (if prev
          (setcdr prev (car args))
        (setq head (car args))))
    (apply-1 fn head)))

(defun funcall (fn &rest args)
  (apply-1 fn args))

(defmacro assert (form)
  (list 'unless form
        '(progn (display 'AssertionFailed)
                (exit))
        (list 'display (list 'quote form))))

(defun caar (x) (car (car x)))
(defun cadr (x) (car (cdr x)))
(defun cdar (x) (cdr (car x)))
(defun cddr (x) (cdr (cdr x)))

(defun 1+ (n) (+ n 1))
(defun 1- (n) (- n 1))

(defun utime ()
  (forth utime drop make-number))

(defun cr ()
  (forth cr nil))

(defun forth-shell ()
  (forth quit))

(defun mapcar (func lst)
  (if lst
      (cons (func (car lst)) (mapcar func (cdr lst)))
    lst))

(defun identity (arg)
  arg)

(defun macroexpand (form)
  (if (consp form)
      (let ((fn (car form)))
        (if (and (symbolp fn)
                 (boundp fn)
                 (macrop (symbol-value fn)))
            (macroexpand (apply (symbol-value fn) (cdr form)))
          form))
    form))

(defun macroexpand-all (form)
  (if (and (consp form)
           (not (eq? (car form) 'quote)))
      (macroexpand (mapcar macroexpand-all form))
    form))

(defun make-vector (len init)
  (let ((v (new-vector len)))
    (dotimes (i len)
      (aset v i init))
    v))

(defun list-length (lst)
  (let ((len 0))
    (while lst
      (setq len (+ len 1))
      (setq lst (cdr lst)))
    len))

(defun list->vector (lst)
  (let ((n (list-length lst))
        (v (new-vector n))
        (i 0))
    (while lst
      (aset v i (car lst))
      (setq i (+ i 1))
      (setq lst (cdr lst)))
    v))

(defun vector (&rest args)
  (list->vector args))

