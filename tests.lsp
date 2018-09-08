
(var start-time (utime))

(defun test (name check)
     (if (not check)
         (progn (print "FAILED TEST: ")
                (println name)
                (bye))
       (println name)))

(test "eq?" (eq? (eq? 1 1) t))
(test "eq? 2" (eq? (eq? 1 3) nil))
(test "eq? 3" (eq? (eq? (cons 1 2) (cons 1 2)) nil))
(test "eq? 4" (eq? (eq? nil nil) t))
(test "eq? 4" (eq? (eq? nil t) nil))
(test "+" (eq? (+ 1 1) 2))
(test "-" (eq? (- 5 4) 1))
(test "- 2" (eq? (- 5 10) -5))
(test "*" (eq? (* 5 4) 20))
(test "/" (eq? (/ 50 2) 25))
(test "1+" (eq? (1+ 3) 4))
(test "1-" (eq? (1- 3) 2))
(test "=" (eq? (= 1 1) t))
(test "= 2" (eq? (= 0 1) nil))
(test "= 3" (eq? (= 0 nil) nil))
(test "= 4" (eq? (= t t) t))
(test ">" (eq? (> 1 2) nil))
(test "> 1" (eq? (> 1 1) nil))
(test "> 2" (eq? (> 2 1) t))
(test "> 3" (eq? (> 2 1) t))
(test "< 1" (eq? (< 1 1) nil))
(test "< 2" (eq? (< 2 1) nil))
(test "< 3" (eq? (< 1 2) t))
(test "<= 1" (eq? (<= 1 1) t))
(test "<= 2" (eq? (<= 2 1) nil))
(test "<= 3" (eq? (<= 1 2) t))
(test ">= 1" (eq? (>= 1 1) t))
(test ">= 2" (eq? (>= 2 1) t))
(test ">= 3" (eq? (>= 1 2) nil))
(test "not" (eq? (not t) nil))
(test "not 2" (eq? (not nil) t))
(test "not 3" (eq? (not (eq? 1 1)) nil))
(test "car" (eq? (car (cons 3 4)) 3))
(test "cdr" (eq? (cdr (cons 3 4)) 4))
(test "cdr 2" (eq? (cdr nil) nil))
(test "int?" (int? 2))
(test "int? 2" (not (int? 'symbol)))
(test "sym?" (sym? 'symbol))
(test "sym? 2" (not (sym? 1)))
(test "str?" (str? "s"))
(test "str? 2" (not (str? 1)))
(test "str? 3" (not (str? nil)))
(test "str? 4" (not (str? t)))
(test "min" (eq? (min 1 2) 1))
(test "max" (eq? (max 1 2) 2))
(test "hex" (= 0xaf 175))
(test "hex 2" (= $af 175))
(test "bin" (= %101 5))

(defun test-equal? ()
     (test "equal? 1" (equal? 1 1))
     (test "equal? 2" (not (equal? 1 2)))
     (test "equal? 3" (equal? (cons 1 2) (cons 1 2)))
     (test "equal? 4" (not (equal? (cons 1 2) (cons 1 (cons 1 nil)))))
     (test "equal? 5" (not (equal? nil (cons 1 2))))
     (test "equal? 6" (equal? (list 1 2 3) (list 1 2 3)))
     (test "equal? 7" (not (equal? (list 1 2 3) (list 1 2 3 1))))
     (test "equal? 8" (equal? nil nil))
     (test "equal? 9" (equal? "s" "s"))
     (test "equal? 10" (not (equal? "s" "ss"))))
(test-equal?)

(defun test-list ()
     (var l (list 1 2 3))
     ;;(test "list 0" (equal? (list) nil))
     (test "list 1" (eq? (car l) 1))
     (test "list 2" (equal? (cdr l) (list 2 3)))
     (test "list 3" (equal? l (cons 1 (cons 2 (cons 3 nil)))))
     ;;(test "list len 1" (eq? (list-len (list)) 0))
     (test "list len 2" (eq? (list-len (list 1)) 1))
     (test "list len 3" (eq? (list-len (list 1 nil t)) 3))
     (set l (list (cons 1 2) (cons 2 3) (cons "s" 4)))
     (test "assoc" (equal? (assoc 2 l) (cons 2 3)))
     (test "assoc 2" (equal? (assoc "s" l) (cons "s" 4)))
     (test "assoc 2" (eq? (assoc 4 l) nil)))
(test-list)

(defun test-string ()
     (var s1 "str")
     (var s2 "str")
     (test "string 1" (equal? s1 s2))
     (test "string 2" (not (eq? s1 s2)))
     ;; (set s1 (intern s1))
     ;; (set s2 (intern s2))
     ;; (test "string 3" (equal? s1 s2))
     ;; (test "string 4" (eq? s1 s2))
     ;; (test "string 5" (eq? (str-len s1) 3))
     (test "string 6" (eq? (str-len "") 0))
     (test "string 7" (= (str->int "45") 45))
     (test "string 8" (= (str->int "-5") -5)))
(test-string)

(defun test-if ()
     (var x 1)
     (test "if 1" (eq? (if (eq? 1 1) 1 2) 1))
     (test "if 2" (eq? (if (eq? 1 2) 1 2) 2))
     ;;(test "if 3" (eq? (if (eq? 1 2) 1 2 3 4) 4)) ; TODO
     (test "if 4" (eq? (if (eq? 1 1) (progn (set x 2) 4) 6) 4))
     (test "if 5" (eq? x 2))
     (if t (if 1 (set x 11) (set x 22)) (set x 33))
     (test "if 6" (eq? x 11)))

(test-if)

(defun test-let* (x)
     (var xx x)
     (let* ((x 11)
            (z 50))
       (test "let*" (not (eq? x xx)))
       (test "let* 1" (eq? x 11))
       (test "let* 2" (eq? z 50))
       (let* ((x 22)
              (z (+ x 1)))
         (test "let* 3" (eq? x 22))
         (test "let* 4" (eq? z 23)))
       (test "let* 5" (eq? x 11))
       (test "let* 6" (eq? z 50)))
     (test "let* 7" (eq? x xx)))
(test-let* 100)

(defun test-while1 ()
     (var x 10)
     (var n 0)
     (while (> x 0)
       (set n (+ n 1))
       (set x (- x 1)))
     (test "while1" (eq? n 10)))
(test-while1)

(defun test-while ()
     (var lst nil)
     (var n 0)
     (var x 2)
     (var inner 0)
     (while (< n 10)
       (while (> x 0)
         (set x (- x 1))
         (set inner (+ 1 inner)))
       (set x 2)
       (set lst (cons n lst))
       (set n (+ n 1)))
     (test "while" (eq? n 10))
     (test "while 2" (equal? lst (list 9 8 7 6 5 4 3 2 1 0)))
     (test "while 3" (eq? inner 20)))
(test-while)

(defun factorial (n)
     (if (= n 1)
         1
       (* n (factorial (- n 1)))))

(test "recursion" (eq? (factorial 5) 120))

(defun test-dolist ()
     (let* ((v nil))
       (dolist (x (list 1 2 3))
         (set v (cons (cons x (* x x)) v)))
       (test "dolist" (equal? v (list (cons 3 9)
                                      (cons 2 4)
                                      (cons 1 1))))
       (set v nil)
       (dolist (x (list 1 2))
         (dolist (x (list 11 22))
           (set v (cons x v)))
         (set v (cons x v)))
       (test "dolist 2" (equal? v (list 2 22 11 1 22 11)))))
(test-dolist)

(defun cond-x (x)
     (cond ((= x 1) "one")
           ((= x 2) "two")
           (t "default")))

(defun test-cond ()
     (test "cond 1" (equal? (cond-x 1) "one"))
     (test "cond 2" (equal? (cond-x 2) "two"))
     (test "cond 3" (equal? (cond-x 32) "default"))
     ;;(test "cond 4" (eq? (cond ((= 1 2) t)) nil)) ; TODO
     (var x nil)
     (cond (t
            (set x (cons 1 x))
            (set x (cons 2 x))))
     (test "cond 4" (equal? x (list 2 1)))
     (cond (t (cond (t (set x 4)))))
     (test "cond 5" (eq? x 4)))

(test-cond)

(defun test-and ()
     (var x 0)
     (and 1
          (progn (set x 11) t)
          nil
          (set x 22))
     (test "and" (eq? x 11))
     (and (= (+ 10 1) x)
          (and t
               (set x 33)
               nil
               (set x 44))
          (eq? 2 3)
          (set x 55))
     (test "and 2" (eq? x 33))
     (if (and 3 4)
         (set x 4)
       (set x 5))
     (test "and 3" (eq? x 4))
     ;;(test "and 4" (eq? (and) t))
     )
(test-and)

(defun test-or ()
     (var x 0)
     (or (progn (set x 11) t)
         (set x 22))
     (test "or" (eq? x 11))
     (or (progn (set x 11) nil)
         (set x 22))
     (test "or 2" (eq? x 22))
     (or nil
         (or nil
             (progn (set x 33) t)
             (set x 44)))
     (print "x = ")
     (println x)
     (test "or 3" (eq? x 33))
     (if (or nil t)
         (set x 4)
       (set x 5))
     (test "or 4" (eq? x 4))
     ;;(test "or 5" (eq? (or) nil))
     )
(test-or)

(defun test-dotimes ()
     (var x nil)
     (dotimes (n 5)
       (set x (cons n x)))
     (test "dotimes" (equal? x (list 4 3 2 1 0)))
     (dotimes (n 0)
       (set x 1))
     (test "dotimes 2" (not (eq? x 1))))

(test-dotimes)

(defun test-list-index ()
     (var l (list 1 nil "str" 'sym))
     (test "list-index 1" (eq? (list-index 1 l) 0))
     (test "list-index 2" (eq? (list-index "str" l) 2))
     (test "list-index 3" (eq? (list-index 'sym l) 3))
     (test "list-index 4" (eq? (list-index 'xx l) -1))
     ;;(test "list-index 5" (eq? (list-index nil (list)) -1))
)
(test-list-index)

;; (defun func-with-no-body ()) ; TODO

(print "--forth init time: ")
(println forth-init-time)
(print "--lisp init time: ")
(println lisp-init-time)
(print "--forth dict space: ")
(println forth-dict-space)
(print "--lisp dict space: ")
(println lisp-dict-space)
(print "--test time: ")
(println (- (utime) start-time))
