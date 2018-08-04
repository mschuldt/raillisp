
(var start-time (utime))

(def test (name check)
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
;;(test "- 2" (eq? (- 5 10) -5))
(test "*" (eq? (* 5 4) 20))
(test "/" (eq? (/ 50 2) 25))
(test "+1" (eq? (+1 3) 4))
(test "-1" (eq? (-1 3) 2))
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
(test "number?" (number? 2))
(test "number? 2" (not (number? 'symbol)))
(test "symbol?" (symbol? 'symbol))
(test "symbol? 2" (not (symbol? 1)))
(test "string?" (string? "s"))
(test "string? 2" (not (string? 1)))
(test "string? 3" (not (string? nil)))
(test "string? 4" (not (string? t)))
(test "min" (eq? (min 1 2) 1))
(test "max" (eq? (max 1 2) 2))

(def test-equal? ()
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

(def test-list ()
     (var l (list 1 2 3))
     (test "list 0" (equal? (list) nil))
     (test "list 1" (eq? (car l) 1))
     (test "list 2" (equal? (cdr l) (list 2 3)))
     (test "list 3" (equal? l (cons 1 (cons 2 (cons 3 nil)))))
     (test "list len 1" (eq? (list-length (list)) 0))
     (test "list len 2" (eq? (list-length (list 1)) 1))
     (test "list len 3" (eq? (list-length (list 1 nil t)) 3))
     (var l (list (cons 1 2) (cons 2 3) (cons "s" 4)))
     (test "assoc" (equal? (assoc 2 l) (cons 2 3)))
     (test "assoc 2" (equal? (assoc "s" l) (cons "s" 4)))
     (test "assoc 2" (eq? (assoc 4 l) nil)))
(test-list)

(def test-if ()
     (test "if 1" (eq? (if (eq? 1 1) 1 2) 1))
     (test "if 2" (eq? (if (eq? 1 2) 1 2) 2))
     ;;(test "if 3" (eq? (if (eq? 1 2) 1 2 3 4) 4)) ; TODO
     (var x 1)
     (test "if 4" (eq? (if (eq? 1 1) (progn (set x 2) 4) 6) 4))
     (test "if 5" (eq? x 2))
     (if t (if 1 (set x 11) (set x 22)) (set x 33))
     (test "if 5" (eq? x 11)))
(test-if)

(def test-let* (x)
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

(def test-while ()
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

(def factorial (n)
     (if (= n 1)
         1
       (* n (factorial (- n 1)))))

(test "recursion" (eq? (factorial 5) 120))

(def test-dolist ()
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

(def cond-x (x)
     (cond ((= x 1) "one")
           ((= x 2) "two")
           (t "default")))

(def test-cond ()
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

;; (def func-with-no-body ()) ; TODO

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
