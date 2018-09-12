
;; prints: forth-init-time lisp-init-words forth-dict-words lisp-dict-words bench-loop-time bench-tak-time bench-fib-time bench-locals-time

(defun whileloop ()
  (var n 0)
  (while (< n 100000)
    (set n (1+ n))))

(defun tak (x y z)
  (if (not (< y x))
      z
    (tak
     (tak (1- x) y z)
     (tak (1- y) z x)
     (tak (1- z) x y))))

(defun fib (n)
  (if (< n 3) 1
    (+ (fib (- n 1)) (fib (- n 2)))))

(defun locals (a b c d e f)
  (set a b) (set b c) (set d e) (set e f) (set a b) (set b c) (set d e)
  (set b a) (set c b) (set e d) (set f e) (set b a) (set c b) (set e d))

(defun runbench-1 (fn count args)
  (var n 0)
  (var m 0)
  (var time 100000000)
  (var start nil)
  (while (< n 20)
    (set m 0)
    (set start (utime))
    (while (< m count)
      (funcall fn args)
      (set m (1+ m)))
    (set time (min (- (utime) start) time))
    (set n (1+ n)))
  time)

(defun runbench (fn count args)
  (- (runbench-1 fn count args)
     (runbench-1 identity count '(1))))

(defun bench-locals ()
  (runbench locals 50000 '(1 2 3 4 5 6)))

(defun bench-tak ()
  (runbench tak 10 '(18 12 6)))

(defun bench-fib ()
  (runbench fib 10 '(22)))

(defun bench-whileloop ()
  (runbench whileloop 10 nil))

(print forth-init-time) (print " ")
(print lisp-init-time) (print " ")
(print forth-dict-space) (print " ")
(print lisp-dict-space) (print " ")
(print (bench-whileloop)) (print " ")
(print (bench-tak)) (print " ")
(print (bench-fib)) (print " ")
(print (bench-locals))
