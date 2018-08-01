
(defcode if (test true &rest false)
  (compile-r test)
  (if,)
  (compile true)
  (else,)
  (progn false)
  (then,))

(defcode while (test &rest body)
  (begin,)
  (compile-r test)
  (while,)
  (compile-list-nr body)
  (repeat,)
  (maybe-ret))

(def println (obj)
     (print obj)
     (cr))

