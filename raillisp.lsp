
(defcode if (test true &rest false)
  (compile-r test)
  (if,)
  (compile true)
  (else,)
  (progn false)
  (then,))
