
(defcode if (test true &rest false)
  (compile test)
  (if,)
  (compile true)
  (else,)
  (compile-list false)
  (then,)
  1)
