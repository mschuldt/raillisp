
(def test (name check)
     (if (not check)
         (progn (print "FAILED TEST: ")
                (println name)
                (bye))
         (println name)))

(test "+" (eq? (+ 1 1) 2))

