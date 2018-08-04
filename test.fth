
: check-stack
  depth 0<> if
    ." stack depth is not zero after loading raillisp.fth" cr
    .s cr
    bye
  then ;

include raillisp.fth

check-stack

s" tests.lsp" lisp-load-from-file drop
." stack: " .s cr
." tests ok" cr bye
