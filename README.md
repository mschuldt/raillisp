
# // raillisp \\\\

Raillisp is a simple lisp implemented in Forth.
It aims to be small, fast, and portable.

Raillisp is in active development. Currently it only runs on Gforth,
but will soon run on everything from microcontrollers to web browsers.

It is designed to give you high level lisp features
while retaining low level access and a small footprint
making it suitable for constrained systems.
Raillisp lets you ride the metal in style.

Raillisp works by compiling lisp functions into forth words.
For example, creating a lisp function and disassembling its forth word:
```lisp
  (defun fib (n)
    (if (< n 3)
        1
      (+ (fib (- n 1)) (fib (- n 2)))))

  (dis fib)
```
prints:
```
 : fib
   dup 7 <
   IF     3
   ELSE   dup 3 - fib over 5 - fib +
   THEN
   nip ;
```
(the number constants are different because of the lisp type tagging,
`dis` just calls the forth word `see`)

More documentation is forthcoming. For now more example code
can be found in `raillisp.lsp` and `tests.lsp`.

The Raillisp dialect is influenced by Common Lisp and Scheme,
but there are substantial differences.
Lots of common features are not currently supported, some never will be.
Features that compromise the performance of the system will
not be implemented.

# Usage

To run a file:
```gforth raillisp.fth FILE.lsp```

For the REPL:
```gforth raillisp.fth```

Run tests:
```make test```

Be careful...There is currently almost no error checking of any kind.
When you do something wrong, the helpful error message is probably a backtrace.

The `make` option to build a gforth image does not currently work
becuase heap pointers are compiled into the dictionary.
