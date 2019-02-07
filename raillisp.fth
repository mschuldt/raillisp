\ -*- forth -*-

0 warnings !

variable start-time
variable start-here
utime drop start-time !
here start-here !

variable exit-on-error
1 exit-on-error !

: maybe-bye exit-on-error @ if 1 throw then ;

: string-new ( a u -- a u )
  dup rot over allocate drop
  dup >r rot cmove r> swap ;

0 constant lisp-pair-tag
1 constant lisp-number-tag
2 constant lisp-symbol-tag
3 constant lisp-string-tag
4 constant lisp-vector-tag
5 constant lisp-function-tag
6 constant lisp-max-tag

lisp-max-tag cells allocate throw constant display-dispatch
lisp-max-tag cells allocate throw constant equal?-dispatch
lisp-max-tag cells allocate throw constant interpret-dispatch
lisp-max-tag cells allocate throw constant compile-dispatch
lisp-max-tag cells allocate throw constant type-names

\ lisp structs. The forth struct feature is not used for portability

\ struct
\ cell% field pair-tag
\ cell% field pair-car
\ cell% field pair-cdr
\ end-struct lisp-pair

\ translates to:

\ : pair-tag 0 + ;
: pair-car [ 1 cells ] literal + ;
: pair-cdr [ 2 cells ] literal + ;
3 cells constant sizeof-pair

\ : symbol-tag 0 + ;
: symbol-namea [ 1 cells ] literal + ;
: symbol-nameu [ 2 cells ] literal + ;
3 cells constant sizeof-symbol

\ : vector-tag 0 + ;
: vector-len [ 1 cells ] literal + ;
: vector-vec [ 2 cells ] literal + ;
3 cells constant sizeof-vector

variable curr-func
variable lisp-latest

-1 4 rshift constant lisp-len-mask
1 63 lshift constant lisp-macro-mask
1 62 lshift constant lisp-special-mask
1 61 lshift constant lisp-&rest-mask
1 60 lshift constant lisp-indirect-mask

: func>parent 1 cells + ;
: func>args 2 cells + ;
: func>returns 3 cells + ;
: func>flags 4 cells + ;

: func-macro? func>flags @ lisp-macro-mask and ;
: func-special? func>flags @ lisp-special-mask and ;
: func-&rest? func>flags @ lisp-&rest-mask and ;
: func-indirect? func>flags @ lisp-indirect-mask and ;

: lispfunc>string ( f - a u )
  func>flags dup @ lisp-len-mask and swap 1 cells + swap ;
: forthfunc>string ( f - a u )
  5 cells + @ name>string ;
: func>string ( f - a u )
  dup func-indirect? if forthfunc>string else lispfunc>string then ;

: func>int
  dup func-indirect? if
    5 cells + @
  else
    func>flags dup @ lisp-len-mask and
    1 cells + + aligned @
  then ;

: func-set-bit ( mask - ) lisp-latest @ func>flags dup @ rot or swap ! ;
: func-indirect! lisp-indirect-mask func-set-bit ;
: func-special! lisp-special-mask func-set-bit ;
: func-macro! lisp-macro-mask func-set-bit func-special! ;
: func-&rest! ( sym - )
  drop \ now only indicate with a bit, don't save parameter symbol
  lisp-&rest-mask func-set-bit ;
: func-args! ( n - ) lisp-latest @ func>args ! ;
: func-returns! lisp-latest @ func>returns ! ;

: function-lookup ( namea nameu - func )
  lisp-latest
  @ >r
  begin
    r@
    0<>
  while
    2dup r@ func>string
    compare 0= if
      2drop r> exit
    then
    r> func>parent @ >r
  repeat
  2drop
  r> drop 0
;

: lisp-print-funcs ( - )
  lisp-latest @
  begin
    dup 0<>
  while
    dup func>string type ."  " func>parent @
  repeat drop cr ;

\ : find-function ( name - ) function-lookup curr-func ! ;
\ : find-function-check ( name - )
\   dup find-function curr-func @ 0= if
\     ." invalid function: " name>string type cr bye
\   then drop ;
: set-curr-func ( func - ) curr-func ! ;

: curr-args ( - n ) curr-func @ dup 0<> if func>args @ then ;
: curr-returns ( - n ) curr-func @ dup 0<> if func>returns @ then ;
: curr-&rest ( - x ) curr-func @ dup 0<> if func-&rest? then ;

: check-alloc dup 1 and if ." lsb set" 1 throw then ;

variable stack-counter

: header-offset align here :noname postpone ; drop here swap - 24 - ;

defined vtcopy, [if]
    : lisp-header, :noname postpone [ 2drop 2drop drop ;
[else]
    : lisp-header, :noname postpone [ 2drop 2drop ;
[then]


: start-defun ( namea nameu - )
  align here
  lisp-function-tag , \ tag
  lisp-latest dup @ , ! \ parent pointer
  0 , \ argument count
  1 , \ return count
  dup , \ flags + name length
  mem, \ name
  align here 1221 , \ xt
  lisp-header, swap !
;

: end-defun postpone exit ;

: (defun ( num-args - ) parse-name
         start-defun
         func-args!
         ] ;

: ) postpone exit postpone [ ; immediate

: func ( word args returns - )
  \ makes a lisp wrapper around a forth word
  align here
  lisp-function-tag , \ tag
  lisp-latest dup @ , ! \ parent pointer
  swap , \ arg count
  , \ return count
  0 , \ flags
  , \ word
  func-indirect! ;

: f-latest ( args ret - ) latest -rot func ;
: f0 ( - ) 0 1 f-latest ;
: f1 ( - ) 1 1 f-latest ;
: f2 ( - ) 2 1 f-latest ;
: f3 ( - ) 3 1 f-latest ;
: f4 ( - ) 4 1 f-latest ;
: fn ( - ) -1 1 f-latest 1 func-&rest! ;

: create-cons ( car cdr -- lisp )
  sizeof-pair allocate throw check-alloc >r
  r@ ( pair-tag) lisp-pair-tag swap !
  r@ pair-cdr !
  r@ pair-car !
  r> ;

: cons create-cons ; f2

: car ( pair -- lisp ) dup 0<> if pair-car @ then ; f1
: cdr ( pair -- lisp ) dup 0<> if pair-cdr @ then ; f1

: setcar ( pair x -- x ) dup rot pair-car ! ; f2
: setcdr ( pair x -- x ) dup rot pair-cdr ! ; f2

: <<1 1 lshift ;
: >>1 1 rshift ;

: tag-num ( number -- lisp ) 1 lshift 1 or ;
: untag-num ( lisp - number ) 1 rshift ;

: create-symbol ( namea nameu -- lisp )
  sizeof-symbol allocate throw check-alloc >r
  r@ ( symbol-tag) lisp-symbol-tag swap !
  r@ symbol-nameu !
  r@ symbol-namea !
  r> ;

: symbol-new ( namea nameu -- lisp )
  string-new create-symbol ;

: symbol->string ( lisp -- namea nameu )
  \  ." *symbol->string:* " dup . cr
  dup symbol-namea @ swap symbol-nameu @ ;

: create-string ( namea nameu -- lisp )
  create-symbol
  dup ( symbol-tag) lisp-string-tag swap ! ;

: create-vector ( length -- lisp )
  sizeof-vector allocate throw check-alloc >r
  r@ ( vector-tag) lisp-vector-tag swap !
  dup r@ vector-len !
  cells allocate throw r@ vector-vec ! r> ;

: get-lisp-tag ( lisp - type )
  dup 1 and if
    drop lisp-number-tag
  else
    dup 0= over -1 = or if
      drop lisp-number-tag
    else
      ( lisp-tag) @
    then
  then ;

: type-of get-lisp-tag tag-num ; f1 \ todo: return symbol
: int? 1 and ; f1
: cons? get-lisp-tag lisp-pair-tag  = ; f2
: sym? get-lisp-tag lisp-symbol-tag = ; f1
: str? get-lisp-tag lisp-string-tag =  ; f1
: vector? get-lisp-tag lisp-vector-tag = ; f1


-1 constant lisp-true
variable t
lisp-true t !

: eq? = ; f2

wordlist constant symbols

: intern ( lisp - lisp )
  \ Intern a string into the dictionary. Return a symbol
  dup >r symbol->string 2dup
  symbols >order find-name previous
  dup if
    \ the symbol already exits
    -rot 2drop name>int execute @ r> drop
    \ TODO: fix: s" cons" intern
  else
    \ create a new variable in the symbols wordlist
    drop get-current -rot symbols set-current
    nextname header reveal dovar: cfa, r@ , set-current
    \ set symbol string to point to header string
    latest name>string drop r@ symbol-namea !
    \ change type to symbol
    lisp-symbol-tag r@ ( symbol-tag) !
    r>
  then ; f1

: sym>value 1 cells + ;
: sym>parent 2 cells + ;
: sym>name 3 cells + ;
: sym>string ( sym - namea nameu )
  sym>name dup 1 cells + swap @ ;

variable lisp-latest-SYM

: make-sym ( namea nameu - lisp )
  align here dup >r
  lisp-symbol-tag ,
  0 , \ symbol value
  lisp-latest-SYM dup @ , ! \ parent pointer
  dup , \ name length
  mem, \ name
  r>
;

: sym-lookup ( namea nameu - sym )
  lisp-latest-SYM @ >r
  begin
    r@ 0<>
  while
    2dup r@ sym>string
    compare 0= if
      2drop r> exit
    then
    r> sym>parent @ >r
  repeat
  2drop r> drop 0 ;

: sym-print ( sym - )
  ." sym(" sym>string type ." )" ;

: print-syms ( - )
  ." symbols: "
  lisp-latest-SYM @
  begin
    dup 0<>
  while
    dup sym>string
    type ."  " sym>parent @
  repeat drop cr ;

: str-intern ( namea nameu - sym )
  2dup sym-lookup dup 0<> if
    nip nip exit \ already interned
  else
    drop make-sym
  then ;

: sym-intern ( str - sym )
  symbol->string str-intern ;

-1 s" t" str-intern sym>value !
 0  s" nil" str-intern sym>value !

: str-equal? ( lisp1 lisp2 -- lisp )
  symbol->string rot symbol->string
  compare 0= if
    lisp-true
  else
    nil
  then ; f2

: sym-equal? str-equal? ;  f2 \ TODO: symbol interning

: str-sub-equal? ( str sub index - bool )
  \ check that SUB matches STR from INDEX
  dup 0< if
    drop 2drop nil exit
  then
  untag-num >r
  swap >r
  symbol->string r> symbol->string
  rot 2dup r@ + >r
  drop -rot r>
  over <= >r drop over
  r> if
    swap r> + swap
    compare 0= if lisp-true else nil then
  else
    r> drop 2drop 2drop nil
  then
; f3

: equal? ( lisp lisp - lisp )
  2dup = if
    2drop lisp-true
  else
    2dup 1 and swap 1 and or if
      2drop nil \ number
    else
      2dup 2dup 0= swap 0= or -rot -1 = swap -1 = or or if
        2drop nil \ nil or t
      else
        2dup get-lisp-tag swap get-lisp-tag <> if
          2drop nil
        else
          dup get-lisp-tag cells equal?-dispatch + @ execute
        then
      then
    then
  then ; f2

: cons-equal? ( lisp lisp - lisp )
  \ todo: non recursive version
  2dup car swap car equal?
  -rot cdr swap cdr equal?
  and ;

' str-equal? equal?-dispatch lisp-symbol-tag cells + !
' str-equal? equal?-dispatch lisp-string-tag cells + !
' cons-equal? equal?-dispatch lisp-pair-tag cells + !

s" &rest" symbol-new intern
variable &rest
&rest !

: get-vararg
  recursive ( arglist - vararg)
  \ return the vararg symbol and remove from arglist
  dup 0<> if
    dup cdr 0<> if
      dup cdr car &rest @ sym-equal? if
        dup cdr cdr car  \ vararg
        swap pair-cdr 0 swap !
      else
        cdr get-vararg
      then
    else
      drop 0
    then
  else
    drop 0
  then ;

: split-args ( arglist - args vararg)
  dup 0<> if
    dup car &rest @ sym-equal? if
      0 swap cdr car
    else
      dup get-vararg
    then
  else
    dup
  then ;

: lisp-display ( lisp -- )
  dup 0= if
    drop ." nil"
  else
    dup -1 = if
      drop ." t"
    else
      dup get-lisp-tag
      cells display-dispatch + @ execute
    then then ;

: print ( lisp -- lisp ) dup lisp-display ; f1

: lisp-display-pair ( lisp -- )
  [char] ( emit ( 32 emit)
  begin
    dup car lisp-display 32 emit
    cdr
    dup 0<> if
      dup get-lisp-tag lisp-pair-tag <> if
        [char] . emit 32 emit lisp-display 0
      then
    then
    dup 0=
  until
  drop
  [char] ) emit ;

' lisp-display-pair display-dispatch lisp-pair-tag cells + !

: lisp-display-number ( lisp -- ) untag-num . ;

' lisp-display-number display-dispatch lisp-number-tag cells + !

: lisp-display-symbol ( lisp -- ) symbol->string type ;

' lisp-display-symbol display-dispatch lisp-symbol-tag cells + !

: lisp-display-string ( lisp -- ) symbol->string type ;

' lisp-display-string display-dispatch lisp-string-tag cells + !

: lisp-display-vector ( lisp -- )
  [char] [ emit
  dup vector-vec @ swap vector-len @ 0 ?do
    dup i cells + @ lisp-display ."  "
  loop
  drop
  [char] ] emit ;

' lisp-display-vector display-dispatch lisp-vector-tag cells + !

: lisp-display-function ( lisp - )
  [char] $ emit func>string type ;

' lisp-display-function display-dispatch lisp-function-tag cells + !

: error-undefined-value
  cr ." undefined value: " lisp-display cr maybe-bye ;

\ interpretation words must return a single lisp value
\ compilation words must return nothing

variable lisp-state
: start-compile 1 lisp-state ! ;
: end-compile 0 lisp-state ! ;
end-compile

\ Used by the compiler to signal when the current
\ form should leave a return value on the stack.
variable return-context \ 1 if currently in a return context

: rcontext{ ( v - ) return-context @ r> swap >r >r return-context ! ;
: }rcontext ( v - ) r> r> swap >r return-context ! ;

: do-list-push ( x list - ) dup @ rot swap cons swap ! ;
: do-list-pop ( list - x ) dup @ dup car swap cdr rot ! ;

\ STACK is a list representing the current stack of the compiled program.
\ symbols in this list represent named stack positons (locals variables).
\ anonymous stack entries are nil.
variable stack
0 stack !
variable stack-depth
0 stack-depth !

: stack-print stack @ lisp-display cr ;

: stack-push ( v - )
  stack-depth dup @ 1+ swap !
  stack do-list-push ;

: stack-push*
  \ pushes a unique number onto the locals stack
  stack-counter dup @ 1+ dup tag-num stack-push swap ! ;

: stack-drop ( - )
  stack-depth dup @ dup 0= if
  then
  1- swap !
  stack do-list-pop drop ;

: stack-drop-n ( n - )
  begin dup 0 > while
    1- stack-drop
  repeat drop ;

: stack-push-n ( n - )
  begin dup while
    1- stack-push*
  repeat drop ;

: check-stack-depth ( n - )
  dup stack-depth @ <> if
    ." COMPILATION ERROR: function '" lisp-latest @ func>string type
    ." ' left " stack-depth @ . ." items on the stack, expected " . cr
    ."   stack: " stack-print cr bye
  then drop ;

: lisp-find-symbol-function ( symbol - func )
  symbol->string
  function-lookup
; \ TODO: error checking


: lisp-interpret ( lisp - lisp? )
  dup 0<> if
    dup get-lisp-tag cells
    lisp-state @
    0= if interpret-dispatch else compile-dispatch then
    + @ execute
  then ;

: lisp-interpret-list ( lisp - a1...an n )
  0 >r
  begin
    dup 0<>
  while
    dup car lisp-interpret
    swap cdr
    r> 1+ >r
  repeat
  drop r> ;

: lisp-compile-list ( lisp - count )
  0 swap
  begin
    dup 0<>
  while
    dup car lisp-interpret
    cdr swap 1+ swap
  repeat drop ;

: lisp-interpret-r ( lisp - lisp?)
  \ forces return context
  \ used when the lisp being compiled consumes the return result
  \ The caller is responsible for maintaining the locals stack
  1 rcontext{ lisp-interpret }rcontext ;

: lisp-compile-list-nr 0 rcontext{ lisp-compile-list drop }rcontext ;

: lisp-compile-progn ( lisp - )
  >r return-context @
  0 return-context !
  begin
    r@ 0<>
  while
    r@ cdr 0= if
      return-context !
    then
    r> dup car lisp-interpret cdr >r
  repeat
  r> drop ;


\ special forms with < 0 args are passed all the arguments as a list
: special ( immediate) -1 0 f-latest func-special! ;

: compile lisp-interpret t ; f1
: compile-r lisp-interpret-r t ; f1
: compile-list lisp-compile-list ; f1
: compile-list-nr lisp-compile-list-nr t ; f1

: compile-progn lisp-compile-progn t ; f1
: progn lisp-compile-progn ; special

: lisp-find-symbol-word ( lisp - word)
  symbol->string
\  ." word: " 2dup type cr
  2dup find-name
  dup 0= if
    drop
    ." ERROR: invalid word: " type cr 1 throw
  then
  -rot 2drop ;

variable macro-flag
: set-macro-flag 1 macro-flag ! ;

\ the reader

variable paren-count
variable stdin-lastchar
variable stdin-unread
variable read-from-string

: update-paren-count ( c - c )
    dup [char] ( = if
      paren-count dup @ 1+ swap !
    else
      dup [char] ) = if
        paren-count dup @ 1- swap !
      then
  then ;

: read-next-line ( - e a )
    pad dup 100 accept
    2dup + 10 swap c! 1+
    over + swap ;

: next-key ( e a - e a c )
    2dup <= if
        \ TODO: reading multi-line strings
        paren-count @ 0<> if
            \ End of line but not end of list, read another line
            cr ." :  "
            drop drop read-next-line
        else
            \ End of line
            0 exit
        then
    then
    dup c@ swap 1+ swap
    update-paren-count \ TODO: only do this when reading lists
;

: lisp-char-from-input
  stdin-unread @ if
    0 stdin-unread !
    stdin-lastchar @
  else
    next-key
    dup stdin-lastchar !
  then ;

: lisp-read-char ( e a -- e a c )
  read-from-string @ if
    2dup <= if
      0
    else
      dup c@ swap 1+ swap
    then
  else
    lisp-char-from-input
  then ;

: lisp-unread-char ( e a -- e a )
  read-from-string @ if
    1-
  else
    1 stdin-unread !
  then ;

: lisp-is-ws ( c -- flag )
  dup 10 = swap dup 13 = swap dup 9 = swap 32 = or or or ;

: lisp-skip-ws ( e a -- e a )
  lisp-read-char
  begin
    dup 0<> over lisp-is-ws and
  while
    drop lisp-read-char
  repeat
  0<> if
    lisp-unread-char
  then ;

: lisp-skip-line
  lisp-read-char
  begin
    dup 0<> over 10 <> and \ 10 = \n
  while
    drop lisp-read-char
  repeat
  0<> if
    lisp-unread-char
  then ;

: lisp-skip-comments
  begin
    lisp-skip-ws lisp-read-char dup 59 =  \ 59 = ;
  while
    drop lisp-skip-line
  repeat
  0<> if lisp-unread-char then  ;

: lisp-skip lisp-skip-ws lisp-skip-comments ;

128 allocate throw constant token-buffer

: lisp-read-token ( e a -- e a a u )
  lisp-skip
  0 >r
  lisp-read-char
  begin
    dup [char] ) <> over 0<> and over lisp-is-ws 0= and
  while
    token-buffer r@ + c! r> 1+ >r lisp-read-char
  repeat
  0<> if
    lisp-unread-char
  then
  token-buffer r> ;

defer lisp-read-lisp

: lisp-read-list-char
  lisp-skip lisp-read-char dup [char] ) = swap 0 = or ;

: lisp-read-list-cons
  lisp-unread-char lisp-read-lisp nil cons ;

: lisp-read-list ( e a -- e a lisp )
  lisp-read-list-char if
    nil
  else
    lisp-read-list-cons dup >r >r
    begin
      lisp-read-list-char 0=
    while
      lisp-read-list-cons dup r> pair-cdr ! >r
    repeat
    r> drop r>
  then ;

: str->int ( lisp - lisp )
  symbol->string s>number? if drop tag-num else nil then ; f1

: lisp-read-symbol ( e a -- e a lisp )
  lisp-read-token 2dup s>number? if
    drop tag-num nip nip
  else
    drop drop string-new create-symbol
  then ;

: lisp-read-quote ( e a -- e a lisp )
  lisp-read-lisp nil create-cons
  s" quote" symbol-new swap create-cons ;

: lisp-escape-char ( c - c )
  dup [char] n = if
    drop 10
  else
    dup [char] \ = if \ todo: move escape codes to lisp
      drop [char] \
    else
      dup [char] " = if
        drop [char] "
      else
        cr ." invalid escape code: " emit cr maybe-bye
      then
    then
  then ;

: lisp-read-string
  0 >r
  lisp-read-char
  begin
    dup 0<> over [char] " <> and
  while
    dup [char] \ = if
      drop lisp-read-char lisp-escape-char
    then
    token-buffer r@ + c! r> 1+ >r lisp-read-char
  repeat
  dup 0<> swap [char] " <> and if
    lisp-unread-char
  then
  token-buffer r>
  string-new create-string ;

: _lisp-read-lisp ( e a -- e a lisp )
  lisp-skip lisp-read-char
  dup 0= if
    drop 0
  else
    dup [char] ( = if
      drop lisp-read-list
    else
      dup [char] ' = if
        drop lisp-read-quote
      else
        dup [char] " = if
          drop lisp-read-string
        else
          [char] ? = if
            lisp-read-char tag-num \ char literal
            else
	      lisp-unread-char lisp-read-symbol
          then
        then
      then
    then
  then ;
' _lisp-read-lisp is lisp-read-lisp

: lisp-load-from-string ( a u -- lisp )
  1 read-from-string !
  over + swap 0 >r
  begin
    lisp-skip 2dup >
  while
    r> drop lisp-read-lisp lisp-interpret >r
  repeat
  2drop r> ;

: lisp-read-from-string ( a u -- lisp )
  1 read-from-string !
  over + swap
  lisp-skip lisp-read-lisp >r 2drop r> ;

8192 allocate throw constant read-buffer

: lisp-load-from-file ( a u -- lisp )
  r/o open-file
  0<> if
    drop 0
  else
    >r read-buffer 8192 r@ read-file
    0<> if
      r> 2drop 0
    else
      r> close-file drop
      read-buffer swap lisp-load-from-string
    then
  then ;

: read-from-input
  0 read-from-string !
  -1 stdin-lastchar !
  0 stdin-unread !
  0 paren-count !
  ." > " read-next-line
  lisp-read-lisp
  >r 2drop r>
; f0

: read ( str - lisp ) symbol->string lisp-read-from-string ; f1
: eval ( lisp - lisp ) lisp-interpret ; f1

: load-lisp ( lisp - lisp ) symbol->string lisp-load-from-file nil ; f1
: load-forth ( lisp - lisp ) symbol->string included nil ; f1

: maybe-ret ( - t ) \ used to return nil if in return context
  return-context @ if 0 postpone literal stack-push* then t ; f0

: lisp-list-len ( list - n )
  0 swap
  begin
    dup 0<>
  while
    swap 1+ swap cdr
  repeat drop ;

: comp, comp' drop postpone literal
        [comp'] compile, drop compile, ; immediate

: maybe-drop \ compile a call to drop if not in return context
  return-context @ 0= if
    lisp-state @ 0= if
      \ drop
    else
      comp, drop
      stack-drop
    then
  then ;

: check-arg-count ( argc - )
  \ ARGC is the arg count curr-func is being called with
  curr-&rest 0= if
    curr-args 2dup <>
    if ." invalid arg count, expected " . ." got " . cr bye
    else 2drop then
  else drop then ;

: lisp-interpret-special ( lisp func - )
  \ special form or macro
  \ TODO: macros can be seporated from special forms now that
  \       they have seporate type bits
  0 macro-flag !
  dup set-curr-func >r
  cdr ( dup check-arg-count )
  dup 0= if drop then \ drop empty list. TODO: but what about passing nil?
  curr-func @ 0<> if
    curr-args dup 0> if
      curr-&rest if
        1- 0 >r else 1 >r then >r
      begin r@ 0> while
        dup car
        swap cdr r> 1- >r
      repeat
      r> ( count) drop
      r> ( &rest @ flag) if drop then
    else
      drop
    then
  then
  r@ func>int execute
  r> func-macro? if lisp-interpret then ;

: lisp-interpret-function ( lisp func - )
  >r return-context @ >r 1 return-context !
  cdr lisp-interpret-list
  r> return-context !
  r> dup set-curr-func func>int swap check-arg-count
  execute ;

: lisp-compile-function ( lisp func - )
  >r return-context @ 1 return-context !
  swap cdr lisp-compile-list
  swap return-context !
  r> dup set-curr-func
  func>int
  swap
  drop \ check-arg-count
  compile, \ DOING: error here. check this function
  curr-args stack-drop-n
  curr-returns stack-push-n ;

: lisp-interpret-pair ( lisp - lisp?)
  dup car
  lisp-find-symbol-function
  dup func-special? if
    lisp-interpret-special
  else \ function
    lisp-state @ 0= if
      lisp-interpret-function
    else
      lisp-compile-function
    then
    maybe-drop
  then ;

' lisp-interpret-pair interpret-dispatch lisp-pair-tag cells + !
' lisp-interpret-pair compile-dispatch lisp-pair-tag cells + !

: lisp-interpret-number ;

: lisp-compile-number
  dup stack-push
  postpone literal
  maybe-drop ;

' lisp-interpret-number interpret-dispatch lisp-number-tag cells + !
' lisp-compile-number compile-dispatch lisp-number-tag cells + !

: lisp-compile-string
  stack-push*
  postpone literal \ todo: compile it into the dictionary
  maybe-drop ;

' lisp-interpret-number interpret-dispatch lisp-string-tag cells + !
' lisp-compile-string compile-dispatch lisp-string-tag cells + !

: quote
  lisp-state @ 0= if
    car
  else
    car postpone literal
    stack-push*
  then
; special

\ locals-counter counts the locals in the current function
variable locals-counter

: ++locals locals-counter dup @ 1+ swap ! ;

: push-local-name ( symbol - ) stack-push ;

: push-local-names ( list - )
  recursive
  dup 0<> if
    dup car push-local-name
    cdr push-local-names
  else drop then ;

: pop-local-names ( n - )
  recursive
  dup 0> if
    stack-drop
    comp, drop
    1- pop-local-names
  else drop then ;

: list-index ( elem list - index )
  0 >r
  begin
    dup 0<> if
      2dup car equal? 0=
    else 0 then
  while
    cdr r> 1+ >r
  repeat
  if drop r> else r> 2drop -1 then ;

: compile-pick postpone literal comp, pick ;
: compile-dup comp, dup ;
: compile-over comp, over ;
: compile-nip comp, nip ;

: compile-stack-set ( n - )
  2 + cells postpone literal
  comp, sp@ comp, + comp, !  ;

: compile-rot-nip comp, -rot comp, nip ;
: compile-rot-2drop comp, -rot comp, 2drop ;

: compile-stack-getter ( n - )
  dup 0= if
    drop compile-dup
  else
    dup 1 = if
      drop compile-over
    else
      compile-pick
    then then ;

: compile-stack-setter ( n - )
  dup 0= if
    drop compile-nip
  else
    dup 1 = if
      drop compile-rot-nip
    else
      compile-stack-set
    then then ;

: compile-drop-locals ( n - )
  comp, >r
  begin
    dup 0>
  while
    \ TODO: use 2drop when possible
    1- comp, drop
  repeat drop
  comp, r> ;

: drop-locals ( n - )
  dup stack-drop-n
  dup 0= if
    drop
  else
    dup 1 = if
      drop compile-nip
    else
      dup 2 = if
        drop compile-rot-2drop
      else
        compile-drop-locals
      then then then ;

: compile-local-var ( symbol value - )
  ++locals lisp-interpret-r \ compile initial value
  stack-drop stack-push ; \ name the stack location

: var ( sv - v)
  dup car swap cdr car \ symbol value
  lisp-state @ 0= if
    lisp-interpret dup rot
    sym-intern sym>value !
  else
    compile-local-var
  then
  maybe-ret drop
; special

: member ( key list - list )
  begin
    dup 0<> if
      2dup car equal? 0=
    else 0 then
  while
    cdr
  repeat
  nip ; f2

: assoc ( key list - list )
  begin
    2dup car
    dup cons? if
      car equal? if
        car nip exit
      then
    else
      2drop
    then
    cdr dup 0= until
  nip ; f2

: list-len lisp-list-len tag-num ; f1

: str-len ( lisp - lisp ) symbol-nameu @ tag-num ; f1

\ counts the number of let bound names in the current word
\ or other names that have been cleaned up with pop-local-names
\ before the end of the function definition
variable let-bound-names

: handle-args ( arglist - len )
  split-args swap dup push-local-names
  lisp-list-len
  swap
  dup func-&rest!
  dup 0<> if push-local-name
             1+ else drop then
  dup func-args! ;

: compile-def ( lisp - )
  1 return-context !
  dup car
  symbol->string
  start-defun \ create dictionary header

  cdr
  dup car

  handle-args
  \ DOING: handle-args is setting the indirect bit

  dup locals-counter !
  swap cdr start-compile
  lisp-compile-progn \ compile function body
  drop locals-counter @ drop-locals

  0 return-context ! ;

: defun ( lisp - lisp)
  compile-def end-compile
  1 func-returns!
  1 check-stack-depth stack-drop
  end-defun
  nil ; special

: defcode ( lisp - lisp)
  \ postpone def
  compile-def
  0 func-returns!
  \ TODO: temp workaround - discard the return value
  comp, drop
  end-compile
  stack-drop  0 check-stack-depth
  end-defun
  func-special!
  ( immediate) nil ; special

: defmacro ( lisp - lisp)
  compile-def end-compile
  \  comp, set-macro-flag
  1 check-stack-depth stack-drop
  end-defun
  func-macro!
  ( immediate) nil ; special

: lisp-interpret-symbol ( lisp - )
  dup symbol->string function-lookup dup 0= if
    drop dup symbol->string sym-lookup dup 0<> if
      nip sym>value @
    else
      drop lisp-find-symbol-word name>int execute @ \ eval variable
    then
  else
    nip \ function value
  then ;

variable _loop-vars
s" loop-vars" str-intern sym>value _loop-vars !
: loop-vars@ _loop-vars @ @ ;

3 cells allocate throw constant loop-var-addrs
comp' i drop loop-var-addrs !
comp' j drop loop-var-addrs 1 cells + !
comp' k drop loop-var-addrs 2 cells + !

: compile-loop-var ( n - )
  cells loop-var-addrs + @ compile,
  comp, tag-num ;

: lisp-compile-global-sym ( lisp - )
  dup loop-vars@ list-index dup -1 <> if
    nip compile-loop-var
  else
    drop dup
    lisp-find-symbol-function
    dup 0= if
      drop
      sym-intern sym>value postpone literal comp, @ \ variable
    else
      nip postpone literal \ function
    then then ;

: lisp-compile-symbol ( lisp - )
  dup stack @ list-index dup -1 <> if \ local variable reference
    compile-stack-getter drop
  else
    drop lisp-compile-global-sym
  then
  stack-push*
  maybe-drop ;

' lisp-interpret-symbol interpret-dispatch lisp-symbol-tag cells + !
' lisp-compile-symbol compile-dispatch lisp-symbol-tag cells + !

: set-interpret ( symbol value - )
  lisp-interpret dup rot sym-intern sym>value ! ;

: set-compile-global ( symbol value - )
  lisp-interpret-r \ compile value
  stack-drop
  sym-intern sym>value postpone literal
  comp, ! ;

: set-compile-local ( symbol value index - )
  swap lisp-interpret-r
  stack-drop compile-stack-setter
  ( symbol ) drop ;

: set-compile ( symbol value - )
  over stack @ list-index dup -1 <> if
    set-compile-local
  else
    drop set-compile-global
  then
  return-context @ if
    0 postpone literal \ TODO: return value instead
    stack-push*
  then ;

: set ( sv - v)
  dup car swap cdr car \ [ symbol value
  lisp-state @ 0= if
    set-interpret
  else
    set-compile
  then
; special

: let* ( lisp - )   \ todo: interpret
  dup car 0 >r
  begin
    dup 0<>
  while
    dup car
    dup car swap cdr car
    lisp-interpret-r
    stack-drop stack-push \ name it
    r> 1+ >r cdr
  repeat
  drop cdr
  lisp-compile-progn
  r> pop-local-names
; special

: list ( lisp - lisp )
  0 >r
  begin dup 0<>
  while
    dup car lisp-interpret cdr r> 1+ >r
  repeat drop
  0 postpone literal
  r> dup
  begin dup 0>
  while comp, cons 1-
  repeat drop
  stack-drop-n stack-push*
; special

: unlist ( list - e1,e2,...,en )
  recursive
  dup 0<> if
    dup car swap cdr unlist
  else drop then ;

: function ( str - func ) symbol->string function-lookup ; f1
: funcall ( fn args - lisp ) swap >r unlist r> func>int execute ; f2
: func-name ( func - str ) func>string create-string ; f1
: func-arity ( func - num ) func>args ; f1

: boundp ( lisp - lisp ) symbol->string find-name 0<> ; f1

: dis ( func - lisp ) func>int xt-see cr nil ; f1

variable _command-line-args
s" command-line-args" str-intern sym>value
_command-line-args !

: do-process-args ( - )
  recursive
  next-arg 2dup 0 0 d<> if
    symbol-new intern do-process-args cons
  else
    drop
  then ;

: process-args do-process-args _command-line-args @ ! t ; f0

: identity ( x - x ) ; f1

s" xcons" symbol-new intern lisp-pair-tag cells type-names + !
s" integer" symbol-new intern lisp-number-tag cells type-names + !
s" symbol" symbol-new intern lisp-symbol-tag cells type-names + !
s" string" symbol-new intern lisp-string-tag cells type-names + !
s" vector" symbol-new intern lisp-vector-tag cells type-names + !
s" xfunction" symbol-new intern lisp-function-tag cells type-names + !
: type-of ( lisp - lisp ) get-lisp-tag cells type-names + @ ; f1

: make-empty-str ( len - str )
  untag-num dup allocate throw swap create-string ; f1

: make-str ( len init - str )
  untag-num swap untag-num swap
  over dup >r allocate throw dup >r
  rot 0 ?do 2dup c! 1+ loop
  2drop r> r> create-string ; f2

: str-ref ( s i - lisp )
  untag-num swap symbol-namea @ + c@ tag-num ; f2

: str-set ( s i v - lisp )
  untag-num swap untag-num rot symbol-namea @ + c! nil ; f3

: str-move! ( s1 s2 i - lisp )
  \ copy s2 into s1 at offset i
  untag-num rot dup >r
  symbol-namea @ + swap dup symbol-namea @
  swap symbol-nameu @ swap -rot cmove r> ; f3

: stack-to-vec ( x1...xn n - vector )
  dup create-vector \ n v
  dup >r vector-vec @ \ n a
  swap 0 ?do
    dup rot swap ! 1 cells +
  loop
  r> ;

: vector
  0 >r
  begin dup 0<>
  while
    dup car lisp-interpret cdr r> 1+ >r
  repeat
  drop r> dup postpone literal
  comp, stack-to-vec
  stack-drop-n stack-push* ; special

: make-empty-vec ( n - )
  \ Contains unintialized lisp objects. Should ever be printed.
  untag-num create-vector ; f1

: vec-ref ( v i - lisp )
  untag-num cells swap vector-vec @ + @ ; f2

: vec-set ( v i e - lisp )
  swap untag-num cells rot vector-vec @ + ! nil ; f3

: vec-len ( vec - len ) vector-len @ tag-num ; f1

: vec-move! ( v1 v2 i - lisp )
  \ copy v2 into v1 at offset i
  untag-num cells rot dup >r
  vector-vec @ + swap dup vector-vec @
  swap vector-len @ cells swap -rot cmove r> ; f3

variable saved-stack-depth
: stack-save ( - )
  stack-depth @ saved-stack-depth do-list-push ;
: stack-reset ( - )
  stack-depth @ saved-stack-depth @ car - stack-drop-n ;
: stack-restore ( - )
  stack-reset saved-stack-depth do-list-pop drop ;

variable if-stack
variable while-stack

: if-push ( n - ) if-stack do-list-push ;
: if-pop ( - n ) if-stack do-list-pop ;
: while-push ( n - ) while-stack do-list-push ;
: while-pop ( - n ) while-stack do-list-pop ;

: if-push3 if-push if-push if-push ;
: if-pop3 if-pop if-pop if-pop ;
: while-push3 while-push while-push while-push ;
: while-pop3 while-pop while-pop while-pop ;

: if, stack-drop stack-save postpone if if-push3 t ; f0
: else, stack-reset if-pop3 postpone else if-push3 t ; f0
: do-then,
  stack-restore if-pop3 postpone then
  return-context @ if stack-push* then ;
: then, comp, do-then, maybe-ret drop ; special

: begin, postpone begin while-push3 t ; f0
: while,
  stack-drop while-pop3 postpone while while-push3 while-push3 t ; f0
: repeat, while-pop3 while-pop3 postpone repeat t ; f0

: do,
  stack-drop stack-drop postpone ?do while-push3 t ; f0
: loop,
  while-pop3 postpone loop t ; f0

\ return-lit used in defcode to return a value from the form
: return-lit ( n - )
  return-context @ if postpone literal else drop then t ; f1
: lit, ( n - ) stack-push* postpone literal t ; f1
: untag-lit, ( n - ) untag-num lit, ; f1
: untag-num, ( - n ) comp, untag-num t ; f0

: stack-push-n ( n - t ) untag-num stack-push-n t ; f0
: stack-drop-n ( n - t ) untag-num stack-drop-n t ; f0

: 1+ ( n - n ) 2 + ; f1
: 1- ( n - n ) 2 - ; f1
: - ( nn - n ) untag-num swap untag-num swap - tag-num ; f2
: * ( nn - n ) untag-num swap untag-num * tag-num ; f2
: / ( nn - n ) untag-num swap untag-num swap / tag-num ; f2
: + ( nn - n ) untag-num swap untag-num + tag-num ; f2
: zero? 0= ; f1
: not 0=  ; f1

: cr cr t ; f0
: exit bye ; f0
: utime utime drop tag-num ; f0
: sleep-ms ( ms - ) untag-num ms t ; f1
: here here tag-num ; f0
: list-index list-index tag-num ; f2
\ : words words nil ; f0

variable lisp-latest-marked
: env-mark symbol->string nextname marker
           lisp-latest @ lisp-latest-marked !
           nil ; f1
: env-revert symbol->string find-name name>int execute
             lisp-latest-marked @ lisp-latest !
             nil ; f1

: print-stack .s nil ; f0

\ TODO: need to declare built in words as lisp words
\ temp fix:
: = = ; f2
: > > ; f2
: < < ; f2
: <= <= ; f2
: >= >= ; f2
: min min ; f2
: max max ; f2
: bye bye ; f0
: quit quit ; f0
\ \\\\\\\\\\\\\\\

variable nil
0 nil !

\ : dump ( lisp - lisp ) symbol->string dump-fi lisp-true ; f1

variable forth-init-time
variable forth-dict-space
utime start-time @ tag-num - forth-init-time !
here start-here @ tag-num - forth-dict-space !

s" raillisp.lsp" lisp-load-from-file drop
