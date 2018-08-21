\ -*- forth -*-

\ utilities

0 warnings !
variable start-time
variable start-here
utime drop start-time !
here start-here !

variable exit-on-error
1 exit-on-error !

: maybe-bye
  exit-on-error @ if 1 throw then ;

: string-new ( a u -- a u )
  dup rot over allocate drop
  dup >r rot cmove r> swap ;

0 constant lisp-pair-tag
1 constant lisp-number-tag
2 constant lisp-symbol-tag
3 constant lisp-string-tag
4 constant lisp-vector-tag
5 constant lisp-max-tag

lisp-max-tag cells allocate throw constant display-dispatch
lisp-max-tag cells allocate throw constant equal?-dispatch
lisp-max-tag cells allocate throw constant interpret-dispatch
lisp-max-tag cells allocate throw constant compile-dispatch

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
2 cells constant sizeof-pair

\ : symbol-tag 0 + ;
: symbol-namea [ 1 cells ] literal + ;
: symbol-nameu [ 2 cells ] literal + ;
2 cells constant sizeof-symbol

\ : vector-tag 0 + ;
: vector-tag [ 1 cells ] literal + ;
: vector-len [ 2 cells ] literal + ;
: vector-vec [ 3 cells ] literal + ;
3 cells constant sizeof-vector

\ function meta data
: func-xt ;
: func-xt [ 1 cells ] literal + ;
: func-args [ 2 cells ] literal + ;
: func-locals [ 3 cells ] literal + ;
: func-&rest [ 4 cells ] literal + ;
: func-returns [ 5 cells ] literal + ;
: func-next [ 6 cells ] literal + ;
7 cells constant sizeof-func

variable function-first
variable curr-func

: function-lookup ( xt -- function )
  function-first @
  begin
    dup 0<>
  while
    2dup func-xt @
    = if nip exit then
    func-next @
  repeat
  2drop 0 ;

: find-function ( xt - ) function-lookup curr-func ! ;
: find-function-check ( xt - )
  find-function curr-func @ 0= if ." invalid function" cr bye then ;

: curr-args ( - n ) curr-func @ dup 0<> if func-args @ then ;
: curr-returns ( - n ) curr-func @ dup 0<> if func-returns @ then ;
: curr-&rest ( - x ) curr-func @ dup 0<> if func-&rest @ then ;

: check-alloc dup 1 and if ." lsb bit is set" 1 throw then ;

variable stack-counter

: new-function ( - )
  0 stack-counter !
  sizeof-func allocate throw check-alloc
  dup func-next function-first @ swap !
  dup func-returns 1 swap !
  function-first ! ;

: set-func-xt ( - ) latest name>int function-first @ func-xt ! ;
: set-func-args ( n - ) function-first @ func-args ! ;
: set-func-&rest ( x - ) function-first @ func-&rest ! ;
: set-func-returns ( x - ) function-first @ func-returns ! ;

: func ( num-args num-ret - )   \ declare a lisp function
  new-function set-func-xt set-func-returns set-func-args ;

: f0 0 1 func ;
: f1 1 1 func ;
: f2 2 1 func ;
: f3 3 1 func ;
: fn -1 1 func 1 set-func-&rest ;

: make-cons ( car cdr -- lisp )
  sizeof-pair allocate throw check-alloc >r
  r@ ( pair-tag) lisp-pair-tag swap !
  r@ pair-cdr !
  r@ pair-car !
  r> ;

: cons make-cons ; f2

: car ( pair -- lisp )
  dup 0<> if pair-car @ then ; f1

: cdr ( pair -- lisp )
  dup 0<> if pair-cdr @ then ; f1

: <<1 1 lshift ;
: >>1 1 rshift ;

: make-number ( num -- lisp )
  <<1 1 or ;

: make-symbol ( namea nameu -- lisp )
  sizeof-symbol allocate throw check-alloc >r
  r@ ( symbol-tag) lisp-symbol-tag swap !
  r@ symbol-nameu !
  r@ symbol-namea !
  r> ;

: symbol-new ( namea nameu -- lisp )
  string-new make-symbol ;

: symbol->string ( lisp -- namea nameu )
  dup symbol-namea @ swap symbol-nameu @ ;

: make-string ( namea nameu -- lisp )
  make-symbol
  dup ( symbol-tag) lisp-string-tag swap ! ;

: make-vector ( length -- lisp )
  sizeof-vector allocate throw check-alloc >r
  r@ vector-tag lisp-vector-tag swap !
  dup r@ vector-len !
  allocate throw r@ vector-vec ! r> ;

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

: type-of get-lisp-tag make-number ; f1 \ todo: return symbol
: number? 1 and ; f1
: cons? get-lisp-tag lisp-pair-tag  = ; f2
: symbol? get-lisp-tag lisp-symbol-tag = ; f1
: string? get-lisp-tag lisp-string-tag =  ; f1
: vector? get-lisp-tag lisp-vector-tag  = ; f1

-1 constant lisp-true
variable t f0
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

: string-equal? ( lisp1 lisp2 -- lisp )
  symbol->string rot symbol->string
  compare 0= if
    lisp-true
  else
    nil
  then ; f2

: symbol-equal? string-equal? ;  f2 \ TODO: symbol interning

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

' string-equal? equal?-dispatch lisp-symbol-tag cells + !
' string-equal? equal?-dispatch lisp-string-tag cells + !
' cons-equal? equal?-dispatch lisp-pair-tag cells + !

s" &rest" symbol-new intern
variable &rest f0
&rest !

: get-vararg
  recursive ( arglist - vararg)
  \ return the vararg symbol and remove from arglist
  dup 0<> if
    dup cdr 0<> if
      dup cdr car &rest @ symbol-equal? if
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
    dup car &rest @ symbol-equal? if
      0 swap cdr car
    else
      dup get-vararg
    then
  else
    dup
  then ;

: lisp-display ( lisp -- )
  dup 0= over -1 = or if
    .
  else
    dup get-lisp-tag
    cells display-dispatch + @ execute
  then ;

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

: lisp-display-number ( lisp -- )
  >>1 . ;

' lisp-display-number display-dispatch lisp-number-tag cells + !

: lisp-display-symbol ( lisp -- )
  symbol->string type ;

' lisp-display-symbol display-dispatch lisp-symbol-tag cells + !

: lisp-display-string ( lisp -- )
  ( [char] " dup emit )
  swap symbol->string
  type ( emit ) ;

' lisp-display-string display-dispatch lisp-string-tag cells + !

: do-display-vector ( vec len -- )
  recursive
  1- dup 0< if
    2dup + @ lisp-display do-display-vector
  else
    2drop
  then ;

: lisp-display-vector ( lisp -- )
  [char] [ emit
  dup vector-vec @ swap vector-len @ do-display-vector
  [char] ] emit ;

' lisp-display-vector display-dispatch lisp-vector-tag cells + !

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

\ return-lit used in defcode to return a value from the form
: return-lit ( n - )
  return-context @ if postpone literal else drop then t ; f1


\ STACK is a list representing the current stack of the compiled program.
\ symbols in this list represent named stack positons (locals variables).
\ anonymous stack entries are nil.
\ --
\ eventually STACK will replace the LOCALS list. but it
\ it will exist alongside it until the new compilation method works.
variable stack
0 stack !
variable stack-depth
0 stack-depth !

: stack-print stack @ lisp-display cr ;

: stack-push ( v - )
  stack-depth dup @ 1+ swap !
  stack @ cons stack ! ;

: stack-push*
  \ pushes a unique number onto the parameter
  stack-counter dup @ 1+ dup make-number stack-push swap ! ;

: stack-pop ( - )
  stack-depth dup @ dup 0= if
  then
  1- swap !
  stack dup @ cdr swap !
;

: stack-pop-n ( n - )
  begin dup 0 > while
    1- stack-pop
  repeat drop ;

: stack-push-n ( n - )
  begin dup while
    1- stack-push*
  repeat drop ;

: check-stack-depth ( n - )
  dup stack-depth @ <> if
    ." ERROR: function left " stack-depth @ .
    ." items on the stack, expected " . cr
    ."   stack: " stack-print cr bye
  then drop ;

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
  \ used when the lisp being compiled consumes the return result
  1 rcontext{ lisp-interpret }rcontext stack-pop ;
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

: special immediate ;
: special?
  cell+ @ immediate-mask and 0<> ;

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

variable frame
: ndrop ( n - )
  begin dup 0> while swap drop 1- repeat drop ;
: stack-space ( n - ) \ adds n things to the stack
  begin dup 0> while dup swap 1- repeat drop ;

: get-local ( n - v ) frame @ swap - @ ;
: set-local ( v n - ) frame @ swap - ! ;

: next-frame (  nargs nlocals - nlocals... nargs+nlocals old-frame magic )
  swap over + >r stack-space r>
  dup 1+ cells sp@ + frame dup @ -rot !
  1112111 \ XXX magic number to help catch stack corruption
;

: prev-frame ( locals... nlocals old-frame magic ret - ret)
  >r
  1112111 <>
  if ." error: magic frame number not found" cr .s 1 throw then
  frame ! ndrop r> ;

\ the reader

variable paren-count
variable stdin-lastchar
variable stdin-unread
variable read-from-string

: check-char ( c - c )
  \ Returns 0 if done reading, else c
  \ Used when reading from input streams
  dup 10 = if \ RET
    paren-count @ 0 = if
      drop 0 exit
    else
      ." :  "
    then
  else
    dup [char] ( = if
      paren-count dup @ 1+ swap !
    else
      dup [char] ) = if
        paren-count dup @ 1- swap !
      then
    then
  then ;

: lisp-char-from-input
  stdin-unread @ if
    0 stdin-unread !
    stdin-lastchar @
  else
    xkey check-char
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

: lisp-skip
  lisp-skip-ws
  lisp-read-char
  59 = if \ 59 = ;
    lisp-skip-line
  else
    lisp-unread-char
  then
  lisp-skip-ws ;

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

: lisp-read-list
  recursive ( e a -- e a lisp )
  lisp-skip lisp-read-char
  dup [char] ) = swap 0 = or if
    0
  else
    lisp-unread-char lisp-read-lisp >r lisp-read-list r> swap make-cons
  then ;

: string->number ( lisp - lisp )
  symbol->string s>number? if drop make-number else nil then ; f1

: lisp-read-symbol ( e a -- e a lisp )
  lisp-read-token 2dup s>number? if
    drop make-number nip nip
  else
    drop drop string-new make-symbol
  then ;

: lisp-read-quote ( e a -- e a lisp )
  lisp-read-lisp nil make-cons
  s" quote" symbol-new swap make-cons ;

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
  string-new make-string ;

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
        [char] " = if
          lisp-read-string
        else
	  lisp-unread-char lisp-read-symbol
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

: lisp-read-from-input
  0 read-from-string !
  -1 stdin-lastchar !
  0 stdin-unread !
  0 paren-count !
  ." > " lisp-read-lisp
;

: maybe-ret ( - t ) \ used to return nil if in return context
  return-context @ if 0 postpone literal stack-push* then t ; f0

: lisp-list-length ( list - n )
  0 swap
  begin
    dup 0<>
  while
    swap 1+ swap cdr
  repeat drop ;

: maybe-drop \ compile a call to drop if not in return context
  return-context @ 0= if
    lisp-state @ 0= if
      \ drop
    else
      [comp'] drop drop compile,
      stack-pop
    then
  then ;

: check-arg-count ( argc - )
  \ ARGC is the arg count curr-func is being called with
  curr-&rest 0= if
    curr-args 2dup <>
    if ." invalid arg count, expected " . ." got " . cr bye
    else 2drop then
  else drop then ;

: lisp-interpret-special ( lisp word - )
  \ special form or macro
  0 macro-flag !
  name>int dup find-function >r
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
  r> execute
  macro-flag @ if lisp-interpret then
  \ can't call 'maybe-drop' for special forms here
  \ because special forms defined in forth don't return anything.
  \ Instead the forms defined in lisp are compiled with
  \ a call to maybe-drop at the end of their definition.
;

: lisp-interpret-function ( lisp word - )
  >r return-context @ >r 1 return-context !
  cdr lisp-interpret-list
  r> return-context !
  r> name>int
  dup find-function-check swap check-arg-count
  execute ;

: lisp-compile-function ( lisp word - )
  >r return-context @ 1 return-context !
  swap cdr lisp-compile-list
  swap return-context !
  r> name>int dup find-function-check swap
  check-arg-count
  compile,
  curr-args stack-pop-n
  curr-returns stack-push-n ;

: lisp-interpret-pair ( lisp - lisp?)
  dup car lisp-find-symbol-word
  dup special? if
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
  \ 444 make-number stack-push
  dup stack-push
  postpone literal
;

' lisp-interpret-number interpret-dispatch lisp-number-tag cells + !
' lisp-compile-number compile-dispatch lisp-number-tag cells + !

: lisp-compile-string
  stack-push*
  postpone literal \ todo: compile it into the dictionary
;

' lisp-interpret-number interpret-dispatch lisp-string-tag cells + !
' lisp-compile-string compile-dispatch lisp-string-tag cells + !

( ( )( )( ) ( lisp words ) ( )( )( )

: quote
  lisp-state @ 0= if
    car
  else
    car postpone literal
    stack-push*
  then
; special

\ locals-counter count the locals in the current function
variable locals-counter
\ locals is an alist of (name . index) pairs.
\  index is a forth integer so this list cannot be printed as lisp
variable locals nil locals !

: ++locals
  locals-counter dup @ 1+ swap ! ;

\ next-local-index is the offset from the frame pointer
variable next-local-index 0 cells next-local-index !
: ++local-index next-local-index dup @ 1 cells + swap ! ;
: --local-index next-local-index dup @ 1 cells - swap ! ;

: push-local-name ( symbol - )
  dup stack-push
  next-local-index @ cons
  locals @ cons locals !
  ++local-index ;

: push-local-names ( list - )
  recursive
  dup 0<> if
    dup car push-local-name
    cdr push-local-names
  else drop then ;

: pop-local-names ( n - )
  recursive
  dup 0> if
    stack-pop
    [comp'] drop drop compile,
    locals dup @ cdr swap !
    --local-index
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

: compile-pick postpone literal [comp'] pick drop compile, ;
: compile-dup [comp'] dup drop compile, ;
: compile-over [comp'] over drop compile, ;
: 2pick 2 compile-pick ;
: 3pick 3 compile-pick ;
: 4pick 4 compile-pick ;
: 5pick 5 compile-pick ;
: 6pick 6 compile-pick ;
: 7pick 7 compile-pick ;
: 8pick 8 compile-pick ;
: 9pick 9 compile-pick ;

: compile-stack-set ( n - )
  3 + cells postpone literal
  [comp'] sp@ drop compile,
  [comp'] ! drop compile, ;
: compile-nip [comp'] nip drop compile, ;
: 1set ( a x v - v x )
  [comp'] -rot drop compile,
  [comp'] nip drop compile, ;
: 2set 3 compile-stack-set ;
: 3set 4 compile-stack-set ;
: 4set 5 compile-stack-set ;
: 5set 6 compile-stack-set ;
: 6set 7 compile-stack-set ;
: 7set 8 compile-stack-set ;
: 8set 9 compile-stack-set ;
: 9set 10 compile-stack-set ;

10 cells allocate throw constant stack-getters
10 cells allocate throw constant stack-setters

: stack-getter cells stack-getters + ! ;
: stack-setter cells stack-setters + ! ;

' compile-dup 0 stack-getter
' compile-over 1 stack-getter
' 2pick 2 stack-getter
' 3pick 3 stack-getter
' 4pick 4 stack-getter
' 5pick 5 stack-getter
' 6pick 6 stack-getter
' 7pick 7 stack-getter
' 8pick 8 stack-getter
' 9pick 9 stack-getter

' compile-nip 0 stack-setter
' 1set 1 stack-setter
' 2set 2 stack-setter
' 3set 3 stack-setter
' 4set 4 stack-setter
' 5set 5 stack-setter
' 6set 6 stack-setter
' 7set 7 stack-setter
' 8set 8 stack-setter
' 9set 9 stack-setter

: compile-local-var ( symbol value - )
  lisp-interpret-r \ compile initial value
  ++locals push-local-name
  next-local-index @ 1 cells - postpone literal
  [comp'] set-local drop compile, ;

: compile-local-var-ng ( symbol value - )
  ++locals lisp-interpret-r \ compile initial value
  stack-pop stack-push ; \ name the stack location

: var ( sv - v)
  dup car swap cdr car \ symbol value
  lisp-state @ 0= if
    lisp-interpret dup rot symbol->string
    nextname create ,
  else
    compile-local-var-ng
  then
; special

: lisp-create ( ua - ) \ create new dictionary entry
  ( gforth) nextname header reveal docol: cfa,
  postpone recursive ;

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

: list-length lisp-list-length make-number ; f1

: string-length ( lisp - lisp ) symbol-nameu @ make-number ; f1

\ counts the number of let bound names in the current word
\ or other names that have been cleaned up with pop-local-names
\ before the end of the function definition
variable let-bound-names

: handle-args ( arglist - len )
  split-args swap dup push-local-names
  lisp-list-length swap dup set-func-&rest
  dup 0<> if push-local-name 1+ else drop then
  dup set-func-args ;

: drop-locals ( n - )
  [comp'] >r drop compile,
  begin
    dup 0>
  while
    1- [comp'] drop drop compile,
    stack-pop
  repeat drop
  [comp'] r> drop compile, ;

: compile-def ( lisp - )
  \ lisp word format:
  \  num-args num-locals next-frame [body...] prev-frame exit
  new-function
  1 return-context !
  0 let-bound-names !
  dup car symbol->string
  lisp-create \ create dictionary header
  set-func-xt
  cdr dup car handle-args
  dup locals-counter !
\  dup postpone literal \ lisp word: arg length
\  here 1 cells + locals-counter ! \ set location of locals count
\  0 postpone literal \ lisp word: locals count
\  [comp'] next-frame drop compile, \ lisp word: start frame
  swap cdr start-compile lisp-compile-progn \ compile function body
\  locals-counter @ @ + \ nlocals+nargs
  \  let-bound-names @ -
  drop locals-counter @
  drop-locals
\  [comp'] prev-frame drop compile, \ lisp word: end frame
  0 return-context !
;

: def ( lisp - lisp)
  compile-def end-compile
  1 check-stack-depth stack-pop
  postpone exit
  nil ; special

: defcode ( lisp - lisp)
  \  postpone def
  compile-def
  \ TODO: temp workaround - discard the return value
  [comp'] drop drop compile,
  end-compile
  stack-pop 0 check-stack-depth
  postpone exit
  immediate nil ; special

: defmacro ( lisp - lisp)
  compile-def end-compile
  [comp'] set-macro-flag drop compile,
  1 check-stack-depth stack-pop
  postpone exit
  immediate nil ; special

: lisp-interpret-symbol ( lisp - )
  lisp-find-symbol-word name>int execute @ ;

: lisp-compile-symbol ( lisp - )
  ." lisp-compile-symbol:" dup lisp-display cr
  dup locals @ assoc dup if \ local variable reference
    cdr postpone literal
    [comp'] get-local drop compile,
    drop
  else \ compile dicationary variable lookup
    drop lisp-find-symbol-word name>int compile,
    [comp'] @ drop compile,
  then ;

: lisp-compile-symbol-ng ( lisp - ) \ todo; rename: symbol ref
  dup stack @ list-index dup -1 <> if \ local variable reference
    cells stack-getters + @ execute
    drop
  else \ compile dicationary variable lookup
    drop lisp-find-symbol-word name>int compile,
    [comp'] @ drop compile,
  then
  stack-push* ;

' lisp-interpret-symbol interpret-dispatch lisp-symbol-tag cells + !
' lisp-compile-symbol-ng compile-dispatch lisp-symbol-tag cells + !

: set-interpret ( symbol value - )
  lisp-interpret dup rot
  lisp-find-symbol-word name>int execute ! ;

: set-compile-local ( symbol value indexcons - )
  swap lisp-interpret-r
  cdr postpone literal
  [comp'] set-local drop compile,
  drop ; \ symbol

: set-compile-local-ng ( symbol value indexcons - )
  drop
  swap lisp-interpret-r
  cdr postpone literal
  [comp'] set-local drop compile,
  drop ; \ symbol

: set-compile-global ( symbol value - )
  lisp-interpret-r \ compile value
  lisp-find-symbol-word name>int compile,
  [comp'] ! drop compile, ;

: set-compile ( symbol value - )
  over locals @ assoc dup if
    set-compile-local
    drop \ symbol
  else
    drop set-compile-global
  then
  return-context @ if
    0 postpone literal \ TODO: return value instead
  then ;

: set-compile-local-ng ( symbol value index - )
  swap lisp-interpret-r
  cells stack-setters + @ execute
  ( symbol ) drop ;

: set-compile-ng ( symbol value - )
  over stack @ list-index dup -1 <> if
    set-compile-local-ng
  else
    drop set-compile-global
  then
  return-context @ if
    0 postpone literal \ TODO: return value instead
  then ;

: set ( sv - v)
  dup car swap cdr car \ [ symbol value
  lisp-state @ 0= if
    set-interpret
  else
    set-compile-ng
  then
; special

: let* ( lisp - )   \ todo: interpret
  dup car 0 >r
  begin
    dup 0<>
  while
    dup car
    dup car swap cdr car
    \ compile-local-var-ng
    lisp-interpret-r stack-pop stack-push
    r> 1+ >r cdr
  repeat
  drop cdr lisp-compile-progn
  r> dup pop-local-names
  let-bound-names dup @ rot + swap !
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
  while [comp'] cons drop compile, 1-
  repeat drop
  stack-pop-n stack-push*
; special

variable saved-stack-depth
: stack-save ( - t ) stack-depth @ saved-stack-depth ! ;
: stack-restore ( - t )
  stack-depth @ saved-stack-depth @ - stack-pop-n ;

: do-if, stack-save postpone if ;
: if, 3 stack-push-n [comp'] do-if, drop compile, ; special
: else, stack-restore postpone else t ; f0
: do-then,
  stack-restore
  stack-push* \ return result
  postpone then  ;
: then,
  3 stack-pop-n
  [comp'] do-then, drop compile,
  maybe-ret drop ; special

: do-begin, postpone begin ;
: begin, 3 stack-push-n [comp'] do-begin, drop compile, ; special
: do-while, postpone while ;
: while, 3 stack-push-n [comp'] do-while, drop compile, ; special
: do-repeat, postpone repeat ; special
: repeat, 6 stack-pop-n [comp'] do-repeat, drop compile, ; special
: lit, postpone literal t ; f0
: drop, [comp'] drop drop compile, t ; f0

: stack-push-n ( n - t ) >>1 stack-push-n t ; f0
: stack-pop-n ( n - t ) >>1 stack-pop-n t ; f0


: 1+ ( n - n ) 2 + ; f1
: 1- ( n - n ) 2 - ; f1
: + ( nn - n ) >>1 swap >>1 + make-number ; f2
: - ( nn - n ) >>1 swap >>1 swap - make-number ; f2
: * ( nn - n ) >>1 swap >>1 * make-number ; f2
: / ( nn - n ) >>1 swap >>1 swap / make-number ; f2

: zero? 0= ; f1
: not 0=  ; f1

: cr cr t ; f0
: exit bye ; f0
: utime utime drop make-number ; f0
: sleep-ms ( ms - ) >>1 ms t ; f1
: here here make-number ; f0
: list-index list-index make-number ; f2

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

variable nil f0
0 nil !

variable forth-init-time f0
variable forth-dict-space f0
utime start-time @ make-number - forth-init-time !
here start-here @ make-number - forth-dict-space !

s" raillisp.lsp" lisp-load-from-file drop
