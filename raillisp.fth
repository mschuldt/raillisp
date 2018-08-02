\ -*- forth -*-

\ utilities

0 warnings !

variable exit-on-error
1 exit-on-error !

: maybe-bye
  exit-on-error @ if 1 throw then ;

: string-new ( a u -- a u )
  dup rot over allocate drop
  dup >r rot cmove r> swap ;

: string>num ( a u -- n )
  0 swap 0 ?do
    10 * over i + c@ [char] 0 - +
  loop
  nip ;

\ function meta data
struct
cell% field func-xt
cell% field func-args
cell% field func-locals
cell% field func-&rest
cell% field func-next
end-struct func

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
: curr-args ( - n ) curr-func @ dup 0<> if func-args @ then ;
: curr-&rest ( - x ) curr-func @ dup 0<> if func-&rest @ then ;

: check-alloc dup 1 and if ." lsb bit is set" 1 throw then ;
: new-function
  func %allocate throw check-alloc
  dup func-next function-first @ swap !
  function-first ! ;

\ todo: latest won't work for recursive functions
: set-func-xt ( - ) latest name>int function-first @ func-xt ! ;
: set-func-args ( n - ) function-first @ func-args ! ;
: set-func-&rest ( x - ) function-first @ func-&rest ! ;

\ lisp interpreter

0 constant lisp-pair-tag
1 constant lisp-number-tag
2 constant lisp-symbol-tag
3 constant lisp-string-tag
4 constant lisp-vector-tag
5 constant lisp-max-tag

lisp-max-tag cells allocate throw constant display-dispatch
lisp-max-tag cells allocate throw constant eq?-dispatch
lisp-max-tag cells allocate throw constant interpret-dispatch
lisp-max-tag cells allocate throw constant compile-dispatch

struct
cell% field lisp-tag
end-struct lisp

struct
cell% field pair-tag
cell% field pair-car
cell% field pair-cdr
end-struct lisp-pair

struct
cell% field symbol-tag
cell% field symbol-namea
cell% field symbol-nameu
end-struct lisp-symbol

struct
cell% field vector-tag
cell% field vector-len
cell% field vector-vec
end-struct lisp-vector

: get-lisp-tag ( lisp - type )
  dup 1 and if
    drop lisp-number-tag
  else
    lisp-tag @
  then ;

: make-cons ( car cdr -- lisp )
  lisp-pair %allocate throw check-alloc >r
  r@ pair-tag lisp-pair-tag swap !
  r@ pair-cdr !
  r@ pair-car !
  r> ;

: car ( pair -- lisp )
  dup 0<> if pair-car @ then ;

: cdr ( pair -- lisp )
  dup 0<> if pair-cdr @ then ;

: <<1 1 lshift ;
: >>1 1 rshift ;

: make-number ( num -- lisp )
  <<1 1 or ;

: make-symbol ( namea nameu -- lisp )
  lisp-symbol %allocate throw check-alloc >r
  r@ symbol-tag lisp-symbol-tag swap !
  r@ symbol-nameu !
  r@ symbol-namea !
  r> ;

: symbol-new ( namea nameu -- lisp )
  string-new make-symbol ;

: symbol->string ( lisp -- namea nameu )
  dup symbol-namea @ swap symbol-nameu @ ;

: make-string ( namea nameu -- lisp )
  make-symbol
  dup symbol-tag lisp-string-tag swap ! ;

: make-vector ( length -- lisp )
  lisp-vector %allocate throw check-alloc >r
  r@ vector-tag lisp-vector-tag swap !
  dup r@ vector-len !
  allocate throw r@ vector-vec ! r> ;

0 0 make-cons constant lisp-true
variable t lisp-true t !

: lisp-eq?-symbol ( lisp1 lisp2 -- lisp )
  symbol->string rot symbol->string
  compare 0= if
    lisp-true
  else
    nil
  then ;

s" &rest" symbol-new constant &rest

: get-vararg
  recursive ( arglist - vararg)
  \ return the vararg symbol and remove from arglist
  dup 0<> if
    dup cdr 0<> if
      dup cdr car &rest lisp-eq?-symbol if
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
    dup car &rest lisp-eq?-symbol if
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
    dup get-lisp-tag cells display-dispatch + @ execute
  then ;

: print ( lisp -- lisp ) dup lisp-display ;

: lisp-display-pair ( lisp -- )
  dup lisp-true = if
    ." t" drop exit
  then
  [char] ( emit ( 32 emit)
  begin
    dup car lisp-display 32 emit
    cdr
    dup 0<> if
      dup get-lisp-tag lisp-pair-tag <> if
        [char] . emit ( 32  emit) lisp-display 0
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
  [char] " dup emit
  swap symbol->string
  type emit ;

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

: eq? ( lisp lisp - lisp )
  2dup = if
    2drop lisp-true
  else
    2dup 0= swap 0= or if
      2drop nil
    else
      2dup get-lisp-tag swap get-lisp-tag <> if
        2drop nil
      else
        dup get-lisp-tag cells eq?-dispatch + @ execute
      then
    then
  then ;

: cons-not-eq 2drop nil ;
' cons-not-eq eq?-dispatch lisp-pair-tag cells + !

: lisp-eq?-number ( lisp lisp -- lisp )
  = if
    lisp-true
  else
    nil
  then ;

' lisp-eq?-number eq?-dispatch lisp-number-tag cells + !

' lisp-eq?-symbol eq?-dispatch lisp-symbol-tag cells + !
' lisp-eq?-symbol eq?-dispatch lisp-string-tag cells + !

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

: maybe-ret ( - t ) \ used to return nil if in return context
  return-context @ if 0 postpone literal then t ;

: lisp-interpret ( lisp - lisp? )
  dup 0<> if
    dup get-lisp-tag cells
    lisp-state @
    0= if interpret-dispatch else compile-dispatch then
    + @ execute
  then ;

: lisp-interpret-list ( lisp - a1...an )
  begin
    dup 0<>
  while
    dup car lisp-interpret
    swap cdr
  repeat
  drop ;

: lisp-compile-list ( lisp - )
  recursive
  dup 0<> if
    dup car lisp-interpret
    cdr lisp-compile-list dup
  then drop ;

: lisp-interpret-r ( lisp - lisp?) 1 rcontext{ lisp-interpret }rcontext ;
: lisp-compile-list-nr 0 rcontext{ lisp-compile-list }rcontext ;

: lisp-compile-progn ( lisp - )
  return-context @ swap
  0 return-context !
  begin
    dup 0<>
  while
    dup cdr 0= if
      swap return-context !
    then
    dup car lisp-interpret cdr
  repeat
  drop ;

: special immediate ;
: special?
  cell+ @ immediate-mask and 0<> ;

: compile lisp-interpret t ;
: compile-r lisp-interpret-r t ;
: compile-list lisp-compile-list t ;
: compile-list-nr lisp-compile-list-nr t ;

: compile-progn lisp-compile-progn t ;
: progn lisp-compile-progn ; special


: lisp-find-symbol-word ( lisp - word)
  symbol->string
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

: lisp-read-number ( e a -- e a lisp )
  lisp-read-token string>num make-number ;

: lisp-read-symbol ( e a -- e a lisp )
  lisp-read-token string-new make-symbol ;

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
      dup [char] 0 >= over [char] 9 <= and if
	drop lisp-unread-char lisp-read-number
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
    then
  then ;

: lisp-interpret-pair ( lisp - lisp?)
  dup car lisp-find-symbol-word
  dup special? if \ special form or macro
    0 macro-flag !
    name>int dup find-function >r
    cdr ( dup check-arg-count )
    curr-func @ 0<> if
      curr-args dup 0> if
        curr-&rest if
          1- 0 >r else 1 >r then >r
        begin r@ 0> while
          dup car
          swap cdr r> 1- >r
        repeat
        r> ( count) drop
        r> ( &rest flag) if drop then
      else
        drop
      then
    then
    r> execute
    macro-flag @ if lisp-interpret then
  else \ function
    lisp-state @ 0= if \ interpet
      >r
      return-context @ >r 1 return-context !
      cdr lisp-interpret-list
      r> return-context !
      r> name>int execute
    else  \ compile
      >r
      return-context @ 1 return-context !
      swap cdr lisp-compile-list
      return-context !
      r> name>int compile,
    then
    maybe-drop
  then ;

' lisp-interpret-pair interpret-dispatch lisp-pair-tag cells + !
' lisp-interpret-pair compile-dispatch lisp-pair-tag cells + !

: lisp-interpret-number ;

: lisp-compile-number
  \ TODO: need a better/faster number representation
  postpone literal
;

' lisp-interpret-number interpret-dispatch lisp-number-tag cells + !
' lisp-compile-number compile-dispatch lisp-number-tag cells + !

: lisp-compile-string
  postpone literal \ todo: compile it into the dictionary
;

' lisp-interpret-number interpret-dispatch lisp-string-tag cells + !
' lisp-compile-string compile-dispatch lisp-string-tag cells + !

( ( )( )( ) ( lisp words ) ( )( )( )

: cons make-cons ;

: quote
  lisp-state @ 0= if
    car
  else
    car postpone literal
  then
; special

\ locals-counter is a pointer to the locals count in
\ the word currently being compiled
variable locals-counter
\ locals is an alist of (name . index) pairs.
\  index is a forth integer so this list cannot be printed as lisp
variable locals nil locals !
: ++locals locals-counter @ dup @ 1+ swap ! ;
\ next-local-index is the offset from the frame pointer
variable next-local-index 0 cells next-local-index !
: ++local-index next-local-index dup @ 1 cells + swap ! ;
: --local-index next-local-index dup @ 1 cells - swap ! ;

: push-local-name ( symbol - )
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
    locals dup @ cdr swap !
    --local-index
    1- pop-local-names
  else drop then ;

: compile-local-var ( symbol value - )
  lisp-interpret-r \ compile initial value
  ++locals push-local-name
  next-local-index @ 1 cells - postpone literal
  [comp'] set-local drop compile, ;

: var ( sv - v)
  dup car swap cdr car \ symbol value
  lisp-state @ 0= if
    lisp-interpret dup rot symbol->string
    nextname create ,
  else
    compile-local-var
  then
; special

: lisp-create ( ua - ) \ create new dictionary entry
  ( gforth) nextname header reveal docol: cfa, ;

: member ( key list - list )
  begin
    dup 0<> if
      2dup car eq? 0=
    else 0 then
  while
    cdr
  repeat
  nip ;

: consp dup 0<> if get-lisp-tag lisp-pair-tag = then ;

: assoc ( key list - list )
  begin
    2dup car
    dup consp if
      car eq? if
        car nip exit
      then
    else
      2drop
    then
    cdr dup 0= until
  nip ;

: list-length lisp-list-length make-number ;


\ counts the number of let bound names in the current word
\ or other names that have been cleaned up with pop-local-names
\ before the end of the function definition
variable let-bound-names

: handle-args ( arglist - len )
  split-args swap dup push-local-names
  lisp-list-length swap dup set-func-&rest
  dup 0<> if push-local-name 1+ else drop then
  dup set-func-args ;

: compile-def ( lisp - )
  \ lisp word format:
  \  num-args num-locals next-frame [body...] prev-frame exit
  new-function
  1 return-context !
  0 let-bound-names !
  dup car symbol->string lisp-create \ create dictionary header
  cdr dup car handle-args
  dup postpone literal \ lisp word: arg length
  here 1 cells + locals-counter ! \ set location of locals count
  0 postpone literal \ lisp word: locals count
  [comp'] next-frame drop compile, \ lisp word: start frame
  swap cdr start-compile lisp-compile-progn \ compile function body
  locals-counter @ @ + \ nlocals+nargs
  let-bound-names @ -
  pop-local-names
  [comp'] prev-frame drop compile, \ lisp word: end frame
  0 return-context !
;

: def ( lisp - lisp)
  compile-def end-compile
  postpone exit set-func-xt
  nil ; special

: defcode ( lisp - lisp)
  \  postpone def
  compile-def
  \ TODO: temp workaround - discard the return value
  [comp'] drop drop compile,
  end-compile postpone exit set-func-xt
  immediate nil ; special

: defmacro ( lisp - lisp)
  compile-def end-compile
  [comp'] set-macro-flag drop compile,
  postpone exit set-func-xt
  immediate nil ; special

: lisp-interpret-symbol ( lisp - )
  lisp-find-symbol-word name>int execute @ ;

: lisp-compile-symbol ( lisp - )
  dup locals @ assoc dup if \ local variable reference
    cdr postpone literal
    [comp'] get-local drop compile,
    drop
  else \ compile dicationary variable lookup
    drop lisp-find-symbol-word name>int compile,
    [comp'] @ drop compile,
  then ;

' lisp-interpret-symbol interpret-dispatch lisp-symbol-tag cells + !
' lisp-compile-symbol compile-dispatch lisp-symbol-tag cells + !

: set ( sv - v)
  dup car swap cdr car \ [ symbol value
  lisp-state @ 0= if \ interpret
    lisp-interpret dup rot
    lisp-find-symbol-word name>int execute !
  else \ compile
    over locals @ assoc dup if \ setting local variable
      swap lisp-interpret-r
      cdr postpone literal
      [comp'] set-local drop compile,
      drop \ symbol
    else \ global
      drop lisp-interpret-r \ compile value
      lisp-find-symbol-word name>int compile,
      [comp'] ! drop compile,
    then
    return-context @ if
      0 postpone literal \ TODO: return value instead
    then
  then
; special


: let* ( lisp - )   \ todo: interpret
  dup car 0 >r
  begin
    dup 0<>
  while
    dup car
    dup car swap cdr car compile-local-var
    r> 1+ >r cdr
  repeat
  drop cdr lisp-compile-progn
  r> dup pop-local-names
  let-bound-names dup @ rot + swap !

; special


: list ( lisp - lisp )
  recursive
  dup 0<> if
    dup car lisp-interpret cdr list
    [comp'] cons drop compile,
  else
    postpone literal
  then
; special

: if, postpone if t ;
: else, postpone else t ;
: then, postpone then t ;
: begin, postpone begin t ;
: while, postpone while t ;
: repeat, postpone repeat t ;
: lit, postpone literal t ;

\ TODO: rename to 1+ and 1- after parser is fixed
: +1 ( n - n ) 2 + ;
: -1 ( n - n ) 2 - ;
: + ( nn - n ) >>1 swap >>1 + make-number ;
: - ( nn - n ) >>1 swap >>1 swap - make-number ;
: * ( nn - n ) >>1 swap >>1 * make-number ;
: / ( nn - n ) >>1 swap >>1 swap / make-number ;

: = = if lisp-true else nil then ;
: > > if lisp-true else nil then ;
: < < if lisp-true else nil then ;
: <= <= if lisp-true else nil then ;
: >= >= if lisp-true else nil then ;

: not 0= if lisp-true else nil then ;

: type-of dup 0<> if get-lisp-tag make-number then ; \ todo: return symbol
: number? 1 and ;
: cons? dup 0<> if get-lisp-tag lisp-pair-tag = then ;
: symbol? dup 0<> if get-lisp-tag lisp-symbol-tag = then ;
: string? dup 0<> if get-lisp-tag lisp-string-tag = then ;
: vector? dup 0<> if get-lisp-tag lisp-vector-tag = then ;

: cr cr t ;

variable nil 0 nil !

s" raillisp.lsp" lisp-load-from-file drop
