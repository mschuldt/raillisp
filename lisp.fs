\ -*- forth -*-

\ utilities

: string-new { a u -- a u }
    a u allocate drop dup >r u cmove
    r> u ;

: string>num ( a u -- n )
    0 swap 0 ?do
	10 * over i + c@ [char] 0 - +
    loop
    nip ;

\ symbol table

struct
    cell% field symtab-namea
    cell% field symtab-nameu
    cell% field symtab-lisp
    cell% field symtab-next
end-struct symtab

0 variable symtab-first
drop

: symtab-lookup { namea nameu -- }
    symtab-first @
    begin
	dup 0<>
    while
	>r
	r@ symtab-namea @ r@ symtab-nameu @ namea nameu compare
	0= if
	    r> symtab-lisp @ unloop exit
	then
	r> symtab-next @
    repeat
    drop 0 ;

: symtab-add { namea nameu lisp -- }
    symtab %allocate throw
    dup symtab-namea namea swap !
    dup symtab-nameu nameu swap !
    dup symtab-lisp lisp swap !
    dup symtab-next symtab-first @ swap !
    symtab-first ! ;

: symtab-save ( -- ptr )
    symtab-first @ ;

: symtab-restore ( ptr -- )
    symtab-first ! ;

\ lisp interpreter

0 constant lisp-pair-tag
1 constant lisp-number-tag
2 constant lisp-builtin-tag
3 constant lisp-symbol-tag
4 constant lisp-special-tag
5 constant lisp-lambda-tag
6 constant lisp-macro-tag
7 constant lisp-max-tag

lisp-max-tag cells allocate throw constant eval-dispatch
lisp-max-tag cells allocate throw constant display-dispatch
lisp-max-tag cells allocate throw constant eq?-dispatch

struct
    cell% field lisp-tag
end-struct lisp

struct
    cell% field pair-tag
    cell% field pair-car
    cell% field pair-cdr
end-struct lisp-pair

struct
    cell% field number-tag
    cell% field number-num
end-struct lisp-number

struct
    cell% field builtin-tag
    cell% field builtin-xt
end-struct lisp-builtin

struct
    cell% field symbol-tag
    cell% field symbol-namea
    cell% field symbol-nameu
end-struct lisp-symbol

struct
    cell% field special-tag
    cell% field special-xt
end-struct lisp-special

struct
    cell% field lambda-tag
    cell% field lambda-args
    cell% field lambda-body
end-struct lisp-lambda

: cons { car cdr -- lisp }
    lisp-pair %allocate throw
    dup pair-tag lisp-pair-tag swap !
    dup pair-car car swap !
    dup pair-cdr cdr swap ! ;

: car ( pair -- lisp )
    pair-car @ ;

: cdr ( pair -- lisp )
    pair-cdr @ ;

: number { num -- lisp }
    lisp-number %allocate throw
    dup number-tag lisp-number-tag swap !
    dup number-num num swap ! ;

: builtin { xt -- lisp }
    lisp-builtin %allocate throw
    dup builtin-tag lisp-builtin-tag swap !
    dup builtin-xt xt swap ! ;

: symbol { namea nameu -- lisp }
    lisp-symbol %allocate throw
    dup symbol-tag lisp-symbol-tag swap !
    dup symbol-namea namea swap !
    dup symbol-nameu nameu swap ! ;

: symbol-new ( namea nameu -- lisp )
    string-new symbol ;

: special { xt -- lisp }
    lisp-special %allocate throw
    dup special-tag lisp-special-tag swap !
    dup special-xt xt swap ! ;

: lambda { args body -- lisp }
    lisp-lambda %allocate throw
    dup lambda-tag lisp-lambda-tag swap !
    dup lambda-args args swap !
    dup lambda-body body swap ! ;

: macro ( args body -- lisp )
       lambda
       dup lambda-tag lisp-macro-tag swap ! ;

: lisp-display ( lisp -- )
    dup 0= if
	drop [char] ( emit [char] ) emit
    else
	dup lisp-tag @ cells display-dispatch + @ execute
    then ;

: lisp-display-pair ( lisp -- )
    [char] ( emit 32 emit
    begin
	dup car lisp-display 32 emit
	cdr
	dup 0=
    until
    drop
    [char] ) emit ;

' lisp-display-pair display-dispatch lisp-pair-tag cells + !

: lisp-display-number ( lisp -- )
    number-num @ . ;

' lisp-display-number display-dispatch lisp-number-tag cells + !

: lisp-display-builtin ( lisp -- )
    [char] $ emit special-xt @ . ;

' lisp-display-builtin display-dispatch lisp-builtin-tag cells + !

: lisp-display-symbol { lisp -- }
    lisp symbol-namea @ lisp symbol-nameu @ type ;

' lisp-display-symbol display-dispatch lisp-symbol-tag cells + !

: lisp-display-special ( lisp -- )
    [char] # emit special-xt @ . ;

' lisp-display-special display-dispatch lisp-special-tag cells + !

: lisp-display-lambda ( lisp -- )
    [char] & emit lambda-body @ . ;

' lisp-display-lambda display-dispatch lisp-lambda-tag cells + !

: lisp-display-macro ( lisp -- )
    [char] * emit lisp-display-lambda ;

' lisp-display-macro display-dispatch lisp-macro-tag cells + !

: lisp-eval ( lisp -- lisp )
    dup 0<> if
	dup lisp-tag @ cells eval-dispatch + @ execute
    then ;

: lisp-eval-list recursive ( lisp -- lisp )
    dup 0<> if
	dup car lisp-eval swap cdr lisp-eval-list cons
    then ;

: lisp-bind-var ( name value -- )
    >r dup symbol-namea @ swap symbol-nameu @ r> symtab-add ;

: lisp-bind-vars ( names values -- )
    swap
    begin
	dup 0<>
    while
	2dup car swap car lisp-bind-var
	cdr swap cdr swap
    repeat
    2drop ;

: lisp-apply-lambda ( func args -- lisp )
    symtab-save >r
    over lambda-args @ swap lisp-bind-vars
    lambda-body @ lisp-eval
    r> symtab-restore ;

: lisp-apply ( func args -- lisp )
    >r dup lisp-tag @ lisp-builtin-tag = if
	r> swap builtin-xt @ execute
    else
	r> lisp-apply-lambda
    then ;

: lisp-eval-pair ( lisp -- lisp )
    >r
    r@ car lisp-eval
    dup lisp-tag @ dup lisp-special-tag = if
	drop r> cdr swap special-xt @ execute
    else
      lisp-macro-tag = if
        r> cdr lisp-apply-lambda
      else
	r> cdr lisp-eval-list lisp-apply
      then
    then ;

' lisp-eval-pair eval-dispatch lisp-pair-tag cells + !

: lisp-eval-number ( lisp -- lisp ) ;

' lisp-eval-number eval-dispatch lisp-number-tag cells + !

: lisp-eval-builtin ( lisp -- lisp ) ;

' lisp-eval-builtin eval-dispatch lisp-builtin-tag cells + !

: lisp-eval-symbol { lisp -- lisp }
    lisp symbol-namea @ lisp symbol-nameu @ symtab-lookup ;

' lisp-eval-symbol eval-dispatch lisp-symbol-tag cells + !

: lisp-eval-special ( lisp -- lisp ) ;

' lisp-eval-special eval-dispatch lisp-special-tag cells + !

: lisp-eval-lambda ( lisp -- lisp ) ;

' lisp-eval-lambda eval-dispatch lisp-lambda-tag cells + !

: lisp-eval-macro ( lisp -- lisp ) ;

' lisp-eval-macro eval-dispatch lisp-macro-tag cells + !


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

128 allocate throw constant token-buffer

: lisp-read-token ( e a -- e a a u )
    lisp-skip-ws
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

: lisp-read-list recursive ( e a -- e a lisp )
    lisp-skip-ws lisp-read-char
    dup [char] ) = swap 0 = or if
	0
    else
	lisp-unread-char lisp-read-lisp >r lisp-read-list r> swap cons
    then ;

: lisp-read-number ( e a -- e a lisp )
    lisp-read-token string>num number ;

: lisp-read-symbol ( e a -- e a lisp )
    lisp-read-token string-new symbol ;

: _lisp-read-lisp ( e a -- e a lisp )
    lisp-skip-ws lisp-read-char
    dup 0= if
	drop 0
    else
	dup [char] ( = if
	    drop lisp-read-list
	else
	    dup [char] 0 >= swap [char] 9 <= and if
		lisp-unread-char lisp-read-number
	    else
		lisp-unread-char lisp-read-symbol
	    then
	then
    then ;
' _lisp-read-lisp is lisp-read-lisp

: lisp-load-from-string ( a u -- lisp )
    1 read-from-string !
    over + swap 0 >r
    begin
	lisp-skip-ws 2dup >
    while
	r> drop lisp-read-lisp lisp-eval >r
    repeat
    2drop r> ;

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
 -1 stdin-lastchar !
  0 stdin-unread !
  0 paren-count !
  ." > " lisp-read-lisp
;

\ specials

: lisp-special-quote ( lisp -- lisp )
    car ;

s" quote" string-new ' lisp-special-quote special symtab-add

: lisp-special-lambda ( lisp -- lisp )
    dup car swap cdr car lambda ;

s" lambda" string-new ' lisp-special-lambda special symtab-add

: lisp-special-macro ( lisp -- lisp )
  dup car swap cdr car macro ;

s" macro" string-new ' lisp-special-macro special symtab-add

: lisp-special-define ( lisp -- lisp )
    dup car swap cdr car lisp-eval lisp-bind-var 0 ;

s" define" string-new ' lisp-special-define special symtab-add

0 constant lisp-false
0 0 cons constant lisp-true

s" t" string-new lisp-true symtab-add

: lisp-special-cond recursive ( lisp -- lisp )
    dup car car lisp-eval 0<> if
	car cdr car lisp-eval
    else
	cdr dup 0<> if
	    lisp-special-cond
	then
    then ;

s" cond" string-new ' lisp-special-cond special symtab-add

: lisp-special-if ( lisp -- lisp )
  dup car lisp-eval 0<> if
    cdr car lisp-eval
  else
    cdr cdr dup 0<> if
      car lisp-eval
    then
  then ;

s" if" string-new ' lisp-special-if special symtab-add

: lisp-special-let ( lisp -- lisp ) \ really let*
  symtab-save >r
  dup car
  begin
    dup 0<>
  while
    dup car
    dup car \ name
    swap cdr car \ value
    lisp-eval lisp-bind-var
    cdr
  repeat
  drop cdr lisp-eval-list
  r> symtab-restore
;

s" let" string-new ' lisp-special-let special symtab-add

\ builtins

: lisp-builtin-+ ( lisp -- lisp )
    0 swap
    begin
	dup 0<>
    while
	dup car number-num @ rot + swap cdr
    repeat
    drop number ;

s" +" string-new ' lisp-builtin-+ builtin symtab-add

: lisp-builtin-- ( lisp -- lisp )
    dup car number-num @ swap cdr dup 0= if
	drop negate number
    else
	swap
	begin
	    over car number-num @ - swap cdr swap
	    over 0=
	until
	nip number
    then ;

s" -" string-new ' lisp-builtin-- builtin symtab-add

: lisp-builtin-* ( lisp -- lisp )
    1 swap
    begin
	dup 0<>
    while
	dup car number-num @ rot * swap cdr
    repeat
    drop number ;

s" *" string-new ' lisp-builtin-* builtin symtab-add

: lisp-builtin-cons ( lisp -- lisp )
    dup car swap cdr car cons ;

s" cons" string-new ' lisp-builtin-cons builtin symtab-add

: lisp-builtin-car ( lisp -- lisp )
    car car ;

s" car" string-new ' lisp-builtin-car builtin symtab-add

: lisp-builtin-cdr ( lisp -- lisp )
    car cdr ;

s" cdr" string-new ' lisp-builtin-cdr builtin symtab-add

: lisp-builtin-eq? ( lisp -- lisp )
    dup car swap cdr car 2dup = if
	2drop lisp-true
    else
	2dup lisp-tag @ swap lisp-tag @ <> if
	    2drop lisp-false
	else
	    dup lisp-tag @ cells eq?-dispatch + @ execute
	then
    then ;

s" eq?" string-new ' lisp-builtin-eq? builtin symtab-add

' lisp-false eq?-dispatch lisp-pair-tag cells + !

: lisp-eq?-number ( lisp lisp -- lisp )
    number-num @ swap number-num @ = if
	lisp-true
    else
	lisp-false
    then ;

' lisp-eq?-number eq?-dispatch lisp-number-tag cells + !

' lisp-false eq?-dispatch lisp-builtin-tag cells + !

: lisp-eq?-symbol { lisp1 lisp2 -- lisp }
    lisp1 symbol-namea @ lisp1 symbol-nameu @
    lisp2 symbol-namea @ lisp2 symbol-nameu @
    compare 0= if
	lisp-true
    else
	lisp-false
    then ;

' lisp-eq?-symbol eq?-dispatch lisp-symbol-tag cells + !

' lisp-false eq?-dispatch lisp-lambda-tag cells + !

: lisp-builtin-display ( lisp -- lisp )
    car lisp-display 0 ;

s" display" string-new ' lisp-builtin-display builtin symtab-add

s" exit" string-new ' bye builtin symtab-add

: repl
  begin
    lisp-read-from-input
    lisp-eval
    lisp-display cr
  0 until ;

s" init.l"  lisp-load-from-file drop
