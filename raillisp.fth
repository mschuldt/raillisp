\ -*- forth -*-

\ utilities

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

\ symbol table

struct
cell% field symtab-namea
cell% field symtab-nameu
cell% field symtab-lisp
cell% field symtab-next
end-struct symtab

0 variable symtab-first
drop

: symtab-lookup ( namea nameu -- symtab )
  symtab-first @
  begin
    dup 0<>
  while
    >r
    2dup r@ symtab-namea @ r@ symtab-nameu @ compare
    0= if
      2drop r> exit
    then
    r> symtab-next @
  repeat
  drop 2drop 0 ;

: symtab-add ( namea nameu lisp -- )
  symtab %allocate throw >r
  r@ symtab-lisp !
  r@ symtab-nameu !
  r@ symtab-namea !
  r@ symtab-next symtab-first @ swap !
  r> symtab-first ! ;

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
7 constant lisp-string-tag
8 constant lisp-vector-tag
9 constant lisp-max-tag

lisp-max-tag cells allocate throw constant eval-dispatch
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
cell% field lambda-vararg
cell% field lambda-body
end-struct lisp-lambda

struct
cell% field vector-tag
cell% field vector-len
cell% field vector-vec
end-struct lisp-vector

: make-cons ( car cdr -- lisp )
  lisp-pair %allocate throw >r
  r@ pair-tag lisp-pair-tag swap !
  r@ pair-cdr !
  r@ pair-car !
  r> ;

: car ( pair -- lisp )
  dup 0<> if pair-car @ then ;

: cdr ( pair -- lisp )
  dup 0<> if pair-cdr @ then ;

: make-number ( num -- lisp )
  lisp-number %allocate throw
  dup number-tag lisp-number-tag swap !
  swap over number-num ! ;

: builtin ( xt -- lisp )
  lisp-builtin %allocate throw
  dup builtin-tag lisp-builtin-tag swap !
  swap over builtin-xt ! ;

: make-symbol ( namea nameu -- lisp )
  lisp-symbol %allocate throw >r
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

: make-special ( xt -- lisp )
  lisp-special %allocate throw
  dup special-tag lisp-special-tag swap !
  swap over special-xt ! ;

: make-vector ( length -- lisp )
  lisp-vector %allocate throw >r
  r@ vector-tag lisp-vector-tag swap !
  dup r@ vector-len !
  allocate throw r@ vector-vec ! r> ;

0 0 make-cons constant lisp-true

s" t" string-new lisp-true symtab-add
s" nil" string-new nil symtab-add

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

: set-lambda-args ( lisp args - lisp )
  swap >r
  split-args
  r@ lambda-vararg !
  r> lambda-args !
;

: make-lambda ( args body -- lisp )
  lisp-lambda %allocate throw >r
  r@ lambda-tag lisp-lambda-tag swap !
  r@ lambda-body !
  r@ swap set-lambda-args
  r> ;

: make-macro ( args body -- lisp )
  make-lambda
  dup lambda-tag lisp-macro-tag swap ! ;

: lisp-display ( lisp -- )
  dup 0= if
    drop ." nil"
  else
    dup lisp-tag @ cells display-dispatch + @ execute
  then ;

: lisp-display-pair ( lisp -- )
  dup lisp-true = if
    ." t" drop exit
  then
  [char] ( emit 32 emit
  begin
    dup car lisp-display 32 emit
    cdr
    dup 0<> if
      dup pair-tag @ lisp-pair-tag <> if
        [char] . emit 32 emit lisp-display 0
      then
    then
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

: lisp-eval-body ( lisp -- lisp )
  \ evaluates a list, returning the result of the last form
  0 swap \ return value
  begin
    dup 0<>
  while
    nip dup car lisp-eval swap cdr
  repeat
  drop ;

: lisp-eval-list
  recursive ( lisp -- lisp )
  dup 0<> if
    dup car lisp-eval swap cdr lisp-eval-list make-cons
  then ;

: lisp-bind-var ( name value -- )
  >r symbol->string r> symtab-add ;

: lisp-bind-vars ( names values -- )
  swap
  begin
    dup 0<>
  while
    2dup car swap car lisp-bind-var
    cdr swap cdr swap
  repeat
  drop ;

: lisp-apply-lambda ( func args -- lisp )
  symtab-save >r
  over lambda-args @ swap lisp-bind-vars
  over lambda-vararg @ dup if
    swap lisp-bind-var
  else
    2drop
  then
  lambda-body @ lisp-eval-body
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
      r> cdr lisp-apply-lambda lisp-eval
    else
      r> cdr lisp-eval-list lisp-apply
    then
  then ;

' lisp-eval-pair eval-dispatch lisp-pair-tag cells + !

: lisp-eval-number ( lisp -- lisp ) ;

' lisp-eval-number eval-dispatch lisp-number-tag cells + !

: lisp-eval-builtin ( lisp -- lisp ) ;

' lisp-eval-builtin eval-dispatch lisp-builtin-tag cells + !

: error-undefined-value
  cr ." undefined value: " lisp-display cr maybe-bye ;

: lisp-eval-symbol ( lisp -- lisp )
  dup symbol->string
  symtab-lookup dup 0= if
    drop error-undefined-value
  else
    symtab-lisp @
    swap drop
  then ;

: lisp-builtin-set ( lisp -- lisp )
  dup car dup
  symbol-namea @ swap symbol-nameu @ symtab-lookup
  dup 0= if
    drop error-undefined-value
  else
    symtab-lisp swap cdr car dup rot !
  then ;

s" set" string-new ' lisp-builtin-set builtin symtab-add

' lisp-eval-symbol eval-dispatch lisp-symbol-tag cells + !

: lisp-eval-string ( lisp --lisp ) ;

' lisp-eval-string eval-dispatch lisp-string-tag cells + !

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
    r> drop lisp-read-lisp lisp-eval >r
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

\ specials

: lisp-special-quote ( lisp -- lisp )
  car ;

s" quote" string-new ' lisp-special-quote make-special symtab-add

: lisp-special-lambda ( lisp -- lisp )
  dup car swap cdr make-lambda ;

s" lambda" string-new ' lisp-special-lambda make-special symtab-add

: lisp-special-macro ( lisp -- lisp )
  dup car swap cdr make-macro ;

s" macro" string-new ' lisp-special-macro make-special symtab-add

: lisp-special-define ( lisp -- lisp )
  dup car swap cdr car lisp-eval lisp-bind-var 0 ;

s" define" string-new ' lisp-special-define make-special symtab-add

: lisp-special-cond ( lisp -- lisp )
  recursive
  dup car car lisp-eval 0<> if
    car cdr car lisp-eval
  else
    cdr dup 0<> if
      lisp-special-cond
    then
  then ;

s" cond" string-new ' lisp-special-cond make-special symtab-add

: lisp-special-if ( lisp -- lisp )
  dup car lisp-eval 0<> if
    cdr car lisp-eval
  else
    cdr cdr dup 0<> if
      car lisp-eval
    then
  then ;

s" if" string-new ' lisp-special-if make-special symtab-add

: lisp-special-and  ( lisp -- lisp )
  lisp-true swap
  begin
    dup 0<>
  while
    nip dup car lisp-eval swap cdr
    over 0= if
      drop 0
    then
  repeat
  drop ;

s" and" string-new ' lisp-special-and make-special symtab-add

: lisp-special-or  ( lisp -- lisp )
  nil swap
  begin
    dup 0<>
  while
    nip dup car lisp-eval swap cdr
    over 0<> if
      drop nil
    then
  repeat
  drop ;

s" or" string-new ' lisp-special-or make-special symtab-add

: lisp-special-while ( lisp -- lisp )
  dup car swap cdr
  begin
    over lisp-eval 0<>
  while
    dup lisp-eval-body drop
  repeat
  2drop 0 ;

s" while" string-new ' lisp-special-while make-special symtab-add

s" progn" string-new ' lisp-eval-body make-special symtab-add

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
  drop cdr lisp-eval-body
  r> symtab-restore
;

s" let" string-new ' lisp-special-let make-special symtab-add

variable forth-args

: lisp-special-forth ( lisp -- lisp)
  \ execute a list of symbols as forth words.
  \ the sequence must return a lisp object by leaving it on the stack
  forth-args !
  begin
    forth-args @ 0<>
  while
    forth-args @ car symbol->string
    2dup find-name dup 0= if
      ." ERROR: invalid word: " drop type 1 throw
    else
      >r 2drop r>
      name>int execute
    then
    forth-args dup @ cdr swap !
  repeat ;

s" forth" string-new ' lisp-special-forth make-special symtab-add

\ builtins

: lisp-builtin-+ ( lisp -- lisp )
  0 swap
  begin
    dup 0<>
  while
    dup car number-num @ rot + swap cdr
  repeat
  drop make-number ;

s" +" string-new ' lisp-builtin-+ builtin symtab-add

: lisp-builtin-- ( lisp -- lisp )
  dup car number-num @ swap cdr dup 0= if
    drop negate make-number
  else
    swap
    begin
      over car number-num @ - swap cdr swap
      over 0=
    until
    nip make-number
  then ;

s" -" string-new ' lisp-builtin-- builtin symtab-add

: lisp-builtin-* ( lisp -- lisp )
  1 swap
  begin
    dup 0<>
  while
    dup car number-num @ rot * swap cdr
  repeat
  drop make-number ;

s" *" string-new ' lisp-builtin-* builtin symtab-add

: lisp-builtin-cons ( lisp -- lisp )
  dup car swap cdr car make-cons ;

s" cons" string-new ' lisp-builtin-cons builtin symtab-add

: lisp-get-arg-numbers ( lisp - n n )
  dup car number-num @
  swap cdr car number-num @ ;

: lisp-builtin-= ( lisp -- lisp )
  lisp-get-arg-numbers
  = if lisp-true else nil then ;

s" =" string-new ' lisp-builtin-= builtin symtab-add

: lisp-builtin-> ( lisp -- lisp )
  lisp-get-arg-numbers
  > if lisp-true else nil then ;

s" >" string-new ' lisp-builtin-> builtin symtab-add

: lisp-builtin-< ( lisp -- lisp )
  lisp-get-arg-numbers
  < if lisp-true else nil then ;

s" <" string-new ' lisp-builtin-< builtin symtab-add

: lisp-builtin-<= ( lisp -- lisp )
  lisp-get-arg-numbers
  <= if lisp-true else nil then ;

s" <=" string-new ' lisp-builtin-<= builtin symtab-add

: lisp-builtin->= ( lisp -- lisp )
  lisp-get-arg-numbers
  >= if lisp-true else nil then ;

s" >=" string-new ' lisp-builtin->= builtin symtab-add

: lisp-builtin-car ( lisp -- lisp )
  car car ;

s" car" string-new ' lisp-builtin-car builtin symtab-add

: lisp-builtin-cdr ( lisp -- lisp )
  car cdr ;

s" cdr" string-new ' lisp-builtin-cdr builtin symtab-add

: lisp-builtin-setcar ( lisp -- lisp )
  dup car swap cdr car over pair-car ! ;

s" setcar" string-new ' lisp-builtin-setcar builtin symtab-add

: lisp-builtin-setcdr ( lisp -- lisp )
  dup car swap cdr car over pair-cdr ! ;

s" setcdr" string-new ' lisp-builtin-setcdr builtin symtab-add

: eq? ( lisp lisp - lisp )
  2dup = if
    2drop lisp-true
  else
    2dup lisp-tag @ swap lisp-tag @ <> if
      2drop nil
    else
      dup lisp-tag @ cells eq?-dispatch + @ execute
    then
  then ;

: lisp-builtin-eq? ( lisp -- lisp )
  dup car swap cdr car eq? ;

s" eq?" string-new ' lisp-builtin-eq? builtin symtab-add

' nil eq?-dispatch lisp-pair-tag cells + !

: lisp-eq?-number ( lisp lisp -- lisp )
  number-num @ swap number-num @ = if
    lisp-true
  else
    nil
  then ;

' lisp-eq?-number eq?-dispatch lisp-number-tag cells + !

' nil eq?-dispatch lisp-builtin-tag cells + !

' lisp-eq?-symbol eq?-dispatch lisp-symbol-tag cells + !
' lisp-eq?-symbol eq?-dispatch lisp-string-tag cells + !

' nil eq?-dispatch lisp-lambda-tag cells + !

: lisp-builtin-display ( lisp -- lisp )
  car lisp-display 0 ;

s" display" string-new ' lisp-builtin-display builtin symtab-add

s" exit" string-new ' bye builtin symtab-add

: lisp-builtin-not
  car 0= if
    lisp-true
  else
    nil
  then ;

s" not" string-new ' lisp-builtin-not builtin symtab-add

: lisp-builtin-read ( lisp - lisp)
  car symbol->string
  1 read-from-string !
  lisp-read-from-string ;

s" read" string-new ' lisp-builtin-read builtin symtab-add

: lisp-builtin-eval ( lisp - lisp)
  car lisp-eval ;

s" eval" string-new ' lisp-builtin-eval builtin symtab-add

: lisp-builtin-apply-1 ( lisp - lisp)
  dup car swap cdr car lisp-apply ;

: lisp-symbol-value? ( lisp - lisp flag)
  car symbol->string
  symtab-lookup dup 0= if
    0
  else
    symtab-lisp @ 1
  then ;

: lisp-builtin-boundp
  lisp-symbol-value? nip 0= if
    nil
  else
    lisp-true
  then ;

: lisp-builtin-symbol-value? \ returns the value or nil if unbound
  lisp-symbol-value? 0= if
    drop nil
  then ;

s" boundp" string-new ' lisp-builtin-boundp builtin symtab-add

s" symbol-value?" string-new ' lisp-builtin-symbol-value? builtin symtab-add

: lisp-builtin-symbol-value
  car lisp-eval-symbol ;

s" symbol-value" string-new ' lisp-builtin-symbol-value builtin symtab-add

s" apply-1" string-new ' lisp-builtin-apply-1 builtin symtab-add

: lisp-type-tag
  car lisp-tag @ make-number ;

s" lisp-type-tag" string-new ' lisp-type-tag builtin symtab-add

\ interpretation words must return a single lisp value
\ compilation words must return nothing

variable lisp-state
: start-compile 1 lisp-state ! ;
: end-compile 0 lisp-state ! ;
end-compile

: lisp-interpret ( lisp - lisp? )
  dup 0<> if
    dup lisp-tag @ cells
    lisp-state @
    0= if interpret-dispatch else compile-dispatch then
    + @ execute
  then ;

: lisp-special-interpret ( lisp - lisp )
  car lisp-interpret ;

s" interpret" string-new ' lisp-special-interpret make-special symtab-add

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

: immediate?
  cell+ @ immediate-mask and 0<> ;

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

: get-local ( n - v )
  frame @ swap cells - @ ;
: set-local ( v n - )
  frame @ swap cells - ! ;

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

: lisp-interpret-pair ( lisp - lisp?)
  dup car
  lisp-find-symbol-word
  dup immediate? if \ special form or macro
    0 macro-flag !
    swap cdr swap name>int execute
    macro-flag @ if lisp-interpret then \ macro
  else \ function
    lisp-state @ 0= if \ interpet
      >r cdr lisp-interpret-list
      r> name>int execute
    else  \ compile
      >r cdr lisp-compile-list
      r> name>int compile,
    then
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

( ( )( )( ) ( lisp words ) ( )( )( )

: :+ ( nn - n ) number-num @ swap number-num @ + make-number ;

: cons make-cons ;

: quote car ; immediate

variable locals-counter
\ locals is an alist of (name . index) pairs.
\  index is a forth integer so this list cannot be printed as lisp
variable locals nil locals !
variable locals-count 0 locals-count !

: ++locals
  locals-counter @ dup @ 1+ swap ! ;

: push-local-name ( symbol - )
  locals-count @ cons
  locals @ cons locals !
  locals-count dup @ 1+ swap !   ;

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
    locals-count dup @ 1- swap !
    1- pop-local-names
  else drop then ;

: compile-local-var ( symbol value - )
  ++locals swap cdr car push-local-name
  lisp-interpret \ compile initial value
  locals-count @ 1- postpone literal
  [comp'] set-local drop compile,
;

: create-var ( sv - v)
  dup car swap cdr car \ symbol value
  lisp-state @ 0= if \ interpret
    swap lisp-interpret \ symbol
    swap lisp-interpret \ value
    dup rot symbol->string
    ( gforth) nextname create ,
  else
    compile-local-var
  then
; immediate

: lisp-create ( ua - ) \ create new dictionary entry
  ( gforth) nextname header reveal docol: cfa, ;

: lisp-list-length ( list - n )
  0 swap
  begin
    dup 0<>
  while
    swap 1+ swap cdr
  repeat drop ;

: member ( key list - list )
  begin
    dup 0<> if
      2dup car eq? 0=
    else 0 then
  while
    cdr
  repeat
  nip ;

: consp dup 0<> if lisp-tag @ lisp-pair-tag = then ;

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


: compile-def ( lisp - )
  \ lisp word format:
  \  lit arg-count dup next-frame [body...] prev-frame exit
  dup car symbol->string lisp-create \ create dictionary header
  cdr dup car dup push-local-names
  lisp-list-length \ length of argument list
  dup postpone literal \ lisp word: arg length
  here 1 cells + locals-counter ! \ set location of locals count
  0 postpone literal \ lisp word: locals count
  [comp'] next-frame drop compile, \ lisp word: start frame
  swap cdr start-compile lisp-compile-list \ compile function body
  locals-counter @ @ + \ nlocals+nargs
  pop-local-names
  [comp'] prev-frame drop compile, \ lisp word: end frame
;

: def ( lisp - lisp)
  compile-def end-compile
  postpone exit
  nil ; immediate


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
    swap lisp-interpret \ symbol
    swap lisp-interpret \ value
    dup rot
    lisp-find-symbol-word name>int execute !
  else \ compile
    over locals @ assoc dup if \ setting local variable
      swap lisp-interpret
      cdr postpone literal
      [comp'] set-local drop compile,
      drop \ symbol
    else \ global
      \ todo: support for (set sexp value)
      \        currently only (set symbol value) is supported
      drop lisp-interpret \ compile value
      lisp-find-symbol-word name>int compile,
      [comp'] ! drop compile,
    then
  then
; immediate


: lisp-builtin-new-vector
  car number-num @ make-vector ;

\ vectors returned by new-vector are undefined so must not be printed
s" new-vector" string-new ' lisp-builtin-new-vector builtin symtab-add

: lisp-builtin-aset
  \ array index newelt
  dup car vector-vec @
  swap cdr dup car number-num @
  rot + swap cdr car swap ! ;

s" aset" string-new ' lisp-builtin-aset builtin symtab-add

: lisp-builtin-aref
  dup car swap cdr car + @ ;

s" aref" string-new ' lisp-builtin-aref builtin symtab-add

: lisp-builtin-vector-length
  car vector-len @ make-number ;

s" vector-length" string-new ' lisp-builtin-vector-length builtin symtab-add

: list-length-builtin car lisp-list-length make-number ;

s" list-length" string-new ' list-length-builtin builtin symtab-add

: list-assoc-builtin dup car swap cdr car assoc ;
s" assoc" string-new ' list-assoc-builtin builtin symtab-add


: repl
  begin
    lisp-read-from-input
    lisp-eval
    lisp-display cr
    0 until ;

s" raillisp.lsp" lisp-load-from-file drop
