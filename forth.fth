
: cells 8 * ;
: space 32 emit ;
: cr 10 emit ;
: not 0= ;

: tuck swap over ;
: align dp @ aligned dp ! ;

: decimal 10 base ! ;
: hex 16 base ! ;
: ? @ . ;

: literal immediate ['] lit , , ;
: postpone parse-name find-name name>int , ; immediate
: [char] char postpone literal ; immediate

: recursive latest @ reveal ; immediate

: here dp @ ;
: if ['] 0branch , here 0 , ; immediate
: then dup here swap - swap ! ; immediate
: else ['] branch , here 0 , swap  dup here swap - swap ! ; immediate

: begin here ; immediate
: until ['] 0branch , here - , ; immediate
: again ['] branch , here - , ; immediate
: while immediate ['] 0branch , here 0 , ;
: repeat ['] branch , swap here - , dup here swap - swap ! ; immediate
: unless ['] not , postpone if ; immediate

: _do-setup r> -rot 2dup >r >r rot >r ;
: unloop r> rdrop rdrop >r ;
: _do-next r> r> r> 1+ 2dup >r >r rot >r ;
: ?do ['] _do-setup , postpone begin ['] > , postpone while ; immediate
: loop ['] _do-next , postpone repeat ['] unloop , ; immediate
: i [ 2 cells ] literal rpick ;
: j [ 4 cells ] literal rpick ;
: k [ 6 cells ] literal rpick ;

: allot	here swap dp +! ;

: constant create docol , ['] lit , , ['] exit , ;
: variable 1 cells allot constant ;

0 constant nil

: pad here 256 cells + ;

: c, dp @ c! 1 dp +! ;

: '"' [ char " ] literal ;

: s" state @ if
       ['] litstring , dp @ 0 ,
       begin key dup '"' <>
       while c,
       repeat drop
       dup dp @ swap - 1 cells - 1- swap ! align
     else
       dp @
       begin key dup '"' <>
       while over c! 1+
       repeat drop
       dp @ - 1- dp @ swap
     then
; immediate

: ." state @ if
       postpone s" ['] type ,
     else
       begin
	 key dup '"' = if drop exit then emit
       again
     then
; immediate

