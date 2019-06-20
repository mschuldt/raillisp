
: cells 8 * ;
: cr 10 emit ;
: not 0= ;

: tuck swap over ;

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

