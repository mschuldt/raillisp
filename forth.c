   // Railforth \\
  //             \\
 // A simple Reference implementation
// for the Raillisp Forth Specification.

#include <readline/readline.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/time.h>
#include <stdint.h>

typedef long long int cell;
typedef long long unsigned int u_cell;

cell tos=0; // top of stack value
cell* sp0; // stack base pointer
cell* sp;  // stack location pointer
cell* rp0; // return stack
cell* rp;
cell* dp0; // dictionary
cell* dp;
cell* ip=0;  // instruction pointer
//int here = 0; // top of dictionary
cell* latest = 0; // last word
#define COMPILE  1
#define INTERPRET 0
#define bytes_per_cell sizeof(cell)
cell state = INTERPRET; // forth compiler state

#define IMM_BIT    0x100000 //TODO
#define CODE_BIT   0x1000000 //TODO
#define HIDDEN_BIT 0x10000000 //TODO
#define LEN_MASK 0xffff

#define false 0
#define true 1

cell* LIT_XT;
cell* DOCOL_XT;
cell* EXIT_XT;
cell* EXEC_XT;

// stack pointers point at next item
#define push(x) *sp++ = tos; tos = (cell)(x)
#define pop() tos; tos = *--sp
#define rpush(x) *rp++ = (cell)(x)
#define rpop() *--rp
#define dict_append(x) *dp++ = (cell)(x)

#define tib_max 128
static char *tib; // Text Input Buffer
int tib_i = 0;
FILE *input_device;

int lineno = 0;
int colno = 0;

uint8_t base = 10;

void error(char* msg){
  printf("ERROR: %s\n", msg);
  exit(1);
}

void print_word(char* a, int c){
  for (int i =0; i < c; i ++){
    printf("%c", a[i]);
  }
  printf("\n");
}

cell digit(unsigned char c) {
  if ('0' <= c && c <= '9') return c - '0';
  if ('a' <= c && c <= 'z') return 10 + c - 'a';
  if ('A' <= c && c <= 'Z') return 10 + c - 'A';
  return -1;
}

int parse_num(char *a, cell len, cell* res) {
  cell b = base;
  int isminus = 0;
  cell n=0;
  if (len <= 0) {
    return false;
  }
  switch (*a) {
  case '%': b = 2;  len--; a++; break;
  case '#': b = 10; len--; a++; break;
  case '$': b = 16; len--; a++; break;
  }
  if( *a == '-' && len > 1) {
    isminus = 1;
    len--;
    a++;
  }
  for( unsigned char c; len > 0; len-- ) {
    c = digit(*a++);
    if (c >= b ) return false;
    n = (n * b) + c;
  }
  *res = isminus ? -n : n;
  return true;
}

static char *_line = (char *)NULL;
int read_stdin(){ // read a line from stdin into tib
  printf(" ok\r\n");
  char* in = readline("");
  if (!in) {
    exit(0);
  }
  strcpy(tib, in);
  free(in);
  return 1;
}

int read_line() {
  lineno++;
  colno = 0;
  tib_i = 0;
  if (input_device == stdin ) {
    return read_stdin();
  }
  return fgets(tib, 128, input_device) != NULL;
}

char next_char(){
  colno++;
  if (tib_i  >= tib_max) {
    return 0;
  }
  return tib[tib_i++];
}

char key(){
  char c = next_char();
  if (c) {
    return c;
  }
  read_line();
  c = next_char();
  if (c){
    return c;
  }
  exit(1);
}

char* word_a = 0;
int word_c = 0;

int parse_name(){ // return true on success
  char c;
  word_c = 0;
  do{
    c = next_char();
  } while (c && isspace(c));
  if (c == 0) {
    return 0;
  }
  word_a = tib + tib_i - 1;
  word_c = 1;
  while(!isspace(c = next_char()) && c) {
    ++word_c;
  }
  tib_i--;
  return 1;
}

void immediate() {
  *(cell*)(latest) |= IMM_BIT;
}

int is_immediate(cell *word) {
  return *word & IMM_BIT ;
}

void hide(){
  *(cell*)(latest) |= HIDDEN_BIT;
}

cell aligned(cell x){
  return (x + sizeof(cell)-1) & ~(sizeof(cell)-1);
}

void dict_append_str(char *a, int c){
  strncpy((char*)(dp), a, c);
  dp += c / bytes_per_cell + c % bytes_per_cell;
}

void create(char* a, cell c){
  dict_append(latest);
  latest = (cell*)dp;
  dict_append(c);
  dict_append_str(a, c);
}

void code(char* name, void* addr){
  create(name, strlen(name));
  dict_append(addr);
  *latest |= CODE_BIT;
}

int str_eq(char *a1, u_cell c1, char *a2, u_cell c2){
  if ( c1 != c2 ) {
    return false;
  }
  for (; c1 && c2; a1++, a2++, c1--, c2--) {
    if (*a1 != *a2) {
      return false;
    }
  }
  return true;
}

int compare(char *a1, u_cell c1, char *a2, u_cell c2) {
  for (;c1 && c2; a1++, a2++, c1--, c2--) {
    if (*a1 != *a2) {
      return (*a1 < *a2) ? -1 : 1;
    }
    a1++; a2++; c1--; c2--;
  }
  return c1 == c2 ? 0 : ((c1 < c2) ? -1 : 1);
}

cell* cfa(cell* word){
  int len = (*word) & LEN_MASK;
  return word + 1 + len/bytes_per_cell + len % bytes_per_cell;
}


cell* find_word(char* a, int c){
  cell *word = latest;
  while (word){
    cell this = *word;
    int len = this & LEN_MASK;
    char* name = (char*)(word+1);
    if (str_eq(a, c, name, len)){
      return word;
    }
    word = (cell*)*(word-1);
  }
  return false;
}

void cr(){ printf("\n"); };

void type(char* a, int c){
  for ( ; c>0; c--, a++) {
    printf("%c", *a);
  }
}

void words(){
  cell *word = latest;
  int col=0;
  while (word){
    cell this = *word;
    int len = this & LEN_MASK;
    char* name = (char*)(word+1);
    type(name, len);
    col += len + 1;
    if (col > 64) {
      cr();
      col = 0;
    } else {
      printf(" ");
    }
    word = (cell*)*(word-1);
  }
  cr();
}

cell* handle_word(cell* word){
  if (state == INTERPRET || *word & IMM_BIT){
    return (cell*)cfa(word); // interpret
  }
  dict_append(cfa(word)); // compile
  return 0;
}

void literal(cell num){
  dict_append((cell)LIT_XT);
  dict_append((cell)num);
}

cell* handle_num(cell num){
  if (state == INTERPRET) {
    push(num);
  } else {
    literal(num);
  }
  return 0;
}

cell* do_interpret(){
  cell num;
  cell* word = find_word(word_a, word_c);
  if (word) {
    return handle_word(word);
  }
  int ok = parse_num(word_a, word_c, &num);
  if (ok) {
    return handle_num(num);
  }
  printf("Undefined word: ");
  print_word(word_a, word_c);
  exit(1);
}

cell* get_xt(char* word){
  cell* x = find_word(word, strlen(word));
  if (!x){
    error("get_xt undefined");
  }
  return cfa(x);
}

int depth(){
  return sp - sp0;
}

void print_stack(){
  printf("<%d> ", depth());
  for (cell* p = sp0+1; p < sp; p++) {
    printf("%llu ", (cell)*p);
  }
  if (depth()){
    printf("%llu\n", tos);
  }
}

void cmove(char *from, char *to, u_cell length) {
  while ((length--) != 0) {
    *to++ = *from++;
  }
}

void see(char* a, int c){
  cell* word = find_word(word_a, word_c);
  if (! word) {
    error("undefined");
  }
  int len = *word & LEN_MASK;
  char* name = (char*)(word+1);
  if (*word & CODE_BIT) {
    printf("codeword\n");
    return;
  }
  printf(": "); print_word(name, len);
  cell* code = cfa(word);
  for(; (cell*)(*code) != EXIT_XT; code++) {
    printf("   %llu:   %llu\n", (cell)code, *code);
  }
  if (is_immediate(word)) {
    printf("  ; immediate\n");
  }
  else printf("  ;\n");
}

#define CODE(name, label) label
#define iCODE(name, label) label
#define NEXT goto **(cell*)(*ip++)

void forth(){
  cell* xt;
  cell x;
  char* str, c;

#include "_forthwords.c"
  LIT_XT = get_xt("lit");
  DOCOL_XT = &&docol;
  EXIT_XT = get_xt("exit");
  EXEC_XT = get_xt("exec");

  // Reserve space used by INTERPRET for executing words.
  dict_append(0); // space for destination address
  cell* interpret_ip = dp;
  dict_append(get_xt("interpret")); // return addres

 CODE("quit", quit):
  rp = rp0;
  while (true) {
    if (!read_line()){
      if(input_device != stdin) { // actually, this will always be true
        fclose(input_device);
        input_device = stdin;
        lineno = 0;
        continue;
      }
      exit(1);
    }
  CODE("interpret", interpret):
    while (parse_name()){
      xt = do_interpret();
      if (xt) {
        goto execute_xt;
      }
    }
  }
 docol:
  rpush(ip);
  ip = (cell*)(*(ip-1)) + 1;
  NEXT;
 CODE("exit", exit):
  ip = (cell*)(*--rp);
  NEXT;
 CODE("drop", drop):
  tos = *--sp;
  NEXT;
 CODE("2drop", _2drop):
  sp--;
  tos = *--sp;
  NEXT;
 CODE("dup", dup):
  *sp++ = tos;
  NEXT;
 CODE("2dup", _2dup):
  *sp++ = tos;
  *sp++ = *(sp-3);
  NEXT;
 CODE("over", over):
  push(*(sp-2));
  NEXT;
 CODE("nip", nip):
  --sp;
  NEXT;
 CODE("swap", swap):
  x = *(sp-1);
  *(sp-1) = tos;
  tos = x;
  NEXT;
 CODE("pick", pick):
  tos = *(sp-1-tos);
  NEXT;
 CODE("rpick", rpick):
  tos = *(rp-1-tos);
  NEXT;
 CODE("rot", rot):
  x = *(sp-2);
  *(sp-2) = *(sp-1);
  *(sp-1) = tos;
  tos = x;
  NEXT;
 CODE("-rot", _rot):
  x = *(sp-2);
  *(sp-2) = tos;
  tos=*(sp-1);
  *(sp-1) = x;
  NEXT;
#define BINOP(name, label, op) CODE(name, label):       \
  tos = *--sp op tos;                                   \
  NEXT;
  BINOP("+", plus, +);
  BINOP("-", minus, -);
  BINOP("*", mul, *);
  BINOP("/", div, /);
  BINOP("and", and, &);
  BINOP("or", or, |);
  BINOP("xor", xor, ^);
  BINOP("=", equal, ==);
  BINOP("<>", not_equal, !=);
  BINOP("<", less_than, <);
  BINOP(">", greater_than, >);
  BINOP(">=", greater_or_eq, >=);
  BINOP("<=", less_or_eq, <=);
 CODE("1+", one_plus):
  tos += 1;
  NEXT;
 CODE("1-", one_minus):
  tos -= 1;
  NEXT;
 CODE("0=", zero_eq):
  tos = (tos == 0);
  NEXT;
 CODE("0<>", zero_not_eq):
  tos = (tos != 0);
  NEXT;
 CODE("0<", zero_less_than):
  tos = (tos < 0);
  NEXT;
 CODE("0>", zero_greater_than):
  tos = (tos > 0);
  NEXT;
 CODE("invert", invert):
  tos = ~tos;
  NEXT;
 CODE("2/", two_div):
  tos >>= 1;
  NEXT;
 CODE("2*", two_times):
  tos <<= 1;
  NEXT;
 CODE("lshift", lshift):
  tos = *--sp << tos;
  NEXT;
 CODE("rshift", rshift):
  tos = *--sp >> tos;
  NEXT;
 CODE("!", store):
  *((cell*)tos) = *--sp;
  pop();
  NEXT;
 CODE("@", fetch):
  tos = *((cell*)tos);
  NEXT;
 CODE("+!", addstore):
  *((cell*)tos) += *--sp;
  pop();
  NEXT;
 CODE("c!", store_byte):
  *((char*)tos) = (char)*--sp;
  pop();
  NEXT;
 CODE("c@", fetch_byte):
  tos = (cell)(*((char*)tos));
  NEXT;
 CODE("cmove", cmove):
  str = (char*)(*--sp);
  cmove((char*)(*--sp), str, (u_cell)tos);
  pop(); NEXT;
 CODE(">r", to_r):
  rpush(tos);
  pop();
  NEXT;
 CODE("r>", from_r):
  push(rpop());
  NEXT;
 CODE("r@", read_r):
  push(*(rp - 1));
  NEXT;
 CODE("rdrop", r_drop):
  rp--;
  NEXT;
 CODE("sp@", sp_fetch):
  push(sp);
  NEXT;
 CODE("emit", emit):
  x = pop();
  printf("%c", (char)x);
  NEXT;
 CODE("create", _create):
  parse_name();
  create(word_a, word_c);
  NEXT;
 CODE("allot", allot):
  dp += pop();
  NEXT;
 iCODE("[", lbrack):
  state = INTERPRET;
  NEXT;
 CODE("]", rbrack):
  state = COMPILE;
  NEXT;
 CODE("parse-name", _parse_name):
  parse_name();
  push(word_a);
  push(word_c);
  NEXT;
 CODE("find-name", find_name):
  x = pop();
  str = (char*)pop();
  push(find_word(str, x));
  NEXT;
 CODE("name>int", name_to_int):
  tos = (cell)cfa((cell*)tos);
  NEXT;
 CODE("'", tick):
  parse_name();
  xt = find_word(word_a, word_c);
  push(cfa(xt));
  NEXT;
 CODE("compile,", compile_comma):
 CODE(",", comma):
  x = pop();
  dict_append(x);
  NEXT;
 CODE("[']", btickb):
  push(*ip++);
  NEXT;
#define do_branch ip = (cell*)((cell)ip + (cell)(*ip))
 CODE("branch", branch):
  do_branch;
  NEXT;
 CODE("0branch", zero_branch):
  x = pop();
  if (x==0) {
    do_branch;
  }else{
    ip++;
  }
  NEXT;
 CODE("litstring", litstring):
  x = *ip++; // len
  push(ip); // addr
  push(x);
  ip = (cell*)aligned((cell)(ip) + x);
  NEXT;
 CODE("char", _char):
  parse_name();
  push(*word_a);
  NEXT;
 CODE(".", dot):
  xt=(cell*)pop();
  printf("%llu ", (cell)xt);
  NEXT;
 CODE(".s", print_stack):
  print_stack();
  NEXT;
 CODE("type", _type):
  type(((char*)*--sp)+1, tos); //TODO: should not need +1
  tos = *--sp;
  NEXT;
 iCODE("execute", execute):
  if (state==COMPILE){
    dict_append(EXEC_XT);
    dict_append(0);
  } else {
    xt = (cell*)pop();
  execute_xt:
    *(interpret_ip - 1) = (cell)xt;
    ip = interpret_ip;
    goto **xt;
  }
  NEXT;
 CODE("exec", exec):
  xt = (cell*)pop();
  *ip++ = (cell)xt;
  goto **xt;
 CODE("bye", bye):
  exit(0);
 CODE("literal", _literal):
  x = pop();
  literal(x);
  NEXT;
 CODE("lit", lit):
  push(*ip++);
  NEXT;
 CODE("words", _words):
  words();
  NEXT;
 iCODE("immediate", _immediate):
  immediate();
  NEXT;
 CODE("reveal", reveal):
  *(cell*)(tos) ^= HIDDEN_BIT;
  pop();
  NEXT;
  #define VAR(name, label, var) CODE(name, label): push( & var ); NEXT
  VAR("latest", _latest, latest);
  VAR("base", _base, base);
  VAR("dp", _dp, dp);
  VAR("state", _state, state);
 CODE(":", colon):
  parse_name();
  create(word_a, word_c);
  dict_append(DOCOL_XT);
  hide();
  state = COMPILE;
  NEXT;
 CODE("see", _see):
  parse_name();
  see(word_a, word_c);
  NEXT;
 iCODE(";", semi):
  dict_append(EXIT_XT);
  state = INTERPRET;
  NEXT;
 CODE("docol", _docol):
  push(DOCOL_XT);
  NEXT;
 iCODE("\\", _slash):
  tib_i = tib_max;
  NEXT;
 iCODE("(", _open_paren):
  while((c = next_char()) && c != ')');
  NEXT;
 CODE("key", _key):
  push(key());
  NEXT;
 CODE("aligned", _aligned):
  tos = aligned(tos);
  NEXT;
}

void init(){
  input_device = fopen("forth.fth", "r");
  tib = (char*)malloc(sizeof(char)*tib_max);
  sp0 = sp = (cell*)malloc(sizeof(cell)*1000);
  rp0 = rp = (cell*)malloc(sizeof(cell)*1000);
  dp0 = dp = (cell*)malloc(sizeof(cell)*100000);
}

int main (){
  init();
  forth();
}
