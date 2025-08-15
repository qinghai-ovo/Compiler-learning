type token =
  | NUM of (
# 9 "parser.mly"
        int
# 6 "parser.ml"
)
  | STR of (
# 10 "parser.mly"
        string
# 11 "parser.ml"
)
  | ID of (
# 10 "parser.mly"
        string
# 16 "parser.ml"
)
  | INT
  | IF
  | WHILE
  | SPRINT
  | IPRINT
  | SCAN
  | EQ
  | NEQ
  | GT
  | LT
  | GE
  | LE
  | ELSE
  | RETURN
  | NEW
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | LB
  | RB
  | LS
  | RS
  | LP
  | RP
  | ASSIGN
  | SEMI
  | COMMA
  | TYPE
  | VOID
  | MOD
  | POWER

open Parsing
let _ = parse_error;;
# 2 "parser.mly"

open Printf
open Ast

# 58 "parser.ml"
let yytransl_const = [|
  260 (* INT *);
  261 (* IF *);
  262 (* WHILE *);
  263 (* SPRINT *);
  264 (* IPRINT *);
  265 (* SCAN *);
  266 (* EQ *);
  267 (* NEQ *);
  268 (* GT *);
  269 (* LT *);
  270 (* GE *);
  271 (* LE *);
  272 (* ELSE *);
  273 (* RETURN *);
  274 (* NEW *);
  275 (* PLUS *);
  276 (* MINUS *);
  277 (* TIMES *);
  278 (* DIV *);
  279 (* LB *);
  280 (* RB *);
  281 (* LS *);
  282 (* RS *);
  283 (* LP *);
  284 (* RP *);
  285 (* ASSIGN *);
  286 (* SEMI *);
  287 (* COMMA *);
  288 (* TYPE *);
  289 (* VOID *);
  290 (* MOD *);
  291 (* POWER *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* STR *);
  259 (* ID *);
    0|]

let yylhs = "\255\255\
\001\000\003\000\003\000\003\000\004\000\004\000\005\000\005\000\
\005\000\005\000\005\000\006\000\006\000\008\000\008\000\010\000\
\010\000\011\000\011\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\013\000\013\000\014\000\014\000\009\000\007\000\007\000\007\000\
\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
\007\000\012\000\012\000\012\000\012\000\012\000\012\000\000\000"

let yylen = "\002\000\
\001\000\001\000\004\000\001\000\002\000\000\000\003\000\005\000\
\005\000\006\000\006\000\003\000\001\000\000\000\001\000\004\000\
\002\000\002\000\001\000\004\000\007\000\005\000\007\000\005\000\
\005\000\005\000\005\000\005\000\005\000\003\000\001\000\001\000\
\000\000\001\000\003\000\001\000\004\000\001\000\001\000\004\000\
\004\000\003\000\003\000\003\000\003\000\003\000\003\000\002\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\006\000\032\000\056\000\001\000\031\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\038\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\048\000\000\000\000\000\000\000\000\000\
\000\000\030\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\019\000\000\000\005\000\000\000\000\000\000\000\000\000\
\020\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\049\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\037\000\018\000\000\000\029\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\024\000\
\025\000\026\000\027\000\041\000\040\000\028\000\000\000\000\000\
\000\000\000\000\000\000\007\000\000\000\000\000\000\000\003\000\
\004\000\000\000\000\000\000\000\000\000\000\000\000\000\012\000\
\021\000\023\000\009\000\017\000\000\000\000\000\000\000\008\000\
\011\000\000\000\010\000\016\000"

let yydgoto = "\002\000\
\013\000\014\000\123\000\030\000\060\000\091\000\032\000\124\000\
\015\000\125\000\061\000\037\000\033\000\034\000"

let yysindex = "\005\000\
\092\255\000\000\243\254\244\254\017\255\026\255\029\255\037\255\
\027\255\049\255\000\000\000\000\000\000\000\000\000\000\027\255\
\027\255\027\255\027\255\027\255\080\255\027\255\093\255\000\000\
\064\255\027\255\027\255\026\000\104\255\018\255\053\255\108\000\
\083\255\081\255\043\000\132\255\085\255\086\255\095\255\047\000\
\096\255\027\255\027\255\000\000\064\000\027\255\027\255\027\255\
\027\255\000\000\027\255\027\255\101\255\243\254\105\255\128\255\
\130\255\000\000\135\255\000\000\060\255\110\255\118\255\027\255\
\000\000\027\255\027\255\027\255\027\255\027\255\027\255\092\255\
\092\255\119\255\120\255\125\255\068\000\107\255\000\000\059\255\
\059\255\121\255\121\255\121\255\121\255\127\255\157\255\136\255\
\145\255\075\255\245\254\000\000\000\000\027\255\000\000\108\000\
\108\000\108\000\108\000\108\000\108\000\108\000\158\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\147\255\028\255\
\028\255\028\255\027\255\000\000\173\255\085\000\092\255\000\000\
\000\000\148\255\178\255\154\255\159\255\163\255\091\000\000\000\
\000\000\000\000\000\000\000\000\169\255\028\255\169\255\000\000\
\000\000\194\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\170\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\106\255\000\000\000\000\000\000\000\000\000\000\000\000\233\254\
\000\000\171\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\170\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\198\255\255\254\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\
\024\000\149\255\174\255\199\255\224\255\000\000\000\000\000\000\
\000\000\040\255\000\000\000\000\000\000\000\000\000\000\021\255\
\175\255\179\255\187\255\188\255\189\255\195\255\001\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\196\255\196\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\200\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\229\255\230\255\000\000\000\000\000\000\247\255\092\000\
\226\255\000\000\000\000\202\000\183\000\000\000"

let yytablesize = 399
let yytable = "\028\000\
\022\000\002\000\058\000\059\000\036\000\001\000\031\000\036\000\
\035\000\036\000\036\000\016\000\040\000\017\000\019\000\018\000\
\044\000\045\000\116\000\117\000\054\000\055\000\004\000\005\000\
\006\000\007\000\008\000\024\000\002\000\025\000\121\000\055\000\
\077\000\093\000\009\000\010\000\080\000\081\000\082\000\083\000\
\011\000\084\000\085\000\020\000\103\000\104\000\026\000\012\000\
\035\000\056\000\057\000\035\000\021\000\027\000\096\000\022\000\
\097\000\098\000\099\000\100\000\101\000\102\000\003\000\023\000\
\004\000\005\000\006\000\007\000\008\000\013\000\013\000\046\000\
\047\000\048\000\049\000\029\000\009\000\010\000\062\000\048\000\
\049\000\039\000\011\000\092\000\118\000\122\000\051\000\052\000\
\042\000\012\000\043\000\130\000\051\000\052\000\003\000\041\000\
\004\000\005\000\006\000\007\000\008\000\114\000\137\000\115\000\
\139\000\127\000\053\000\138\000\009\000\010\000\063\000\064\000\
\072\000\073\000\011\000\039\000\039\000\039\000\039\000\039\000\
\039\000\012\000\074\000\076\000\039\000\039\000\039\000\039\000\
\086\000\087\000\088\000\039\000\089\000\039\000\109\000\039\000\
\039\000\090\000\094\000\039\000\039\000\066\000\067\000\068\000\
\069\000\070\000\071\000\095\000\105\000\106\000\046\000\047\000\
\048\000\049\000\107\000\052\000\110\000\111\000\044\000\044\000\
\044\000\044\000\044\000\044\000\112\000\051\000\052\000\044\000\
\044\000\044\000\044\000\113\000\120\000\119\000\044\000\128\000\
\044\000\131\000\044\000\044\000\132\000\133\000\044\000\045\000\
\045\000\045\000\045\000\045\000\045\000\134\000\135\000\011\000\
\045\000\045\000\045\000\045\000\140\000\033\000\034\000\045\000\
\004\000\045\000\050\000\045\000\045\000\126\000\051\000\045\000\
\046\000\046\000\046\000\046\000\046\000\046\000\052\000\053\000\
\054\000\046\000\046\000\046\000\046\000\038\000\055\000\014\000\
\046\000\078\000\046\000\015\000\046\000\046\000\000\000\000\000\
\046\000\047\000\047\000\047\000\047\000\047\000\047\000\000\000\
\000\000\000\000\047\000\047\000\047\000\047\000\000\000\000\000\
\000\000\047\000\000\000\047\000\000\000\047\000\047\000\000\000\
\000\000\047\000\000\000\022\000\000\000\022\000\022\000\022\000\
\022\000\022\000\000\000\042\000\042\000\042\000\042\000\042\000\
\042\000\022\000\022\000\000\000\042\000\042\000\000\000\022\000\
\022\000\000\000\000\000\042\000\000\000\042\000\022\000\042\000\
\042\000\043\000\043\000\043\000\043\000\043\000\043\000\000\000\
\000\000\000\000\043\000\043\000\046\000\047\000\048\000\049\000\
\000\000\043\000\000\000\043\000\000\000\043\000\043\000\050\000\
\000\000\000\000\000\000\051\000\052\000\046\000\047\000\048\000\
\049\000\046\000\047\000\048\000\049\000\000\000\000\000\000\000\
\065\000\000\000\075\000\000\000\051\000\052\000\000\000\000\000\
\051\000\052\000\046\000\047\000\048\000\049\000\046\000\047\000\
\048\000\049\000\000\000\079\000\000\000\108\000\000\000\000\000\
\000\000\051\000\052\000\000\000\000\000\051\000\052\000\046\000\
\047\000\048\000\049\000\000\000\000\000\046\000\047\000\048\000\
\049\000\000\000\129\000\000\000\000\000\000\000\051\000\052\000\
\136\000\000\000\000\000\000\000\051\000\052\000\046\000\047\000\
\048\000\049\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\051\000\052\000"

let yycheck = "\009\000\
\000\000\003\001\030\000\030\000\028\001\001\000\016\000\031\001\
\018\000\019\000\020\000\025\001\022\000\027\001\027\001\029\001\
\026\000\027\000\030\001\031\001\003\001\004\001\005\001\006\001\
\007\001\008\001\009\001\001\001\030\001\003\001\003\001\004\001\
\042\000\061\000\017\001\018\001\046\000\047\000\048\000\049\000\
\023\001\051\000\052\000\027\001\072\000\073\000\020\001\030\001\
\028\001\032\001\033\001\031\001\027\001\027\001\064\000\027\001\
\066\000\067\000\068\000\069\000\070\000\071\000\003\001\027\001\
\005\001\006\001\007\001\008\001\009\001\030\001\031\001\019\001\
\020\001\021\001\022\001\027\001\017\001\018\001\026\001\021\001\
\022\001\002\001\023\001\024\001\094\000\112\000\034\001\035\001\
\025\001\030\001\027\001\119\000\034\001\035\001\003\001\003\001\
\005\001\006\001\007\001\008\001\009\001\027\001\133\000\029\001\
\135\000\115\000\003\001\134\000\017\001\018\001\028\001\031\001\
\028\001\028\001\023\001\010\001\011\001\012\001\013\001\014\001\
\015\001\030\001\028\001\028\001\019\001\020\001\021\001\022\001\
\028\001\025\001\003\001\026\001\003\001\028\001\028\001\030\001\
\031\001\003\001\029\001\034\001\035\001\010\001\011\001\012\001\
\013\001\014\001\015\001\030\001\030\001\030\001\019\001\020\001\
\021\001\022\001\030\001\035\001\030\001\001\001\010\001\011\001\
\012\001\013\001\014\001\015\001\029\001\034\001\035\001\019\001\
\020\001\021\001\022\001\027\001\026\001\016\001\026\001\003\001\
\028\001\030\001\030\001\031\001\003\001\028\001\034\001\010\001\
\011\001\012\001\013\001\014\001\015\001\031\001\028\001\023\001\
\019\001\020\001\021\001\022\001\003\001\028\001\028\001\026\001\
\003\001\028\001\028\001\030\001\031\001\114\000\028\001\034\001\
\010\001\011\001\012\001\013\001\014\001\015\001\028\001\028\001\
\028\001\019\001\020\001\021\001\022\001\020\000\028\001\028\001\
\026\001\043\000\028\001\028\001\030\001\031\001\255\255\255\255\
\034\001\010\001\011\001\012\001\013\001\014\001\015\001\255\255\
\255\255\255\255\019\001\020\001\021\001\022\001\255\255\255\255\
\255\255\026\001\255\255\028\001\255\255\030\001\031\001\255\255\
\255\255\034\001\255\255\003\001\255\255\005\001\006\001\007\001\
\008\001\009\001\255\255\010\001\011\001\012\001\013\001\014\001\
\015\001\017\001\018\001\255\255\019\001\020\001\255\255\023\001\
\024\001\255\255\255\255\026\001\255\255\028\001\030\001\030\001\
\031\001\010\001\011\001\012\001\013\001\014\001\015\001\255\255\
\255\255\255\255\019\001\020\001\019\001\020\001\021\001\022\001\
\255\255\026\001\255\255\028\001\255\255\030\001\031\001\030\001\
\255\255\255\255\255\255\034\001\035\001\019\001\020\001\021\001\
\022\001\019\001\020\001\021\001\022\001\255\255\255\255\255\255\
\030\001\255\255\028\001\255\255\034\001\035\001\255\255\255\255\
\034\001\035\001\019\001\020\001\021\001\022\001\019\001\020\001\
\021\001\022\001\255\255\028\001\255\255\026\001\255\255\255\255\
\255\255\034\001\035\001\255\255\255\255\034\001\035\001\019\001\
\020\001\021\001\022\001\255\255\255\255\019\001\020\001\021\001\
\022\001\255\255\030\001\255\255\255\255\255\255\034\001\035\001\
\030\001\255\255\255\255\255\255\034\001\035\001\019\001\020\001\
\021\001\022\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\034\001\035\001"

let yynames_const = "\
  INT\000\
  IF\000\
  WHILE\000\
  SPRINT\000\
  IPRINT\000\
  SCAN\000\
  EQ\000\
  NEQ\000\
  GT\000\
  LT\000\
  GE\000\
  LE\000\
  ELSE\000\
  RETURN\000\
  NEW\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  LB\000\
  RB\000\
  LS\000\
  RS\000\
  LP\000\
  RP\000\
  ASSIGN\000\
  SEMI\000\
  COMMA\000\
  TYPE\000\
  VOID\000\
  MOD\000\
  POWER\000\
  "

let yynames_block = "\
  NUM\000\
  STR\000\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 27 "parser.mly"
             (  _1  )
# 339 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 30 "parser.mly"
           ( IntTyp )
# 345 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 31 "parser.mly"
                     ( ArrayTyp (_3, IntTyp) )
# 352 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 32 "parser.mly"
               ( NameTyp _1 )
# 359 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'dec) in
    Obj.repr(
# 35 "parser.mly"
                ( _1@_2 )
# 367 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    Obj.repr(
# 36 "parser.mly"
                ( [] )
# 373 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'ids) in
    Obj.repr(
# 39 "parser.mly"
                     ( List.map (fun x -> VarDec (_1,x, None)) _2 )
# 381 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 40 "parser.mly"
                              ( [VarDec (_1, _2, Some _4)] )
# 390 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    Obj.repr(
# 41 "parser.mly"
                              ( [TypeDec (_2,_4)] )
# 398 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 42 "parser.mly"
                                    ( [FuncDec(_2, _4, _1, _6)] )
# 408 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 43 "parser.mly"
                                      ( [FuncDec(_2, _4, VoidTyp, _6)] )
# 417 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ids) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 46 "parser.mly"
                       ( _1@[_3] )
# 425 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 47 "parser.mly"
                       ( [_1]  )
# 432 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "parser.mly"
                        ( [] )
# 438 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fargs) in
    Obj.repr(
# 51 "parser.mly"
                        ( _1 )
# 445 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'fargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 54 "parser.mly"
                             ( _1@[(_3,_4)] )
# 454 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 55 "parser.mly"
                             ( [(_1,_2)] )
# 462 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 58 "parser.mly"
                   ( _1@[_2] )
# 470 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 59 "parser.mly"
                   ( [_1] )
# 477 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 62 "parser.mly"
                              ( Assign (Var _1, _3) )
# 485 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 63 "parser.mly"
                                       ( Assign (IndexedVar (Var _1, _3), _6) )
# 494 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 64 "parser.mly"
                              ( If (_3, _5, None) )
# 502 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 66 "parser.mly"
                              ( If (_3, _5, Some _7) )
# 511 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 67 "parser.mly"
                              ( While (_3, _5) )
# 519 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 68 "parser.mly"
                              ( CallProc ("sprint", [StrExp _3]) )
# 526 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    Obj.repr(
# 69 "parser.mly"
                              ( CallProc ("iprint", [_3]) )
# 533 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 70 "parser.mly"
                           ( CallProc ("scan", [VarExp (Var _3)]) )
# 540 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 71 "parser.mly"
                           ( CallProc ("new", [ VarExp (Var _3)]) )
# 547 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'aargs_opt) in
    Obj.repr(
# 72 "parser.mly"
                                ( CallProc (_1, _3) )
# 555 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 73 "parser.mly"
                           ( CallProc ("return", [_2]) )
# 562 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 74 "parser.mly"
             ( _1 )
# 569 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 75 "parser.mly"
            ( NilStmt )
# 575 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "parser.mly"
                           ( [] )
# 581 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aargs) in
    Obj.repr(
# 79 "parser.mly"
                           ( _1 )
# 588 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 82 "parser.mly"
                          ( _1@[_3] )
# 596 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 83 "parser.mly"
                           ( [_1] )
# 603 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'decs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 86 "parser.mly"
                         ( Block (_2, _3) )
# 611 "parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 89 "parser.mly"
           ( IntExp _1  )
# 618 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 90 "parser.mly"
          ( VarExp (Var _1) )
# 625 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'aargs_opt) in
    Obj.repr(
# 91 "parser.mly"
                          ( CallFunc (_1, _3) )
# 633 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 92 "parser.mly"
                      ( VarExp (IndexedVar (Var _1, _3)) )
# 641 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 93 "parser.mly"
                      ( CallFunc ("+", [_1; _3]) )
# 649 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 94 "parser.mly"
                       ( CallFunc ("-", [_1; _3]) )
# 657 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 95 "parser.mly"
                       ( CallFunc ("*", [_1; _3]) )
# 665 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                     ( CallFunc ("/", [_1; _3]) )
# 673 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 97 "parser.mly"
                     ( CallFunc ("-", [_1; CallFunc ("*", [CallFunc ("/", [_1; _3]); _3])]))
# 681 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
                       ( CallFunc ("^", [_1; _3]) )
# 689 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 99 "parser.mly"
                               ( CallFunc("!", [_2]) )
# 696 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 100 "parser.mly"
                   ( _2 )
# 703 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 103 "parser.mly"
                     ( CallFunc ("==", [_1; _3]) )
# 711 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 104 "parser.mly"
                     ( CallFunc ("!=", [_1; _3]) )
# 719 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 105 "parser.mly"
                     ( CallFunc (">", [_1; _3]) )
# 727 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                     ( CallFunc ("<", [_1; _3]) )
# 735 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 107 "parser.mly"
                     ( CallFunc (">=", [_1; _3]) )
# 743 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 108 "parser.mly"
                     ( CallFunc ("<=", [_1; _3]) )
# 751 "parser.ml"
               : 'cond))
(* Entry prog *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let prog (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.stmt)
;;
