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
  | MOD
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

open Parsing
let _ = parse_error;;
# 2 "parser.mly"

open Printf
open Ast

# 57 "parser.ml"
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
  279 (* MOD *);
  280 (* LB *);
  281 (* RB *);
  282 (* LS *);
  283 (* RS *);
  284 (* LP *);
  285 (* RP *);
  286 (* ASSIGN *);
  287 (* SEMI *);
  288 (* COMMA *);
  289 (* TYPE *);
  290 (* VOID *);
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
\012\000\012\000\012\000\012\000\012\000\012\000\000\000"

let yylen = "\002\000\
\001\000\001\000\004\000\001\000\002\000\000\000\003\000\005\000\
\005\000\006\000\006\000\003\000\001\000\000\000\001\000\004\000\
\002\000\002\000\001\000\004\000\007\000\005\000\007\000\005\000\
\005\000\005\000\005\000\005\000\005\000\003\000\001\000\001\000\
\000\000\001\000\003\000\001\000\004\000\001\000\001\000\004\000\
\004\000\003\000\003\000\003\000\003\000\003\000\002\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\006\000\032\000\055\000\001\000\031\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\038\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\047\000\000\000\000\000\000\000\000\000\
\000\000\000\000\030\000\000\000\000\000\000\000\000\000\000\000\
\019\000\000\000\005\000\000\000\000\000\000\000\000\000\020\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\048\000\000\000\000\000\
\044\000\045\000\046\000\000\000\000\000\000\000\000\000\000\000\
\000\000\037\000\018\000\000\000\029\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\024\000\025\000\026\000\
\027\000\041\000\040\000\028\000\000\000\000\000\000\000\000\000\
\000\000\007\000\000\000\000\000\000\000\003\000\004\000\000\000\
\000\000\000\000\000\000\000\000\000\000\012\000\021\000\023\000\
\009\000\017\000\000\000\000\000\000\000\008\000\011\000\000\000\
\010\000\016\000"

let yydgoto = "\002\000\
\013\000\014\000\121\000\030\000\059\000\089\000\032\000\122\000\
\015\000\123\000\060\000\037\000\033\000\034\000"

let yysindex = "\005\000\
\090\255\000\000\242\254\243\254\001\255\006\255\022\255\025\255\
\027\255\034\255\000\000\000\000\000\000\000\000\000\000\027\255\
\027\255\027\255\027\255\027\255\044\255\027\255\084\255\000\000\
\037\255\027\255\027\255\179\255\088\255\018\255\131\255\220\255\
\065\255\071\255\184\255\174\255\076\255\082\255\083\255\052\255\
\093\255\027\255\027\255\000\000\215\255\027\255\027\255\027\255\
\027\255\027\255\000\000\094\255\242\254\087\255\126\255\127\255\
\000\000\130\255\000\000\061\255\101\255\104\255\027\255\000\000\
\027\255\027\255\027\255\027\255\027\255\027\255\090\255\090\255\
\113\255\114\255\115\255\154\255\120\255\000\000\079\255\079\255\
\000\000\000\000\000\000\125\255\166\255\138\255\141\255\060\255\
\244\254\000\000\000\000\027\255\000\000\220\255\220\255\220\255\
\220\255\220\255\220\255\220\255\156\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\152\255\073\255\073\255\073\255\
\027\255\000\000\187\255\197\255\090\255\000\000\000\000\160\255\
\189\255\180\255\176\255\182\255\202\255\000\000\000\000\000\000\
\000\000\000\000\188\255\073\255\188\255\000\000\000\000\210\255\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\185\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\105\255\000\000\000\000\000\000\000\000\000\000\000\000\232\254\
\000\000\198\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\185\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\223\255\000\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\128\255\151\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\078\255\
\000\000\000\000\000\000\000\000\000\000\016\255\200\255\201\255\
\203\255\216\255\217\255\218\255\001\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\219\255\219\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\221\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\228\255\230\255\000\000\000\000\000\000\247\255\119\000\
\205\255\000\000\000\000\229\000\208\000\000\000"

let yytablesize = 288
let yytable = "\028\000\
\022\000\057\000\002\000\058\000\036\000\001\000\031\000\036\000\
\035\000\036\000\036\000\016\000\040\000\017\000\019\000\018\000\
\044\000\045\000\114\000\115\000\053\000\054\000\004\000\005\000\
\006\000\007\000\008\000\024\000\020\000\025\000\002\000\091\000\
\076\000\021\000\009\000\010\000\079\000\080\000\081\000\082\000\
\083\000\011\000\101\000\102\000\035\000\039\000\026\000\035\000\
\012\000\022\000\055\000\056\000\023\000\094\000\027\000\095\000\
\096\000\097\000\098\000\099\000\100\000\029\000\042\000\003\000\
\043\000\004\000\005\000\006\000\007\000\008\000\046\000\047\000\
\048\000\049\000\050\000\119\000\054\000\009\000\010\000\135\000\
\074\000\137\000\116\000\120\000\011\000\090\000\041\000\112\000\
\128\000\113\000\052\000\012\000\003\000\062\000\004\000\005\000\
\006\000\007\000\008\000\048\000\049\000\050\000\063\000\125\000\
\071\000\136\000\009\000\010\000\013\000\013\000\072\000\073\000\
\085\000\011\000\039\000\039\000\039\000\039\000\039\000\039\000\
\012\000\075\000\084\000\039\000\039\000\039\000\039\000\039\000\
\086\000\087\000\092\000\039\000\088\000\039\000\093\000\039\000\
\039\000\042\000\042\000\042\000\042\000\042\000\042\000\103\000\
\104\000\105\000\042\000\042\000\107\000\046\000\047\000\048\000\
\049\000\050\000\042\000\108\000\042\000\061\000\042\000\042\000\
\043\000\043\000\043\000\043\000\043\000\043\000\109\000\110\000\
\111\000\043\000\043\000\117\000\046\000\047\000\048\000\049\000\
\050\000\043\000\118\000\043\000\106\000\043\000\043\000\065\000\
\066\000\067\000\068\000\069\000\070\000\126\000\129\000\130\000\
\046\000\047\000\048\000\049\000\050\000\046\000\047\000\048\000\
\049\000\050\000\046\000\047\000\048\000\049\000\050\000\132\000\
\131\000\051\000\133\000\011\000\138\000\033\000\064\000\046\000\
\047\000\048\000\049\000\050\000\046\000\047\000\048\000\049\000\
\050\000\004\000\034\000\127\000\049\000\050\000\124\000\051\000\
\134\000\046\000\047\000\048\000\049\000\050\000\046\000\047\000\
\048\000\049\000\050\000\078\000\052\000\053\000\054\000\014\000\
\038\000\015\000\077\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\022\000\000\000\022\000\022\000\022\000\
\022\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\022\000\022\000\000\000\000\000\000\000\000\000\000\000\
\022\000\022\000\000\000\000\000\000\000\000\000\000\000\022\000"

let yycheck = "\009\000\
\000\000\030\000\003\001\030\000\029\001\001\000\016\000\032\001\
\018\000\019\000\020\000\026\001\022\000\028\001\028\001\030\001\
\026\000\027\000\031\001\032\001\003\001\004\001\005\001\006\001\
\007\001\008\001\009\001\001\001\028\001\003\001\031\001\060\000\
\042\000\028\001\017\001\018\001\046\000\047\000\048\000\049\000\
\050\000\024\001\071\000\072\000\029\001\002\001\020\001\032\001\
\031\001\028\001\033\001\034\001\028\001\063\000\028\001\065\000\
\066\000\067\000\068\000\069\000\070\000\028\001\026\001\003\001\
\028\001\005\001\006\001\007\001\008\001\009\001\019\001\020\001\
\021\001\022\001\023\001\003\001\004\001\017\001\018\001\131\000\
\029\001\133\000\092\000\110\000\024\001\025\001\003\001\028\001\
\117\000\030\001\003\001\031\001\003\001\029\001\005\001\006\001\
\007\001\008\001\009\001\021\001\022\001\023\001\032\001\113\000\
\029\001\132\000\017\001\018\001\031\001\032\001\029\001\029\001\
\026\001\024\001\010\001\011\001\012\001\013\001\014\001\015\001\
\031\001\029\001\029\001\019\001\020\001\021\001\022\001\023\001\
\003\001\003\001\030\001\027\001\003\001\029\001\031\001\031\001\
\032\001\010\001\011\001\012\001\013\001\014\001\015\001\031\001\
\031\001\031\001\019\001\020\001\029\001\019\001\020\001\021\001\
\022\001\023\001\027\001\031\001\029\001\027\001\031\001\032\001\
\010\001\011\001\012\001\013\001\014\001\015\001\001\001\030\001\
\028\001\019\001\020\001\016\001\019\001\020\001\021\001\022\001\
\023\001\027\001\027\001\029\001\027\001\031\001\032\001\010\001\
\011\001\012\001\013\001\014\001\015\001\003\001\031\001\003\001\
\019\001\020\001\021\001\022\001\023\001\019\001\020\001\021\001\
\022\001\023\001\019\001\020\001\021\001\022\001\023\001\032\001\
\029\001\031\001\029\001\024\001\003\001\029\001\031\001\019\001\
\020\001\021\001\022\001\023\001\019\001\020\001\021\001\022\001\
\023\001\003\001\029\001\031\001\029\001\029\001\112\000\029\001\
\031\001\019\001\020\001\021\001\022\001\023\001\019\001\020\001\
\021\001\022\001\023\001\029\001\029\001\029\001\029\001\029\001\
\020\000\029\001\043\000\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\003\001\255\255\005\001\006\001\007\001\
\008\001\009\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\017\001\018\001\255\255\255\255\255\255\255\255\255\255\
\024\001\025\001\255\255\255\255\255\255\255\255\255\255\031\001"

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
  MOD\000\
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
# 26 "parser.mly"
             (  _1  )
# 308 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 29 "parser.mly"
           ( IntTyp )
# 314 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 30 "parser.mly"
                     ( ArrayTyp (_3, IntTyp) )
# 321 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 31 "parser.mly"
               ( NameTyp _1 )
# 328 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'dec) in
    Obj.repr(
# 34 "parser.mly"
                ( _1@_2 )
# 336 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    Obj.repr(
# 35 "parser.mly"
                ( [] )
# 342 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'ids) in
    Obj.repr(
# 38 "parser.mly"
                     ( List.map (fun x -> VarDec (_1,x, None)) _2 )
# 350 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 39 "parser.mly"
                              ( [VarDec (_1, _2, Some _4)] )
# 359 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    Obj.repr(
# 40 "parser.mly"
                              ( [TypeDec (_2,_4)] )
# 367 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 41 "parser.mly"
                                    ( [FuncDec(_2, _4, _1, _6)] )
# 377 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 42 "parser.mly"
                                      ( [FuncDec(_2, _4, VoidTyp, _6)] )
# 386 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ids) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 45 "parser.mly"
                       ( _1@[_3] )
# 394 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 46 "parser.mly"
                       ( [_1]  )
# 401 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    Obj.repr(
# 49 "parser.mly"
                        ( [] )
# 407 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fargs) in
    Obj.repr(
# 50 "parser.mly"
                        ( _1 )
# 414 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'fargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 53 "parser.mly"
                             ( _1@[(_3,_4)] )
# 423 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 54 "parser.mly"
                             ( [(_1,_2)] )
# 431 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 57 "parser.mly"
                   ( _1@[_2] )
# 439 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 58 "parser.mly"
                   ( [_1] )
# 446 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 61 "parser.mly"
                              ( Assign (Var _1, _3) )
# 454 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 62 "parser.mly"
                                       ( Assign (IndexedVar (Var _1, _3), _6) )
# 463 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 63 "parser.mly"
                              ( If (_3, _5, None) )
# 471 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 65 "parser.mly"
                              ( If (_3, _5, Some _7) )
# 480 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 66 "parser.mly"
                              ( While (_3, _5) )
# 488 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 67 "parser.mly"
                              ( CallProc ("sprint", [StrExp _3]) )
# 495 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    Obj.repr(
# 68 "parser.mly"
                              ( CallProc ("iprint", [_3]) )
# 502 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 69 "parser.mly"
                           ( CallProc ("scan", [VarExp (Var _3)]) )
# 509 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 70 "parser.mly"
                           ( CallProc ("new", [ VarExp (Var _3)]) )
# 516 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'aargs_opt) in
    Obj.repr(
# 71 "parser.mly"
                                ( CallProc (_1, _3) )
# 524 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 72 "parser.mly"
                           ( CallProc ("return", [_2]) )
# 531 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 73 "parser.mly"
             ( _1 )
# 538 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
            ( NilStmt )
# 544 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 77 "parser.mly"
                           ( [] )
# 550 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aargs) in
    Obj.repr(
# 78 "parser.mly"
                           ( _1 )
# 557 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 81 "parser.mly"
                          ( _1@[_3] )
# 565 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 82 "parser.mly"
                           ( [_1] )
# 572 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'decs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 85 "parser.mly"
                         ( Block (_2, _3) )
# 580 "parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 88 "parser.mly"
           ( IntExp _1  )
# 587 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 89 "parser.mly"
          ( VarExp (Var _1) )
# 594 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'aargs_opt) in
    Obj.repr(
# 90 "parser.mly"
                          ( CallFunc (_1, _3) )
# 602 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 91 "parser.mly"
                      ( VarExp (IndexedVar (Var _1, _3)) )
# 610 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 92 "parser.mly"
                      ( CallFunc ("+", [_1; _3]) )
# 618 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 93 "parser.mly"
                       ( CallFunc ("-", [_1; _3]) )
# 626 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 94 "parser.mly"
                       ( CallFunc ("*", [_1; _3]) )
# 634 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 95 "parser.mly"
                     ( CallFunc ("/", [_1; _3]) )
# 642 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                     ( CallFunc ("-", [_1; CallFunc ("*", [CallFunc ("/", [_1; _3]); _3])]))
# 650 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 97 "parser.mly"
                               ( CallFunc("!", [_2]) )
# 657 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
                   ( _2 )
# 664 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 101 "parser.mly"
                     ( CallFunc ("==", [_1; _3]) )
# 672 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 102 "parser.mly"
                     ( CallFunc ("!=", [_1; _3]) )
# 680 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 103 "parser.mly"
                     ( CallFunc (">", [_1; _3]) )
# 688 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 104 "parser.mly"
                     ( CallFunc ("<", [_1; _3]) )
# 696 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 105 "parser.mly"
                     ( CallFunc (">=", [_1; _3]) )
# 704 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                     ( CallFunc ("<=", [_1; _3]) )
# 712 "parser.ml"
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
