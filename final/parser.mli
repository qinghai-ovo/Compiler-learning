type token =
  | NUM of (
# 9 "parser.mly"
        int
# 6 "parser.mli"
)
  | STR of (
# 10 "parser.mly"
        string
# 11 "parser.mli"
)
  | ID of (
# 10 "parser.mly"
        string
# 16 "parser.mli"
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

val prog :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.stmt
