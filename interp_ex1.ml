type id = string
type stmt = Stmts of stmt * stmt
        | Assign of id * exp
        | Print of exp
and exp = Id of id
        | Num of int
        | Plus of exp * exp
        | Minus of exp * exp
        | Times of exp * exp
        | Div of exp * exp
        | StmtExp of stmt * exp

exception No_such_symbol
let e0 = fun _ -> raise No_such_symbol
let update var vl env = fun v -> if v = var then vl else env v
(*update "x" 1 e0 -> (fun v -> if v = "x" then 1 else e0 v) = let e1
  update "y "2 e1 -> (fun v -> if v = "y" then 2 else e1 v) = let e2
  e2 "y"*)

let rec trans_stmt ast env = 
      match ast with
        | Stmts (s1,s2) -> let env' = trans_stmt s1 env in
                                       trans_stmt s2 env' 
        | Assign (var,e) -> let vl = trans_exp e env in
                                       update var vl env
        | Print e -> let vl = trans_exp e env in 
                         (print_int vl; print_string "\n"; env)
and trans_exp ast env =
      match ast with
        | Id v -> env v
        | Num n -> n
        | Plus (e1,e2) -> let vl1 = trans_exp e1 env in
                            let vl2 = trans_exp e2 env in
                                    vl1 + vl2
        | Minus (e1,e2) -> let vl1 = trans_exp e1 env in
                            let vl2 = trans_exp e2 env in
                                    vl1 - vl2
        | Times (e1,e2) -> let vl1 = trans_exp e1 env in
                            let vl2 = trans_exp e2 env in
                                    vl1 * vl2
        | Div (e1,e2) -> let vl1 = trans_exp e1 env in
                            let vl2 = trans_exp e2 env in
                                    vl1 / vl2
        (*ex1:「文」を「式」に埋め込む値構成子「StmtExp (文，式)」（「式」の値 を返す）を付加し，
        「文」の中で代入した変数を「式」で利用できる ようにしなさい．*)
        |StmtExp (s1, e1) -> let env' = trans_stmt s1 env in
                                trans_exp e1 env'



let prog = Stmts (Assign ("x",Plus (Num 1,Times (Num 2,Num 3))),
              Stmts (Assign ("y",Div (Id "x",Num 4)), Print (Id "y")))

let interp ast = trans_stmt ast e0
