#use "reader.ml";;
#use "topfind";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

exception X_sexp of string;;

(* -------------------------------------help functions------------------------------------------------------------ *)

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

let rec is_proper list = 
  match list with  
    | Nil -> true 
    | Pair(x, y) -> is_proper y
    | _ -> false;;

let rec string_the_list args ret = 
  (match args with 
  | Nil -> ret 
  | Pair(Symbol x, y) -> 
    let indic = List.mem x reserved_word_list in
    (match indic with 
      | true -> raise X_syntax_error
      | false -> string_the_list y (List.append ret [x]))
  | Symbol z -> List.append ret [z] 
  | _ -> raise X_syntax_error)


let rec string_the_list_no_last args ret = 
  (match args with 
  | Pair(Symbol x, y) -> 
    let indic = List.mem x reserved_word_list in
    (match indic with 
      | true -> raise X_syntax_error
      | false -> string_the_list_no_last y (List.append ret [x]))
  | Symbol z -> ret 
  | _ -> raise X_syntax_error)
  

let rec get_last list = 
  (match list with 
    | Symbol z -> z 
    | Pair(x, y) -> get_last y
    | _ -> raise X_syntax_error)

(* -------------------------------------------------------------------------------------------- *)





(* -------------------------------------THE TAG PARSE!---------------------------------------- *)
let rec tag_parse = function



(*-----------------------------MACRO EXPANSIONS-------------------------*)
(*---------------------------------And----------------------------------*)
  | Pair(Symbol("and"), Nil) -> Const(Sexpr(Bool(true)))
  | Pair(Symbol("and"), Pair(x, Nil)) -> tag_parse x
  | Pair(Symbol("and"), Pair(x, y)) -> If(tag_parse x, tag_parse (Pair(Symbol("and"), y)), Const(Sexpr(Bool(false))))




(*---------------------------------Let-------------------------*)
  | Pair (Symbol "let" , Pair (vars , body)) ->
      tag_parse (Pair(Pair(Symbol "lambda" , Pair(vars_list vars , body)), args_list vars))


(*---------------------------------Let*-------------------------*)
  | Pair(Symbol "let*" , Pair (vars , body)) ->
      (match vars with
        | Nil -> tag_parse (Pair (Symbol "let", Pair(vars, body)))
        | Pair(x, y) -> 
          (match y with 
            | Nil -> tag_parse (Pair (Symbol "let", Pair(vars, body)))
            | _ -> (match vars with 
                    | Pair(x, y) -> tag_parse (Pair (Symbol "let", Pair(Pair(x, Nil), Pair(Pair(Symbol "let*", Pair(y , body)), Nil))))
                    | _ -> raise X_syntax_error))
        | _ -> raise X_syntax_error)


(*---------------------------------Let rec-------------------------*)
  | Pair (Symbol "letrec" , Pair (vars , body)) ->
      tag_parse (Pair(Symbol "let" , Pair((letrec_vars_list vars) , (letrec_body vars body))))



(*---------------------------------Quasiquoted expressions-------------------------*)
  | Pair(Symbol("quasiquote"),Pair (sexp , Nil)) ->
    (match sexp with
          | Pair(Symbol "unquote-splicing" , sexpr) -> raise (X_sexp "unvalid expresion")
          | _ -> (quasi_exps sexp))
                



(*---------------------------------cond expressions-------------------------*)
  | Pair(Symbol "cond" , ribs) -> 
      cond_expander ribs 

               
(*---------------------------------define MIT expressions-------------------------*)
| Pair(Symbol "define" , Pair (Pair (var , args) , body )) -> 
    tag_parse (Pair(Symbol "define", Pair(var, Pair(Pair(Symbol "lambda", Pair(args, body)), Nil))))



(*------------------------------   CORE FORMS  -------------------------*)
(*---------------------------------Sequences---------------------------*)
  | Pair(Symbol("begin"), Nil) -> Const(Void) 
  | Pair(Symbol("begin"), args) -> 
    let args = tag_parse_list args [] in 
    (match args with 
    | x :: [] -> x
    | _ -> Seq(args))

(*---------------------------------Assignments-------------------------*)
  | Pair(Symbol("set!"), Pair(Symbol x, Pair(y, Nil))) -> 
    let var = Var(x) in 
    let exp = tag_parse y in 
    Set(var, exp)


(*---------------------------------Definitions-------------------------*)
  | Pair(Symbol("define"), Pair(Symbol x, Pair(y, Nil))) -> 
    let var = Var(x) in 
    let exp = tag_parse y in 
    Def(var, exp)


(*---------------------------------Disjunctions-------------------------*)
  | Pair(Symbol "or", args) -> (match args with 
    | Nil -> Const (Sexpr (Bool (false)))
    | _ -> let exps = tag_parse_list args [] in
            (match exps with
            | x :: [] -> x
            | _ -> Or(exps)))


(*---------------------------------Lambda Exps-------------------------*)
  | Pair(Symbol("lambda"), Pair(args, body)) -> 
      let exp_body = (match body with 
          | Pair(x, y) -> let exps = tag_parse_list body ([]) in
                          (match exps with
                          | x :: [] -> x
                          | _ -> Seq(exps)) 
          | _ -> tag_parse body) in 
      (match args with 
        | Symbol x -> LambdaOpt([], x, exp_body)
        | _ ->
        let proper = is_proper args in 
        let args_list = string_the_list args ([]) in 
        (match proper with 
          | true -> LambdaSimple(args_list, exp_body)
          | false -> 
            let last = get_last args in 
            let list = string_the_list_no_last args ([]) in 
            LambdaOpt(list, last, exp_body)))


(*---------------------------------Conditionals-------------------------*)
  | Pair(Symbol "if" , Pair(test, Pair(dit, Nil))) -> If(tag_parse test, tag_parse dit, Const (Void))
  | Pair(Symbol "if", Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parse test, tag_parse dit, tag_parse dif)


(*---------------------------------quote-------------------------*)

| Pair(Symbol("quote"), x) -> (match x with
                        | Pair(y,Nil) -> Const(Sexpr(y))
                        | _ -> raise X_syntax_error)


(*---------------------------------Applications-------------------------*)
| Pair(proc, args) -> 
    (match proc with
            | Symbol x -> let indicator = List.mem x reserved_word_list in 
                          (match indicator with
                            | false -> Applic(tag_parse proc, (tag_parse_list args []))
                            | _ -> raise X_syntax_error)
            | _ -> Applic(tag_parse proc, (tag_parse_list args [])))


(*-------------------------------------Vars-----------------------------*)
  | Symbol(x) -> 
    let indicator = List.mem x reserved_word_list in 
    (match indicator with 
      | false -> Var (x)
      | true -> raise X_syntax_error)


(*----------------------------------Constants---------------------------*)
  | TagRef(x) -> Const(Sexpr(TagRef (x)))

  | TaggedSexpr(x, y) -> (match y with
                      | Pair(first,sec) -> (match first with
                                        | Symbol "quote" -> 
                                              (match sec with 
                                                    | Pair(a,Nil) -> Const(Sexpr (TaggedSexpr (x, a)))
                                                    | _ -> raise X_syntax_error)
                                        | _ -> Const(Sexpr (TaggedSexpr (x, y))))
                      | _ -> Const(Sexpr (TaggedSexpr (x, y))))

  | Number (x) -> Const(Sexpr(Number(x)))
  | Bool (x) -> Const(Sexpr(Bool(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | String(x) -> Const(Sexpr(String(x)))

  | _ -> raise X_syntax_error



(*----------------------------------Recursive tag parsing list of elemnts---------------------------*)
  and tag_parse_list list ret =
    (match list with   
      | Nil -> ret 
      | Pair(x, y) ->  
        let x2 = tag_parse x in 
        tag_parse_list y (List.append ret [x2])
      | _ -> raise X_syntax_error)


(*------------------------------------------------------------------------------------------------------------------*)

  and quasi_exps sexp=
    (match sexp with
        | Pair(Symbol "unquote" , Pair (sexpr , Nil)) -> tag_parse sexpr
        | Pair(Symbol "unquote-splicing", Pair (sexpr , Nil)) -> tag_parse sexpr
        | Symbol x -> tag_parse (Pair(Symbol "quote" , Pair(sexp,Nil)))
        | Nil -> (tag_parse (Pair(Symbol "quote" , Pair(Nil,Nil))))
        | Pair(a,b) -> (match a with 
            | Pair(Symbol "unquote-splicing", Pair (expr , Nil)) -> Applic(tag_parse (Symbol "append"),[(tag_parse expr) ; (quasi_exps b)])
            | _ -> Applic(tag_parse (Symbol "cons"),[(quasi_exps a) ; (quasi_exps b)]))
        | _ -> (tag_parse sexp))

(*------------------------------------------------------------------------------------------------------------------*)

and cond_expander ribs=
    (match ribs with
        | Pair (x , Nil) -> (match x with
             | Pair (test , rest) -> (match test with 
                | Symbol "else" -> tag_parse (Pair (Symbol "begin" , rest))
                | _ -> (match rest with 
                    |  Pair (first , others) -> (match first with
                        | Symbol "=>" -> tag_parse (Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(test, Nil)), 
                                                                                Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, others)), Nil)),Nil)),
                                                                            Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Nil))), Nil))))
                        | _ -> tag_parse (Pair(Symbol "if", Pair(test, Pair(Pair(Symbol "begin", rest),Nil)))))
                    | _ -> raise X_syntax_error))
                | _ -> raise X_syntax_error)

        | Pair (x, y) -> (match x with
             | Pair (test , rest) -> (match test with 
                | Symbol "else" -> tag_parse (Pair (Symbol "begin" , rest))
                | _ -> (match rest with 
                    |  Pair (first , others) -> (match first with
                        | Symbol "=>" -> tag_parse (Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(test, Nil)), 
                                                                                Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, others)), Nil)),
                                                                                     Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(Pair (Symbol "cond" , y),Nil))),Nil)),Nil))), 
                                                                            Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil))))

     
                        | _ -> tag_parse (Pair(Symbol "if", Pair(test, Pair(Pair(Symbol "begin", rest), Pair (Pair (Symbol "cond" , y),Nil))))))
                    | _ -> raise X_syntax_error))
              | _ -> raise X_syntax_error)
        | _ -> raise X_syntax_error)



(*------------------------------------------------------------------------------------------------------------------*)
and vars_list vars=
  (match vars with
    | Nil -> Nil
    | Pair(first, rest) -> (match first with
                | Pair(var,init) -> Pair(var , (vars_list rest)) 
                | _ -> raise X_syntax_error)
    | _ -> raise X_syntax_error)


and args_list vars=
  (match vars with
    | Nil -> Nil
    | Pair(first, rest) -> (match first with
                | Pair(var,init) -> (match init with
                            | Pair (exp , Nil) ->  Pair(exp , (args_list rest))
                            | _ -> raise X_syntax_error)
                | _ -> raise X_syntax_error)
    | _ -> raise X_syntax_error)



and letrec_vars_list vars=
  (match vars with
    | Nil -> Nil
    | Pair(first, rest) -> (match first with
                | Pair(var,init) ->  Pair(Pair(var , Pair(Pair (Symbol "quote" , Pair (Symbol "whatever" ,Nil)),Nil)), (letrec_vars_list rest))
                | _ -> raise X_syntax_error)
    | _ -> raise X_syntax_error)



and letrec_body vars body=
  (match vars with
    | Nil -> body
    | Pair(first, rest) -> (match first with
                | Pair(var , init) ->  Pair(Pair(Symbol "set!" , Pair (var ,init)), (letrec_body rest body))
                | _ -> raise X_syntax_error)
    | _ -> raise X_syntax_error)


(*------------------------------------------------------------------------------------------------------------------*)


module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let tag_parse_expression sexpr = tag_parse sexpr;;

let tag_parse_expressions sexpr = List.map tag_parse sexpr;;

  
end;; (* struct Tag_Parser *)

