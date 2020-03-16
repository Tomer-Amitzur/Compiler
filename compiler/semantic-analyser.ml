#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;


(* -----------------------------Lexical Adreesing HELPERS---------------------------------------------- *)

  let rec check_env local_env var min = 
    match local_env with 
      | [] -> None
      | head::tail -> 
        if head = var then Some(min) else match (check_env tail var (min+1)) with  
                                            | Some(min) -> Some(min)
                                            | None -> None                           


  let rec search_var local_envs var maj = 
    (match local_envs with 
      | [] -> VarFree(var)
      | head::tail -> 
        (match maj with 
          | (-1) -> (match (check_env head var 0) with 
                    | None -> search_var tail var 0
                    | Some(min) -> VarParam(var, min))
          | (x) -> (match (check_env head var 0) with
                    | None -> search_var tail var (maj+1)
                    | Some(min) -> VarBound(var, x, min))))


(* ------------------------------Lexical Addressing RECURSIVE FUNCTION------------------------------------------ *)

  let rec lex_rec exp local_envs = 
    (match exp with 
      | Const(x) -> Const'(x)
      | Var(x) -> Var'(search_var local_envs x (-1))
      | If(test, dit, dif) -> If'((lex_rec test local_envs), (lex_rec dit local_envs), (lex_rec dif local_envs))
      | Seq(exp_lst) -> Seq'(List.map (fun (x) -> lex_rec x local_envs) exp_lst)
      | Set(var, exp) -> Set'((lex_rec var local_envs), (lex_rec exp local_envs))
      | Def(var, exp) -> Def'((lex_rec var local_envs), (lex_rec exp local_envs))
      | Or(exp_lst) -> Or'(List.map (fun (x) -> lex_rec x local_envs) exp_lst)
      | LambdaSimple(params, body) -> 
          LambdaSimple'(params, (lex_rec body ([params] @ local_envs)))
      | LambdaOpt (params, param ,body) -> 
          let new_params = params @ [param] in  
          LambdaOpt'(params, param, (lex_rec body ([new_params] @ local_envs)))
      | Applic(proc, args) -> Applic'((lex_rec proc local_envs), (List.map (fun (x) -> lex_rec x local_envs) args)));;

	
  (* --------------------------------------Tail Calls RECURSIVE FUNCTION---------------------------------------------------------------\ *)

   let rec tail_calls e in_tp =
  (match e with
    | If' (test , dit , dif) ->  If'( (tail_calls test false) , (tail_calls dit in_tp) , (tail_calls dif in_tp) )                                          
    | Seq' (expr_list) -> Seq'((annotate_list expr_list in_tp))
    | Set' (var , expr) -> Set' (var , (tail_calls expr false))
    | Def' (var , expr) -> Def' (var , (tail_calls expr false))
    | Or' (expr_list) -> Or'((annotate_list expr_list in_tp))
    | LambdaSimple' (params , body) -> LambdaSimple'(params , (tail_calls body true))
    | LambdaOpt' (params , opt , body) -> LambdaOpt' (params , opt , (tail_calls body true))
    | Applic' (proc , args_list) -> 
        (match in_tp with
        | true -> ApplicTP'( (tail_calls proc false) , (List.map (fun (x) -> tail_calls x false) args_list))
        | _ -> Applic'( (tail_calls proc false) , (List.map (fun (x) -> tail_calls x false) args_list)))
    | ApplicTP' (proc , args_list) -> ApplicTP'( (tail_calls proc false) , (List.map (fun (x) -> tail_calls x false) args_list))
    | _ -> e)

    and annotate_list list in_tp =
    (match list with
      | exp :: [] -> [(tail_calls exp in_tp)]
      | exp :: rest -> (List.append [(tail_calls exp false)] (annotate_list rest in_tp))
      | _ -> raise X_syntax_error);;
    
(* ----------------------------------------Boxing RECURSIVE FUNCTION------------------------------------------------------------------- *)
(* ----------------------------------------Boxing RECURSIVE FUNCTION------------------------------------------------------------------- *)
(* ----------------------------------------Boxing RECURSIVE FUNCTION------------------------------------------------------------------- *)

let rec expr_box expr var = match expr with 
                          | If' (test , dit , dif) ->  If'((expr_box test var), (expr_box dit var) , (expr_box dif var))                                          
                          | Seq' (expr_list) -> Seq'(List.map (fun (x) -> expr_box x var) expr_list)
                          | Set' (var2 , exp) -> (match var2 with
                                                | Var'(x) ->  (match x with 
                                                            | VarBound(var_name, int1, int2) ->  if (var_name = var) then BoxSet'(x, (expr_box exp var)) else Set' (var2 , (expr_box exp var))
                                                            | VarParam(var_name, int) -> if (var_name = var) then BoxSet'(x, (expr_box exp var)) else Set' (var2 , (expr_box exp var))
                                                            | _ -> Set' (var2 , (expr_box exp var)))
                                                | _ -> raise X_syntax_error)
                          | BoxSet' (var2 , expr) -> BoxSet'(var2 , (expr_box expr var))
                          | Var'(x) -> (match x with 
                                                | VarBound(var_name, int1, int2) ->  if (var_name = var) then BoxGet'(x) else expr
                                                | VarParam(var_name, int) -> if (var_name = var) then BoxGet'(x) else expr
                                                | _ -> expr)
                          | Def' (var2 , expr) -> Def' (var2 , (expr_box expr var))
                          | Or' (expr_list) -> Or'((List.map (fun (x) -> expr_box x var) expr_list))
                          | LambdaSimple' (params , body) -> (match (List.mem var params) with 
                                                                  | true -> LambdaSimple' (params , body)
                                                                  | false -> LambdaSimple'(params, (expr_box body var)))
                          | LambdaOpt' (params , opt , body) -> (match (List.mem var (params @ [opt])) with 
                                                                  | true -> LambdaOpt' (params, opt,  body)
                                                                  | false -> LambdaOpt'(params, opt, (expr_box body var)))
                          | Applic' (proc , args_list) -> Applic'((expr_box proc var), (List.map (fun (x) -> expr_box x var) args_list))
                          | ApplicTP' (proc , args_list) -> ApplicTP'((expr_box proc var), (List.map (fun (x) -> expr_box x var) args_list))

                          | _ -> expr

let rec body_change params_list boxing_lst body = match boxing_lst with
                                | [] -> body  
                                | var :: tail -> 
                                      (match body with 
                                              | Seq'(exprs_list) -> 
                                                        let new_exprs_lst = List.map (fun (exp) -> (expr_box exp var)) exprs_list in 
                                                        let new_body = Seq'(new_exprs_lst) in 
                                                        body_change params_list tail new_body 
                                              | exp -> 
                                                        let new_exp = expr_box exp var in
                                                        let new_body = new_exp in 
                                                        body_change params_list tail new_body)




(*--------------------------------------------------------Check if need to box----------------------------------------------------------------*)
(*-----------------------------------------------------------------------------------------------------------------------------------------------*)
(*------------------------------------------------Helpers for checking if var is param/bound0/bound-------------------------------------------------------------*)
let rec check_bound_0_rec var exp = match exp with 
                                | If' (test , dit , dif) ->  ((check_bound_0_rec var test) || (check_bound_0_rec var dit) || (check_bound_0_rec var dif))                                          
                                | Seq' (expr_list) -> (List.fold_right (||) (List.map (fun (x) -> check_bound_0_rec var x) expr_list) (false))
                                | Set' (var2 , expr) -> ((check_bound_0_rec var var2) || (check_bound_0_rec var expr))
                                | Var'(x) -> (match x with 
                                                | VarBound(var_name, 0 ,int) -> if (var_name = var) then true else false
                                                | _ -> false)
                                | Def' (var2 , expr) -> (check_bound_0_rec var expr)
                                | Or' (expr_list) -> (List.fold_right (||) (List.map (fun (x) -> check_bound_0_rec var x) expr_list) (false))
                                | LambdaSimple' (params , body) -> (check_bound_0_rec var body)
                                | LambdaOpt' (params , opt , body) -> (check_bound_0_rec var body)
                                | Applic' (proc , args_list) -> ((check_bound_0_rec var proc) || (List.fold_right (||) (List.map (fun (x) -> check_bound_0_rec var x) args_list) (false)))
                                | ApplicTP' (proc , args_list) -> ((check_bound_0_rec var proc) || (List.fold_right (||) (List.map (fun (x) -> check_bound_0_rec var x) args_list) (false)))
                                | _ -> false  

let check_bound_0 var lambda = (match lambda with 
                                | LambdaSimple'(params, body) -> check_bound_0_rec var body 
                                | LambdaOpt'(params, opt, body) -> check_bound_0_rec var body
                                | _ -> raise X_syntax_error)

let rec check_bound_rec var exp = match exp with 
                                | If' (test , dit , dif) ->  ((check_bound_rec var test) || (check_bound_rec var dit) || (check_bound_rec var dif))                                          
                                | Seq' (expr_list) -> (List.fold_right (||) (List.map (fun (x) -> check_bound_rec var x) expr_list) (false))
                                | Set' (var2 , expr) -> ((check_bound_rec var var2) || (check_bound_rec var expr))
                                | Var'(x) -> (match x with 
                                                | VarBound(var_name, int1 , int2) -> if (var_name = var) then true else false
                                                | _ -> false)
                                | Def' (var2 , expr) -> (check_bound_rec var expr)
                                | Or' (expr_list) -> (List.fold_right (||) (List.map (fun (x) -> check_bound_rec var x) expr_list) (false))
                                | LambdaSimple' (params , body) -> (check_bound_rec var body)
                                | LambdaOpt' (params , opt , body) -> (check_bound_rec var body)
                                | Applic' (proc , args_list) -> ((check_bound_rec var proc) || (List.fold_right (||) (List.map (fun (x) -> check_bound_rec var x) args_list) (false)))
                                | ApplicTP' (proc , args_list) -> ((check_bound_rec var proc) || (List.fold_right (||) (List.map (fun (x) -> check_bound_rec var x) args_list) (false)))
                                | _ -> false  


let check_bound var lambda = (match lambda with 
                                | LambdaSimple'(params, body) -> check_bound_rec var body 
                                | LambdaOpt'(params, opt, body) -> check_bound_rec var body 
                                | _ -> raise X_syntax_error)

let rec check_param_rec var exp = match exp with 
                                | If' (test , dit , dif) ->  ((check_param_rec var test) || (check_param_rec var dit) || (check_param_rec var dif))                                          
                                | Seq' (expr_list) -> (List.fold_right (||) (List.map (fun (x) -> check_param_rec var x) expr_list) (false))
                                | Set' (var2 , expr) -> ((check_param_rec var var2) || (check_param_rec var expr))
                                | Var'(x) -> (match x with 
                                                | VarParam(var_name, int) -> if (var_name = var) then true else false
                                                | _ -> false)
                                | Def' (var2 , expr) -> (check_param_rec var expr)
                                | Or' (expr_list) -> (List.fold_right (||) (List.map (fun (x) -> check_bound_rec var x) expr_list) (false))
                                | LambdaSimple' (params , body) -> (check_param_rec var body)
                                | LambdaOpt' (params , opt , body) -> (check_param_rec var body)
                                | Applic' (proc , args_list) -> ((check_param_rec var proc) || (List.fold_right (||) (List.map (fun (x) -> check_param_rec var x) args_list) (false)))
                                | ApplicTP' (proc , args_list) -> ((check_param_rec var proc) || (List.fold_right (||) (List.map (fun (x) -> check_param_rec var x) args_list) (false)))
                                | _ -> false


let check_param var lambda = (match lambda with 
                                | LambdaSimple'(params, body) -> check_param_rec var body 
                                | LambdaOpt'(params, opt, body) -> check_param_rec var body
                                | _ -> raise X_syntax_error)

(*------------------------------------------------looping over read & write lists and doing Cartesian multi-------------------------------------------------------------*)
let rec first_loop var read_lst write_lst =  
    match read_lst with 
        | [] -> false
        | read_lambda :: read_tail -> second_loop var read_lambda write_lst write_lst read_tail


and second_loop var read_lambda write_lst write_lst_org read_tail = 
    match write_lst with 
        | [] -> first_loop var read_tail write_lst_org 
        | write_lambda :: write_tail -> 
            if (read_lambda == write_lambda) 
                then second_loop var read_lambda write_tail write_lst_org read_tail 
                else ( if  ((check_bound_0 var read_lambda)
                      || (check_bound_0 var write_lambda) 
                      || ((check_param var read_lambda) && (check_bound var write_lambda)) 
                      || ((check_param var write_lambda) && (check_bound var read_lambda))) 
                      then true
                      else second_loop var read_lambda write_tail write_lst_org read_tail);;

(*------------------------------------------------Making lambda() lists-------------------------------------------------------------*)
(* ----------------------------------------------Helper functions for finding if var is read | write -------------------------------------------------------------------------- *)
let rec check_write_v var exp = match exp with
                                | If' (test , dit , dif) ->  ((check_write_v var test) || (check_write_v var dit) || (check_write_v var dif))                                          
                                | Seq' (expr_list) -> (List.fold_right (||) (List.map (fun (x) -> check_write_v var x) expr_list) (false))
                                | Set' (var2 , expr) -> 
                                    let check_var2 = (match var2 with 
                                                        | Var'(x) -> (match x with  
                                                            | VarBound(var_name, int1, int2) -> (var_name = var)
                                                            | VarParam(var_name, int) -> (var_name = var)
                                                            | VarFree(var_name) -> false)
                                                        | _ -> raise X_syntax_error) in 
                                    (match check_var2 with 
                                        | true -> true 
                                        | false -> (check_write_v var expr))
                                | Def' (var2 , expr) -> (check_write_v var expr)
                                | Or' (expr_list) -> (List.fold_right (||) (List.map (fun (x) -> check_write_v var x) expr_list) (false))
                                | LambdaSimple' (params , body) -> false
                                | LambdaOpt' (params , opt , body) ->  false
                                | Applic' (proc , args_list) -> ((check_write_v var proc) || (List.fold_right (||) (List.map (fun (x) -> check_write_v var x) args_list) (false)))
                                | ApplicTP' (proc , args_list) -> ((check_write_v var proc) || (List.fold_right (||) (List.map (fun (x) -> check_write_v var x) args_list) (false)))
                                | _ -> false

let rec check_read_v var exp = match exp with
                                | If' (test , dit , dif) ->  ((check_read_v var test) || (check_read_v var dit) || (check_read_v var dif))                                          
                                | Seq' (expr_list) -> (List.fold_right (||) (List.map (fun (x) -> check_read_v var x) expr_list) (false))
                                | Set' (var2 , expr) -> (check_read_v var expr)
                                | Var'(x) -> (match x with 
                                                | VarBound(var_name, int1, int2) -> (var_name = var)
                                                | VarParam(var_name, int) -> (var_name = var)
                                                | VarFree(var_name) -> false )
                                | Def' (var2 , expr) -> (check_read_v var expr)
                                | Or' (expr_list) -> (List.fold_right (||) (List.map (fun (x) -> check_read_v var x) expr_list) (false))
                                | LambdaSimple' (params , body) -> false
                                | LambdaOpt' (params , opt , body) ->  false
                                | Applic' (proc , args_list) -> ((check_read_v var proc) || (List.fold_right (||) (List.map (fun (x) -> check_read_v var x) args_list) (false)))
                                | ApplicTP' (proc , args_list) -> ((check_read_v var proc) || (List.fold_right (||) (List.map (fun (x) -> check_read_v var x) args_list) (false)))
                                | _ -> false




(* ----------------------------------------------Main functions for finding if var is read | write -------------------------------------------------------------------------- *)
let rec write_lst_fun var exp lst = match exp with 
                                | If' (test , dit , dif) ->  ((write_lst_fun var test lst) @ (write_lst_fun var dit lst) @ (write_lst_fun var dif lst))                                          
                                | Seq' (expr_list) -> (List.fold_right (@) (List.map (fun (x) -> write_lst_fun var x lst) expr_list) ([]))
                                | Set' (var2 , expr) -> (write_lst_fun var expr lst)
                                | Def' (var2 , expr) -> (write_lst_fun var expr lst)
                                | Or' (expr_list) -> (List.fold_right (@) (List.map (fun (x) -> write_lst_fun var x lst) expr_list) ([]))
                                | LambdaSimple' (params , body) -> if  (check_write_v var body) then ((write_lst_fun var body lst) @ [exp]) else (write_lst_fun var body lst) 
                                | LambdaOpt' (params , opt , body) ->  if  (check_write_v var body) then ((write_lst_fun var body lst) @ [exp]) else (write_lst_fun var body lst) 
                                | Applic' (proc , args_list) -> ((write_lst_fun var proc lst) @ (List.fold_right (@) (List.map (fun (x) -> write_lst_fun var x lst) args_list) ([])))
                                | ApplicTP' (proc , args_list) -> ((write_lst_fun var proc lst) @ (List.fold_right (@) (List.map (fun (x) -> write_lst_fun var x lst) args_list) ([])))
                                | _ -> lst 


let rec read_lst_fun var exp lst = match exp with 
                                | If' (test , dit , dif) ->  ((read_lst_fun var test lst) @ (read_lst_fun var dit lst) @ (read_lst_fun var dif lst))                                          
                                | Seq' (expr_list) -> (List.fold_right (@) (List.map (fun (x) -> read_lst_fun var x lst) expr_list) ([]))
                                | Set' (var2 , expr) -> (read_lst_fun var expr lst)
                                | Def' (var2 , expr) -> (read_lst_fun var expr lst)
                                | Or' (expr_list) -> (List.fold_right (@) (List.map (fun (x) -> read_lst_fun var x lst) expr_list) ([]))
                                | LambdaSimple' (params , body) -> if  (check_read_v var body) then ((read_lst_fun var body lst) @ [exp]) else (read_lst_fun var body lst) 
                                | LambdaOpt' (params , opt , body) ->  if  (check_read_v var body) then ((read_lst_fun var body lst) @ [exp]) else (read_lst_fun var body lst) 
                                | Applic' (proc , args_list) -> ((read_lst_fun var proc lst) @ (List.fold_right (@) (List.map (fun (x) -> read_lst_fun var x lst) args_list) ([])))
                                | ApplicTP' (proc , args_list) -> ((read_lst_fun var proc lst) @ (List.fold_right (@) (List.map (fun (x) -> read_lst_fun var x lst) args_list) ([])))
                                | _ -> lst 


(*------------------------------------------------Main func of checking if need to box-------------------------------------------------------------*)
let rec check_box var body = 
    let read_lst = read_lst_fun var body [] in 
    let write_lst = write_lst_fun var body [] in
    first_loop var read_lst write_lst
    

let rec make_sets params_list vars_list = 
  (match vars_list with
  | [] -> []
  | var :: rest -> let minor = (match (check_env params_list var 0) with 
                                             | Some(x) -> x
                                             | _ -> raise X_syntax_error) in
                  let y = [Set'(Var'(VarParam(var , minor)), Box'(VarParam(var , minor)))] in
                  (y @ (make_sets params_list rest)))

(*------------------------------------------------Recursive Main Boxing Func-------------------------------------------------------------*)
(*------------------------------------------------Recursive Main Boxing Func-------------------------------------------------------------*)
(*------------------------------------------------Recursive Main Boxing Func-------------------------------------------------------------*)
let rec box_rec e =
  (match e with
    | If' (test , dit , dif) ->  If'((box_rec test), (box_rec dit), (box_rec dif))                                          
    | Seq' (expr_list) -> Seq'(List.map box_rec expr_list)
    | Set' (var , expr) -> Set' (var, (box_rec expr))
    | Def' (var , expr) -> Def' (var , (box_rec expr))
    | Or' (expr_list) -> Or'(List.map box_rec expr_list)
    
    | LambdaSimple' (params, body) -> 
        let boxing_lst = (List.filter (fun (x) -> check_box x e) params) in
        let new_body = (match boxing_lst with 
                          | [] -> box_rec body 
                          | _ ->   let set_exsps = make_sets params boxing_lst in
                                   let temp_body = (body_change params boxing_lst body) in
                                   Seq'(set_exsps @ [temp_body])) in          
        LambdaSimple'(params, (box_rec new_body))

    | LambdaOpt' (params , opt , body) -> 
        let boxing_lst = (List.filter (fun (x) -> check_box x e) (params @ [opt])) in
        let new_body = (match boxing_lst with 
                          | [] -> box_rec body 
                          | _ ->   let set_exsps = make_sets (params @ [opt]) boxing_lst in
                                   let temp_body = (body_change (params @ [opt]) boxing_lst body) in
                                   Seq'(set_exsps @ [temp_body])) in  
        LambdaOpt'(params, opt, (box_rec new_body))

    | Applic' (proc , args_list) -> Applic'((box_rec proc), (List.map box_rec args_list)) 
    | ApplicTP' (proc , args_list) -> ApplicTP'((box_rec proc), (List.map box_rec args_list)) 
    | _ -> e)


exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let annotate_lexical_addresses e = lex_rec e [];;

let annotate_tail_calls e = tail_calls e false;;
(* (tail_calls e false);; *)

let box_set e = box_rec e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)



