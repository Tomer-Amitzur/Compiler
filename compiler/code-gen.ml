#use "reader.ml"
#use "semantic-analyser.ml";;



(* ------------------------------------------------------------------------------------------------------------------------------------------- *)
(* -------------------------------------------------RENAMING FUNCTION------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------------------------------------------------------- *)
let tagged_lst = ref [];;

let rec renaming_sexp sexp ind = (match sexp with
  | Pair (sexpr1, sexpr2) -> Pair((renaming_sexp sexpr1 ind), (renaming_sexp sexpr2 ind))
  | TaggedSexpr (var, sexpr) -> TaggedSexpr((var ^ (string_of_int ind)), (renaming_sexp sexpr ind))
  | TagRef (var) -> TagRef((var ^ (string_of_int ind)))
  | _ -> sexp);;

 



let rec renaming_ast ast ind = match ast with 
  | Const'(x) -> (match x with 
                  | Void -> (ast) 
                  | Sexpr(sexp) -> (match sexp with 
                                    | TaggedSexpr(var, exp) -> (Const'(Sexpr(TaggedSexpr((var ^ (string_of_int ind)), (renaming_sexp exp ind)))))
                                    | TagRef(var) -> Const'(Sexpr(TagRef((var ^ (string_of_int ind)))))
                                    | Pair(first, sec) -> Const'(Sexpr(renaming_sexp sexp ind))
                                    | _-> ast))
  | Var' (var) -> ast
  | Box'(x) -> ast 
  | BoxGet'(x) -> ast 
  | BoxSet'(var, exp) -> BoxSet'(var, (renaming_ast exp ind)) 
  | If'(test, dit, dif) -> If'((renaming_ast test ind), (renaming_ast dit ind), (renaming_ast dif ind))
  | Seq'(exprs_lst) -> Seq'(List.map (fun (x) -> (renaming_ast x ind)) exprs_lst)
  | Set'(var, exp) -> Set'(var, (renaming_ast exp ind))
  | Def'(var, exp) -> Def'(var, (renaming_ast exp ind))
  | Or'(exprs_lst) -> Or'(List.map (fun (x) -> (renaming_ast x ind)) exprs_lst)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (renaming_ast body ind))
  | LambdaOpt'(params, opt, body) -> LambdaOpt'(params, opt, (renaming_ast body ind))
  | Applic'(proc, args_lst) -> Applic'((renaming_ast proc ind), (List.map (fun (x) -> (renaming_ast x ind)) args_lst))
  | ApplicTP'(proc, args_lst) -> ApplicTP'((renaming_ast proc ind), (List.map (fun (x) -> (renaming_ast x ind)) args_lst))   ;; 


let rec renaming_asts asts ind = (match asts with 
  | [] -> []
  | ast :: tail -> [(renaming_ast ast ind)] @ (renaming_asts tail (ind + 1))) 
  
(* ---------------------------------------------MAKE CONSTANTS TABLE FUNCTION----------------------------------------------------------------- *)
(* --------------------------------------scan for consts all over asts-------------------------------------------------------------- *)
 
 let rec cut_taggedSexps exp = (match exp with
  | Pair (sexpr1, sexpr2) -> Pair((cut_taggedSexps sexpr1), (cut_taggedSexps sexpr2))
  | TaggedSexpr (var, sexpr) -> let new_body = (cut_taggedSexps sexpr) in
                                let z = (var, new_body) in
                                tagged_lst := !tagged_lst @ [z] ; 
                                new_body;
  | _ -> exp);;


  let rec find_consts ast = (match ast with 
                            | Const'(x) -> (match x with 
                                            | Void -> []
                                            | Sexpr(sexp) -> (match sexp with 
                                                              | TaggedSexpr(var, exp) -> let new_body = (cut_taggedSexps exp) in
                                                                                         let z = (var, new_body) in
                                                                                         tagged_lst := !tagged_lst @ [z] ; 
                                                                                         [new_body];
                                                              | TagRef(var) -> [sexp]
                                                              | Pair(first, sec) -> [(cut_taggedSexps sexp)]
                                                              | _ -> [sexp] ))
                            | Var'(x) -> [] 
                            | Box'(x) -> [] 
                            | BoxGet'(x) -> [] 
                            | BoxSet'(var, exp) -> (find_consts exp)
                            | If'(test, dit, dif) -> ((find_consts test) @ (find_consts dit) @ (find_consts dif))
                            | Seq'(exprs_lst) -> (List.fold_left (@) ([]) (List.map find_consts exprs_lst))
                            | Set'(var, exp) -> find_consts exp 
                            | Def'(var, exp) -> find_consts exp
                            | Or'(exprs_lst) -> (List.fold_left (@) ([]) (List.map find_consts exprs_lst))
                            | LambdaSimple'(params, body) -> find_consts body
                            | LambdaOpt'(params, opt, body) -> find_consts body 
                            | Applic'(proc, args_lst) -> (find_consts proc) @ (List.fold_left (@) ([]) (List.map find_consts args_lst))
                            | ApplicTP'(proc, args_lst) -> (find_consts proc) @ (List.fold_left (@) ([]) (List.map find_consts args_lst)) ) ;;


 let rec scan asts = match asts with
    | [] -> []
    | ast :: tail -> (find_consts ast) @ (scan tail)

(* ----------------------------------------convert list to set without duplicates sexpressions------------------------------------------------------------------------------ *)

let rec check_lst sexp lst = match lst with 
    | [] -> false 
    | head :: tail -> if (sexpr_eq sexp head) then true else (check_lst sexp tail)


  let rec convert_to_set old_lst new_lst = (match old_lst with 
    | [] -> new_lst 
    | head :: tail -> match (check_lst head new_lst) with 
                        | true -> (convert_to_set tail new_lst) 
                        | false -> let lst = new_lst @ [head] in 
                                   (convert_to_set tail lst)) 


(* ----------------------------------------expand the constants list------------------------------------------------------------------------------ *)

 let rec fix_sexps sexp = (match sexp with 
    | Bool(x) -> [sexp]
    | Nil -> [sexp]
    | Number(x) -> [sexp]
    | Char(x) -> [sexp]
    | String(x) -> [sexp]
    | Symbol(x) -> [String(x)] @ [sexp]
    | Pair(x, y) -> (fix_sexps x) @ (fix_sexps y) @ [sexp]
    | TagRef(var) -> [sexp]
    | _ -> raise X_syntax_error)


  let rec expand constants_lst = match constants_lst with
    | [] -> []
    | sexp :: tail -> (fix_sexps sexp) @ (expand tail)

(* ----------------------------------------expand the constants list------------------------------------------------------------------------------ *)

let rec wrap_sexpr lst = match lst with 
  | [] -> []
  | head :: tail -> [Sexpr(head)] @ (wrap_sexpr tail)

(* ----------------------------------------search in the constants list for constants and return offset------------------------------------------------------------------------------ *)

let rec search_offset consts_list var = 
  (match consts_list with
    | [] -> -1
    | (x, (offset, string)) :: tail -> (match x with 
                                      | Sexpr(sexp) -> if sexpr_eq sexp var then offset
                                                      else search_offset tail var 
                                      | _ -> search_offset tail var))


let rec search_tagged consts_list tagged_list var_name = 
  (match tagged_list with
    | [] -> -1
    | (name, exp) :: tail  -> if (String.equal name var_name) then (search_offset consts_list exp) 
                              else (search_tagged consts_list tail var_name))


(* ----------------------------------------actually make the constants list------------------------------------------------------------------------------ *)

let rec make_table const_lst offset lst  = 
  (match const_lst with 
    | [] -> lst
    | head :: tail -> (match head with 
                        Sexpr(x) -> (match x with
                          | Nil -> let lst = lst @ [((head), (offset, "MAKE_NIL"))] in 
                                    (make_table tail (offset+1) lst)
                          | Char(x) -> let lst = lst @ [((head), (offset, "MAKE_LITERAL_CHAR(" ^ (Printf.sprintf "%d" (Char.code x)) ^ ")"))] in 
                                        (make_table tail (offset+2) lst)
                          | Bool(x) -> (match x with
                                       | false -> let lst = lst @ [((head), (offset, "MAKE_BOOL(" ^ string_of_int(0) ^ ")"))] in  
                                                  (make_table tail (offset+2) lst)
                                       | true -> let lst = lst @ [((head), (offset, "MAKE_BOOL(" ^ string_of_int(1) ^ ")"))] in  
                                                  (make_table tail (offset+2) lst))
                          | Number(x) -> (match x with 
                                          | Int(a) -> let lst = lst @ [((head), (offset, "MAKE_LITERAL_INT(" ^ string_of_int(a) ^ ")"))] in 
                                                      (make_table tail (offset+9) lst)
                                          | Float(a) -> let lst = lst @ [((head), (offset, Printf.sprintf "MAKE_LITERAL_FLOAT(%f)" a))] in 
                                                        (make_table tail (offset+9) lst))
                          | String(x) -> let lst = lst @ [((head), (offset, "MAKE_LITERAL_STRING(\"" ^ (String.escaped x) ^ "\")"))] in 
                                          let length = (String.length x) in
                                          (make_table tail (offset + length + 9) lst)
                          | Symbol(x) -> let sym_offset = search_offset lst (String(x)) in 
                                          let lst = lst @ [((head), (offset, "MAKE_LITERAL_SYMBOL(const_tbl+" ^ string_of_int(sym_offset) ^ ")"))] in 
                                          (make_table tail (offset + 9) lst)
                          | Pair(TagRef(a), TagRef(b)) -> let new_lst = lst @ [((head), (offset, ""))] in  
                                                          (make_table tail (offset + 17) new_lst)
                          | Pair(TagRef(a), b) -> let new_lst = lst @ [((head), (offset, ""))] in
                                                  (make_table tail (offset + 17) new_lst)
                          | Pair(a, TagRef(b)) -> let new_lst = lst @ [((head), (offset, ""))] in  
                                                  (make_table tail (offset + 17) new_lst)
                          | Pair(a, b) -> let a_offset = (search_offset lst a) in 
                                          let b_offset = (search_offset lst b) in 
                                          let new_lst =  lst @ [((head), (offset, "MAKE_LITERAL_PAIR(const_tbl+" ^ string_of_int(a_offset) ^ ", const_tbl+" ^ string_of_int(b_offset) ^ ")"))] in 
                                          (make_table tail (offset + 17) new_lst)
                          | TagRef(x) -> make_table tail offset lst
                          
                          | _ ->raise X_syntax_error)

                        | _ -> raise X_syntax_error))





(* ----------------------------------------change refrrences offsets------------------------------------------------------------------------------ *)

let rec change_ref_offsets old_const_lst constst_lst new_const_lst = match old_const_lst with 
  | [] -> new_const_lst
  | head :: tail -> (match head with 
                      | (sexp, (offset, string)) -> (match sexp with 
                                                  | Sexpr(x) -> (match x with 
                                                                | Pair(TagRef(a), TagRef(b)) -> let a_offset = (search_tagged constst_lst !tagged_lst a) in                                                                                              
                                                                                                let b_offset = (search_tagged constst_lst !tagged_lst b) in 
                                                                                                let new_const_lst = new_const_lst @ [(sexp, (offset, "MAKE_LITERAL_PAIR(const_tbl+" ^ string_of_int(a_offset) ^ ", const_tbl+" ^ string_of_int(b_offset) ^ ")"))] in  
                                                                                                (change_ref_offsets tail constst_lst new_const_lst)
                                                                | Pair(TagRef(a), b) -> let a_offset = (search_tagged constst_lst !tagged_lst a) in
                                                                                        let b_offset = (search_offset constst_lst b) in                                                                                     
                                                                                        let new_const_lst = new_const_lst @ [(sexp, (offset, "MAKE_LITERAL_PAIR(const_tbl+" ^ string_of_int(a_offset) ^ ", const_tbl+" ^ string_of_int(b_offset) ^ ")"))] in  
                                                                                        (change_ref_offsets tail constst_lst new_const_lst) 
                                                                | Pair(a, TagRef(b)) -> let a_offset = (search_offset constst_lst a) in
                                                                                        let b_offset = (search_tagged constst_lst !tagged_lst b) in                                                                    
                                                                                        let new_const_lst = new_const_lst @ [(sexp, (offset, "MAKE_LITERAL_PAIR(const_tbl+" ^ string_of_int(a_offset) ^ ", const_tbl+" ^ string_of_int(b_offset) ^ ")"))] in  
                                                                                        (change_ref_offsets tail constst_lst new_const_lst)                                              

                                                                | _ -> let new_const_lst =  new_const_lst @ [head] in 
                                                                    (change_ref_offsets tail constst_lst new_const_lst))
                                                  | _ -> raise X_syntax_error) 
                      )









(* ------------------------------------------------------------------------------------------------------------------------------------------- *)
  let make_consts_table asts = 
    let asts = renaming_asts asts 1 in
    let scan_consts = [Nil ; Bool(false) ; Bool(true)] @ (scan asts) in
    let cut_duplicates = (convert_to_set scan_consts []) in
    let expand_consts_list = (expand cut_duplicates) in
    let cut = (convert_to_set expand_consts_list []) in
    let make_consts_Sexps = wrap_sexpr cut in
    let consts_table = make_table make_consts_Sexps 1 [] in
    let const_lst_whithout_tagref = (change_ref_offsets consts_table consts_table []) in
    [(Void, (0, "MAKE_VOID"))] @ const_lst_whithout_tagref
    
(* ------------------------------------------------------------------------------------------------------------------------------------------- *)
(* -----------------------------------------MAKE FREE VARS TABLE-------------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------------------------------------------------------- *)
let index = ref (-1);;

let rec make_fvars_ast ast = (match ast with 
  | Const'(x) -> []
  | Var'(x) -> (match x with 
                | VarFree(var_name) -> index := !index + 1;
                                       [(var_name, !index)]
                | VarParam(var_name, maj) -> []
                | VarBound(var_name, maj, min) -> [])
  | Box'(x) -> (match x with 
                | VarFree(var_name) -> index := !index + 1;
                                       [(var_name, !index)]
                | VarParam(var_name, maj) -> []
                | VarBound(var_name, maj, min) -> [])
  | BoxGet'(x) -> (match x with 
                | VarFree(var_name) -> index := !index + 1;
                                       [(var_name,  !index)]
                | VarParam(var_name, maj) -> []
                | VarBound(var_name, maj, min) -> [])
  | BoxSet'(var, exp) -> (match var with 
                | VarFree(var_name) -> index := !index + 1;
                                       let tuple = [(var_name, !index)] in 
                                       tuple @ (make_fvars_ast exp)
                | VarParam(var_name, maj) -> [] @ (make_fvars_ast exp)
                | VarBound(var_name, maj, min) -> [] @ (make_fvars_ast exp)) 
  | If'(test, dit, dif) -> let test_tupples = (make_fvars_ast test) in 
                           let dit_tupples = (make_fvars_ast dit) in 
                           let dif_tupples = (make_fvars_ast dif) in 
                           test_tupples @ dit_tupples @ dif_tupples
  | Seq'(exprs_lst) -> change_vars_lst exprs_lst
  | Set'(var, exp) -> let var_t = (make_fvars_ast var) in
                      let exp_t = (make_fvars_ast exp) in 
                      var_t @ exp_t
  | Def'(var, exp) -> let var_t = (make_fvars_ast var) in
                      let exp_t = (make_fvars_ast exp) in 
                      var_t @ exp_t
  | Or'(exprs_lst) -> change_vars_lst exprs_lst
  | LambdaSimple'(params, body) -> make_fvars_ast body
  | LambdaOpt'(params, opt, body) -> make_fvars_ast body
  | Applic'(proc, args_lst) -> let proc_t = (make_fvars_ast proc) in
                               let args_lst_t = (change_vars_lst args_lst) in 
                               proc_t @ args_lst_t
  | ApplicTP'(proc, args_lst) -> let proc_t = (make_fvars_ast proc) in
                                let args_lst_t = (change_vars_lst args_lst) in 
                                 proc_t @ args_lst_t)

and change_vars_lst lst = (match lst with 
  | [] -> []
  | ast :: tail -> let t = (make_fvars_ast ast) in 
                    let ts = (change_vars_lst tail) in 
                    t @ ts) 
  
let rec add_vars_from_asts asts primitives =
  let lst = change_vars_lst asts in 
  primitives @ lst 

(* ------------------------------------Make fvars list to Set without duplicates------------------------------------------------------------------------------------------------------- *)

let rec search_if_exist (var_name, var_ind) lst = (match lst with 
  | [] -> false 
  | tuple :: tail -> (match tuple with 
                      | (name, ind) -> if (String.equal name var_name) then true else search_if_exist (var_name, var_ind) tail))
                                                                

let rec cut_dups old_fvars_tbl new_fvars_tbl = (match old_fvars_tbl with 
                                                | [] -> new_fvars_tbl
                                                | head :: tail -> (match (search_if_exist head new_fvars_tbl) with 
                                                                    | true -> index := !index - 1; (cut_dups tail new_fvars_tbl)
                                                                    | false ->  let new_fvars_tbl = new_fvars_tbl @ [head] in 
                                                                                (cut_dups tail new_fvars_tbl)))

let rec make_index tupple_lst new_tupple_lst new_ind = 
  (match tupple_lst with
    | [] -> new_tupple_lst
    | tuple :: tail -> (match tuple with
                        | (name , ind) -> [(name, new_ind)] @ (make_index tail new_tupple_lst (new_ind + 1))))

let rec make_fvars_table asts primitives = 
  let fvars_tbl = add_vars_from_asts asts primitives in 
  (make_index (cut_dups fvars_tbl []) [] 0)

(* ------------------------------------------------------------------------------------------------------------------------------------------- *)
(* -----------------------------------------GENERATE ASSEMBLY CODE-------------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------------------------------------------------------- *)

(* -----------------------------------------Global counters for generate------------------------------------------------------------------------------------------------ *)


 let global_env_counter = ref 0;;
 let global_applic_counter = ref 0;;
 let global_if_label_counter = ref 0;;
 let global_or_label_counter = ref 0;;

(* ---------------------------------------------GENERATE HELPERS---------------------------------------------------------------------------------------------- *)

let rec search_label fvars x = (match fvars with
                                | [] -> -1
                                | head :: tail -> (match head with 
                                                    (name, label) -> if String.equal name x then label else search_label tail x)) 

let rec or_generate new_generated_or_lst str counter = (match new_generated_or_lst with 
  | [] -> ""
  | head :: [] -> head ^ "orLexit" ^ (string_of_int counter) ^ ":\n" 
  | head :: tail -> let new_str = head ^ str in 
                    new_str ^ or_generate tail str counter)  

let rec reverse_list old_lst new_lst = match old_lst with 
  | [] -> new_lst 
  | head :: tail -> reverse_list tail ([head] @ new_lst)

(* -------------------------------MAIN FUNCTION FOR GENERATE------------------------------------------------------------------------------------------------------------ *)

let rec generate_exp consts fvars e env_counter = (match e with 
  | Const'(x) -> (match x with 
                  | Void -> "mov rax, const_tbl+0\n" 
                  | Sexpr(a) -> let x_offset = search_offset consts a in 
                             "mov rax, const_tbl+" ^ (string_of_int x_offset) ^ "\n")

  | Var'(x) -> (match x with
                | VarParam(name, minor) -> let new_minor = (8 * (4 + minor)) in  
                                           "mov rax, qword [rbp + " ^ (string_of_int new_minor) ^ "]\n"   
                | VarBound(name, major, minor) -> let new_major = 8 * major in
                                                  let new_minor = 8 * minor in 
                                                   "mov rax, qword [rbp + 16]\n" ^
                                                  "mov rax, qword [rax + " ^ (string_of_int new_major) ^ "]\n" ^
                                                  "mov rax, qword [rax + " ^ (string_of_int new_minor) ^ "]\n"
                | VarFree(x) -> let x_label = search_label fvars x in
                                "mov rax, qword [fvar_tbl + (8 * " ^ (string_of_int x_label) ^ ")]\n")
  | Box'(x) ->  let new_x = Var'(x) in
                let x_str = (generate_exp consts fvars new_x env_counter) in
                "MALLOC r10, 8\n" ^
                x_str ^
               "mov [r10], rax\n" ^
               "mov rax, r10\n"
  | BoxGet'(x) -> let a = Var'(x) in 
                  let x_str = (generate_exp consts fvars a env_counter) in 
                  x_str ^ 
                  "mov rax, qword [rax]\n"
  | BoxSet'(var, exp) -> let exp_str = (generate_exp consts fvars exp env_counter) in
                         let a = Var'(var) in  
                         let var_str = (generate_exp consts fvars a env_counter) in 
                         exp_str ^
                         "push rax\n" ^
                         var_str ^ 
                         "pop qword [rax]\n" ^
                         "mov rax, SOB_VOID_ADDRESS\n"

  | If'(test, dit, dif) -> ignore(global_if_label_counter := (!global_if_label_counter + 1));
                           let local_counter = !global_if_label_counter in
                           let test_str = (generate_exp consts fvars test env_counter) in  
                           let dit_str = (generate_exp consts fvars dit env_counter) in 
                           let dif_str = (generate_exp consts fvars dif env_counter) in 
                           test_str ^ 
                           "cmp rax, SOB_FALSE_ADDRESS\n" ^
                           "je ifLelse" ^ (string_of_int local_counter) ^ "\n" ^
                           dit_str ^ 
                           "jmp ifLexit" ^ (string_of_int local_counter) ^ "\n" ^
                           "ifLelse" ^ (string_of_int local_counter) ^ ":\n" ^
                           dif_str ^ 
                           "ifLexit" ^ (string_of_int local_counter) ^ ":\n" 

  | Seq'(exprs_lst) -> List.fold_left (^) "" (List.map (fun (x) -> (generate_exp consts fvars x env_counter))  exprs_lst)
  | Set'(var, exp) -> (match var with 
                        | Var'(x) -> (match x with  
                                      | VarParam(name, minor) -> let new_minor = (8 * (4 + minor)) in  
                                                                (generate_exp consts fvars exp env_counter) ^
                                                                "mov qword [rbp + " ^ (string_of_int new_minor) ^ "], rax\n" ^
                                                                "mov rax, SOB_VOID_ADDRESS\n"
                                      | VarBound(name, major, minor) -> let new_major = 8 * major in
                                                                        let new_minor = 8 * minor in 
                                                                        (generate_exp consts fvars exp env_counter) ^
                                                                        "mov rbx, qword [rbp + 16]\n" ^
                                                                        "mov rbx, qword [rbx + " ^ (string_of_int new_major) ^ "]\n" ^
                                                                        "mov qword [rbx + " ^  (string_of_int new_minor) ^ "], rax\n" ^
                                                                        "mov rax, SOB_VOID_ADDRESS\n"
                                      | VarFree(x) -> let x_label = search_label fvars x in  
                                                      (generate_exp consts fvars exp env_counter) ^ 
                                                      "mov qword [fvar_tbl+ (8 * " ^ string_of_int(x_label) ^ ")], rax\n" ^
                                                      "mov rax, SOB_VOID_ADDRESS\n")
                          | _ -> raise X_syntax_error)




  | Def'(var, exp) -> (match var with 
                        | Var'(x) -> (match x with  
                                      | VarFree(x) -> let x_label = search_label fvars x in  
                                                      (generate_exp consts fvars exp env_counter) ^
                                                      "mov qword [fvar_tbl+ (8 * " ^ string_of_int(x_label) ^ ")], rax\n" ^
                                                      "mov rax, SOB_VOID_ADDRESS\n"
                                      | _ -> raise X_syntax_error)
                        | _ -> raise X_syntax_error)






  | Or'(exprs_lst) ->   (global_or_label_counter := (!global_or_label_counter + 1));
                        let local_counter = !global_or_label_counter in
                        let new_generated_or = (List.map (fun (x) -> (generate_exp consts fvars x env_counter))  exprs_lst) in
                        let str = "cmp rax, SOB_FALSE_ADDRESS\n
                                   jne orLexit" ^ (string_of_int local_counter) ^ "\n"  in
                        or_generate new_generated_or str local_counter
  | LambdaSimple'(params, body) -> global_env_counter := (!global_env_counter + 1);
                                   let global_env_counter_str = (string_of_int !global_env_counter) in
                                   let new_env_counter = (env_counter + 1) in
                                   let body_str = (generate_exp consts fvars body new_env_counter) in
                                    "lambda_simple" ^ global_env_counter_str ^ ":\n" ^
                                    "extand_env" ^ global_env_counter_str ^ ":\n" ^
                                    "mov rbx, qword [rbp + 8 * 2]                                     ; move old env to rbx\n" ^
                                    "MALLOC rax, " ^ (string_of_int (new_env_counter * 8)) ^ "\n" ^
                                    "mov rcx, " ^ (string_of_int env_counter) ^ "                     ; move to ecx the loop counter\n" ^ 
                                    "cmp rcx, 0\n" ^
                                    "je allocate_closer" ^ global_env_counter_str ^ "\n" ^
                                    "loop_env" ^ global_env_counter_str ^ ":                              ; go over old enviroment and copy all the pointers to the new enviroment\n" ^
                                    "dec rcx\n" ^
                                    "mov rdx, qword[rbx + 8*rcx]                                      ; takes the pointer from old env to vector i\n" ^
                                    "inc rcx\n" ^
                                    "mov [rax + 8 * rcx], rdx                                         ; old_env[i] -> new_env[i+1]\n" ^
                                    "loop loop_env" ^ global_env_counter_str ^ ", rcx                     ; keep on going until rcx = 0\n" ^
                                    "move_params" ^ global_env_counter_str ^ ":                           ; move paramters to new_env[0]\n" ^
                                    "mov rcx, qword [rbp + 8 * 3]                                     ; move to rbx old_n\n" ^
                                    "cmp rcx, 0\n" ^
                                    "je allocate_closer" ^ global_env_counter_str ^ "\n" ^
                                    "inc rcx\n" ^
                                    "mov rsi, rcx\n" ^
                                    "shl rsi, 3\n" ^
                                    "MALLOC rbx, rsi                                                  ; allocate space for new vector\n" ^
                                    "get_first_param_address" ^ global_env_counter_str ^ ":\n" ^
                                    "mov rdx, 32\n" ^
                                    "add rdx, rbp                                                     ; now rdx holds first parameter pointer\n" ^
                                    "loop_args" ^ global_env_counter_str ^ ":                             ; move all the parameters to new_env[0] loop\n" ^
                                    "dec rcx\n" ^
                                    "mov rsi, [rdx + (8 * rcx)]                                       ; rsi will now point on the last parameter\n" ^
                                    "mov [rbx + 8 * rcx], rsi                                         ; move the paramter to the new vector\n" ^
                                    "inc rcx\n" ^
                                    "loop loop_args" ^ global_env_counter_str ^ ", rcx\n" ^                  
                                    "mov [rax], rbx                                                   ; copy the address of new vector to new_env [0]\n" ^
                                    "allocate_closer" ^ global_env_counter_str ^ ":\n" ^
                                    "mov rbx, rax                                                     ; save new env address at rbx\n" ^
                                    "MALLOC rax, 17\n" ^
                                    "mov rcx, 0\n" ^
                                    "mov cl, 9\n" ^
                                    "mov byte [rax], cl                                               ; keep closure tag at rax[0]\n" ^
                                    "mov qword [rax + 1], rbx                                         ; keep env pointer at rax[1]\n" ^
                                    "mov qword [rax + 9], Lcode" ^ global_env_counter_str ^ "                                       ; keep lcode address at rax[9]\n" ^
                                    "jmp Lcont" ^ global_env_counter_str ^ "\n" ^
                                    "Lcode" ^ global_env_counter_str ^ ":\n" ^
                                    "push rbp\n" ^
                                    "mov rbp , rsp\n" ^
                                    body_str ^
                                    "leave\n" ^
                                    "ret\n" ^
                                    "Lcont" ^ global_env_counter_str ^ ":\n" 
                                    
  | LambdaOpt'(params, opt, body) -> global_env_counter := (!global_env_counter + 1);
                                   let params_length = (List.length params) in
                                   let params_length_str = (string_of_int params_length) in
                                   let global_env_counter_str = (string_of_int !global_env_counter) in
                                   let new_env_counter = (env_counter + 1) in
                                   let body_str = (generate_exp consts fvars body new_env_counter) in
                                    "lambda_opt" ^ global_env_counter_str ^ ":\n" ^
                                    "extand_env" ^ global_env_counter_str ^ ":\n" ^
                                    "mov rbx, qword [rbp + 8 * 2]                                     ; move old env to rbx\n" ^
                                    "MALLOC rax, " ^ (string_of_int (new_env_counter * 8)) ^ "\n" ^
                                    "mov rcx, " ^ (string_of_int env_counter) ^ "                        ; move to ecx the loop counter\n" ^ 
                                    "cmp rcx, 0\n" ^
                                    "je allocate_closer" ^ global_env_counter_str ^ "\n" ^
                                    "loop_env" ^ global_env_counter_str ^ ":                                                        ; go over old enviroment and copy all the pointers to the new enviroment\n" ^
                                    "dec rcx\n" ^
                                    "mov rdx, qword[rbx + 8*rcx]                                      ; takes the pointer from old env to vector i\n" ^
                                    "inc rcx\n" ^
                                    "mov [rax + 8 * rcx], rdx                                         ; old_env[i] -> new_env[i+1]\n" ^
                                    "loop loop_env" ^ global_env_counter_str ^ ", rcx                                                   ; keep on going until rcx = 0\n" ^
                                    "move_params" ^ global_env_counter_str ^ ":                                                     ; move paramters to new_env[0]\n" ^
                                    "mov rcx, qword [rbp + 8 * 3]                                     ; move to rbx old_n\n" ^
                                    "cmp rcx, 0\n" ^
                                    "je allocate_closer" ^ global_env_counter_str ^ "\n" ^
                                    "inc rcx\n" ^
                                    "mov rsi, rcx\n" ^
                                    "shl rsi, 3\n" ^
                                    "MALLOC rbx, rsi                                                  ; allocate space for new vector\n" ^
                                    "get_first_param_address" ^ global_env_counter_str ^ ":\n" ^
                                    "mov rdx, 32\n" ^
                                    "add rdx, rbp                                                     ; now rdx holds first parameter pointer\n" ^
                                    "loop_args" ^ global_env_counter_str ^ ":                                                       ; move all the parameters to new_env[0] loop\n" ^
                                    "dec rcx\n" ^
                                    "mov rsi, [rdx + (8 * rcx)]                                       ; rsi will now point on the last parameter\n" ^
                                    "mov [rbx + 8 * rcx], rsi                                         ; move the paramter to the new vector\n" ^
                                    "inc rcx\n" ^
                                    "loop loop_args" ^ global_env_counter_str ^ ", rcx\n" ^                  
                                    "mov [rax], rbx                                                   ; copy the address of new vector to new_env [0]\n" ^
                                    "allocate_closer" ^ global_env_counter_str ^ ":\n" ^
                                    "mov rbx, rax                                                     ; save new env address at rbx\n" ^
                                    "MALLOC rax, 17\n" ^
                                    "mov rcx, 0\n" ^
                                    "mov cl, 9\n" ^
                                    "mov byte [rax], cl                                               ; keep closure tag at rax[0]\n" ^
                                    "mov qword [rax + 1], rbx                                         ; keep env pointer at rax[1]\n" ^
                                    "mov qword [rax + 9], Lcode" ^ global_env_counter_str ^ "                                       ; keep lcode address at rax[9]\n" ^
                                    "jmp Lcont" ^ global_env_counter_str ^ "\n" ^
                                    "Lcode" ^ global_env_counter_str ^ ":\n" ^
                                    "push rbp\n" ^
                                    "mov rbp , rsp\n" ^


                                    "mov rcx, qword [rbp + 24] \n" ^
                                    "mov rbx, " ^ params_length_str ^ "\n" ^
                                    "cmp rcx, rbx                                                      ; check if p.length < n\n" ^
                                    "je equal_lets_dance" ^ global_env_counter_str ^ "\n" ^
                                    "mov rdx, " ^ params_length_str ^ "\n" ^
                                    "add rdx, 4\n" ^
                                    "shl rdx, 3\n" ^
                                    "add rdx, rbp                                                      ; now rdx will point to A[first_opt_argument] \n" ^
                                    "sub rcx, " ^ params_length_str ^ "\n" ^
 

                                    "mov rdi, const_tbl+1\n" ^
                                    "move_opt_params" ^ global_env_counter_str ^ ":                        ; move all the parameters to new array located in rax\n" ^
                                    "dec rcx\n" ^
                                    "mov rbx, rcx\n" ^
                                    "shl rbx, 3\n" ^
                                    "mov rsi, rbx\n" ^
                                    "add rsi, rdx\n" ^
                                    "mov rsi, qword [rsi]\n" ^
                                    "MAKE_PAIR(rax, rsi, rdi)\n" ^
                                    "mov rdi, rax\n" ^
                                    "inc rcx\n"^
                                    "loop move_opt_params" ^ global_env_counter_str ^ ", rcx\n" ^
                                    "mov [rdx], rdi                                                     ;  we put the new vector opt_parameters to 'magic place'\n" ^

                                    "mov rax, qword [rbp + 24]\n" ^
                                    "dec rax\n" ^
                                    "add rax, 4\n"^
                                    "shl rax, 3\n" ^
                                    "add rax, rbp\n" ^
                                    "mov rbx," ^ params_length_str ^ "\n" ^
                                    "add rbx, 4\n" ^
                                    "shl rbx, 3\n" ^
                                    "add rbx, rbp\n" ^
                                    "mov rcx, "^ params_length_str ^ "\n" ^
                                    "add rcx, 5\n" ^
                                    "adjust_stack"^ global_env_counter_str ^ ":\n"^
                                    "mov rsi, qword [rbx]\n" ^
                                    "mov [rax], rsi\n" ^
                                    "sub rax, 8\n" ^
                                    "sub rbx, 8\n" ^
                                    "loop adjust_stack" ^ global_env_counter_str ^ ", rcx\n" ^
                                    "add rax, 8\n" ^
                                    "mov rbp, rax\n" ^
                                    "mov rsp, rax\n" ^
                                    "mov rbx," ^ params_length_str ^ "\n" ^
                                    "inc rbx\n" ^
                                    "mov [rbp + 24], rbx\n"^
                                    "jmp cont_to_body"^ global_env_counter_str ^ "\n" ^

                                    "equal_lets_dance" ^ global_env_counter_str ^ ":\n" ^                             
                                    "mov rbx," ^ params_length_str ^ "\n" ^
                                    "mov [rbp + 24], rbx\n"^

                                    "cont_to_body"^ global_env_counter_str ^ ":\n" ^
                                    body_str ^
                                    "leave\n" ^
                                    "ret\n" ^
                                    "Lcont" ^ global_env_counter_str ^ ":\n" 





  | Applic'(proc, args_lst) -> global_applic_counter := !global_applic_counter + 1;
                               let global_applic_counter_str = (string_of_int !global_applic_counter) in
                               let args_n = (List.length args_lst) in
                               let args_n_str = (string_of_int args_n) in 
                               let reversed_args_lst = reverse_list args_lst [] in 
                               let generated_reversed_args_lst = (List.map (fun (x) -> (generate_exp consts fvars x env_counter)) reversed_args_lst) in 
                               let generated_reversed_args_lst_with_str = (List.map (fun (x) -> x ^ "push rax\n") generated_reversed_args_lst) in 
                               let args_lst_str = (List.fold_left (^) ("") generated_reversed_args_lst_with_str) in 
                               let proc_str = ((generate_exp consts fvars proc env_counter)) in 
                               let nil_str = (generate_exp consts fvars (Const'(Sexpr(Nil))) env_counter) in
                               "applic_start" ^ global_applic_counter_str ^ ":\n" ^ 

                               nil_str ^
                               "push rax\n" ^
                               args_lst_str ^ 
                               "push " ^ args_n_str ^ "\n" ^
                               proc_str ^


                               "mov rdx, 0\n" ^
                               "mov dl, byte [rax]                                                 ; check if rax has type closure\n" ^
                               "cmp dl, 9\n" ^
                               "je finish_applic" ^ global_applic_counter_str ^ "\n" ^
                               "mov rax, 60\n" ^
                               "jmp error\n" ^


                               "finish_applic" ^ global_applic_counter_str ^ ":\n" ^


                               "push qword [rax+1]\n" ^
                               "call [rax+9]\n" ^
                               "add rsp , 8*1                                                       ; pop env\n" ^
                               "pop rbx                                                             ; pop arg count\n" ^
                               "inc rbx\n" ^
                               "shl rbx , 3                                                         ; rbx = rbx * 8\n" ^
                               "add rsp , rbx; pop args\n"






  | ApplicTP'(proc, args_lst) ->  global_applic_counter := !global_applic_counter + 1;
                                  let global_applic_counter_str = (string_of_int !global_applic_counter) in
                                  let args_n = (List.length args_lst) in
                                  let args_n_str = (string_of_int args_n) in 
                                  let frame_n = (args_n + 5) in
                                  let frame_n_str = (string_of_int frame_n) in 
                                  let reversed_args_lst = reverse_list args_lst [] in 
                                  let generated_reversed_args_lst = (List.map (fun (x) -> (generate_exp consts fvars x env_counter)) reversed_args_lst) in 
                                  let generated_reversed_args_lst_with_str = (List.map (fun (x) -> x ^ "push rax\n") generated_reversed_args_lst) in 
                                  let args_lst_str = (List.fold_left (^) ("") generated_reversed_args_lst_with_str) in 
                                  let proc_str = ((generate_exp consts fvars proc env_counter)) in 
                                  let nil_str = (generate_exp consts fvars (Const'(Sexpr(Nil))) env_counter) in
                                  "applicTP_start" ^ global_applic_counter_str ^ ":\n" ^ 

                                  nil_str ^
                                  "push rax\n" ^
                                  args_lst_str ^ 
                                  "push " ^ args_n_str ^ "\n" ^
                                  proc_str ^


                                  "mov rdx, 0\n" ^
                                  "mov dl, byte [rax]                                                 ; check if rax has type closure\n" ^
                                  "cmp dl, 9\n" ^
                                  "je finish_applic" ^ global_applic_counter_str ^ "\n" ^
                                  "mov rax, 60\n" ^
                                  "jmp error\n" ^


                                  "finish_applic" ^ global_applic_counter_str ^ ":\n" ^

                                  "push qword [rax+1]\n" ^
                                  "push qword [rbp + 8]\n" ^

                                   "debug_start" ^ global_applic_counter_str ^ ":\n" ^ 

                                  "mov r12, qword [rbp+3*WORD_SIZE]\n" ^                          
                                  "mov r10, [rbp]\n" ^

                                  "push rax\n" ^
                                  "mov rax, qword [rbp+3*WORD_SIZE]\n" ^
                                  "add rax, 5\n" ^
                                  "mov rsi, 1\n" ^
                                  "mov rcx, " ^ frame_n_str ^ "\n" ^ 
                                  "loop_move_frame" ^ global_applic_counter_str ^ ":\n" ^
                                  "dec rax\n" ^
                                  "mov rdi, rsi\n" ^
                                  "shl rdi, 3\n" ^
                                  "mov rbx, rbp\n" ^
                                  "sub rbx, rdi\n" ^
                                  "push qword [rbx]\n" ^
                                  "mov rdi, rax\n" ^
                                  "shl rdi, 3\n" ^
                                  "mov rbx, rbp\n" ^
                                  "add rbx, rdi\n" ^
                                  "pop qword [rbx]\n" ^
                                  "inc rsi\n" ^
                                  "cmp rsi, rcx\n" ^
                                  "je end_loop" ^ global_applic_counter_str ^ "\n" ^
                                  "jmp loop_move_frame" ^ global_applic_counter_str ^ "\n" ^
                                  "end_loop" ^ global_applic_counter_str ^ ":\n" ^
                                  "pop rax\n" ^


                                  "add r12, 5\n" ^
                                  "shl r12, 3\n" ^
                                  "add rsp, r12\n" ^
                                  "mov rbp,r10\n" ^

                                  "jmp [rax+9]\n" ^
                  
                                  "add rsp , 8*1                                                       ; pop env\n" ^
                                  "pop rbx                                                             ; pop arg count\n" ^
                                  "inc rbx\n" ^
                                  "shl rbx , 3                                                         ; rbx = rbx * 8\n" ^
                                  "add rsp , rbx; pop args\n"
    );;

(* ---------------------------------------------------------Create primitives table---------------------------------------------------------------------------------- *)

 let rec create_prim_tbl prim_lst prim_tbl = (match prim_lst with 
  | [] -> prim_tbl
  | tuple :: tail -> (match tuple with 
                      | (name, func_pointer) -> index := !index + 1;
                                                let prim_t = prim_tbl @ [(name, !index)] in 
                                                create_prim_tbl tail prim_t))

(* ------------------------------------------------------------------------------------------------------------------------------------------- *)
(* ---------------------------------------------------------STRUCT---------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------------------------------------------------------- *)



(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig

  val create_primitives : (string * string) list -> (string * int) list 
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:let x = (file_to_string "stdlib.scm")


let z = string_to_asts code
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string

end;;

module Code_Gen : CODE_GEN = struct
  let create_primitives prim_lst = create_prim_tbl prim_lst [];;
  let make_consts_tbl asts = make_consts_table asts;;
  let make_fvars_tbl asts primitives = make_fvars_table asts primitives;;
  let generate consts fvars e = generate_exp consts fvars e 0;;
end;;






