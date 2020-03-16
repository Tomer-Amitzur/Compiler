
#use "pc.ml";;

open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;



type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;


(* --------------------------------------------------------------- *)


(* ----------------make skip help functions-------------------------------------- *)

(* ----------------------help simple functions---------------------------------- *)


let nt_whitespace = const(fun ch -> ch <= ' ');;
let nt_semicolon = const(fun ch -> ch = 59);;
let sign = disj (char '+') (char '-');;
let sym_ch = one_of_ci "abcdefghijklmnopqrstuvwxyz!$^*-_=+<>/?";;
let sym = one_of_ci "0123456789abcdefghijklmnopqrstuvwxyz!$^*-_=+<>/?";;
let digit = range '0' '9';;

let make_paired nt_left nt_right nt =
    let nt = caten nt_left nt in
    let nt = pack nt (function (_, e) -> e) in
    let nt = caten nt nt_right in
    let nt = pack nt (function (e, _) -> e) in
    nt;;

let make_nt_digit ch_from ch_to displacement =
    let nt = const (fun ch -> ch_from <= ch && ch <= ch_to) in
    let nt = pack nt (let delta = (Char.code ch_from) - displacement in
          fun (ch) -> (Char.code ch) - delta) in
    nt;;

let get_base s = 
  let (l,r) = s in 
  l;;


(* ---------------------help recursion fuctions----------------------------- *)


let rec pairs sexpList =
  match sexpList with
  | [] -> Nil
  | first :: second ->  Pair(first, pairs second);;

let rec dot_pairs sexpList = 
  match sexpList with
  | [] -> Nil
  | first :: [] -> first
  | first :: second ->  Pair(first, dot_pairs second);;


(* ---------------------help tagged functions----------------------------------- *)


let rec tagged_error sexp1 sexp2 name =
  (match sexp2 with
    | TaggedSexpr(a,b) -> if a=name then raise X_this_should_not_happen
                                    else sexp1
    | Pair(f,s) ->( match f with
          | TaggedSexpr(name4,sexp4) -> if name4=name then raise X_this_should_not_happen
                                                      else (tagged_error sexp1 s name)
          | _ -> (tagged_error sexp1 s name))
    | _ -> sexp1);;


let rec list_append p=
  (match p with
    | Pair(f,s) -> (match f with 
                    | TaggedSexpr(name,sexp) -> (List.append (List.append [name] (list_append s)) (list_append sexp))  
                    | _ -> (list_append s))
    | TaggedSexpr(name,sexp) -> [name]
    | _ -> [] ) ;;
  

let rec find_error names_lst=
  (match names_lst with
    | [] -> true
    | s :: [] -> true
    | s :: r ->  (match r with
              | s1 :: [] -> (not (s=s1))
              | s1 :: r1 -> ((find_error (s :: r1)) && (find_error r) && not(s=s1))
              | _ -> true))
                 ;;


(* ----------------------main sexp recursion----------------------------------- *)

let rec nt_sexp s =
  (* let nt = string_to_list s in  *)
  let nt = (disj_list [nt_boolean;
                      nt_number;
                      nt_float;
                      nt_not;
                      nt_symbol;
                      nt_string;
                      nt_nil;
                      nt_char;
                      nt_list;
                      nt_dotList;
                      nt_tagged;
                      nt_quote;
                      nt_rad_int;
                      nt_rad_float;]) in                    
  make_skip nt s

and nt_boolean s = 
  let bool = pack (disj (word_ci "#t") (word_ci "#f")) (fun (ch) -> match ch with
  | ['#';'t'] -> Bool(true)
  | ['#';'T'] -> Bool(true)
  | ['#'; 'f'] -> Bool(false)
  | ['#'; 'F'] -> Bool(false)
  | _ -> raise X_no_match) in 
  bool s

and nt_number s = 
  let nt = make_nt_digit '0' '9' 0 in
  let nt = plus nt in
  let nt = pack nt (fun digits ->
		  List.fold_left (fun a b -> 10 * a + b) 0 digits) in
  let add_sign = caten (maybe sign) nt in 
  let nt = pack add_sign (fun (sign, num) -> 
    match sign with
    |Some '-' -> Number(Int(num * -1))
    |Some '+' -> Number(Int(num))
    |Some(result) -> raise X_no_match
    |None -> Number(Int(num))) in 
  let nt = not_followed_by nt (disj sym_ch (char '.')) in
  nt s

  and nt_float s = 
    let digits = caten (caten (plus digit) (char '.')) (plus digit) in
    let digitStrings = pack digits (fun ((a,b), c) -> ((list_to_string a), (String.make 1 b) , (list_to_string c))) in
    let nt = pack digitStrings (fun (a,b,c) -> (a^b^c)) in
    let nt = pack nt (fun (lst1) -> (float_of_string lst1)) in
    let nt = caten (maybe sign) nt in 
    let nt = pack nt (fun (sign, num) -> 
      match sign with
      |Some '-' -> Number(Float(num *. -1.0))
      |Some '+' -> Number(Float(num))
      |Some(result) -> raise X_no_match
      |None -> Number(Float(num))) in
    let nt = not_followed_by nt (sym_ch) in
    nt s

  and nt_symbol s =
    let lower_list = fun ch_arr -> List.map (fun ch -> (lowercase_ascii ch)) ch_arr in
    let lst = plus sym in
    let lst = pack lst (lower_list) in
    let str = pack lst list_to_string in
    let nt = pack str (fun a -> Symbol(a)) in
    nt s

  and nt_string s =
    let str_out = one_of "\\\"" in
    let str_ch_regular = diff nt_any str_out in
    let str_ch_special = disj_list [(pack (word_ci "\\n") (fun (a) -> '\n'));
                                    (pack (word_ci "\\r") (fun (a) -> '\r'));
                                    (pack (word_ci "\\t") (fun (a) -> '\t'));
                                    (pack (word_ci "\\f") (fun a -> '\012'));
                                    (pack (word_ci "\\\\") (fun (a) -> '\\'));
                                    (pack (word_ci "\\\"") (fun (a) -> '\"'))] in
    let str_ch = disj str_ch_regular str_ch_special in
    let str_str = (star str_ch) in 
    let find_str = caten (caten (char '\"') str_str) (char '\"') in 
    let chars_in_string = pack find_str (fun ((a,b), c) -> b) in
    let nt = pack chars_in_string (fun a -> String(list_to_string a)) in
    nt s

  and nt_nil s =
    let nt = pack (word "()") (fun (ch) -> Nil) in
  nt s

  and nt_char s = 
    let special_ch = disj_list[ (word_ci "nul");      
                                (word_ci "newline");    
                                (word_ci "return");  
                                (word_ci "tab");  
                                (word_ci "page");  
                                (word_ci "space");] in 
    let reg_ch = pack nt_any (fun a -> [a;]) in 
    let all_chars = disj special_ch reg_ch in
    let one_char = caten (word "#\\") all_chars in
    let one_char = pack one_char (fun (a,b) -> (a, (list_to_string b))) in
    let nt = pack one_char (fun (a,b) -> let b_insensitive = (String.lowercase_ascii b) in 
                                          (match b_insensitive with
                                          | "nul" -> Char(char_of_int 0)
                                          | "newline" -> Char(char_of_int 10)
                                          | "return" -> Char(char_of_int 13)
                                          | "tab" -> Char(char_of_int 9)
                                          | "page" -> Char(char_of_int 12)
                                          | "space" -> Char(char_of_int 32)
                                          | _ -> Char(String.get b 0))) in
    nt s

  and nt_list s =
    let nt = (make_paired (make_paired (star nt_whitespace) (star nt_whitespace) (char '(')) (char ')') (star (make_paired (star nt_whitespace) (star nt_whitespace) nt_sexp))) in
    let nt = pack nt (fun (lst)-> (pairs lst)) in
    let nt = pack nt (fun (p)-> (match (find_error (list_append p)) with
                                  | false -> raise X_this_should_not_happen
                                  | true -> p)) in
    nt s

  and nt_dotList s =
    let nt = (make_paired (char '(') (char ')')
    (caten (caten (plus (make_paired (star nt_whitespace) (star nt_whitespace) nt_sexp)) (char '.')) 
    ((make_paired (star nt_whitespace) (star nt_whitespace) nt_sexp)))) in
    let nt = pack nt (fun ((a,b),c) -> (List.append a [c])) in
    let nt = pack nt (fun (lst)-> dot_pairs lst) in
    let nt = pack nt (fun (p)-> (match (find_error (list_append p)) with
                                  | false -> raise X_this_should_not_happen
                                  | true -> p)) in
    nt s

  and nt_quote s =
    let quote_type = disj_list [(pack (word "'") (fun a -> Symbol("quote")));
                                (pack (word "`") (fun a -> Symbol("quasiquote")));
                                (pack (word ",@") (fun a -> Symbol("unquote-splicing")));
                                (pack (word ",") (fun a -> Symbol("unquote")));] in
    let nt = caten quote_type nt_sexp in
    let nt = pack nt (fun (a,b) -> Pair(a, Pair(b, Nil))) in 
    nt s


  and nt_not s = 
    let nt = make_nt_digit '0' '9' 0 in
    let nt = plus nt in
    let nt = pack nt (fun digits ->
        List.fold_left (fun a b -> 10 * a + b) 0 digits) in
    let add_sign = caten (maybe sign) nt in 
    let nt = pack add_sign (fun (sign, num) -> 
      match sign with
      |Some '-' -> float_of_int(num * -1)
      |Some (result) -> float_of_int(num)
      |None -> float_of_int(num)) in 
    let int = not_followed_by nt (diff nt_any (disj (range '0' '9') (char_ci 'e'))) in

    let digits = caten (caten (plus digit) (char '.')) (plus digit) in
    let digitStrings = pack digits (fun ((a,b), c) -> ((list_to_string a), (String.make 1 b) , (list_to_string c))) in
    let nt = pack digitStrings (fun (a,b,c) -> (a^b^c)) in
    let nt = pack nt (fun (lst1) -> (float_of_string lst1)) in
    let nt = caten (maybe sign) nt in 
    let float = pack nt (fun (sign, num) -> 
      match sign with
      |Some '-' -> num *. -1.0
      |Some (result) -> num
      |None -> num) in

    let number = disj float int in
    let nt = pack (caten number (caten (char_ci 'e') number)) (fun (a, (b,c)) -> Number(Float(a*.(float_of_int(10)**c)))) in 
    nt s

and nt_tagged s =
  let nt = (caten (char '#') (make_paired (char '{') (char '}') (plus (one_of_ci "0123456789abcdefghijklmnopqrstuvwxyz!$^*-_=+<>/?")))) in
  let nt = (caten nt (maybe (caten (char '=') nt_sexp)))  in
  let nt = pack nt (fun ((a,name),b) -> 
   match b with
          |Some (c,sexp) -> TaggedSexpr ((list_to_string name),sexp)
          |None -> TagRef((list_to_string name))) in
  let nt = pack nt (fun (a) -> match a with
          | TaggedSexpr(name,sexp) -> (tagged_error a sexp name)
          | _ -> a ) in
  nt s

  and nt_rad_int s = 
    let make_nt_digits = make_nt_digit '0' '9' 0 in 
    let make_nt_digits = disj make_nt_digits (make_nt_digit 'a' 'z' 10) in 
    let make_nt_digits = disj make_nt_digits (make_nt_digit 'A' 'Z' 10) in 
    let nt = (char '#') in 
    let nt = caten nt (plus digit) in
    let nt = pack nt (fun (a, digits) -> int_of_string(list_to_string(digits))) in
    let base = get_base((nt s)) in 
    let nt = caten nt (char_ci 'r') in 
    let int = caten nt (plus (make_nt_digits)) in 
    let int = not_followed_by int (char '.') in
    let int = pack int (fun (some, digits) ->
		    List.fold_left (fun a b -> base * a + b) 0 digits) in
    let add_sign = caten (maybe sign) int in 
    let nt = pack add_sign (fun (sign, num) -> 
    match sign with
    |Some '-' -> Number(Int(num * -1))
    |Some (result) -> Number(Int(num))
    |None -> Number(Int(num))) in 
    nt s

    and nt_rad_float s = 
      let make_nt_digits = make_nt_digit '0' '9' 0 in 
      let make_nt_digits = disj make_nt_digits (make_nt_digit 'a' 'z' 10) in 
      let make_nt_digits = disj make_nt_digits (make_nt_digit 'A' 'Z' 10) in 
      let special_digit = disj digit (range 'a' 'z') in
      let special_digit = disj special_digit (range 'A' 'Z') in 
      let special_digit = disj special_digit (char '.') in
      let nt = (char '#') in 
      let nt = caten nt (plus digit) in
      let nt = pack nt (fun (a, digits) -> int_of_string(list_to_string(digits))) in
      let base = get_base((nt s)) in 
      let nt = caten nt (char_ci 'r') in 
      let float = caten nt (plus (make_nt_digits)) in 
      let float = pack float (fun (some, digits) -> digits) in
      let exp  = pack (caten float (star (special_digit))) (fun (some,digits) -> (list_to_string(digits))) in 
      let (l,r) = exp s in 
      let exp = String.length(l) - 1 in
      let exp = float_of_int(exp) in
      let exp = exp *. (-1.) in 
      let floati = pack (caten float (char '.')) (fun (a,b) -> a) in 
      let float  = pack (caten floati (star (make_nt_digits))) (fun (some,digits) -> 
          (float_of_int(List.fold_left (fun a b -> base * a + b) 0 some)) +. (float_of_int(List.fold_left (fun a b -> (base * a + b)) 0 digits)) *. float_of_int(base)**(exp)) in  
      let add_sign = caten (maybe sign) float in 
      let nt = pack add_sign (fun (sign, num) -> 
      match sign with
      |Some '-' -> Number(Float(num *. -1.))
      |Some (result) -> Number(Float(num))
      |None -> Number(Float(num))) in 
      nt s

      and whitespace s = 
        let ws = pack (char ' ') (fun a -> ()) in
        ws s

      and enter s = 
        let ws = pack (char '\n') (fun a -> ()) in
        ws s

      and r s = 
      let ws = pack (char '\r') (fun a -> ()) in
      ws s

      and t s = 
      let ws = pack (char '\t') (fun a -> ()) in
      ws s

       and linecomment s = 
        let terminate = disj (pack nt_end_of_input (fun (a) -> ())) (pack (char '\n') (fun (a) -> ())) in 
        let l_c = pack (char ';') (fun (a) -> ()) in 
        let l_c = pack (caten l_c (star (diff nt_any terminate))) (fun (a) -> ()) in 
        l_c s
      
      and sexprcomments s =
      let nt = word "#;" in 
      let nt = caten nt nt_sexp in
      let nt = pack nt (fun a -> ()) in 
      nt s

      and skip s = 
      let nt = disj sexprcomments linecomment in 
      let nt = disj nt whitespace in
      let nt = disj enter nt in
      let nt = disj r nt in
      let nt = disj t nt in
      nt s

      and make_skip nt =
        make_paired (star skip) (star skip) nt;; 


(* -----------------module------------------------------------------- *)


module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list

end

= struct

let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let read_sexpr string =
  let string = string_to_list string in
  let nt = nt_sexp string in 
  match nt with 
  | (exp, []) -> exp
  | _ -> raise X_not_yet_implemented ;;

let read_sexprs string = 
  let string = string_to_list string in 
  let nt = (star nt_sexp) string in
  (fun (a,b) -> a) nt;;



  
end;; (* struct Reader *)

