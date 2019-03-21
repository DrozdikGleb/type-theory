open Buffer;;
open Printf;;
open Tree;;
open String;;
open Str;;

let (>>) x f = f x;;

let (ic,oc) = (stdin, stdout);;
(*let (ic,oc) = (open_in "input.txt", open_out "output.txt");;*)

let var_table = Hashtbl.create 10000;;

let global_table = Hashtbl.create 10000;;

let counter = ref 0;;

let lol = ref 0;;

let tab = "*   ";;

let read_file  =
let lines = ref [] in
let chan = stdin in
try
  while true; do
    lines := input_line chan :: !lines
  done; !lines
with End_of_file ->
  close_in chan;
  List.rev !lines ;;

let rec print_expr expr s = match expr with
	| AtomVar(s_var) -> s ^ s_var 
	| Impl(a, b) -> let left = print_expr a "" in let right = print_expr b ""  in 
									s ^ "(" ^ left ^ " -> " ^ right ^ ")";;

let print_left_and_right left right = fprintf oc "%s = %s\n" (print_expr left "") (print_expr right "");;

let rec print_elements tuples_list = 
       match tuples_list with
            [] -> ()
            |Equality(s, i)::tl -> print_left_and_right s i;
            						print_elements tl;;
   
let print_equations (tuple_list, v, d) = print_elements tuple_list;;

let print_equations_after_unification cur_list = print_elements cur_list;;

let inc x = x + 1;;

let gen_new_var k = "a" ^ string_of_int(k);;

let gen_new_var_1 k = "t" ^ string_of_int(k);;

let string_of_lambda lambda =
		let rec brackets_gen lambda s =
				match lambda with
				| Var (x) -> s ^ x
				| Abs (x, y) -> s ^ "(\\" ^ x ^ "." ^ (brackets_gen y "")  ^ ")"
				| App (x, y) -> s ^ "(" ^ (brackets_gen x "") ^ " " ^ (brackets_gen y "") ^ ")" in
					brackets_gen lambda "";;

let rec back expr = match expr with
		| (Var(x), l) -> Var(x)
		| (Abs(x, y), l) -> Abs(x, y)
		| (App(x, y), l) -> App(x, y);;

let rec rename_expr expr map_bound k = match expr with
		| Var(s) -> if (Hashtbl.mem map_bound s) then let asd = Hashtbl.add global_table (Var(gen_new_var_1 (Hashtbl.find map_bound s))) s 
									in (Var(gen_new_var_1 (Hashtbl.find map_bound s)), (k + 1)) else 
											let asd = Hashtbl.add global_table (Var(s)) s in (Var(s), (k + 1))
		| App(a, b) -> let (left, k_1) = rename_expr a map_bound (k + 1) in
                    		let (right, k_2) = rename_expr b map_bound k_1 in (App(left, right), k_2 + 1)
		| Abs(s, r) -> Hashtbl.add map_bound s (k + 1);
						let asd = Hashtbl.add global_table (Var(gen_new_var_1 (k + 1))) s in
                            let (tt, k_1) = rename_expr r map_bound (k + 1) in
                            Hashtbl.remove map_bound s;
                            (Abs(gen_new_var_1 (k + 1), tt), k_1)

let rec build_system expr k = match expr with
		| Var(s) -> if (Hashtbl.mem var_table s) then ([], Hashtbl.find var_table s, k) 
							else let a = Hashtbl.add var_table s (AtomVar(gen_new_var (k + 1))) in 
																	 ([], AtomVar(gen_new_var (k + 1)), k + 1)

		| App(a, b) -> let (system_left, var_left, counter_left) = build_system a k in 
						let (system_right, var_right, counter_right) = build_system b counter_left in 
							let new_eq = Equality(var_left, Impl(var_right, AtomVar(gen_new_var (counter_right + 1)))) in 
								let left = List.append system_left system_right in (List.append left [new_eq], AtomVar(gen_new_var (counter_right + 1)), (counter_right + 1))
		
		| Abs(s, a) -> let (system, var, counter) = build_system a k in let (ins_val, cur_k) = if (Hashtbl.mem var_table s) then (Hashtbl.find var_table s, counter) else 
											let ff = Hashtbl.add var_table s (AtomVar(gen_new_var (counter + 1))) in (AtomVar(gen_new_var (counter + 1)), counter + 1) in (system, Impl(ins_val, var), cur_k);;
(*!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!*)
let rec rewrite system ans_list = match system with
		| [] -> ans_list
		| Equality(Impl(a, b), AtomVar(v)) :: tl -> rewrite tl (List.append ans_list [Equality(AtomVar(v), Impl(a, b))])
		| Equality(a, b) :: tl -> rewrite tl (List.append ans_list [Equality(a, b)]);;

let rec delete_same system ans_list = match system with
		| [] -> ans_list
		| Equality(AtomVar(a), AtomVar(b)) :: tl -> if (a = b) then delete_same tl ans_list else delete_same tl (List.append ans_list [Equality(AtomVar(a), AtomVar(b))])
		| Equality(a, b) :: tl -> delete_same tl (List.append ans_list [Equality(a, b)]);;

let rec reduct_system system ans_list = match system with
			| [] -> ans_list
			| Equality(Impl(a, b), Impl(c, d)) :: tl -> reduct_system tl (List.append ans_list [Equality(a, c); Equality(b, d)])
			| Equality(a, b) :: tl -> reduct_system tl (List.append ans_list [Equality(a, b)]);;
(* достаём все ai = Oi*)
let rec sub_system system ans_list substitutions flag expr = match system with
			| [] -> (ans_list, substitutions, flag, expr)
			| Equality(AtomVar(a), b) :: tl -> 
					if (flag = true) then let sub_sys1, sub1, cur_flag1, cur_expr = sub_system tl ans_list substitutions true expr in
						(List.append sub_sys1 [Equality(AtomVar(a), b)], sub1, true, cur_expr) else if (Hashtbl.mem substitutions (a)) 
									then let sub_sys, sub, cur_flag, cur_expr_1 = sub_system tl ans_list substitutions false expr in (List.append sub_sys [Equality(AtomVar(a), b)], sub, cur_flag, cur_expr_1) 
												else let k = Hashtbl.add substitutions (a) (b) in 
													let sub_sys_2, sub_2, cur_flag_2, cur_expr_2 = sub_system tl ans_list substitutions true [Equality(AtomVar(a), b)] 
																	in (sub_sys_2, sub_2, true, [Equality(AtomVar(a), b)])
													
			| Equality(a, b) :: tl -> (List.append ans_list [Equality(a, b)], substitutions, flag, expr);;

let do_subs expr1 subs1 = 
	let rec do_subs1 expr = match expr with
			| Impl(a, b) -> let left = do_subs1 a in let right = do_subs1 b in Impl(left, right)
			| AtomVar(a) -> if (Hashtbl.mem subs1 (a)) then Hashtbl.find subs1 (a) else AtomVar(a)
			in do_subs1 expr1;;

(*проходимся по уравнением и вызываем метод подстановки*)
let rec apply_subst system subs ans_list = match system with
				| [] -> ans_list 
				| Equality(a, b) :: tl -> let other_eq = apply_subst tl subs ans_list in 
																let new_impl_l = do_subs (a) subs in let new_impl_r = do_subs (b) subs in
																	(List.append other_eq [Equality(new_impl_l, new_impl_r)]) ;;

let rec check_incompat_inner expr term = match expr with
			| AtomVar(a) -> a = term
			| Impl(l, r) -> check_incompat_inner l term || check_incompat_inner r term ;;

let check_incompat system = match system with
			| Equality(AtomVar(a), Impl(b, c)) -> check_incompat_inner (Impl(b, c)) a
			| _ -> false ;;

let has_new_sub substed equality = match equality with
    | Equality(AtomVar(a), b) -> not (Hashtbl.mem substed (AtomVar(a)))
    | _ -> false;;

let rec substitute substitution term = match term with
    | AtomVar(v) -> (match substitution with
    		| Equality(a, b) -> if (a = term) then b else term
			| _ -> (term))
    | Impl(l, r) -> Impl((substitute substitution l), (substitute substitution r))
    | _ -> term;;

let substitute_mapper substitution equality = 
    if (substitution = equality) then
        equality
    else begin
    	match equality with
    	| Equality(a, b) -> let l = substitute substitution a in let r = substitute substitution b in (Equality(l, r))
    	| _ -> equality
    end
(* делаем подстановки *)
let start_solve (system_main, v, d) substed_1 =
	let rec solve_system system substed = 
	counter := !counter + 1; 
	  if (!counter > 75) then system else 
		if (List.exists check_incompat system) then [Equality(AtomVar("тук"), AtomVar("тук"))] else
		let prev = system in 
			let rewrited_system = reduct_system system [] in
				let deleted_system = rewrite rewrited_system [] in 
					let cleaned_system = delete_same deleted_system [] in 
							if (List.exists (has_new_sub substed) cleaned_system) then begin
            					let substitution = List.find (has_new_sub substed) cleaned_system in
            						(match substitution with
            							| Equality(a, b) -> Hashtbl.add substed a true;
            							| _ -> () );
            							 	solve_system (List.rev_map (substitute_mapper substitution) cleaned_system) substed
       											 end else begin
            											solve_system cleaned_system substed
            										end in solve_system system_main substed_1;;

let rec find_type expr system ans = match system with
		| Equality(a, b) :: tl -> if (a = expr) then let cur_ans = find_type expr tl b in (cur_ans) else let cur_ans_1 = find_type expr tl ans in (cur_ans_1)
		| [] -> if (ans = AtomVar("4")) then expr else ans

let rec get_ctx tuples_list system str =
       match tuples_list with
            [] -> str
            |(s, i)::tl -> let cur_str = str ^ s ^ " : " ^ (match i with
            		| AtomVar(v) -> print_expr (find_type (AtomVar(v)) system (AtomVar("4"))) ""
            		| _ -> raise (Failure("get_ctx")))  in let comma = if (tl = []) then cur_str else cur_str ^ ", " in
            			get_ctx tl system comma;;

let take_free_vars_and_types t_in = 		
		let rec free_vars t = match t with
		  | Var(v)    -> [(v, Hashtbl.find var_table v)]
		  | Abs(a, b) -> List.filter (fun (x, y) -> x <> a) (free_vars b)
		  | App(a, b) ->
		      let f_a = free_vars a in
		      let f_b = free_vars b in
		        List.append f_a (List.filter (fun x -> not (List.mem x f_a)) f_b) in free_vars t_in;;

let start expr = let (a, b, c) = build_system expr 0 in   (*fprintf oc "type - %s\n" (print_expr b "");*) (a, b, c);;

let start_solve_1 expr = start_solve expr (Hashtbl.create 10000);;

let rec apply_subst_1 term system = match term with
  | AtomVar(x) ->  (match (List.find_opt (fun (Equality(a, b)) -> a = term) system) with
                  | None -> term
                  | Some(Equality(a, b)) -> b 
                )
  | Impl(a, b) -> Impl((apply_subst_1 a system), (apply_subst_1 b system))
;;

let get_type expr = match expr with
	| Impl(a, b) -> b
    | AtomVar(x) -> AtomVar(x);;

let rec proof_maker expr system free_list ctx cur_tab k = match expr with
  | Var(s) ->  let var = if ((Hashtbl.mem var_table s) && (not (List.exists (fun (a, b) -> a = s) free_list))) then Hashtbl.find var_table s else 
  				let (f, s1) = List.find (fun (a, b) -> a = s) free_list in (s1)
             		in (*fprintf oc "%s - %s\n" (s) (gen_new_var (k + 1));*) let s_type = apply_subst_1 (var) system in
             				let ss = if (Hashtbl.mem global_table (Var(s))) then (Hashtbl.find global_table (Var(s))) else (s) in 
             			let full_str = cur_tab ^ ctx ^ "|- " ^ ss ^ " : " ^ (print_expr s_type "") ^ " [rule #1]" in
             				(ss, s_type, [full_str], (k + 1))                  
  | Abs(s, p) ->	let new_tab = cur_tab ^ tab in
                           	let s_type = apply_subst_1 (Hashtbl.find var_table s) system in
                           		let ss = if (Hashtbl.mem global_table (Var(s))) then Hashtbl.find global_table (Var(s)) else (s) in
                           		let s_type_s = print_expr s_type "" in
                           			let comma = if ((String.length ctx) = 0) then "" else ", " in
                           				let tail_ctx = ctx ^ comma ^ ss ^ " : " ^ s_type_s in
                           					let (p_s, p_t, tail_proof, k_1) = proof_maker p system free_list tail_ctx new_tab (k + 1) in
                          							let cur_s = "(\\" ^ ss ^ ". " ^ p_s ^ ")"  in
                           								let full_str = cur_tab ^ ctx ^ "|- " ^ cur_s ^ " : (" ^ s_type_s ^ " -> " ^ (print_expr p_t "") ^ ")" ^ " [rule #3]" in
                           										let cur_t = Impl(s_type, p_t) in
                           											(cur_s, cur_t, full_str::tail_proof, k_1)
                         
  | App(l, r) ->  let new_tab = cur_tab ^ tab in 
  						let (left_s, left_t, left_proof, k_1) = proof_maker l system free_list ctx new_tab k in
  							let (right_s, right_t, right_proof, k_2) = proof_maker r system free_list ctx new_tab k_1 in 
  								let cur_str = "(" ^ left_s ^ " " ^ right_s ^ ")" in 
  									let cur_type = get_type left_t in 
  										let full_str = cur_tab ^ ctx ^ "|- " ^ cur_str ^ " : " ^ (print_expr cur_type "") ^ " [rule #2]" in 
  											(cur_str, cur_type, full_str :: (List.rev_append (List.rev left_proof) right_proof), k_2 + 1)

let build_proof expr system free_list ctx = begin
  				let (a, b, proof, d) = proof_maker expr system free_list ctx "" 0 in
  					proof
  					 end;;

let remove_blanks = Str.global_replace (Str.regexp " ") "";;

(*String.concat "\n" (read_file) >> Lexing.from_string >> Parser.main Lexer.main >> toDebrujin >> normalize >> debrujin_to_string >> fprintf oc "%s\n";;*)
let in_str = (*input_line ic;;*) String.concat "\n" (read_file);;
let in_expr = let map_bound = Hashtbl.create 1000 in let expr = Parser.main Lexer.main (Lexing.from_string (in_str)) in let rmd_expr = back (rename_expr expr map_bound 0) in (rmd_expr);;
(*let in_expr = Parser.main Lexer.main (Lexing.from_string (in_str));;*)
(*let main = start_solve_1 (start in_expr);;*)
(*let check_system = print_equations_after_unification main;;
let free_vars = take_free_vars_and_types in_expr;;
let ctxx = get_ctx free_vars main "";;*)


let global_solve = let main = start_solve_1 (start in_expr) in if (main = [Equality(AtomVar("тук"), AtomVar("тук"))]) then fprintf oc "%s\n" "Expression has no type" else let free_vars = take_free_vars_and_types in_expr in 
					let ctxx = get_ctx free_vars main "" in
						let proof = build_proof in_expr main free_vars ctxx in 
                       		 List.iter (fun line -> fprintf oc "%s\n" line) proof;;
close_out oc;;
close_in ic;;
