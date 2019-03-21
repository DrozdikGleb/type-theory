open Buffer;;
open Printf;;
open Tree;;

let (>>) x f = f x;;

(*let (ic,oc) = (stdin, stdout);;*)
let (ic,oc) = (open_in "input.txt", open_out "output.txt");;

let var_table = Hashtbl.create 100000;;
let free_table = Hashtbl.create 100000;;

(*let read_file  =
let lines = ref [] in
let chan = stdin in
try
  while true; do
    lines := input_line chan :: !lines
  done; !lines
with End_of_file ->
  close_in chan;
  List.rev !lines ;;*)

 let rec print_elements tuples_list =
       match tuples_list with
            [] -> ()
            |(s, i)::tl -> fprintf oc "%s\n" s;
            			(*Hashtbl.add free_table i s;*)
            			print_elements tl;;

let take_free_vars t_in = 		
		let rec free_vars t = match t with
		  | Var(v)    -> [v]
		  | Abs(a, b) -> List.filter (fun x -> x <> a) (free_vars b)
		  | App(a, b) ->
		      let f_a = free_vars a in
		      let f_b = free_vars b in
		        List.append f_a (List.filter (fun x -> not (List.mem x f_a)) f_b) in free_vars t_in;;

let free_var_and_index free_vars = 
		let rec next_var n = 
				if n = 0 then [] 
					else n + 10000 :: (next_var (n - 1))
						in List.combine (free_vars) (next_var (List.length free_vars));;

let string_of_lambda lambda =
		let rec brackets_gen lambda s =
				match lambda with
				| Var (x) -> s ^ x
				| Abs (x, y) -> s ^ "(\\" ^ x ^ "." ^ (brackets_gen y "")  ^ ")"
				| App (x, y) -> s ^ "(" ^ (brackets_gen x "") ^ " " ^ (brackets_gen y "") ^ ")" in
					brackets_gen lambda "";;

let coco num str = Hashtbl.add free_table num str ; num ;;

let toDebrujin t =
  let rec count indices =
      function
          Var(a) -> 
            if List.mem_assoc a indices then
              VarD(coco (List.assoc a indices) a) else VarD (-1)
        | Abs(a, b) -> 
            	let last = List.map (function (a, i) -> (a, if (i < 10000) then i + 1 else i)) (List.remove_assoc a indices) in
              		AbsD(count ((a, 0) :: last) b)
        | App(a, b) -> AppD(count indices a, count indices b)
  					in let free = free_var_and_index (take_free_vars t) in
   				 													count free t;;

let rec rename expr level plus = match expr with
		| AppD(a, b) -> AppD(rename a level plus, rename b level plus)
		| AbsD(a) -> AbsD(rename a (level + 1) plus)
		| VarD(n) -> if (n >= level && n < 10000) then VarD(n + plus) else VarD(n);;


let rec substitute expr term level = match expr with			
		| AppD(a, b) -> AppD(substitute a term level, substitute b term level)
		| AbsD(a) -> AbsD(substitute a term (level + 1))
		| VarD(n) -> if (n = level) then rename term 0 level else (if ((n < 10000) && (n >= level)) then VarD(n - 1) else VarD(n));;

(*если есть в аппликации слева бета редекс, то cправа не трогаем*)		
let rec reduction t = match t with
	| AppD(AbsD(a), b) -> ((substitute a b 0), true) 
	| AppD(a, b) -> let red_result_a, need_beta_a = reduction a in if (need_beta_a = true) then (AppD(red_result_a, b), true) 
											else let red_result_b, need_beta_b = reduction b in (AppD(red_result_a, red_result_b), need_beta_b)
	| AbsD(a) -> let red_result, need_beta = reduction a in (AbsD(red_result), need_beta)
	| VarD(n) -> (VarD(n), false);;

let rec normalize t =
  let red_result, need_beta = reduction t in
    if (need_beta = true) then normalize red_result
    	else red_result;;

let debrujin_to_string debruijn =
		let rec to_string debruijn s level = match debruijn with
  			| VarD(n)    ->  if (n < level) then Hashtbl.find var_table (level - n) else Hashtbl.find free_table n (*  if (n < level) then if (Hashtbl.mem var_table (level - n)) then s ^ "a" ^ Hashtbl.find var_table (level - n) ^ " " else  s ^ "b" ^ string_of_int(n) ^ " " else if (Hashtbl.mem free_table (n)) then s ^  Hashtbl.find free_table (n) ^ " " else s ^ "b" ^ string_of_int(n) ^ " "   (*if (Hashtbl.mem var_table (n + 1)) then s ^ Hashtbl.find var_table (n + 1) else s ^ ("b" ^ string_of_int (n + 1) ^ " ") *) *)

  			| AbsD(a)    -> Hashtbl.add var_table (level + 1) ("a" ^ string_of_int(level + 1));
  								s ^ "(\\" ^ ("a" ^ string_of_int(level + 1) ^ ".") ^ (to_string a "" (level + 1)) ^ ")"

  			| AppD(a, b) -> s ^ "(" ^ (to_string a "" level) ^ " " ^ (to_string b "" level) ^ ")" 
  				in to_string debruijn "" 0;;

(*String.concat "\n" (read_file) >> Lexing.from_string >> Parser.main Lexer.main >> toDebrujin >> normalize >> debrujin_to_string >> fprintf oc "%s\n";;*)
ic >> input_line >> Lexing.from_string >> Parser.main Lexer.main >> toDebrujin >> normalize >> debrujin_to_string >> fprintf oc "%s\n" ;;

close_out oc;;
close_in ic;;
