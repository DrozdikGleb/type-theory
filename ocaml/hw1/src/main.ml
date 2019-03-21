open Buffer;;
open Printf;;
open Tree;;

let (>>) x f = f x;;

let (ic,oc) = (stdin, stdout);;

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

let string_of_lambda lambda = 
		let rec brackets_gen lambda s = 
				match lambda with
				| Var (x) -> s ^ x
				| Abs (x, y) -> s ^ "(\\" ^ x ^ "." ^ (brackets_gen y "")  ^ ")"
				| App (x, y) -> s ^ "(" ^ (brackets_gen x "") ^ " " ^ (brackets_gen y "") ^ ")" in
					brackets_gen lambda "";;

String.concat "\n" (read_file) >> Lexing.from_string >> Parser.main Lexer.main >> string_of_lambda >> fprintf oc "%s\n";;

close_out oc;;
close_in ic;;