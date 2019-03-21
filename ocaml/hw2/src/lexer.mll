{
	open Parser
}
let ws = [' ' '\t' '\n' '\r']

let var = ['a' - 'z'] ['a' - 'z' '0' - '9' ''']*

rule main = parse
		| ws 		{ main lexbuf }
		| var as v  { VAR (v) }
		| "(" 		{ OPEN }
		| ")"		{ CLOSE }
		| "."		{ DOT }
		| "\\"		{ LAMBDA }
		| eof		{ EOF }
