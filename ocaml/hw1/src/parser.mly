%{
	open Tree;;
%}
%token <string> VAR
%token OPEN CLOSE
%token EOF
%token DOT
%token LAMBDA
%start main
%type <Tree.lambda> main
%%
main: 	
		expr EOF			{ $1 }

expr: 
		app 						{ $1 }
		| app LAMBDA VAR DOT expr  	{ App($1, Abs($3, $5)) }
		| LAMBDA VAR DOT expr { Abs($2, $4) }

atom:
		OPEN expr CLOSE		{ $2 }
		| VAR 				{ Var ($1)}

app:
		atom				{ $1 }
		| app atom			{ App($1, $2) }