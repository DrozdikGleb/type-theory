type lambda = 
		Var of string 
		| Abs of string * lambda
		| App of lambda * lambda;;

type alg_type = 
		AtomVar of string
		| Impl of alg_type * alg_type;;

type equation = 
		Equality of alg_type * alg_type;;
