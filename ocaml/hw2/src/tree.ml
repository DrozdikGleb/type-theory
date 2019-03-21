type lambda = 
		Var of string 
		| Abs of string * lambda
		| App of lambda * lambda;;

type debrujin = 
		| VarD of int
		| AbsD of debrujin
		| AppD of debrujin * debrujin
