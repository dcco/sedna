open Parser.Dusk_type
open Codegen.Fin_type

	(*
		#######################
		## left-handed types ##
		#######################
		types that can only be used in the left-hand side of a subtyping expression
		
		ex:
		- these types may be given to values/expression
		- they may NOT be given to variables or in function types
	*)

type lhs_type =
	LT of g_type
	| NullLT
	| RawTupleLT of lhs_type list

let nullable_type (t: lhs_type): bool = match t with
	LT (NullableTy _) -> true
	| LT (CPtrTy _) -> true
	| LT BotTy -> true
	| LT _ -> false
	| NullLT -> true
	| RawTupleLT _ -> false

let rec string_of_ltype (tau: lhs_type): string = match tau with
	LT t -> string_of_type cr t
	| NullLT -> "_Null"
	| RawTupleLT [] -> "(??)"
	| RawTupleLT (tau0 :: tau_t) -> "(" ^ string_of_ltype tau0 ^ " ?? " ^
		String.concat ", " (List.map string_of_ltype tau_t) ^ ")"

	(*
		- values always have enough of their type to "approximate" the type
			well enough for code generation
	*)

let rec approxGenType (tau: lhs_type): g_type = match tau with
	LT t -> t
	| NullLT -> VarTy "A"
	| RawTupleLT tau_l -> TupleTy(false, List.map approxGenType tau_l)
