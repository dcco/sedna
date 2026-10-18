open Commons.Try_log
open Parser.Lex_token
open Parser.Dusk_type
open Codegen.Fin_type
open Tc_type

	(*
		#####################
		## error/info data ##
		#####################
	*)

	(* extra context for type-checking function calls *)

type tc_info =
	FieldTCInfo of string * string * g_type
	| CallTCInfo of string * g_type list * g_type * int option
	| ListTCInfo of int option
	| AssignTCInfo of string * g_type

let string_of_tc_info (info: tc_info): string = match info with
	FieldTCInfo(ctor, x, tau_p) ->
		ctor ^ "{ " ^ x ^ ": << " ^ (string_of_type cr tau_p) ^ " >>, .. }"
	| CallTCInfo(f, tau_pl, tau_r, argOpt) ->
		let argStrList = List.mapi (fun i t ->
			let s = string_of_type cr t in
			if Some i = argOpt then	"<< " ^ s ^ " >>" else s
		) tau_pl in 
		let rs = string_of_type cr tau_r in
		let retStr = if Some (List.length tau_pl) = argOpt then "<< " ^ rs ^ " >>" else rs in
		f ^ "(" ^ (String.concat ", " argStrList) ^ ") " ^ retStr
	| ListTCInfo argOpt -> (match argOpt with
		None -> "[<< type annotation >>]"
		| Some i ->	"[] Index: " ^ (string_of_int i)
	)
	| AssignTCInfo(x, t) -> "var " ^ x ^ ": " ^ (string_of_type cr t)

type tc_info_stub =
	CallTCInfoStub of string * g_type list * g_type
	| ListTCInfoStub

let index_stub (info: tc_info_stub) (i: int option): tc_info = match info with
	CallTCInfoStub(f, tau_pl, tau_r) -> CallTCInfo(f, tau_pl, tau_r, i)
	| ListTCInfoStub -> ListTCInfo i

	(* error types *)

type tc_err =
	BadType_Err of lhs_type * g_type * tc_info * l_pos
	| BadJoin_Err of lhs_type * lhs_type * tc_info * l_pos
	| MismatchedArgNum_Err of int * int * tc_info * l_pos
	| IncompleteType_Err of lhs_type * l_pos
		(* functions *)
	| NoOverload_Err of string * lhs_type option * l_pos
		(* tuples *)
	| NonTuple_Err of lhs_type * l_pos
	| NonTuplePat_Err of g_type * l_pos
	| RawTupleOp_Err of lhs_type * l_pos
	| MismatchedPatNum_Err of int * int * l_pos
	| TupleIndexOOB_Err of g_type * int * l_pos
		(* enum / tag tuples *)
	| NonCtor_Err of string * l_pos
	| NonCtorU_Err of string * l_pos
	| NonTagType_Err of lhs_type * l_pos
	| NonEnum_Err of lhs_type * l_pos
	| BadAttr_Err of string * string * l_pos
	| MismatchedAttrNum_Err of string * int * int * l_pos
		(* arrays *)
	| MismatchedArrayDim_Err of int list * int * int * l_pos
	| NestedFormat_Err of l_pos
		(* structs *)
	| NonStruct_Err of lhs_type * l_pos
	| BadCtorStruct_Err of string * l_pos
	| MissingField_Err of string * string * tc_info * l_pos
	| BadField_Err of string * string * l_pos
		(* nullable *)
	| BadNullCheck_Err of g_type * l_pos
		(* functions *)
	| NonFunction_Err of lhs_type * l_pos
		(* returns *)
	| EarlyReturn_Err of string * l_pos
	| NoReturn_Err of string * l_pos
	| BadReturn_Err of lhs_type * g_type * l_pos
		(* constant evaluation *)
	| NonCVar_Err of string * l_pos
	| BadCLoad_Err of string * l_pos
	| FailCLoad_Err of l_pos

type 'a tc_res = ('a, tc_err) try_res

let string_of_first_arg (t: lhs_type option): string = match t with
	None -> "empty arg list"
	| Some tau -> "type \"" ^ (string_of_ltype tau) ^ "\""

let string_of_tc_err (e: tc_err) = match e with
	| BadType_Err(s, t, info, p) -> "Expected type \"" ^ (string_of_type cr t) ^ "\" and received type \"" ^
		(string_of_ltype s) ^ "\" at " ^ (string_of_pos p) ^ ".\n" ^
		"  From: " ^ (string_of_tc_info info)
	| BadJoin_Err(s, t, info, p) -> "Could not reconcile type \"" ^ (string_of_ltype t) ^ "\" with expected type \"" ^
		(string_of_ltype s) ^ "\" at " ^ (string_of_pos p) ^ ".\n" ^
		"  From: " ^ (string_of_tc_info info)
	| MismatchedArgNum_Err(s, t, info, p) -> "Function call expected " ^ (string_of_int t) ^ " arguments and received " ^
		(string_of_int s) ^ " at " ^ (string_of_pos p) ^ ".\n" ^
		"  From: " ^ (string_of_tc_info info)
	| IncompleteType_Err(t, p) -> "Could not determine final type of \"" ^ (string_of_ltype t) ^
		"\" needed at " ^ (string_of_pos p) ^ ".\n"
	| NoOverload_Err(f, t, p) -> "Function \"" ^ f ^ "\" does not have overload for " ^
		(string_of_first_arg t) ^ " at " ^ (string_of_pos p) ^ "."
	| NonTuple_Err(t, p) -> "Tuple operation called on non-tuple type \"" ^ (string_of_ltype t) ^ "\" at " ^ (string_of_pos p) ^ "."
	| NonTuplePat_Err(t, p) -> "Tuple pattern used on non-tuple type \"" ^ (string_of_type cr t) ^ "\" at " ^ (string_of_pos p) ^ "."
	| RawTupleOp_Err(t, p) -> "(Redundant) Operation called on raw tuple literal \"" ^ (string_of_ltype t) ^ "\" at " ^ (string_of_pos p) ^ "."
	| MismatchedPatNum_Err(s, t, p) -> "Pattern expected tuple of " ^ (string_of_int t) ^ " values and received " ^
		(string_of_int s) ^ " at " ^ (string_of_pos p) ^ "."
	| TupleIndexOOB_Err(t, i, p) -> "Attempted to access index " ^ (string_of_int i ) ^ " of tuple type \"" ^
		(string_of_type cr t) ^ "\" at " ^ (string_of_pos p) ^ "."
	| NonCtor_Err(t, p) -> "Type name \"" ^ t ^ "\" did not resolve to a constructor at " ^ (string_of_pos p) ^ "."
	| NonCtorU_Err(t, p) -> "Type name \"" ^ t ^ "\" did not resolve to a union constructor at " ^ (string_of_pos p) ^ "."
	| NonTagType_Err(t, p) -> "Tag requested for untagged type \"" ^ (string_of_ltype t) ^ "\" at " ^ (string_of_pos p) ^ "."
	| NonEnum_Err(t, p) -> "Enum operation called on non-enum type \"" ^ (string_of_ltype t) ^ "\" at " ^ (string_of_pos p) ^ "."
	| BadAttr_Err(t, x, p) -> "Attempted to read non-existent attribute \"" ^ x ^
		"\" from enum \"" ^ t ^ "\" at " ^ (string_of_pos p) ^ "."
	| MismatchedAttrNum_Err(tx, s, t, p) -> "Enum constructor \"" ^ tx ^ "\" expected " ^ (string_of_int t) ^ " attributes and received " ^
		(string_of_int s) ^ " at " ^ (string_of_pos p) ^ "."
	| MismatchedArrayDim_Err(dim_l, dim_prod, n, p) ->
		"Array initializer has " ^ (string_of_int n) ^ " elements, but specified dimensions [" ^
		(String.concat ", " (List.map string_of_int dim_l)) ^ "] require " ^
		(string_of_int dim_prod) ^ " at " ^ (string_of_pos p) ^ "." 
	| NestedFormat_Err p  -> "Variable-size array constructor found outside of top-level assignment at " ^ (string_of_pos p) ^ "."
	| NonStruct_Err(t, p) -> "Struct operation called on non-struct type \"" ^ (string_of_ltype t) ^ "\" at " ^ (string_of_pos p) ^ "."
	| BadCtorStruct_Err(t, p) -> "Attempted to initialize struct with non-struct constructor \"" ^ t ^ "\" at " ^ (string_of_pos p) ^ "."
	| MissingField_Err(t, x, info, p) -> "Initialization of struct \"" ^ t ^
		"\" missing field \"" ^ x ^ "\" at " ^ (string_of_pos p) ^ ".\n" ^
		"  From: " ^ (string_of_tc_info info)
	| BadField_Err(t, x, p) -> "Attempted to read non-existent field \"" ^ x ^
		"\" from struct \"" ^ t ^ "\" at " ^ (string_of_pos p) ^ "."
	| BadNullCheck_Err(t, p) -> "Attempted to perform null check on non-nullable type \"" ^
		(string_of_type cr t) ^ "\" at " ^ (string_of_pos p) ^ "."
	| NonFunction_Err(t, p) -> "Function call on non-function type \"" ^ (string_of_ltype t) ^ "\" at " ^ (string_of_pos p) ^ "."
	| EarlyReturn_Err(f, p) ->
		"Early return from function \"" ^ f ^ "\" producing unreachable code at " ^ (string_of_pos p) ^ "."
	| NoReturn_Err(f, p) ->
		"Declaration of function \"" ^ f ^ "\" does not return on all paths at " ^ (string_of_pos p) ^ "."
	| BadReturn_Err(s, t, p) ->
		"Function expected return type \"" ^ (string_of_type cr t) ^ "\" and received value of type \"" ^
			(string_of_ltype s) ^ "\" at " ^ (string_of_pos p) ^ "."
	| NonCVar_Err(x, p) ->
		"Use of non-constant variable \"" ^ x ^ "\" in constant expression at " ^ (string_of_pos p) ^ "."
	| BadCLoad_Err(f, p) ->
		"Failed cLoad, could not find file \"" ^ f ^ "\" at " ^ (string_of_pos p) ^ "."
	| FailCLoad_Err p -> "Failed cLoad at " ^ (string_of_pos p) ^ "."
