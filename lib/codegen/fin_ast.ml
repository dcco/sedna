open Parser.Dusk_ast
open Fin_type

	(*
		representation for raw code
		- type annotations are generally included for
		-- initialization
		-- box creation
	*)

type gen_exp =
	ConstExpC of const
	| VarExpC of string
	| UnaryExpC of string * gen_exp
	| BinExpC of string * gen_exp * gen_exp
	| CallExpC of int option * gen_exp * gen_exp list * g_type
		(* boxes a value inside a pointer *)
	| BoxExpC of int * gen_exp * g_type
		(* tuple operations (tuple creation also requires a box) *)
	| TagExpC of gen_exp
	| EnumExpC of string
	| EnumRawExpC of gen_exp
	| TupleExpC of int * g_type * gen_exp list
	| MemoryFieldExpC of gen_rw * gen_exp * int option
		(* array operations *)
	| ConstArrayExpC of int list * gen_exp list * g_type
	| NewArrayExpC of gen_exp list * gen_exp list * g_type
	| ArrayIndexExpC of gen_rw * gen_exp * gen_index
	| ArrayLengthExpC of gen_exp
	| ArrayDimsExpC of int * gen_exp
	| ArrayAddExpC of gen_exp * gen_exp
		(* struct operations *)
	| NewStructExpC of string * gen_exp list
		(* misc memory operations *)
	| SizeExpC of g_type
		(* garbage collection *)
	| GCNewRootExpC of gen_exp
and gen_rw = RC of int option * g_type | WC of gen_exp
and gen_index =
	RawIndexC of gen_exp
	| FullIndexC of gen_exp list
and gen_stmt =
	EvalStmtC of gen_exp
	| AssignStmtC of string * gen_exp
	| ReturnStmtC of gen_exp option
	| UnreachableStmtC
	| VarStmtC of string * gen_exp * g_type
	| IfStmtC of gen_exp * gen_stmt list * bool * gen_stmt list * bool
	| WhileStmtC of gen_exp * gen_stmt list
		(* garbage collection *)
	| GCCollectStmtC

type gen_met =
	MethodC of (string * g_type) list * g_type * gen_stmt list

let type_of_method (MethodC(arg_l, tau_r, _): gen_met): g_type list * g_type =
	(List.map (fun (_, tau) -> tau) arg_l, tau_r)

type gen_dec =
	FunDecC of gen_met
	| TDefDecC of g_tdef
	| ConstDecC of gen_exp
	| GlobalDecC of g_type
	| InitDecC of gen_stmt list

	(*
		auxiliary gathering functions
	*)
let rec collect_thru_exp (f: gen_exp -> 'a list) (e: gen_exp): 'a list = match e with
	UnaryExpC(_, e') -> collect_thru_exp f e'
	| BinExpC(_, e1, e2) -> (collect_thru_exp f e1) @ (collect_thru_exp f e2)
	| CallExpC(_, ef, el, _) -> (f e) @ (collect_thru_exp f ef) @ (List.concat (List.map (collect_thru_exp f) el))
	| BoxExpC(_, e', _) -> (f e) @ (collect_thru_exp f e')
	| TagExpC e' -> collect_thru_exp f e'
	| EnumRawExpC e' -> collect_thru_exp f e'
	| TupleExpC(_, _, el) -> (f e) @ (List.concat (List.map (collect_thru_exp f) el))
	| MemoryFieldExpC(rw, e', _) -> (f e) @ (collect_thru_rw f rw) @ (collect_thru_exp f e')
	| NewArrayExpC(dim_l, el, _) ->
		(List.concat (List.map (collect_thru_exp f) dim_l)) @
		(List.concat (List.map (collect_thru_exp f) el))
	| ArrayIndexExpC(rw, e', RawIndexC ei) ->
		(f e) @ (collect_thru_rw f rw) @ (collect_thru_exp f e') @ (collect_thru_exp f ei)
	| ArrayIndexExpC(rw, e', FullIndexC el) ->
		(f e) @ (collect_thru_rw f rw) @ (collect_thru_exp f e') @ (List.concat (List.map (collect_thru_exp f) el))
	| ArrayLengthExpC e' -> collect_thru_exp f e'
	| ArrayDimsExpC(_, e') -> collect_thru_exp f e'
	| ArrayAddExpC(ea, ev) -> (collect_thru_exp f ea) @ (collect_thru_exp f ev)
	| NewStructExpC(_, el) -> List.concat (List.map (collect_thru_exp f) el)
	| GCNewRootExpC e' -> collect_thru_exp f e'
	| ConstExpC _ | VarExpC _ | EnumExpC _ | ConstArrayExpC _ | SizeExpC _ -> f e
and collect_thru_stmt (f: gen_exp -> 'a list) (s: gen_stmt): 'a list = match s with
	EvalStmtC e -> collect_thru_exp f e
	| AssignStmtC(_, e) -> collect_thru_exp f e
	| ReturnStmtC eo -> (match eo with None -> [] | Some e -> collect_thru_exp f e)
	| UnreachableStmtC -> []
	| VarStmtC(_, e, _) -> collect_thru_exp f e
	| IfStmtC(e, b1, _, b2, _) -> (collect_thru_exp f e) @ (collect_thru_body f b1) @ (collect_thru_body f b2)
	| WhileStmtC(e, b) -> (collect_thru_exp f e) @ (collect_thru_body f b)
	| GCCollectStmtC -> []
and collect_thru_body (f: gen_exp -> 'a list) (b: gen_stmt list): 'a list = match b with
	[] -> []
	| s :: st -> (collect_thru_stmt f s) @ (collect_thru_body f st)
and collect_thru_rw (f: gen_exp -> 'a list) (rw: gen_rw): 'a list = match rw with
	RC _ -> []
	| WC e -> collect_thru_exp f e

type box_type =
	VBoxTy of g_type

let debug_box_id (debug: string) (i: int): unit =
	print_string ("box " ^ (string_of_int i) ^ " (" ^ debug ^ ")\n")

let collect_box_body: gen_stmt list -> (int * box_type) list = collect_thru_body (fun e -> match e with
	BoxExpC(i, _, tau_r) -> [(i, VBoxTy tau_r)]
	| CallExpC(iOpt, _, _, tau_r) -> (match iOpt with None -> [] | Some i -> [(i, VBoxTy tau_r)])
	| TupleExpC(i, tau, _) -> [(i, VBoxTy tau)]
	| MemoryFieldExpC(RC (Some i, tau_b), _, _) -> [(i, VBoxTy tau_b)]
	| ArrayIndexExpC(RC (Some i, tau_b), _, _) -> [(i, VBoxTy tau_b)]
	| _ -> []
)

let rec collect_var_stmt (s: gen_stmt): (string * g_type) list = match s with
	EvalStmtC _ -> []
	| AssignStmtC(_, _) -> []
	| ReturnStmtC _ -> []
	| UnreachableStmtC -> []
	| VarStmtC(x, _, tau) -> [(x, tau)]
	| IfStmtC(_, b1, _, b2, _) -> (collect_var_body b1) @ (collect_var_body b2)
	| WhileStmtC(_, b) -> collect_var_body b
	| GCCollectStmtC -> []
and collect_var_body (b: gen_stmt list): (string * g_type) list = match b with
	[] -> []
	| s :: st -> (collect_var_stmt s) @ (collect_var_body st)