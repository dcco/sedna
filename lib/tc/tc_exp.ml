open Commons.Try_log
open Builtin.Builtin_core
open Parser.Lex_token
open Parser.Dusk_type
open Parser.Dusk_ast
open Resolve.Res_cont
open Codegen.Fin_type
open Codegen.Fin_ast
open Guard_map
open Tc_type
open Tc_err
open Tc_cont
open Tc_subtype
open Calc_exp
	
	(*
		** type discrimination

		types come in 3 flavors
		- primitive types
		- stack pointer types (boxed types)
		- heap pointer types (heap types)
	*)

let is_boxed_type (env: type_env) (tau: g_type): bool = match tau with
	TupleTy _ -> true
	| NamedTy(cx, _) -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
		Some (_, TcTDef td) -> (match td with
			UnionTD _ -> true
			| _ -> false
		)
		| _ -> failwith "BUG: tc_exp.ml - Invalid type encountered while checking boxed type status."
	)
	| _ -> false

let is_heap_type (env: type_env) (tau: g_type): bool = match tau with
	NamedTy(cx, _) -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
		Some (_, TcTDef td) -> (match td with
			StructTD _ -> true
			| _ -> false
		)
		| _ -> failwith "BUG: tc_exp.ml - Invalid type encountered while checking heap type status."
	)
	| ArrayTy(_, _) -> true
	| _ -> false

	(* boxed type auxiliaries *)

let rc_of_type (env: type_env) (tau: g_type): gen_rw =
	if is_boxed_type env tau then RC(Some (get_box_id_tenv env), tau)
	else RC(None, tau)

	(* type-checking auxiliaries *)

let lookup_gen (t: ('a, 'b) Hashtbl.t) (k: 'a) (e: tc_err): 'b tc_res = match Hashtbl.find_opt t k with
	None -> Error e
	| Some v -> Valid v

let rec index_type_list (tau_l: g_type list) (i: int) (e: tc_err): g_type tc_res = match tau_l with
	[] -> Error e
	| tau :: tau_t -> if i = 0 then Valid tau else index_type_list tau_t (i - 1) e

let lookup_field_list (fl: (string * g_type) list) (x: string) (e: tc_err): (g_type * int) tc_res =
	let rec lfl_rec fl i = match fl with
		[] -> Error e
		| (y, tau) :: ft -> if x = y then Valid (tau, i) else lfl_rec ft (i + 1)
	in lfl_rec fl 0

	(* special type narrowing functions *)

	(* TODO: add substitution for union case lookup *)
let lookup_union_cases (env: type_env) (tau: g_type): (canon_name * (canon_name union_case) list) option = match tau with
	NamedTy(tx, _) -> (match Hashtbl.find_opt env.globalTIds (cr tx) with
		Some (_, TcTDef (UnionTD ul)) -> Some (tx, ul)
		| _ -> None
	)
	| _ -> None

	(* guard / narrowing related functions *)

let guard_set_of_type (env: type_env) (tau: lhs_type): guard_set option = match tau with
	LT (CPtrTy _) -> None
	| LT tau -> if is_heap_type env tau then Some (null_guard_set false) else None
	| NullLT -> Some (null_guard_set true)
	| _ -> None

let narrow_type (env: type_env) (x: string) (tau: g_type): lhs_type = match try_narrow_guard_map env.guardMap x with
	None -> LT tau
	| Some true -> NullLT
	| Some false -> (match tau with
		NullableTy t -> LT t
		| _ -> LT tau
	)

(*
let narrow_type (env: type_env) (x: string) (tau: g_type): g_type = match try_narrow_guard_map env.guardMap x with
	None -> tau
	| Some "valid" -> (match tau with
		NullableTy t -> t
		| _ -> tau
	)
	| Some "null" -> NullTy
	| Some ctor -> (match lookup_union_cases env tau with
		None -> tau
		| Some (tx, ul) -> (match List.find_opt (fun (cx, _, _) -> ctor = cr cx) ul with
			None -> tau
			| Some (_, tau_l, _) -> TagTupleTy(tx, tau_l)
		)
	)*)

	(* enum attribute auxiliaries *)

let attrConstName (tx: canon_name) (x: string): string =
	"ATTR" ^ (cr tx) ^ "_" ^ x

	(* function / operator type-checking *)

type gen_exp_fun = gen_exp list -> g_type -> gen_exp tc_res

let tc_fun_var (env: type_env) (f: canon_name) (tau_a: lhs_type option)
	(p: l_pos): (string * canon_name fun_type * gen_exp_fun) tc_res = match lookup_fun_tenv env f tau_a with
	Some (_f, (d, tau_f)) -> (match d with
		UnaryASMSym fsm -> Valid (cr _f, tau_f, fun el _ -> Valid (UnaryExpC(fsm, List.hd el)))
		| BinaryASMSym fsm -> Valid (cr _f, tau_f, fun el _ -> Valid (BinExpC(fsm, List.hd el, List.nth el 1)))
		| InternalSym fsm -> Valid (cr _f, tau_f, fun el tau_r -> calc_cfun env fsm el tau_r p)
		| _ -> Valid (cr _f, tau_f, fun el tau_r ->
			let iOpt = if is_boxed_type env tau_r then Some (get_box_id_tenv env) else None in
			Valid (CallExpC(iOpt, VarExpC (cr _f), el, tau_r))
		)
	)
	| None -> Error (NoOverload_Err(cr f, tau_a, p))

let stub_cn (x: string): canon_name = CN(x, [x])

let tc_op (env: type_env) (xop: x_op) (tau_a: lhs_type) (p: l_pos): (string * canon_name fun_type * gen_exp_fun) tc_res = match (xop, tau_a) with
		(* tuple lookup *)
	(TupleIndexOp i, LT (TupleTy(zFlag, tau_l))) ->
		let* tau_i = index_type_list tau_l (i - 1) (TupleIndexOOB_Err(TupleTy(zFlag, tau_l), i, p)) in
		Valid ("", ([TupleTy(zFlag, tau_l)], tau_i), fun el tau_r ->
			Valid (MemoryFieldExpC(rc_of_type env tau_r, List.hd el, Some (i - 1)))
		)
	| (TupleIndexOp _, RawTupleLT _) -> Error (RawTupleOp_Err(tau_a, p))
	| (TupleIndexOp _, _) -> Error (NonTuple_Err(tau_a, p))
		(* array lookup *)
	| (ArrayIndexOp rw, LT (ArrayTy(i, tau_v))) -> 
		let tau_i = List.init i (fun _ -> intTy) in
		let tau_il = if rw = RR then tau_i else tau_v :: tau_i in
		Valid ("<< array index >>", (ArrayTy(i, tau_v) :: tau_il, if rw = RR then tau_v else unitTy), fun el tau_r ->
			let (rw', eil) =
				if rw = RR then (rc_of_type env tau_r, List.tl el)
				else (WC (List.nth el 1), List.tl (List.tl el))
			in Valid (ArrayIndexExpC(rw', List.hd el, FullIndexC eil))
		)
	| (ArrayIndexOp _, _) -> tc_fun_var env (stub_cn "_builtin_lookup") (Some tau_a) p
		(* struct / enum attr lookup *)
		(* TODO: polymorphism for named type here *)
	| (StructFieldOp(rw, x), LT (NamedTy(cx, tau_al))) -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
			(* check field *)
		Some (_, TcTDef (StructTD(xl, fl))) -> 
			let sol = gen_sol xl tau_al in
			let fl' = List.map (fun (f, tau) -> (f, apply_sol sol tau)) fl in
			let* (tau, i) = lookup_field_list fl' x (BadField_Err(cr cx, x, p)) in
			let (tau_args, tau_r) =
				if rw = RR then ([NamedTy(cx, tau_al)], tau)
				else ([NamedTy(cx, tau_al); tau], unitTy)
			in Valid ("<< struct field >>", (tau_args, tau_r), fun el _ ->
				let rw' = if rw = RR then rc_of_type env tau_r else WC (List.nth el 1) in
				Valid (MemoryFieldExpC(rw', List.hd el, Some i))
			)
		| Some (_, TcTDef (EnumTD _)) ->
			let* attrs = lookup_gen env.globalAttrs (cr cx) (NonStruct_Err(tau_a, p)) in
			let* tau = lookup_gen attrs x (BadAttr_Err(cr cx, x, p)) in
			Valid ("", ([NamedTy(cx, tau_al)], tau), fun el tau_r ->
				let rc = rc_of_type env tau_r in
				Valid (ArrayIndexExpC(rc, VarExpC (attrConstName cx x), RawIndexC (List.hd el)))
			)
		| _ -> Error (NonStruct_Err(tau_a, p))
	)
	| (StructFieldOp _, _) -> Error (NonStruct_Err(tau_a, p))
		(* union -> enum *)
	| (TupleTagOp, LT (NamedTy(cx, tau_l))) -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
		Some (_, TcTDef (UnionTD _)) ->
			Valid ("", ([NamedTy(cx, tau_l)], TagOfTy cx), fun el tau_r ->
				Valid (MemoryFieldExpC(rc_of_type env tau_r, List.hd el, Some 0))
			)
		| _ -> Error (NonTagType_Err(tau_a, p))
	)
	| (TupleTagOp, _) -> Error (NonTagType_Err(tau_a, p))
		(* enum -> raw int *)
	| (EnumRawOp, LT (NamedTy(cx, tau_l))) -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
		Some (_, TcTDef (EnumTD _)) ->
			Valid ("<< raw enum value >>", ([NamedTy(cx, tau_l)], intTy), fun el _ ->
				Valid (EnumRawExpC (List.hd el))
			)
		| _ -> Error (NonEnum_Err(tau_a, p))
	)
	| (EnumRawOp, _) -> Error (NonEnum_Err(tau_a, p))
		(* array measure *)
	| (MeasureOp, LT (ArrayTy(i, tau_v))) ->
		if i = 1 then Valid ("", ([ArrayTy(i, tau_v)], intTy), fun el _ ->
			Valid (ArrayLengthExpC (List.hd el))
		) else Valid ("", ([ArrayTy(i, tau_v)], TupleTy(false, List.init i (fun _ -> intTy))), fun el _ ->
			Valid (ArrayDimsExpC(i, List.hd el))
		)
	| (MeasureOp, _) -> tc_fun_var env (stub_cn "_builtin_measure") (Some tau_a) p
		(* array insertion *)
	| (ArrayAddOp, LT (ArrayTy(1, tau_v))) ->
		Valid ("", ([ArrayTy(1, tau_v); tau_v], unitTy), fun el _ ->
			Valid (ArrayAddExpC(List.hd el, List.nth el 1))
		)
	| (ArrayAddOp, _) -> tc_fun_var env (stub_cn "_builtin_insert") (Some tau_a) p


	(*| (EnumRawOp, TagTupleTy _) ->
			failwith "UNIMPLEMENTED: tc_exp.ml - Tag operation on narrowed union type."
		| Some tau -> Error (NonEnum_Err(tau, p))
	)*)
		(* pseudo-functions *)



(*
			| ArrayLengthGF -> Valid (ArrayLengthExpC (List.hd el'), tau_rf)
			| ArrayDimsGF i -> Valid (ArrayDimsExpC(i, List.hd el'), tau_rf)
			| ArrayAddGF -> Valid (ArrayAddExpC(List.hd el', List.nth el' 1), tau_rf)
			| EnumRawGF -> Valid (EnumRawExpC (List.hd el'), tau_rf)


	| OpExp(ArrayIndexOp rw, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for array index operation."
		| Some (ArrayTy(i, tau_v)) ->
				(* strictly speaking, it should return unit for the WRITE case,
					but we need the inner type for code-gen *)
			let tau_i = List.init i (fun _ -> intTy) in
			let tau_il = if rw = RR then tau_i else tau_v :: tau_i in
			Valid ("", ArrayIndexGF rw, (ArrayTy(i, tau_v) :: tau_il, tau_v))
		| Some _ ->
			let fName = if rw = RR then "_builtin_lookup" else "_builtin_update" in
			tc_fun_exp env (VarExp(stub_cn fName, p)) tau_a
	)
	| OpExp(StructFieldOp(rw, x), p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for struct field operation."
		| Some (NamedTy(cx, _)) -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
				(* check field *)
			Some (_, TcTDef (StructTD fl)) -> (match lookup_field_list fl x with
				None -> Error (BadField_Err(cr cx, x, p))
				| Some (tau, i) ->
					(* read / write case *)
					let (tau_args, tau_r) =
						if rw = RR then ([NamedTy(cx, [])], tau)
						else ([NamedTy(cx, []); tau], unitTy)
					in Valid ("", StructFieldGF(rw, i), (tau_args, tau_r))
			)
			| Some (_, TcTDef (EnumTD _)) -> (match Hashtbl.find_opt env.globalAttrs (cr cx) with
				None -> Error (NonStruct_Err(NamedTy(cx, []), p))
				| Some attrs -> (match Hashtbl.find_opt attrs x with
					None -> Error (BadAttr_Err(cr cx, x, p))
					| Some tau -> Valid ("", EnumAttrGF(cx, x), ([NamedTy(cx, [])], tau))
				)
			)
			| _ -> Error (NonStruct_Err(NamedTy(cx, []), p))
		)
		| Some tau -> Error (NonStruct_Err(tau, p))
	)
	| OpExp(MeasureOp, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for measure operation."
		| Some (ArrayTy(i, tau_v)) ->
			if i = 1 then Valid ("", ArrayLengthGF, ([ArrayTy(i, tau_v)], intTy))
			else Valid ("", ArrayDimsGF i, ([ArrayTy(i, tau_v)], TupleTy(false, List.init i (fun _ -> intTy))))
		| Some _ -> tc_fun_exp env (VarExp(stub_cn "_builtin_measure", p)) tau_a
	)
	| OpExp(ArrayAddOp, _) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for array add operation."
		| Some (ArrayTy(1, tau_v)) ->
			Valid ("", ArrayAddGF, ([ArrayTy(1, tau_v); tau_v], unitTy))
		| Some _ -> failwith "UNIMPLEMENTED: tc_exp.ml - No default function name for array add operation."
	)
	| OpExp(ArrayRemoveOp, _) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for array removal operation."
		| Some (ArrayTy(1, tau_v)) ->
			Valid ("_a1_builtin_remove", CallGF, ([ArrayTy(1, tau_v); intTy], unitTy))
		| Some _ -> failwith "UNIMPLEMENTED: tc_exp.ml - No default function name for array removal operation."
	)
	| OpExp(TupleTagOp, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for tuple tag operation."
		| Some (NamedTy(cx, tau_l)) ->
			let tau = NamedTy(cx, tau_l) in
			(match Hashtbl.find_opt env.globalTIds (cr cx) with
				Some (_, TcTDef (UnionTD _)) -> Valid ("", TupleIndexGF 0, ([tau], TagOfTy tau))
				| _ -> Error (NonTagType_Err(tau, p))
			)
		| Some (TagTupleTy _) ->
			failwith "UNIMPLEMENTED: tc_exp.ml - Tag operation on narrowed union type."
		| Some tau -> Error (NonTagType_Err(tau, p))
	)
	| OpExp(EnumRawOp, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for raw enum operation."
		| Some (NamedTy(cx, tau_l)) ->
			let tau = NamedTy(cx, tau_l) in
			(match Hashtbl.find_opt env.globalTIds (cr cx) with
				Some (_, TcTDef (EnumTD _)) -> Valid ("", EnumRawGF, ([tau], intTy))
				| _ -> Error (NonEnum_Err(tau, p))
			)
		| Some (TagTupleTy _) ->
			failwith "UNIMPLEMENTED: tc_exp.ml - Tag operation on narrowed union type."
		| Some tau -> Error (NonEnum_Err(tau, p))
	)
*)
	(* expression type-checking *)

let tc_const (c: const): lhs_type = match c with
	IConst(_, u, s) -> LT (IntTy(u, s))
	| FConst _ -> LT floatTy
	| SConst _ -> LT stringTy
	| BConst _ -> LT boolTy
	| NullConst -> NullLT

let tc_simple_var (env: type_env) (x: string): g_type = match StringMap.find_opt x env.localIds with
	Some tau -> tau
	| _ -> (match Hashtbl.find_opt env.globalIds x with
		Some (_, tau, _) -> tau
		| _ -> failwith "BUG: tc_exp.ml - Failed variable lookup during type-checking phase."
	)

let tc_var (env: type_env) (x: canon_name): string * g_type = match StringMap.find_opt (cr x) env.localIds with
	Some tau -> (cr x, tau)
	| _ -> (match Hashtbl.find_opt env.globalIds (cr x) with
		Some (_, tau, _) -> (cr x, tau)
		| _ -> (match lookup_fun_tenv_nodis env x with
			Some (x', (_, (tau_pl, tau_r))) -> (cr x', FunTy(tau_pl, tau_r))
			| _ -> failwith "UNIMPLEMENTED: tc_exp.ml - Error for ambiguous function deref"
		)
	)

let rec tc_exp (env: type_env) (e: r_exp): (gen_exp * lhs_type) tc_res = match e with
	ConstExp(c, _) -> Valid (ConstExpC c, tc_const c)
	| TConstExp(t, _) -> Valid (SizeExpC t, LT (TValTy t))
	| VarExp(x, _) -> 
		let (x', tau) = tc_var env x in
		Valid (VarExpC x', narrow_type env x' tau) (*match StringMap.find_opt (cr x) env.localIds with
		Some tau -> Valid (VarExpC (cr x), tau)
		| _ -> (match Hashtbl.find_opt env.globalIds (cr x) with
			Some (_, tau) -> Valid (VarExpC (cr x), tau)
			| _ -> failwith "BUG: tc_exp.ml - Failed variable lookup during type-checking phase."
		)
	*)
	| OpExp(_, _) -> failwith "BUG: tc_exp.ml - Operator expression in non-application position."
		(* TODO: named ty args for @ constructor + tuple *)
	| AtCtorExp(ctor, p) -> (match Hashtbl.find_opt env.globalTIds (cr ctor) with
		Some (_, TcCtorU c) -> Valid (EnumExpC (cr ctor), LT (TagOfTy c))
		| _ -> Error (NonCtorU_Err(cr ctor, p))
	)
	| TupleExp(ctor, el, p) ->
		let* et_l' = tc_exp_list env el in (match ctor with
			None ->
					(* - raw tuple *)
				let tau_s = RawTupleLT (List.map snd et_l') in
				Valid (TupleExpC(get_box_id_tenv env, approxGenType tau_s, List.map fst et_l'), tau_s)
			| Some cx -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
					(* - enum ctor (no args) *)
				Some (_, TcCtorE c) -> Valid (EnumExpC (cr cx), LT (NamedTy(c, [])))
				| Some (_, TcCtorU c) ->
					(* - union ctor (args) *)
					let tau_s = NamedTy(c, []) in
					Valid (TupleExpC(get_box_id_tenv env, tau_s, (EnumExpC (cr cx)) :: List.map fst et_l'), LT tau_s)
				| Some (_, TcTDef (EnumTD _)) ->
					(* - raw int -> enum ctor *)
					let (e', _) = List.hd et_l' in
					Valid (TagExpC e', LT (NamedTy(cx, [])))
				| _ -> Error (NonCtor_Err(cr cx, p))
			)
		)
	| DataArrayExp(i, tau_o, dim_l, el, p) ->
		(* let tau = (match tau_o with None -> snd (List.hd et_l') | Some tau -> LT tau) in*)
		let* et_l' = tc_exp_list env el in
		let* tau_inner = tc_type_join ListTCInfoStub (List.map snd et_l') p in
		let* tau_a = (match tau_o with
			None -> let* tau_inner' = complete_type tau_inner p in Valid tau_inner'
			| Some tau_x ->
				let* _ = tc_simp_subtype (ListTCInfo None) tau_inner tau_x p in Valid tau_x
		) in
		let dim_prod = List.fold_left (fun i p -> i * p) 1 dim_l in
		if dim_prod <> List.length el then Error (MismatchedArrayDim_Err (dim_l, dim_prod, List.length el, p))
		else let dim_v = List.map (fun i -> ConstExpC (i_const i)) dim_l in
			Valid (NewArrayExpC(dim_v, List.map fst et_l', tau_a), LT (ArrayTy(i, tau_a)))
	| FormatArrayExp(_, _, _, p) -> Error (NestedFormat_Err p)
	| ZeroArrayExp(i, dim_l, tau, _) ->
		let* dt_l' = tc_exp_list env dim_l in
		Valid (NewArrayExpC(List.map fst dt_l', [], tau), LT (ArrayTy(i, tau)))
		(* TODO: when constructing a struct type, figure out how the "type inference" will work *)
	| NewStructExp(cx, fl, p) ->
		let* ftl' = map_try_res (fun (x, e) -> let* (e', t) = tc_exp env e in Valid (x, e', t)) fl in
		let* (el', tau_l) = (match Hashtbl.find_opt env.globalTIds (cr cx) with
			Some (_, TcTDef (StructTD(xl, pl))) ->
				let sol = new_sol () in
				let* el' = map_try_res (fun (x, tau_p) ->
					match List.find_opt (fun (y, _, _) -> x = y) ftl' with
						None -> Error (MissingField_Err(cr cx, x, FieldTCInfo(cr cx, x, tau_p), p))
						| Some (_, e', tau_a) ->
							let* _ = tc_subtype sol (FieldTCInfo(cr cx, x, tau_p)) tau_a tau_p p in Valid e' 
				) pl in
				let* _ = complete_sol sol p in
				let tau_l = extract_sol sol xl in Valid (el', tau_l)
			| Some _ -> Error (BadCtorStruct_Err(cr cx, p))
			| _ -> Error (NonCtor_Err(cr cx, p))
		) in Valid (NewStructExpC(cr cx, el'), LT (NamedTy(cx, tau_l)))
	| IsNullExp(e, y, p) ->
		let* (ev, tau) = tc_exp env e in
		let asm = if y then "ptr_eq" else "ptr_neq" in
		if nullable_type tau then Valid (BinExpC(asm, ev, ConstExpC NullConst), LT boolTy)
		else Error (BadNullCheck_Err(tau, p))
	(*| IsExp(e, None, p) ->
		let* (ev, tau) = tc_exp env e in
		if is_subtype (new_sol ()) NullTy tau then Valid (BinExpC("ptr_eq", ev, ConstExpC NullConst), boolTy)
		else Error (BadNullCheck_Err(tau, p))
	| IsExp(e, Some ctor, p) ->
		let* (ex, tau) = tc_exp env e in
		let* (derefFlag, ec) = (match Hashtbl.find_opt env.globalTIds (cr ctor) with
			Some (_, TcCtorE _) -> Valid (false, EnumExpC (cr ctor))
			| Some (_, TcCtorU _) -> Valid (true, EnumExpC (cr ctor))
			| _ -> Error (NonCtorU_Err(cr ctor, p))
		) in
		let ev = if derefFlag then MemoryFieldExpC(rc_of_type env tau, ex, None) else ex in
		Valid (BinExpC("tag_eq", ev, ec), boolTy)*)
	(*match Hashtbl.find_opt env.globalIds f with
		Some (_, tau, _) -> (
		)
		| _ -> failwith "BUG: tc_exp.ml - Failed function variable lookup during type-checking phase."
	*)
	| AppExp(ef, el, p) ->
			(* - type-check the arguments *)
		let* et_l' = tc_exp_list env el in
		let tau_al = List.map snd et_l' in
		let el' = List.map fst et_l' in
		let* (fRaw, (tau_pl, _tau_rn), f_res) = tc_fun_exp env ef (hd_opt tau_al) in
		try let sol = new_sol () in
			let* _ = tc_type_list sol (CallTCInfoStub(fRaw, tau_pl, _tau_rn)) tau_al tau_pl p in
			let* _ = complete_sol sol p in
			let tau_rf = apply_sol sol _tau_rn in
			let* ef' = f_res el' tau_rf in Valid (ef', LT tau_rf)
		with Invalid_argument _ -> failwith "BUG: tc_exp.ml - Unknown operator OOB exception."
			(* - get the function type + check the types *)
		(*let* (fRaw, d, (tau_pl, _tau_rn)) = tc_fun_exp env ef (hd_opt tau_al) in
		try let sol = new_sol () in
			let* _ = tc_type_list sol (CallTCInfoStub(fRaw, tau_pl, _tau_rn)) tau_al tau_pl p in
			let tau_rf = apply_sol sol _tau_rn in (match d with
			UnaryGF fsm -> Valid (UnaryExpC(fsm, List.nth el' 0), tau_rf)
			| BinaryGF fsm -> Valid (BinExpC(fsm, List.nth el' 0, List.nth el' 1), tau_rf)
			| InternalGF fsm ->	let* c = calc_cfun env fsm el' tau_rf p in Valid (c, tau_rf)
			| TupleIndexGF i -> Valid (MemoryFieldExpC(rc_of_type env tau_rf, List.hd el', Some i), tau_rf)
			| ArrayIndexGF rw ->
				let (rw', tau_r', et') =
					if rw = RR then (rc_of_type env tau_rf, tau_rf, List.tl el')
					else (WC (List.nth el' 1), unitTy, List.tl (List.tl el')) in
				Valid (ArrayIndexExpC(rw', List.hd el', FullIndexC et'), tau_r')
			| ArrayLengthGF -> Valid (ArrayLengthExpC (List.hd el'), tau_rf)
			| ArrayDimsGF i -> Valid (ArrayDimsExpC(i, List.hd el'), tau_rf)
			| ArrayAddGF -> Valid (ArrayAddExpC(List.hd el', List.nth el' 1), tau_rf)
			| StructFieldGF(rw, i) ->
				let rw' = if rw = RR then rc_of_type env tau_rf else WC (List.nth el' 1) in
				Valid (MemoryFieldExpC(rw', List.nth el' 0, Some i), tau_rf)
			| CallGF ->
				let elx = List.map (fun (e', _) -> e') et_l' in
				let iOpt = if is_boxed_type env tau_rf then Some (get_box_id_tenv env) else None in
				Valid (CallExpC(iOpt, VarExpC fRaw, elx, tau_rf), tau_rf)
			| EnumRawGF -> Valid (EnumRawExpC (List.hd el'), tau_rf)
			| EnumAttrGF(tx, x) ->
				let rc = rc_of_type env tau_rf in
				Valid (ArrayIndexExpC(rc, VarExpC (attrConstName tx x), RawIndexC (List.hd el')), tau_rf)
		)
		with Invalid_argument _ -> failwith "BUG: tc_exp.ml - Unknown operator OOB exception." *)
and tc_fun_exp (env: type_env) (ef: r_exp) (tau_a: lhs_type option): (string * canon_name fun_type * gen_exp_fun) tc_res = match ef with
	VarExp(f, p) -> tc_fun_var env f tau_a p
	(*VarExp(f, p) -> (match lookup_fun_tenv env f tau_a with
		Some (_f, (d, tau_f)) -> (match d with
			UnaryASMSym fsm -> Valid (cr _f, tau_f, fun el _ -> Valid (UnaryExpC(fsm, List.hd el)))
			| BinaryASMSym fsm -> Valid (cr _f, tau_f, fun el _ -> Valid (BinExpC(fsm, List.hd el, List.nth el 1)))
			| InternalSym fsm -> Valid (cr _f, tau_f, fun el tau_r -> calc_cfun env fsm el tau_r p)
			| _ -> Valid (cr _f, tau_f, fun el tau_r ->
				let iOpt = if is_boxed_type env tau_r then Some (get_box_id_tenv env) else None in
				Valid (CallExpC(iOpt, VarExpC (cr _f), el, tau_r))
			)
		)
		| None -> Error (NoOverload_Err(cr f, tau_a, p))
	)*)
	| OpExp(xop, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - Operator invoked without argument."
		| Some tau_a -> tc_op env xop tau_a p
	)
	| _ -> let* (ef', tau_f) = tc_exp env ef in (match tau_f with
		LT (FunTy(tau_pl, tau_r)) -> 
			Valid ("<< function pointer >>", (tau_pl, tau_r), fun el tau_r ->
				let iOpt = if is_boxed_type env tau_r then Some (get_box_id_tenv env) else None in
				Valid (CallExpC(iOpt, ef', el, tau_r))
			)
		| _ -> Error (NonFunction_Err(tau_f, ann_exp ef))
	)
(*and tc_fun_exp (env: type_env) (ef: r_exp) (tau_a: g_type option): (string * g_fun * canon_name fun_type) tc_res = match ef with
	VarExp(f, p) -> (match lookup_fun_tenv env f tau_a with
		Some (_f, (d, tau_f)) -> (match d with
			UnaryASMSym fsm -> Valid (cr _f, UnaryGF fsm, tau_f)
			| BinaryASMSym fsm -> Valid (cr _f, BinaryGF fsm, tau_f)
			| InternalSym fsm -> Valid (cr _f, InternalGF fsm, tau_f)
			| ExternalSym -> Valid (cr _f, CallGF, tau_f)
			| _ -> Valid (cr _f, CallGF, tau_f)
		)
		| None -> Error (NoOverload_Err(cr f, tau_a, p))
	)
		(* TODO: tuple index op with narrowing *)
	| OpExp(TupleIndexOp i, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for tuple index operation."
		| Some (TupleTy(zFlag, tau_l)) -> (match index_type_list tau_l (i - 1) with
			None -> Error (TupleIndexOOB_Err(TupleTy(zFlag, tau_l), i, p))
			| Some tau_i ->	Valid ("", TupleIndexGF (i - 1), ([TupleTy(zFlag, tau_l)], tau_i))
		)
		| Some (TagTupleTy(tx, tau_l)) -> (match index_type_list tau_l (i - 1) with
			None -> Error (TupleIndexOOB_Err(NamedTy(tx, []), i, p))
			| Some tau_i ->	Valid ("", TupleIndexGF i, ([TagTupleTy(tx, tau_l)], tau_i))
		)
		| Some tau -> Error (NonTuple_Err(tau, p))
	)
	| OpExp(ArrayIndexOp rw, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for array index operation."
		| Some (ArrayTy(i, tau_v)) ->
				(* strictly speaking, it should return unit for the WRITE case,
					but we need the inner type for code-gen *)
			let tau_i = List.init i (fun _ -> intTy) in
			let tau_il = if rw = RR then tau_i else tau_v :: tau_i in
			Valid ("", ArrayIndexGF rw, (ArrayTy(i, tau_v) :: tau_il, tau_v))
		| Some _ ->
			let fName = if rw = RR then "_builtin_lookup" else "_builtin_update" in
			tc_fun_exp env (VarExp(stub_cn fName, p)) tau_a
	)
	| OpExp(StructFieldOp(rw, x), p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for struct field operation."
		| Some (NamedTy(cx, _)) -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
				(* check field *)
			Some (_, TcTDef (StructTD fl)) -> (match lookup_field_list fl x with
				None -> Error (BadField_Err(cr cx, x, p))
				| Some (tau, i) ->
					(* read / write case *)
					let (tau_args, tau_r) =
						if rw = RR then ([NamedTy(cx, [])], tau)
						else ([NamedTy(cx, []); tau], unitTy)
					in Valid ("", StructFieldGF(rw, i), (tau_args, tau_r))
			)
			| Some (_, TcTDef (EnumTD _)) -> (match Hashtbl.find_opt env.globalAttrs (cr cx) with
				None -> Error (NonStruct_Err(NamedTy(cx, []), p))
				| Some attrs -> (match Hashtbl.find_opt attrs x with
					None -> Error (BadAttr_Err(cr cx, x, p))
					| Some tau -> Valid ("", EnumAttrGF(cx, x), ([NamedTy(cx, [])], tau))
				)
			)
			| _ -> Error (NonStruct_Err(NamedTy(cx, []), p))
		)
		| Some tau -> Error (NonStruct_Err(tau, p))
	)
	| OpExp(MeasureOp, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for measure operation."
		| Some (ArrayTy(i, tau_v)) ->
			if i = 1 then Valid ("", ArrayLengthGF, ([ArrayTy(i, tau_v)], intTy))
			else Valid ("", ArrayDimsGF i, ([ArrayTy(i, tau_v)], TupleTy(false, List.init i (fun _ -> intTy))))
		| Some _ -> tc_fun_exp env (VarExp(stub_cn "_builtin_measure", p)) tau_a
	)
	| OpExp(ArrayAddOp, _) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for array add operation."
		| Some (ArrayTy(1, tau_v)) ->
			Valid ("", ArrayAddGF, ([ArrayTy(1, tau_v); tau_v], unitTy))
		| Some _ -> failwith "UNIMPLEMENTED: tc_exp.ml - No default function name for array add operation."
	)
	| OpExp(ArrayRemoveOp, _) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for array removal operation."
		| Some (ArrayTy(1, tau_v)) ->
			Valid ("_a1_builtin_remove", CallGF, ([ArrayTy(1, tau_v); intTy], unitTy))
		| Some _ -> failwith "UNIMPLEMENTED: tc_exp.ml - No default function name for array removal operation."
	)
	| OpExp(TupleTagOp, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for tuple tag operation."
		| Some (NamedTy(cx, tau_l)) ->
			let tau = NamedTy(cx, tau_l) in
			(match Hashtbl.find_opt env.globalTIds (cr cx) with
				Some (_, TcTDef (UnionTD _)) -> Valid ("", TupleIndexGF 0, ([tau], TagOfTy tau))
				| _ -> Error (NonTagType_Err(tau, p))
			)
		| Some (TagTupleTy _) ->
			failwith "UNIMPLEMENTED: tc_exp.ml - Tag operation on narrowed union type."
		| Some tau -> Error (NonTagType_Err(tau, p))
	)
	| OpExp(EnumRawOp, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for raw enum operation."
		| Some (NamedTy(cx, tau_l)) ->
			let tau = NamedTy(cx, tau_l) in
			(match Hashtbl.find_opt env.globalTIds (cr cx) with
				Some (_, TcTDef (EnumTD _)) -> Valid ("", EnumRawGF, ([tau], intTy))
				| _ -> Error (NonEnum_Err(tau, p))
			)
		| Some (TagTupleTy _) ->
			failwith "UNIMPLEMENTED: tc_exp.ml - Tag operation on narrowed union type."
		| Some tau -> Error (NonEnum_Err(tau, p))
	)
	| _ -> failwith "UNIMPLEMENTED: tc_exp.ml - function non-var case."*)
and tc_exp_list (env: type_env) (el: r_exp list): ((gen_exp * lhs_type) list) tc_res = match el with
	[] -> Valid []
	| e :: et ->
		let* res = tc_exp env e in
		let* res_t = tc_exp_list env et in Valid (res :: res_t)

let tc_extra_exp (env: type_env) (e: r_exp) (x: string): (gen_exp * lhs_type * gen_stmt list) tc_res = match e with
	FormatArrayExp(i, dim_l, ei, p) ->
		let* dt_l' = tc_exp_list env dim_l in
		let* (ei', tau) = tc_exp env ei in
		let* tau_f = complete_type tau p in
		let b = [
			VarStmtC("__i", ConstExpC (i_const 0), intTy);
			WhileStmtC(BinExpC("ilt", VarExpC "__i", ArrayLengthExpC (VarExpC x)), [
				EvalStmtC (ArrayIndexExpC(WC ei', VarExpC x, RawIndexC (VarExpC "__i")));
				AssignStmtC("__i", BinExpC("xadd", VarExpC "__i", ConstExpC (i_const 1)))
			])
		] in Valid (NewArrayExpC(List.map fst dt_l', [], tau_f), LT (ArrayTy(i, tau_f)), b)
	| _ -> let* (e', tau) = tc_exp env e in Valid (e', tau, [])

	(* guard reader *)

let var_ctor_list (env: type_env) (x: string): string list =
	let vcl_aux tx =
		let td = (match Hashtbl.find_opt env.globalTIds tx with
			Some (_, TcTDef td) -> td
			| _ -> failwith "BUG: tc_exp.ml - Attempted to read constructor list for non-existent type definition."
		) in (match td with
			EnumTD cl -> List.map (fun (_, cx, _) -> cr cx) cl
			| UnionTD ul -> List.map (fun (_, cx, _, _) -> cr cx) ul
			| _ -> print_string tx; failwith "BUG: tc_exp.ml - Attempted to read constructor list for non-enum/union variable."
		)
	in match tc_simple_var env x with
	NamedTy(tx, _) -> vcl_aux (cr tx)
	| TagOfTy tx -> vcl_aux (cr tx)
	| _ -> failwith "BUG: tc_exp.ml - Attempted to read constructor list for non-enum/union variable."

let rec read_guard_exp (env: type_env) (e: gen_exp): guard_map = match e with
	BinExpC("ptr_eq", VarExpC x, ConstExpC NullConst) ->
		new_guard_map x (null_guard_set true)
	| BinExpC("ptr_neq", VarExpC x, ConstExpC NullConst) ->
		new_guard_map x (null_guard_set false)
	(*| BinExpC("tag_eq", VarExpC x, EnumExpC y) ->
		new_guard_map x (new_guard_set y (var_ctor_list env x))
	| BinExpC("tag_eq", MemoryFieldExpC(_, VarExpC x, None), EnumExpC y) ->
		new_guard_map x (new_guard_set y (var_ctor_list env x))*)
	| UnaryExpC("bnot", ev) -> neg_read_guard_exp env ev
	| BinExpC("band", e1, e2) ->
		conj_guard_map (read_guard_exp env e1) (read_guard_exp env e2)
	| BinExpC("bor", e1, e2) ->
		disj_guard_map (read_guard_exp env e1) (read_guard_exp env e2)
	| _ -> StringMap.empty
	(*
		- this is not as simple as negating the guard set normally,
			because of how unrelated propositions work within this
	*)
and neg_read_guard_exp (env: type_env) (e: gen_exp): guard_map = match e with
	BinExpC("ptr_eq", VarExpC x, ConstExpC NullConst) ->
		new_guard_map x (null_guard_set false)
	| BinExpC("ptr_neq", VarExpC x, ConstExpC NullConst) ->
		new_guard_map x (null_guard_set true)
	| UnaryExpC("bnot", ev) -> read_guard_exp env ev
	| BinExpC("band", e1, e2) ->
		disj_guard_map (neg_read_guard_exp env e1) (neg_read_guard_exp env e2)
	| BinExpC("bor", e1, e2) ->
		conj_guard_map (neg_read_guard_exp env e1) (neg_read_guard_exp env e2)
	| _ -> StringMap.empty

let update_guard_map (env: type_env) (guardMap: guard_map) (x: string) (tau: lhs_type): guard_map =
	StringMap.update x (fun _ -> guard_set_of_type env tau) guardMap

	(* pattern type-checking *)

let tc_update_env (cont: fun_cont) (env: type_env) (x: string) (tau: g_type) (e: gen_exp): (gen_exp * type_env) =
	let e' = if cont.lf = Lin && is_heap_type env tau then GCNewRootExpC e else e in
	(e', { env with localIds = StringMap.add x tau env.localIds })

let temp_bind_pat (cont: fun_cont) (env: type_env) (px: pat) (e: gen_exp) (tau_v: g_type): (type_env * string option * gen_stmt) = match px with
	VarPat x ->
		let (e', env') = tc_update_env cont env x tau_v e in
		(env', Some x, VarStmtC(x, e', tau_v))
	| ListPat _ -> (env, None, VarStmtC("__pat", e, tau_v))
	| EmptyPat -> failwith "BUG: tc_exp.ml - Allowed empty pattern outside of match statement."
	| NullListPat -> failwith "BUG: tc_exp.ml - Allowed null tuple pattern outside of match statement."
(*
let tc_unpack_tuple_type (env: type_env) (tag_o: string option) (tau_v: g_type): (g_type list) tc_res = match tau_v with
	TupleTy(_, tau_l) -> Valid tau_l
	| NamedTy(cx, tau_al) -> (match Hashtbl.find_opt env.globalTIds (cr x) with
		Some (_, TcTDef(UnionTD cl)) ->
		| Some _ ->
		| None ->
	)*)

let tc_unpack_pat (cont: fun_cont) (env: type_env) (yo: string option) (px: pat) (tau_v: g_type) (p: l_pos): (type_env * gen_stmt list) tc_res = match px with
	EmptyPat -> Valid (env, [])
	| VarPat x -> (match yo with
		Some _ -> Valid (env, [])
		| None ->
			let (e', env') = tc_update_env cont env x tau_v (VarExpC "__pat") in
			Valid (env', [VarStmtC(x, e', tau_v)])
	)
	| ListPat(_, xol) ->
			(* extract tuple type *)
		let* tau_vl = (match tau_v with
			TupleTy(_, tau_l) ->
				if List.length tau_l <> List.length xol then
					Error (MismatchedPatNum_Err(List.length tau_l, List.length xol, p))
				else Valid tau_l
			| _ -> Error (NonTuplePat_Err(tau_v, p))
		) in
			(* bind to variables *)
		let (envX, b', _) = List.fold_left (fun (env', b', i) xo -> match xo with
			None -> (env', b', i + 1)
			| Some x ->
				let tau_v = List.nth tau_vl i in
				let e = MemoryFieldExpC(rc_of_type env' tau_v, VarExpC "__pat", Some i) in
				let (e', envX) = tc_update_env cont env' x tau_v e in
				(envX, b' @ [VarStmtC(x, e', tau_v)], i + 1)
		) (env, [], 0) xol in
		Valid (envX, b')
	| NullListPat -> Valid (env, [])

	(*
		takes pattern, returns expression needed to check pattern
		- needs the actual type to write the comparisons
	*)

let tc_cond_pat (env: type_env) (px: pat) (tau_v: g_type) (p: l_pos): (gen_exp option) tc_res = match px with
	EmptyPat -> Valid None
	| VarPat _ -> Valid None
	| ListPat(None, _) -> (match tau_v with
		TupleTy(zf, _) ->
			if zf then
				let e1 = MemoryFieldExpC(RC(None, tau_v), VarExpC "__pat", Some 0) in
				Valid (Some (BinExpC("ptr_neq", e1, ConstExpC NullConst)))
			else Valid None
		| _ -> Error (NonTuplePat_Err(tau_v, p))
	)
	| ListPat(Some tag, _) ->
			(* - we are given the type, so we can lookup the tag directly (which never requires disambiguation) *)
		let* (_, ucl) = (match lookup_union_cases env tau_v with
			Some ucl -> Valid ucl
			| None -> Error (NonTagTuple_Err(tau_v, p))
		) in
		let* cx = (match List.find_opt (fun (x, _, _, _) -> x = tag) ucl with
			Some (_, cx, _, _) -> Valid cx
			| None -> Error (BadTag_Err(tau_v, tag, p))
		) in
		let e1 = MemoryFieldExpC(RC(None, tau_v), VarExpC "__pat", Some 0) in
		Valid (Some (BinExpC("tag_eq", e1, EnumExpC (cr cx))))
	| NullListPat ->
		let e1 = MemoryFieldExpC(RC(None, tau_v), VarExpC "__pat", Some 0) in
		Valid (Some (BinExpC("ptr_eq", e1, ConstExpC NullConst)))

	(* statement type-checking *)

let rec tc_stmt (cont: fun_cont) (env: type_env) (s: r_stmt) (tau_r: g_type): (type_env * gen_stmt list * bool) tc_res = match s with
	EvalStmt(e, _) ->
		let* (e', t) = tc_exp env e in
		if t = LT BotTy then Valid (env, [EvalStmtC e'; UnreachableStmtC], true)
		else Valid (env, [EvalStmtC e'], false)
	| AssignStmt(x, e, p) ->
		let* (e', tau) = tc_exp env e in
		let tau_x = tc_simple_var env (cr x) in
		let* _ = tc_simp_subtype (AssignTCInfo(cr x, tau_x)) tau tau_x p in 
		let env' = { env with guardMap = update_guard_map env env.guardMap (cr x) tau } in
		Valid (env', [AssignStmtC(cr x, e')], false)
	| ReturnStmt(eo, p) -> (match eo with
		None ->
			if not (simp_subtype (LT unitTy) tau_r) then Error (BadReturn_Err(LT unitTy, tau_r, p))
			else Valid (env, [ReturnStmtC None], true)
		| Some e ->
			let* (e', t) = tc_exp env e in
			if not (simp_subtype t tau_r) then Error (BadReturn_Err(t, tau_r, p))
			else Valid (env, [ReturnStmtC (Some e')], true)
	)
	| PatStmt(px, e, p) -> 
		let* (e', tau_e, b) = (match px with
			VarPat x -> tc_extra_exp env e x
			| _ -> let* (e', tau_e) = tc_exp env e in Valid (e', tau_e, [])
		) in
		let* tau_x = complete_type tau_e p in
		let (env', x_temp, s) = temp_bind_pat cont env px e' tau_x in
		let* (env'', b') = tc_unpack_pat cont env' x_temp px tau_x p in
		Valid (env'', s :: b @ b', false)
	(*(match px with
		VarPat x ->
			let* (e', tau_e, b) = tc_extra_exp env e x in
			let* tau_x = complete_type tau_e p in
			let ef = if cont.lf = Lin && is_heap_type env tau_x then GCNewRootExpC e' else e' in
			let env' = {
				env with localIds = StringMap.add x tau_x env.localIds
				(*; guardMap = update_guard_map env env.guardMap x tau_e*)
			} in
			Valid (env', (VarStmtC(x, ef, tau_x)) :: b, false)
			(* TODO: allow a tuple to be used as a GC root *)
		| ListPat xol ->
			let* (e', tau_e) = tc_exp env e in
			let* tau_x = complete_type tau_e p in
			let* tau_vl = (match tau_x with
				TupleTy(_, tau_l) ->
					if List.length tau_l <> List.length xol then
						Error (MismatchedPatNum_Err(List.length tau_l, List.length xol, p))
					else Valid tau_l
				| _ -> Error (NonTuplePat_Err(tau_x, p))
			) in (*let dt = TypeDeref tau_e in*)
			let (envX, b, _) = List.fold_left (fun (env', b, i) xo -> match xo with
				None -> (env', b, i + 1)
				| Some x ->
					let tau_v = List.nth tau_vl i in
					let envX = {
						env' with localIds = StringMap.add x tau_v env'.localIds;
						guardMap = update_guard_map env env.guardMap x (LT tau_v)
					} in
					(envX, b @ [VarStmtC(x, MemoryFieldExpC(rc_of_type env' tau_v, VarExpC "__pat", Some i), tau_v)], i + 1)
			) (env, [], 0) xol in
			Valid (envX, (VarStmtC("__pat", e', tau_x)) :: b, false)
	)*)
	| IfStmt(ec, b1, b2, _) ->
		let* (ec', _) = tc_exp env ec in
		let gc = read_guard_exp env ec' in
		let ngc = neg_read_guard_exp env ec' in
		let env1 = { env with guardMap = conj_guard_map gc env.guardMap } in
		let* (env1', b1', term1) = tc_body (nonLinCont cont) env1 b1 tau_r in
		let env2 = { env with guardMap = conj_guard_map ngc env.guardMap } in
		let* (env2', b2', term2) = tc_body (nonLinCont cont) env2 b2 tau_r in
			(* if either branch is terminating, we can use the other branch's guard *)
		let envF =
			if term1 && term2 then { env with guardMap = conj_guard_map env1'.guardMap env2.guardMap }
			else if term1 then env2' else if term2 then env1' else env in  
		Valid (envF, [IfStmtC(ec', b1', term1, b2', term2)], term1 && term2)
	| WhileStmt(ec, b, _) ->
		let* (ec', _) = tc_exp env ec in
		let gc = read_guard_exp env ec' in
		let ngc = neg_read_guard_exp env ec' in
		let envY = { env with guardMap = conj_guard_map gc env.guardMap } in
		let* (_, b', _) = tc_body (nonLinCont cont) envY b tau_r in
		let envN = { env with guardMap = conj_guard_map ngc env.guardMap } in
		Valid (envN, [WhileStmtC(ec', b')], false)
	| ForStmt(x, rt, e, b, _) ->
		let* (e', _) = tc_exp env e in
		let* (tau_x, cmp, _) = (match rt with
			LtRange -> Valid (intTy, "ilt", false)
			| LeqRange -> Valid (intTy, "ileq", false)
			| ListRange -> failwith "UNIMPLEMENTED: tc_exp.ml - List case for for loop."
			(*| ListRange -> (match tau_e with
				ArrayTy(_, tau_a) -> Valid (tau_a, "ilt", true)
				| _ -> Error (NonArrayType_Err(simplify_type tau_e, p))
			)*)
		) in let env' = { env with localIds = StringMap.add x tau_x env.localIds } in
			(* for loop header:  _iterator, conditional depending on list case *)
		let (i', end') = (x, e') (*if list_flag then ("__i", LengthExpC e') else (x, e') *) in
		let x' = VarExpC i' in
		let cond' = BinExpC(cmp, x', end') in
			(* for loop body: body; _iterator = _iterator + 1 *)
		let* (_, b', _) = tc_body (nonLinCont cont) env' b tau_r in
		let b'' = b' @ [AssignStmtC(i', BinExpC("xadd", x', ConstExpC (i_const 1)))] in
			(* for loop body: prefix with x = e[_iterator] for list case *)
		(*let bf' = if list_flag then AssignStmtC(i', ArrayIndexExpC(e', [x'], tau_x)) :: b'' else b'' in*)
		Valid (env, [VarStmtC(i', ConstExpC (i_const 0), intTy); WhileStmtC(cond', b'')], false)
	| MatchStmt(e, mcl, p) ->
		let* (e', tau_e) = tc_exp env e in
		let* tau_v = complete_type tau_e p in
		let* (b', term) = tc_match_case_list cont env tau_v mcl tau_r in
		Valid (env, (VarStmtC("__pat", e', approxGenType tau_e)) :: b', term)
	| GCCollectStmt _ -> Valid (env, [GCCollectStmtC], false)
and tc_body (cont: fun_cont) (env: type_env) (b: r_stmt list) (tau_r: g_type): (type_env * gen_stmt list * bool) tc_res = match b with
	[] -> Valid (env, [], false)
	| s :: st ->
		let* (env2, s', term0) = tc_stmt cont env s tau_r in (match st with
			[] -> Valid (env2, s', term0)
			| _ ->
				if term0 then Error (EarlyReturn_Err (cont.f, ann_stmt s))
				else let* (env3, st', termX) = tc_body cont env2 st tau_r in Valid (env3, s' @ st', termX)
		)
and tc_match_case_list (cont: fun_cont) (env: type_env) (tau_v: g_type) (mcl: rm_case list) (tau_r: g_type): (gen_stmt list * bool) tc_res = match mcl with
	[] -> failwith "BUG: tc_exp.ml - Match with no cases encountered."
	| [mc] ->
		let* (_, b', term) = tc_match_case cont env tau_v mc tau_r in
		Valid (b', term)
	| mc :: mct ->
		let MCase(_, _, p) = mc in
		let* (ec_o', b1', term1) = tc_match_case cont env tau_v mc tau_r in
		let* ec' = (match ec_o' with
			None -> Error (EarlyEndMatch_Err p)
			| Some ec' -> Valid ec'
		) in
		let* (b2', term2) = tc_match_case_list cont env tau_v mct tau_r in
		Valid ([IfStmtC(ec', b1', term1, b2', term2)], term1 && term2)
and tc_match_case (cont: fun_cont) (env: type_env) (tau_v: g_type) (MCase(px, b, p): rm_case) (tau_r: g_type): (gen_exp option * gen_stmt list * bool) tc_res =
	let* ec' = tc_cond_pat env px tau_v p in
	let* (env', b1) = tc_unpack_pat cont env None px tau_v p in
	let* (_, b2, term) = tc_body cont env' b tau_r in
	Valid (ec', b1 @ b2, term)

	(* declaration / sectional type-checking *)

let rec add_param_list (env: type_env) (pl: (string * g_type) list): type_env = match pl with
	[] -> env
	| (x, tau) :: pt ->
		add_param_list { env with localIds = StringMap.add x tau env.localIds } pt

let tc_dec (env: type_env) (d: r_dec): ((string * gen_dec) list) tc_res = match d with
	FunDec(Method(lf, f, pl, tau_r, b), p) ->
		let tau_pl = List.map (fun (_, tau) -> tau) pl in
			(* uses non-type-canon function name (to allow for overloads on lookup) *)
		add_fun_tenv env f (UserDefSym, (tau_pl, tau_r));
		let localEnv = add_param_list env pl in
			(* use canon name for error messages + final declaration *)
		let fName = "_" ^ (tag_of_type (hd_opt tau_pl)) ^ (cr f) in
		let* (_, b', term) = tc_body { f = fName; lf = lf; } localEnv b tau_r in
		if not term then (
			if tau_r <> unitTy then Error (NoReturn_Err(fName, p))
			else Valid [(fName, FunDecC (MethodC(pl, tau_r, b' @ [ReturnStmtC None])))]
		) else Valid [(fName, FunDecC (MethodC(pl, tau_r, b')))]
	| TDefDec(x, td, _) -> add_tdef_tenv env x td; Valid [(cr x, TDefDecC td)]
	(*| ExtendsDec(_, _, _, _) -> Valid []*)
	| AttrsDec(tx, fl, cl, p) ->
			(* add attributes to type environment *)
		Hashtbl.add env.globalAttrs (cr tx) (
			Hashtbl.of_seq (List.to_seq fl)
		);
			(* check that each case has the right number of attributes *)
		let total = List.length fl in
		let* _ = map_try_res (fun (_, ctor, el) ->
			if List.length el <> total then
				Error (MismatchedAttrNum_Err(cr ctor, List.length el, total, p))
			else Valid ()
		) cl in
			(* make each attribute constant *)
		map_try_resi (fun (fx, tau) ix ->
			let* el' = map_try_res (fun (_, _, el) ->
				let* (e', tau_e) = tc_exp env (List.nth el ix) in
				let* _ = tc_subtype (new_sol ()) (FieldTCInfo(cr tx, fx, tau)) tau_e tau p in
				calc_exp env p e'
			) cl in
			let ea = ConstArrayExpC([List.length cl], el', tau) in
			let f = attrConstName tx fx in
			Valid (f, ConstDecC ea)
		) fl
	| ConstDec(x, e, p) ->
		let* (e', tau) = tc_exp env e in
		let* tau_f = complete_type tau p in
		let* ef = calc_exp env p e' in
		Hashtbl.add env.globalIds (cr x) (x, tau_f, Some ef);
		Valid [(cr x, ConstDecC ef)]
	| GlobalsDec(x, c, fl, p) ->
		let* fl' = map_try_res (fun (f, e) ->
			let* (e', tau) = tc_exp env e in
			let* tau_f = complete_type tau p in
			(*let gName = x ^ "_" ^ f in*)
			Hashtbl.add env.globalIds (cr f) (f, tau_f, None);
			Valid (cr f, e', tau_f)
		) fl in
		let sl = List.map (fun (x, e', tau) ->
			let e_gc = if is_heap_type env tau then GCNewRootExpC e' else e' in
			AssignStmtC(x, e_gc)
		) fl' in
		let iDec =
			if c = None then [("", InitDecC sl)]
			else
				let m = MethodC([], unitTy, sl @ [ReturnStmtC None]) in
				[("init" ^ (cr x), FunDecC m)]
		in Valid ((List.map (fun (x, _, tau) -> (x, GlobalDecC tau)) fl') @ iDec)

let tc_section (env: type_env) (SectionR dl: r_section): ((string * gen_dec) list) tc_res =
	let rec tcs_rec dl = match dl with
		[] -> Valid []
		| d :: dt ->
			let* d' = tc_dec env d in
			let* dt' = tcs_rec dt in Valid (d' @ dt')
	in tcs_rec dl
