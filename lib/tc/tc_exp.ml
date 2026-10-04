open Commons.Try_log
open Builtin.Builtin_core
open Parser.Lex_token
open Parser.Dusk_type
open Parser.Dusk_ast
open Resolve.Res_cont
open Codegen.Fin_type
open Codegen.Fin_ast
open Tc_cont
open Tc_err
open Calc_exp
	
	(* type-checking basics *)

let is_boxed_type (env: type_env) (tau: g_type): bool = match tau with
	TupleTy _ -> true
	| NamedTy cx -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
		Some (_, TcTDef td) -> (match td with
			UnionTD _ -> true
			| _ -> false
		)
		| _ -> failwith "BUG: tc_exp.ml - Invalid type encountered while checking boxed type status."
	)
	| _ -> false

let is_heap_type (env: type_env) (tau: g_type): bool = match tau with
	NamedTy cx -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
		Some (_, TcTDef td) -> (match td with
			StructTD _ -> true
			| _ -> false
		)
		| _ -> failwith "BUG: tc_exp.ml - Invalid type encountered while checking heap type status."
	)
	| ArrayTy(_, _) -> true
	| _ -> false

let rc_of_type (env: type_env) (tau: g_type): gen_rw =
	if is_boxed_type env tau then RC(Some (get_box_id_tenv env), tau)
	else RC(None, tau)

let attrConstName (tx: canon_name) (x: string): string =
	"ATTR" ^ (cr tx) ^ "_" ^ x

	(* type-checking auxiliaries *)

type g_fun =
	UnaryGF of string
	| BinaryGF of string
	| InternalGF of string
	| TupleIndexGF of int
	| ArrayIndexGF of rw
	| ArrayLengthGF
	| ArrayDimsGF of int
	| ArrayAddGF
	| StructFieldGF of rw * int
	| CallGF
	| EnumRawGF
	| EnumAttrGF of canon_name * string

let rec index_type_list (tau_l: g_type list) (i: int): g_type option = match tau_l with
	[] -> None
	| tau :: tau_t -> if i = 0 then Some tau else index_type_list tau_t (i - 1)

let lookup_field_list (fl: (string * g_type) list) (x: string): (g_type * int) option =
	let rec lfl_rec fl i = match fl with
		[] -> None
		| (y, tau) :: ft -> if x = y then Some (tau, i) else lfl_rec ft (i + 1)
	in lfl_rec fl 0

	(* basic type checks *)

type tvar_env = (string, g_type) Hashtbl.t

let new_sol (): tvar_env = Hashtbl.create 10

let rec apply_sol (sol: tvar_env) (t: g_type): g_type = match t with
	TupleTy _tl -> TupleTy (List.map (apply_sol sol) _tl)
	| ArrayTy(i, t) -> ArrayTy(i, apply_sol sol t)
	| TagOfTy t -> TagOfTy (apply_sol sol t)
	| NullableTy t -> NullableTy (apply_sol sol t)
	| EmptyableTy t -> EmptyableTy (apply_sol sol t)
	| FunTy(t_pl, t_r) -> FunTy(List.map (apply_sol sol) t_pl, apply_sol sol t_r)
	| CPtrTy t -> CPtrTy (apply_sol sol t)
	| VarTy a -> (match Hashtbl.find_opt sol a with
		Some t -> t
		| _ -> failwith "BUG: tc_exp.ml - Failed lookup of variable type for return type."
	)
	| KindTy _ -> failwith "BUG: tc_exp.ml - Kind type found iun return type."
	| TagTupleTy _ -> failwith "BUG: tc_exp.ml - Tag tuple type found in return type."
	| BotTy | PrimTy _ | IntTy _ | NamedTy _ | NullTy -> t

let rec is_subtype (sol: tvar_env) (s: g_type) (t: g_type): bool = match (s, t) with
	(BotTy, _) -> true
	| (PrimTy s', PrimTy t') -> s' = t'
	| (IntTy(u', s'), IntTy(v', t')) -> u' = v' && s' = t'
	| (NamedTy s', NamedTy t') -> cr s' = cr t'
	| (TupleTy _sl, TupleTy _tl) ->
		if List.length _sl <> List.length _tl then false
		else List.for_all (fun (s, t) -> is_subtype sol s t) (List.combine _sl _tl)
	| (TagTupleTy(s', _), NamedTy t') -> cr s' = cr t'
	| (ArrayTy(i, s'), ArrayTy(j, t')) -> i = j && is_subtype sol s' t'
	| (TagOfTy s', TagOfTy t') -> is_subtype sol s' t'
	| (NullTy, NullTy) -> true
	| (NullTy, NullableTy _) -> true
	| (NullTy, CPtrTy _) -> true
	| (NullableTy s, NullableTy t) -> is_subtype sol s t
	| (s, NullableTy t) -> is_subtype sol s t
	| (EmptyableTy s, EmptyableTy t) -> is_subtype sol s t
	| (s, EmptyableTy t) -> is_subtype sol s t
	| (FunTy(s_pl, s_r), FunTy(t_pl, t_r)) ->
		(List.for_all (fun (s, t) -> is_subtype sol s t) (List.combine s_pl t_pl)) && (is_subtype sol s_r t_r)
	| (CPtrTy s', CPtrTy t') -> is_subtype sol s' t'
	| (VarTy _, _) -> failwith "BUG: tc_exp.ml - Variable type found in left-hand position."
	| (_, VarTy i) -> (match Hashtbl.find_opt sol i with
		None -> Hashtbl.add sol i s; true
		| Some t' -> is_subtype sol s t' 
	)
	| (KindTy _, KindTy _) -> true
	| (_, BotTy) | (_, PrimTy _) | (_, IntTy _) | (_, NamedTy _)
	| (_, TupleTy _) | (_, TagTupleTy _) | (_, ArrayTy _) | (_, TagOfTy _)
	| (_, NullTy) | (_, FunTy _) | (_, CPtrTy _) | (_, KindTy _) -> false

let tc_type (sol: tvar_env) (info: tc_info) (s: g_type) (t: g_type) (p: l_pos): unit tc_res =
	if is_subtype sol s t then Valid () else Error (BadType_Err(s, t, info, p))

let tc_type_list (sol: tvar_env) (info: tc_info_stub) (arg_l: (gen_exp * g_type) list) (_tl: g_type list) (p: l_pos): unit tc_res =
	if List.length arg_l <> List.length _tl then
		Error (MismatchedArgNum_Err(List.length arg_l, List.length _tl, index_stub info None, p))
	else let rec tctl_rec _al _tl ix = match (_al, _tl) with
		([], []) -> Valid ()
		| ((e, s) :: st, t :: tt) ->
			let* _ = tc_type sol (index_stub info (Some ix)) s t p in
			let* _ = (match (e, t) with
				(SizeExpC s', KindTy a) -> (match Hashtbl.find_opt sol a with
					None -> Hashtbl.add sol a s'; Valid ()
					| Some t' -> tc_type sol (index_stub info (Some ix)) s' t' p 
				)
				| (_, KindTy _) -> failwith "BUG: tc_exp.ml - Bad value for kind value in type-checking."
				| _ -> Valid ()
			) in tctl_rec st tt (ix + 1)
		| _ -> failwith "BUG: tc_exp.ml - Type-checking for mismatched arguments reached unexpected location."
	in tctl_rec arg_l _tl 0

	(* special type narrowing functions *)

let lookup_union_cases (env: type_env) (tau: g_type): (canon_name * (canon_name union_case) list) option = match tau with
	NamedTy tx -> (match Hashtbl.find_opt env.globalTIds (cr tx) with
		Some (_, TcTDef (UnionTD ul)) -> Some (tx, ul)
		| _ -> None
	)
	| _ -> None

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
	)

	(* expression type-checking *)

let tc_const (c: const): g_type = match c with
	IConst(_, u, s) -> IntTy(u, s)
	| FConst _ -> floatTy
	| SConst _ -> stringTy
	| BConst _ -> boolTy
	| NullConst -> NullTy

let stub_cn (x: string): canon_name = CN(x, [x])

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

let rec tc_exp (env: type_env) (e: r_exp): (gen_exp * g_type) tc_res = match e with
	ConstExp(c, _) -> Valid (ConstExpC c, tc_const c)
	| TConstExp(t, _) -> Valid (SizeExpC t, KindTy "A")
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
	| AtCtorExp(ctor, p) -> (match Hashtbl.find_opt env.globalTIds (cr ctor) with
			Some (_, TcCtorU c) -> Valid (EnumExpC (cr ctor), TagOfTy (NamedTy c))
			| _ -> Error (NonCtorU_Err(cr ctor, p))
		)
	| TupleExp(ctor, el, p) ->
		let* et_l' = tc_exp_list env el in (match ctor with
			None ->
				let tau_s = TupleTy(List.map snd et_l') in
				Valid (TupleExpC(get_box_id_tenv env, tau_s, List.map fst et_l'), tau_s)
			| Some cx -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
				Some (_, TcCtorE c) -> Valid (EnumExpC (cr cx), NamedTy c)
				| Some (_, TcCtorU c) ->
					let tau_s = NamedTy c in
					Valid (TupleExpC(get_box_id_tenv env, tau_s, (EnumExpC (cr cx)) :: List.map fst et_l'), tau_s)
				| Some (_, TcTDef (EnumTD _)) ->
					let (e', _) = List.hd et_l' in
					Valid (TagExpC e', NamedTy cx)
				| _ -> Error (NonCtor_Err(cr cx, p))
			)
		)
	| DataArrayExp(i, tau_o, dim_l, el, p) ->
		let* et_l' = tc_exp_list env el in
		let tau = (match tau_o with None -> snd (List.hd et_l') | Some tau -> tau) in
		let dim_prod = List.fold_left (fun i p -> i * p) 1 dim_l in
		if dim_prod <> List.length el then Error (MismatchedArrayDim_Err (dim_l, dim_prod, List.length el, p))
		else let dim_v = List.map (fun i -> ConstExpC (i_const i)) dim_l in
			Valid (NewArrayExpC(dim_v, List.map fst et_l', tau), ArrayTy(i, tau))
	| FormatArrayExp(_, _, _, p) -> Error (NestedFormat_Err p)
	| NewStructExp(cx, fl, p) ->
		let* ftl' = map_try_res (fun (x, e) -> let* (e', t) = tc_exp env e in Valid (x, e', t)) fl in
		let* el' = (match Hashtbl.find_opt env.globalTIds (cr cx) with
			Some (_, TcTDef (StructTD pl)) ->
				let sol = new_sol () in
				map_try_res (fun (x, tau_p) ->
					match List.find_opt (fun (y, _, _) -> x = y) ftl' with
						None -> Error (MissingField_Err(cr cx, x, FieldTCInfo(cr cx, x, tau_p), p))
						| Some (_, e', tau_a) ->
							let* _ = tc_type sol (FieldTCInfo(cr cx, x, tau_p)) tau_a tau_p p in Valid e' 
				) pl
			| Some _ -> Error (BadCtorStruct_Err(cr cx, p))
			| _ -> Error (NonCtor_Err(cr cx, p))
		) in Valid (NewStructExpC(cr cx, el'), NamedTy cx)
	| IsExp(e, None, p) ->
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
		Valid (BinExpC("tag_eq", ev, ec), boolTy)
	(*match Hashtbl.find_opt env.globalIds f with
		Some (_, tau, _) -> (
		)
		| _ -> failwith "BUG: tc_exp.ml - Failed function variable lookup during type-checking phase."
	*)
	| AppExp(ef, el, p) ->
		let* et_l' = tc_exp_list env el in
		let tau_al = List.map snd et_l' in
		let el' = List.map fst et_l' in
		let* (fRaw, d, (tau_pl, _tau_rn)) = tc_fun_exp env ef (hd_opt tau_al) in
		try let sol = new_sol () in
			let* _ = tc_type_list sol (CallTCInfoStub(fRaw, tau_pl, _tau_rn)) et_l' tau_pl p in
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
		with Invalid_argument _ -> failwith "BUG: tc_exp.ml - Unknown operator OOB exception." 
and tc_fun_exp (env: type_env) (ef: r_exp) (tau_a: g_type option): (string * g_fun * canon_name fun_type) tc_res = match ef with
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
	| OpExp(TupleIndexOp i, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for tuple index operation."
		| Some (TupleTy tau_l) -> (match index_type_list tau_l (i - 1) with
			None -> Error (TupleIndexOOB_Err(TupleTy tau_l, i, p))
			| Some tau_i ->	Valid ("", TupleIndexGF (i - 1), ([TupleTy tau_l], tau_i))
		)
		| Some (TagTupleTy(tx, tau_l)) -> (match index_type_list tau_l (i - 1) with
			None -> Error (TupleIndexOOB_Err(NamedTy tx, i, p))
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
		| Some (NamedTy cx) -> (match Hashtbl.find_opt env.globalTIds (cr cx) with
				(* check field *)
			Some (_, TcTDef (StructTD fl)) -> (match lookup_field_list fl x with
				None -> Error (BadField_Err(cr cx, x, p))
				| Some (tau, i) ->
					(* read / write case *)
					let (tau_args, tau_r) =
						if rw = RR then ([NamedTy cx], tau)
						else ([NamedTy cx; tau], unitTy)
					in Valid ("", StructFieldGF(rw, i), (tau_args, tau_r))
			)
			| Some (_, TcTDef (EnumTD _)) -> (match Hashtbl.find_opt env.globalAttrs (cr cx) with
				None -> Error (NonStruct_Err(NamedTy cx, p))
				| Some attrs -> (match Hashtbl.find_opt attrs x with
					None -> Error (BadAttr_Err(cr cx, x, p))
					| Some tau -> Valid ("", EnumAttrGF(cx, x), ([NamedTy cx], tau))
				)
			)
			| _ -> Error (NonStruct_Err(NamedTy cx, p))
		)
		| Some tau -> Error (NonStruct_Err(tau, p))
	)
	| OpExp(MeasureOp, p) -> (match tau_a with
		None -> failwith "BUG: tc_exp.ml - No argument for measure operation."
		| Some (ArrayTy(i, tau_v)) ->
			if i = 1 then Valid ("", ArrayLengthGF, ([ArrayTy(i, tau_v)], intTy))
			else Valid ("", ArrayDimsGF i, ([ArrayTy(i, tau_v)], TupleTy (List.init i (fun _ -> intTy))))
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
		| Some (NamedTy cx) ->
			let tau = NamedTy cx in
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
		| Some (NamedTy cx) ->
			let tau = NamedTy cx in
			(match Hashtbl.find_opt env.globalTIds (cr cx) with
				Some (_, TcTDef (EnumTD _)) -> Valid ("", EnumRawGF, ([tau], intTy))
				| _ -> Error (NonEnum_Err(tau, p))
			)
		| Some (TagTupleTy _) ->
			failwith "UNIMPLEMENTED: tc_exp.ml - Tag operation on narrowed union type."
		| Some tau -> Error (NonEnum_Err(tau, p))
	)
	| _ -> failwith "UNIMPLEMENTED: tc_exp.ml - function non-var case."
and tc_exp_list (env: type_env) (el: r_exp list): ((gen_exp * g_type) list) tc_res = match el with
	[] -> Valid []
	| e :: et ->
		let* res = tc_exp env e in
		let* res_t = tc_exp_list env et in Valid (res :: res_t)

let tc_extra_exp (env: type_env) (e: r_exp) (x: string): (gen_exp * g_type * gen_stmt list) tc_res = match e with
	FormatArrayExp(i, dim_l, e, _) ->
		let* dt_l' = tc_exp_list env dim_l in
		let* (e', tau) = tc_exp env e in
		let b = [
			VarStmtC("__i", ConstExpC (i_const 0), intTy);
			WhileStmtC(BinExpC("ilt", VarExpC "__i", ArrayLengthExpC (VarExpC x)), [
				EvalStmtC (ArrayIndexExpC(WC e', VarExpC x, RawIndexC (VarExpC "__i")));
				AssignStmtC("__i", BinExpC("xadd", VarExpC "__i", ConstExpC (i_const 1)))
			])
		] in Valid (NewArrayExpC(List.map fst dt_l', [], tau), ArrayTy(i, tau), b)
	| _ -> let* (e', tau) = tc_exp env e in Valid (e', tau, [])

	(* guard reader *)

let var_ctor_list (env: type_env) (x: string): string list =
	let vcl_aux tx =
		let td = (match Hashtbl.find_opt env.globalTIds tx with
			Some (_, TcTDef td) -> td
			| _ -> failwith "BUG: tc_exp.ml - Attempted to read constructor list for non-existent type definition."
		) in (match td with
			EnumTD cl -> List.map (fun (cx, _) -> cr cx) cl
			| UnionTD ul -> List.map (fun (cx, _, _) -> cr cx) ul
			| _ -> print_string tx; failwith "BUG: tc_exp.ml - Attempted to read constructor list for non-enum/union variable."
		)
	in match tc_simple_var env x with
	NamedTy tx -> vcl_aux (cr tx)
	| TagOfTy (NamedTy tx) -> vcl_aux (cr tx)
	| _ -> failwith "BUG: tc_exp.ml - Attempted to read constructor list for non-enum/union variable."

let rec read_guard_exp (env: type_env) (e: gen_exp): guard_map = match e with
	BinExpC("ptr_eq", VarExpC x, ConstExpC NullConst) ->
		new_guard_map x null_guard_set
	| BinExpC("tag_eq", VarExpC x, EnumExpC y) ->
		new_guard_map x (new_guard_set y (var_ctor_list env x))
	| BinExpC("tag_eq", MemoryFieldExpC(_, VarExpC x, None), EnumExpC y) ->
		new_guard_map x (new_guard_set y (var_ctor_list env x))
	| UnaryExpC("bnot", ev) ->
		neg_guard_map (read_guard_exp env ev)
	| BinExpC("band", e1, e2) ->
		conj_guard_map (read_guard_exp env e1) (read_guard_exp env e2)
	| BinExpC("bor", e1, e2) ->
		disj_guard_map (read_guard_exp env e1) (read_guard_exp env e2)
	| _ -> StringMap.empty

	(* statement type-checking *)

let rec tc_stmt (cont: fun_cont) (env: type_env) (s: r_stmt) (tau_r: g_type): (type_env * gen_stmt list * bool) tc_res = match s with
	EvalStmt(e, _) ->
		let* (e', t) = tc_exp env e in
		if t = BotTy then Valid (env, [EvalStmtC e'; UnreachableStmtC], true)
		else Valid (env, [EvalStmtC e'], false)
	| AssignStmt(x, e, p) ->
		let* (e', tau) = tc_exp env e in
		let tau_x = tc_simple_var env (cr x) in
		let* _ = tc_type (new_sol ()) (AssignTCInfo(cr x, tau_x)) tau tau_x p in 
		let env' = { env with guardMap = StringMap.update (cr x) (fun _ -> None) env.guardMap } in
		Valid (env', [AssignStmtC(cr x, e')], false)
	| ReturnStmt(eo, p) -> (match eo with
		None ->
			if not (is_subtype (new_sol ()) unitTy tau_r) then Error (BadReturn_Err(unitTy, tau_r, p))
			else Valid (env, [ReturnStmtC None], true)
		| Some e ->
			let* (e', t) = tc_exp env e in
			if not (is_subtype (new_sol ()) t tau_r) then Error (BadReturn_Err(t, tau_r, p))
			else Valid (env, [ReturnStmtC (Some e')], true)
	)
	| PatStmt(px, e, p) -> (match px with
		VarPat x ->
			let* (e', tau_e, b) = tc_extra_exp env e x in
			let ef = if cont.lf = Lin && is_heap_type env tau_e then GCNewRootExpC e' else e' in
			Valid ({ env with localIds = StringMap.add x tau_e env.localIds }, (VarStmtC(x, ef, tau_e)) :: b, false)
			(* TODO: allow a tuple to be used as a GC root *)
		| ListPat xol ->
			let* (e', tau_e) = tc_exp env e in
			let* tau_vl = (match tau_e with
				TupleTy tau_l ->
					if List.length tau_l <> List.length xol then
						Error (MismatchedPatNum_Err(List.length tau_l, List.length xol, p))
					else Valid tau_l
				| _ -> Error (NonTuplePat_Err(tau_e, p))
			) in (*let dt = TypeDeref tau_e in*)
			let (envX, b, _) = List.fold_left (fun (env', b, i) xo -> match xo with
				None -> (env', b, i + 1)
				| Some x ->
					let tau_v = List.nth tau_vl i in
					({ env' with localIds = StringMap.add x tau_v env'.localIds },
						b @ [VarStmtC(x, MemoryFieldExpC(rc_of_type env' tau_v, VarExpC "__pat", Some i), tau_v)], i + 1)
			) (env, [], 0) xol in
			Valid (envX, (VarStmtC("__pat", e', tau_e)) :: b, false)
	)
	| IfStmt(ec, b1, b2, _) ->
		let* (ec', _) = tc_exp env ec in
		let gc = read_guard_exp env ec' in
		let env1 = { env with guardMap = conj_guard_map gc env.guardMap } in
		let* (env1', b1', term1) = tc_body (nonLinCont cont) env1 b1 tau_r in
		let env2 = { env with guardMap = conj_guard_map (neg_guard_map gc) env.guardMap } in
		let* (env2', b2', term2) = tc_body (nonLinCont cont) env2 b2 tau_r in
			(* if either branch is terminating, we can use the other branch's guard *)
		let envF =
			if term1 && term2 then { env with guardMap = conj_guard_map env1'.guardMap env2.guardMap }
			else if term1 then env2' else if term2 then env1' else env in  
		Valid (envF, [IfStmtC(ec', b1', term1, b2', term2)], term1 && term2)
	| WhileStmt(ec, b, _) ->
		let* (ec', _) = tc_exp env ec in
		let gc = read_guard_exp env ec' in
		let envY = { env with guardMap = conj_guard_map gc env.guardMap } in
		let* (_, b', _) = tc_body (nonLinCont cont) envY b tau_r in
		let envN = { env with guardMap = conj_guard_map (neg_guard_map gc) env.guardMap } in
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
		let* _ = map_try_res (fun (ctor, el) ->
			if List.length el <> total then
				Error (MismatchedAttrNum_Err(cr ctor, List.length el, total, p))
			else Valid ()
		) cl in
			(* make each attribute constant *)
		map_try_resi (fun (fx, tau) ix ->
			let* el' = map_try_res (fun (_, el) ->
				let* (e', tau_e) = tc_exp env (List.nth el ix) in
				let* _ = tc_type (new_sol ()) (FieldTCInfo(cr tx, fx, tau)) tau_e tau p in
				calc_exp env p e'
			) cl in
			let ea = ConstArrayExpC([List.length cl], el', tau) in
			let f = attrConstName tx fx in
			Valid (f, ConstDecC ea)
		) fl
	| ConstDec(x, e, p) ->
		let* (e', tau) = tc_exp env e in
		let* ef = calc_exp env p e' in
		Hashtbl.add env.globalIds (cr x) (x, tau, Some ef);
		Valid [(cr x, ConstDecC ef)]
	| GlobalsDec(x, c, fl, _) ->
		let* fl' = map_try_res (fun (f, e) ->
			let* (e', tau) = tc_exp env e in
			(*let gName = x ^ "_" ^ f in*)
			Hashtbl.add env.globalIds (cr f) (f, tau, None);
			Valid (cr f, e', tau)
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
