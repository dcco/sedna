open Commons.Try_log
open Commons.Tree_map
open Parser.Lex_token
open Parser.Dusk_type
open Builtin.Builtin_core
open Codegen.Fin_type
open Res_cont

	(*
		type resolution
	*)

let rec resolve_type (env: res_env) (p: l_pos) (tau: m_type): g_type rs_res = match tau with
	PrimTy x -> Valid (PrimTy x)
	| IntTy(u, s) -> Valid (IntTy(u, s))
	| NamedTy(q, tau_l) ->
		let* x' = resolve_name env p q in
		let* tau_l' = map_try_res (resolve_type env p) tau_l in Valid (NamedTy(x', tau_l'))
	| TupleTy(zFlag, tau_l) -> let* tau_l' = map_try_res (resolve_type env p) tau_l in Valid (TupleTy(zFlag, tau_l'))
	| ArrayTy(i, tau) -> let* tau' = resolve_type env p tau in Valid (ArrayTy(i, tau'))
	| TagOfTy q -> let* x' = resolve_name env p q in Valid (TagOfTy x')
	| FunTy(tau_pl, tau_r) ->
		let* tau_pl' = map_try_res (resolve_type env p) tau_pl in
		let* tau_r' = resolve_type env p tau_r in Valid (FunTy(tau_pl', tau_r'))
	| NullableTy tau -> let* tau' = resolve_type env p tau in Valid (NullableTy tau')
	| TValTy tau -> let* tau' = resolve_type env p tau in Valid (TValTy tau')
	| BotTy -> Valid BotTy
	| VarTy i -> Valid (VarTy i)
	| CPtrTy tau -> let* tau' = resolve_type env p tau in Valid (CPtrTy tau')

let resolve_type_def (env: res_env) (p: l_pos) (td: m_tdef): g_tdef rs_res = match td with
	StructTD(xl, fl) ->
		let* fl' = map_try_res (fun (x, tau) ->
			let* tau' = resolve_type env p tau in Valid (x, tau')
		) fl in Valid (StructTD(xl, fl'))
	| EnumTD cl ->
		let* cl' = map_try_res (fun (cx, x, ext) ->
			let* x' = add_dec_renv env p LocalOr x in Valid (cx, x', ext)
		) cl in Valid (EnumTD cl')
	| UnionTD cl ->
		let* cl' = map_try_res (fun (cx, x, tau_l, ext) ->
			let* x' = add_dec_renv env p LocalOr x in
			let* tau_l' = map_try_res (resolve_type env p) tau_l in
			Valid (cx, x', tau_l', ext)
		) cl in Valid (UnionTD cl')
	| ExternTD -> Valid ExternTD

	(* 
		builtin resolution
	*)

let resolve_virt_dec (env: res_env) (p: l_pos) (vd: qual_name virt_dec): (canon_name virt_dec) rs_res = match vd with
	SymVD(s, (tau_pl, tau_r)) ->
		let* tau_pl' = map_try_res (resolve_type env p) tau_pl in
		let* tau_r' = resolve_type env p tau_r in Valid (SymVD(s, (tau_pl', tau_r')))
	| TDefVD td ->
		let* td' = resolve_type_def env p td in
		Valid (TDefVD td')

let resolve_virt_bindings (env: res_env) (l: string) (p: l_pos)
	(bindings: (string list * m_virt_bind) list): g_virt_bind list rs_res =
		(* add builtin symbols to environment + self with default import strategy *)
	let env' = freeze_env env [] in
	let pl = paths_tree !(env.globalModules) in
	let* _ = try map_try_res (fun path ->
		let i = List.length path - 1 in
		let libName = List.nth path 0 in
			if libName = "builtin" || libName = l then 
				add_import_renv env' p path (List.nth path i)
			else Valid ()
	) pl
	with Invalid_argument _ -> failwith "BUG: res_type.ml - Path without library name."
		(* canonize virtual declarations (especially types / typedefs) *)
	in map_try_res (fun (path, (b, vd, px)) ->
		let envX = { env' with curPath = path } in
		let x' = (match b with PrimBind x -> canonize_prim x | RawBind x -> canonize_scope path x) in
		let* vd' = resolve_virt_dec envX px vd in
		Valid (x', vd', px)
	) bindings
