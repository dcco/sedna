open Commons.Try_log
open Commons.Tree_map
open Builtin.Builtin_core
open Parser.Lex_token
open Parser.Dusk_type
open Parser.Dusk_ast
open Overload_env

module StringMap = Map.Make(String)

	(*
		output of resolution phase
	*)

type r_exp = (canon_name, l_pos) exp
type r_stmt = (canon_name, l_pos) stmt
type rm_case = (canon_name, l_pos) m_case
type r_met = (canon_name, l_pos) met
type r_dec = (canon_name, l_pos) dec

type r_section = SectionR of r_dec list

	(*
		resolution error types
	*)

type resolve_err =
	BadLookup_Err of qual_name * l_pos
	| AmbiguousLookup_Err of qual_name * canon_name list * l_pos
	| Redeclare_Err of qual_name * l_pos
	| AmbiguousOverload_Err of qual_name * canon_name list * l_pos
	| ReuseHandle_Err of string list * string * l_pos
	| NonEmptyReqList_Err of l_pos
	| BadReq_Err of string list * l_pos

type 'a rs_res = ('a, resolve_err) try_res

let string_of_qname (QN(prefix, x): qual_name): string = match prefix with
	None -> x
	| Some m -> m ^ "." ^ x

let string_of_rs_err (e: resolve_err): string = match e with
	BadLookup_Err(x, p) -> "Bad lookup of \"" ^ (string_of_qname x) ^ "\" at " ^ (string_of_pos p) ^ "."
	| AmbiguousLookup_Err(x, xl, p) ->
		"Ambiguous lookup of \"" ^ (string_of_qname x) ^ "\" at " ^ (string_of_pos p) ^ ". Options:\n --"
		^ (String.concat "\n --" (List.map cr xl))
	| Redeclare_Err(x, p) ->
		"Re-declaration of \"" ^ (string_of_qname x) ^ "\" at " ^ (string_of_pos p) ^ "."
	| AmbiguousOverload_Err(x, xl, p) ->
		"Ambiguous overload options for declaration \"" ^ (string_of_qname x) ^ "\" at " ^ (string_of_pos p) ^ ". Options:\n --"
		^ (String.concat "\n --" (List.map cr xl))
	| ReuseHandle_Err(path, x, p) ->
		"Re-use of handle \"" ^ x ^ "\" while importing \"" ^ (String.concat "." path) ^ "\" at " ^ (string_of_pos p) ^ "."
	| NonEmptyReqList_Err p -> "Requirement given outside of TOC / top-level at " ^ (string_of_pos p) ^ "."
	| BadReq_Err(xl, p) -> "Bad requirement \"" ^ (String.concat "." xl) ^ "\" at " ^ (string_of_pos p) ^ "."

	(*
		resolution environment
		* globalModules - maps module paths -> binding lists (bindings w/ module structure preserved)
		* importPrefixes - maps import prefixes -> full path names
		* importIds - (all) bindings imported locally to the module / declared at module level
		-- mapping includes import prefix + original name (applicable when aliased)
		* localIds - (values) bindings declared locally in a function
	*)

	(*
		res_binding - bindings as they are stored in the global module structure
		* sym - normal symbol binding
			(raw symbol, canon name)
		* global - list of symbols qualified as part of a global namespace
			(global handle, canon global name, raw symbol, canon name)
	*)

type res_binding =
	SymBind of string * canon_name
	| GlobalSymBind of string * canon_name * string * canon_name
(*

let only_true_local_handle ((ox, _): import_origin * 'a): bool =
	match ox with LocalOr -> true | _ -> false

*)
(*type bind_origin = PrimOr | LocalOr | ImportOr of string | GlobalOr of string * string*)

type res_env = {
	curPath: string list;
	globalModules: ((res_binding list) tree_map) ref;
	importHandles: (string, unit) Hashtbl.t; 
	importIds: overload_env; 
	localIds: unit StringMap.t;
}

	(* - TEST fun: used to dump *)

let dump_renv (env: res_env): unit =
	print_string "#RESOLUTION_ENV {\n";
	dump_tree (fun _ -> "< bindings >") !(env.globalModules);
	Hashtbl.iter (fun x l -> List.iter (fun (ox, _) -> match ox with
		LocalOr -> print_string ("local: " ^ x ^ "\n")
		| ImportOr o -> print_string ("import: " ^ o ^ " - " ^ x ^ "\n")
		| StrictOr(_, x) -> print_string ("global: " ^ x ^ "\n")
	) l) env.importIds;
	print_string "}\n";;

	(*
		canonization functions
	*)

let canonize_prim (x: string): canon_name = CN(x, [x])
let canonize_flocal (x: string): canon_name = canonize_prim x

let canonize_scope (scope: string list) (x: string): canon_name =
	let x' =
		if List.length scope = 0 then "_" ^ x
		else "_" ^ (String.concat "_" scope) ^ "_" ^ x
	in CN(x', scope @ [x])

let canonize_scope_ox (scope: string list) (_: 'a) (x: string): canon_name = canonize_scope scope x

let globalize_binding (env: res_env) (ox: import_origin) (x: string) (x': canon_name): res_binding list = match ox with
	LocalOr -> [SymBind(x, x')]
	| ImportOr _ -> []
	| StrictOr(localFlag, h) -> if localFlag then [GlobalSymBind(h, canonize_scope env.curPath h, x, x')] else []

(*
let canonize_binding (env: res_env) (ox: bind_origin) (x: string): string = match ox with
	PrimOr -> x
	| LocalOr -> canonize_scope env.curPath x
	| ImportOr handle -> (match Hashtbl.find_opt env.importPrefixes handle with
		None -> failwith "BUG: res_cont.ml - Attempted to lookup unknown import handle."
		| Some path -> canonize_scope path x
	)
	| GlobalOr(_, tName) -> tName ^ "_" ^ x

let origin_handle (ox: bind_origin): string option = match ox with
	ImportOr handle -> Some handle
	| GlobalOr(handle, _) -> Some handle
	| _ -> None*)

	(*
		resolution lookup
		- looks up qualified name, returns all canonization options
	*)
(*
let _lookup_renv (env: res_env) (QN(p, x): qual_name): (import_origin * canon_name) list = match p with
	Some prefix -> (match Hashtbl.find_opt env.importIds x with
		None -> []
		| Some xl -> List.filter (match_handle (Some prefix)) xl)
	| None -> (match Hashtbl.find_opt env.importIds x with
		None -> []
		| Some xl -> List.filter not_strict_handle xl)*)

let resolve_name (env: res_env) (p: l_pos) (q: qual_name): canon_name rs_res =
	let QN(prefix, x) = q in
	if prefix = None && StringMap.mem x env.localIds then Valid (canonize_flocal x)
	else match unique_overload_list (lookup_oenv_disambig env.importIds q) with
		[] -> Error (BadLookup_Err(q, p))
		| [x'] -> Valid x'
		| xl -> Error (AmbiguousLookup_Err(q, xl, p))

	(*match lookup_oenv env.importIds q with
		[] -> Error (BadLookup_Err(q, p))
		| [(_, x')] -> Valid x'
		| xl ->
			let xl' = List.filter only_local_handle xl in
			if List.length xl' = 0 then Error (AmbiguousLookup_Err(q, List.map snd xl, p))
			else if List.length xl' > 1 then Error (AmbiguousLookup_Err(q, List.map snd xl', p))
			else Valid (snd (List.hd xl'))*)

(*
let lookup_env (env: res_env) (p: qual_name) (x: string): (bind_origin * string) list = match p with
	QT (Some prefix) -> (match Hashtbl.find_opt env.importIds x with
		None -> []
		| Some xl -> List.filter (fun (ox, _) -> origin_handle ox = Some prefix) xl)
	| QT None -> if StringMap.mem x env.localIds then [(PrimOr, x)] else (match Hashtbl.find_opt env.importIds x with
		None -> []
		| Some xl -> xl)

let lookup_bind_dec_env (env: res_env) (ox: bind_origin) (x: string): string option =
	match Hashtbl.find_opt env.importIds x with
		None -> None
		| Some xl ->
			if List.exists (fun (b, _) -> b = ox) xl then
				Some (canonize_scope env.curPath x)
			else None
*)

	(* 
		resolution declaration functions
		- adds the bindings, returns canonical name
		- returns notice if the type is ambiguous
	*)

	(* - non-overload case: adds declaration to local module *)
let add_dec_renv (env: res_env) (p: l_pos) (ox: import_origin) (q: qual_name): canon_name rs_res =
	match add_oenv env.importIds (canonize_scope_ox env.curPath) ox q with
		None -> Error (Redeclare_Err(q, p))
		| Some x' -> Valid x'

(*	let QN(_, x) = q in
	let x' = canonize_scope env.curPath x in
	match Hashtbl.find_opt env.importIds x with
		None -> Hashtbl.add env.importIds x [(ox, x')]; Valid x'
		| Some xl -> (match List.filter (match_handle (origin_handle ox)) xl with
			[] -> Hashtbl.replace env.importIds x ((ox, x') :: xl); Valid x'
			| _ -> Error (Redeclare_Err(q, p))
		) 
*)

	(*
		- overload case: adds declaration to local module
			* if does not exist, add as normal
			* if does exist, overload pre-existing name
	*)

let add_dec_renv_ol (env: res_env) (p: l_pos) (q: qual_name): canon_name rs_res =
	match unique_overload_list (lookup_oenv_disambig env.importIds q) with
	[] -> (match add_oenv env.importIds (canonize_scope_ox env.curPath) LocalOr q with
		None -> failwith "BUG: res_cont.ml - Failed to add new bindings in spite of empty lookup."
		| Some x' -> Valid x')
	| [x'] ->
		let _ = (if not (has_local_oenv env.importIds q) then
			add_oenv env.importIds (fun _ _ -> x') LocalOr q
		else None) in Valid x'
	| xl -> Error (AmbiguousOverload_Err(q, xl, p))

	(*let QN(_, x) = q in
	let x' = canonize_scope env.curPath x in
	match Hashtbl.find_opt env.importIds x with
		None -> Hashtbl.add env.importIds x [(LocalOr, x')]; Valid x'
		| Some xl -> (match List.filter only_true_local_handle xl with
			[] -> (match extract_unique_names (List.map snd (List.filter not_strict_handle xl)) with
				[] -> failwith "BUG: res_cont.ml - Disambiguating over empty overload list."
				| [y] -> Valid y
				| xl' -> Error (AmbiguousOverload_Err(q, xl', p)) 
			)
			| _ -> Valid x' 
		)*)

(*let add_dec_renv_ol (env: res_env) (q: qual_name) (p: l_pos): canon_name rs_res = match _add_dec_renv_ol env q with
	[] -> 
		let x' = canonize_scope env.curPath x in
		Hashtbl.add env.importIds x [(LocalOr, x')]; Valid x'
	| [(ox, x')] -> (match ox with
		LocalOr | OverloadOr _ -> Valid x'
		| ImportOr h ->
			let QN(_, x) = q in
			let xl = Hashtbl.find env.importIds x in
			Hashtbl.replace env.importIds x ((ImportOr, ) :: xl) Valid x'
		| NewGlobalOr(_, _) -> failwith "BUG: res_cont.ml - Un-filtered global encountered while considering overloads."
	) 
	| xl ->
		(* if it's ambiguous, first we check whether it's because we already overloaded it *)
		Error (AmbiguousOverload_Err(q, List.map snd xl, p))*)

(*let add_dec_renv_ol (env: res_env) (q: qual_name): (canon_name * string) list =
	let QN(_, x) = q in
	let x' = canonize_scope env.curPath x in
	match Hashtbl.find_opt env.importIds x with
		None -> Hashtbl.add env.importIds x [(LocalOr, x')]; [(LocalOr, x')]
		| Some xl -> xl*)

	(*
		import functions
	*)

let valid_import_path_renv (env: res_env) (path: string list): bool =
	has_path_tree !(env.globalModules) path

let add_import_renv (env: res_env) (p: l_pos) (path: string list) (handle: string): unit rs_res =
		(* check whether handle already exists *)
	let* _ = (match Hashtbl.find_opt env.importHandles handle with
		None -> Hashtbl.add env.importHandles handle (); Valid ()
		| _ -> dump_renv env; Error (ReuseHandle_Err(path, handle, p))
	) in
		(* otherwise, iterate through all bindings and dump them in *)
	let symList = lookup_tree !(env.globalModules) path in
	List.iter (fun bind ->
		let (ox, x, x') = match bind with
			SymBind(x, x') -> (ImportOr handle, x, x')
			| GlobalSymBind(h, _, x, x') -> (ImportOr h, x, x')
		in let binding = (ox, x') in match Hashtbl.find_opt env.importIds x with
			None -> Hashtbl.add env.importIds x [binding]
			| Some l -> (match List.find_opt (fun (b, _) -> b = ox) l with
				None -> Hashtbl.replace env.importIds x (binding :: l)
				| _ -> ()
			)
	) symList; Valid ()

	(*
		resolution env creation / modification
	*)

let rawBindingWrap (path: string list) (q: raw_bind): res_binding = match q with
	PrimBind x -> SymBind(x, canonize_prim x)
	| RawBind x -> SymBind(x, canonize_scope path x)

let builtin_env (treeMap: (m_virt_bind list) tree_map): res_env = let env = {
	curPath = [];
	globalModules = ref (map_tree_p (fun path vbl -> List.map (rawBindingWrap path) (extractSymbols vbl)) treeMap);
	(*importPrefixes = Hashtbl.create 5;*)
	importHandles = Hashtbl.create 5;
	importIds = Hashtbl.create 20;
	localIds = StringMap.empty
} in ignore (add_import_renv env Lexing.dummy_pos ["builtin"] ""); env

let freeze_env (env: res_env) (path: string list): res_env = let env = {
	curPath = path;
	globalModules = env.globalModules;
	(*importPrefixes = Hashtbl.create 5;*)
	importHandles = Hashtbl.create 5;
	importIds = Hashtbl.create 20;
	localIds = StringMap.empty
} in ignore (add_import_renv env Lexing.dummy_pos ["builtin"] ""); env

	(*
		- saves locally declared bindings under a specific import path
	*)

let _extract_local_bindings (env: res_env) (importIds: overload_env): res_binding list =
	Hashtbl.fold (fun x ol bindings ->
		let ol_binds = List.map (fun (ox, x') -> globalize_binding env ox x x') ol in
		(List.concat ol_binds) @ bindings
	) importIds []
	(*let rec _find_global_overload ol x x' = match ol with
		[] -> []
		| (NewGlobalOr(h, g), _) :: _ -> [(GlobalSymBind(h, g, x, x'))]
		| _ :: ot -> _find_global_overload ot x x'
	in Hashtbl.fold (fun x ol bindings ->
		if List.exists (fun (ox, _) -> match ox with
			LocalOr -> true | _ -> false
		) ol then (SymBind x) :: bindings
		else (_find_global_overload ol x x') @ bindings
	) importIds []*)

let save_local_dec_renv (env: res_env) (path: string list): unit =
	let bindings = _extract_local_bindings env env.importIds in
	env.globalModules := add_tree !(env.globalModules) path bindings

let save_ext_dec_renv (env: res_env) (path: string list): unit =
	let bindings = _extract_local_bindings env env.importIds in
		(* TODO: sanity check on extending the bindings here *)
	env.globalModules := update_tree !(env.globalModules) path
		(fun oldBindings -> oldBindings @ bindings) []




