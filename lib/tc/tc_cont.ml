open Builtin.Builtin_core
open Parser.Dusk_type
open Parser.Dusk_ast
open Codegen.Fin_type
open Codegen.Fin_ast

module StringMap = Map.Make(String)

	(*
		tags of types (for overloading)
	*)

let tag_of_ntuple (n: int): string =
	if n = 2 then "pair"
	else if n = 3 then "triple"
	else "t" ^ (string_of_int n)

let rec tag_of_type (tau_o: g_type option): string = match tau_o with
	None -> "none"
	| Some (PrimTy x) -> x
	| Some (IntTy(false, S32)) -> "Int"
	| Some (IntTy(u, s)) -> string_of_type (fun _ -> "") (IntTy(u, s)) 
	| Some (NamedTy x) -> cr x
	| Some (TupleTy tau_l) -> tag_of_ntuple (List.length tau_l)
	| Some (ArrayTy(i, _)) -> "a" ^ (string_of_int i)
	| Some (TagOfTy _) -> "tag"
	| Some (FunTy _) -> "fn"
	| Some (NullableTy t) -> tag_of_type (Some t)
	| Some (EmptyableTy t) -> tag_of_type (Some t)
	| Some BotTy -> "bot"
	| Some (VarTy _) -> "any"
	| Some (KindTy _) -> "type"
		(* TODO: maybe make more robust overloading (currently impeded by need for cptr[any] functions) *)
	| Some (CPtrTy _) -> "ptr"
	| Some (TagTupleTy(x, _)) -> cr x
	| Some NullTy -> "null"

let aug_cn (tag: string) (CN(x, xl): canon_name): canon_name = CN(tag ^ x, xl)

	(*
		overloaded (polymorphic) function types
	*)

type 'a poly_type = (string * 'a) list

let add_ptype (rho: 'a poly_type) (tag: string) (v: 'a) (debug: string): 'a poly_type =
	match List.find_opt (fun (tag', _) -> tag = tag') rho with
		None -> (tag, v) :: rho
		| Some _ -> failwith ("(TODO?) (IMPORTANT) BUG: tc_cont.ml - Attempted to add to polymorphic type with already existing tag " ^
			tag ^ " " ^ debug ^ ".")

let disambig_ptype (rho: 'a poly_type) (tag: string): 'a option =
	let rec dp_rec tagX rho = match rho with
		[] -> None
		| (tag', v) :: rho' -> if tagX = tag' then Some v else dp_rec tagX rho'
	in let res = dp_rec tag rho in (match res with
		None -> dp_rec "any" rho
		| _ -> res
	)

	(*
		individual guard set
	*)

type guard_set = GuardSet of string list * string list

let null_guard_set: guard_set = GuardSet(["null"], ["valid"; "null"])

let new_guard_set (x: string) (all: string list): guard_set = GuardSet([x], all)

let neg_guard_set (GuardSet(g, all): guard_set): guard_set =
	GuardSet(List.filter (fun x -> not (List.mem x g)) all, all)

let conj_guard_set (GuardSet(g, all): guard_set) (GuardSet(h, _): guard_set): guard_set =
	GuardSet(List.filter (fun x -> List.mem x h) g, all)

let disj_guard_set (GuardSet(g, all): guard_set) (GuardSet(h, _): guard_set): guard_set =
	GuardSet(g @ (List.filter (fun x -> not (List.mem x g)) h), all) 

let disj_guard_set_opt (g: guard_set option) (h: guard_set option): guard_set option = match (g, h) with
	(Some g, Some h) -> Some (disj_guard_set g h)
	| _ -> None

	(*
		full guard set
	*)

type guard_map = guard_set StringMap.t

let new_guard_map (x: string) (g: guard_set): guard_map = StringMap.singleton x g

let neg_guard_map (g: guard_map): guard_map = StringMap.map neg_guard_set g

let conj_guard_map (g: guard_map) (h: guard_map): guard_map = 
	StringMap.union (fun _ g h -> Some (conj_guard_set g h)) g h

let disj_guard_map (g: guard_map) (h: guard_map): guard_map = 
	StringMap.merge (fun _ g h -> disj_guard_set_opt g h) g h

let try_narrow_guard_map (g: guard_map) (x: string): string option = match StringMap.find_opt x g with
	Some (GuardSet([x], _)) -> Some x
	| _ -> None

	(*
		typed environment
	*)

type sym_fun_type = sym * canon_name fun_type

type poly_dec = sym_fun_type poly_type

type tc_attrs = (string, g_type) Hashtbl.t

type tc_tval =
	TcTDef of g_tdef
	| TcCtorE of canon_name
	| TcCtorU of canon_name

type type_env = {
	curDir: string option;
	globalFIds: (string, canon_name * poly_dec) Hashtbl.t;
	globalTIds: (string, canon_name * tc_tval) Hashtbl.t;
	globalIds: (string, canon_name * g_type * gen_exp option) Hashtbl.t;
	globalAttrs: (string, tc_attrs) Hashtbl.t;
	localIds: g_type StringMap.t;
	guardMap: guard_map;
	boxCount: int ref
}

	(* - TEST fun: used to dump *)

let dump_tenv (env: type_env): unit =
	print_string "#TYPE_ENV {\n";
	Hashtbl.iter (fun x (_, rho) ->
		print_string (" " ^ x ^ ": ");
		if List.length rho = 1 then	print_string (string_of_fun_type cr (snd (snd (List.hd rho))))
		else (print_string " [\n";
			List.iter (fun (_, (_, tau_f)) -> print_string ("  - " ^ (string_of_fun_type cr tau_f) ^ "\n")) rho;
			print_string " ]"
		); print_string "\n"
	) env.globalFIds;
	print_string "} {\n";
	Hashtbl.iter (fun x (_, td) ->
		print_string (" " ^ x ^ ": "); (
		let rec print_tc_item td = match td with
			TcTDef (TFunTD(_, td')) -> print_tc_item (TcTDef td'); print_string "[_]"
			| TcTDef (StructTD _) -> print_string "struct"
			| TcTDef (EnumTD _) -> print_string "enum"
			| TcTDef (UnionTD _) -> print_string "union"
			| TcTDef ExternTD -> print_string "extern"
			| TcCtorE f -> print_string ("ctor (e): " ^ (cr f))
			| TcCtorU f -> print_string ("ctor (u): " ^ (cr f))
		in print_tc_item td); print_string "\n"
	) env.globalTIds;
	Hashtbl.iter (fun x (_, tau, _) ->
		print_string (" " ^ x ^ ": " ^ (string_of_type cr tau) ^ "\n")
	) env.globalIds;
	print_string "}\n";;

let add_fun_tenv (env: type_env) (f: canon_name) (v: sym_fun_type): unit =
	let (_, (tau_pl, _)) = v in
	let tag = tag_of_type (hd_opt tau_pl) in match Hashtbl.find_opt env.globalFIds (cr f) with
		None -> Hashtbl.add env.globalFIds (cr f) (f, [(tag, v)])
		| Some (_f, rho) -> Hashtbl.replace env.globalFIds (cr f) (_f, add_ptype rho tag v ("for function " ^ (cr f))) 

let add_tdef_tenv (env: type_env) (f: canon_name) (td: g_tdef): unit =
	Hashtbl.add env.globalTIds (cr f) (f, TcTDef td);
	let rec att_aux td = match td with
		TFunTD(_, td') -> att_aux td'
		| EnumTD cl ->
			List.iter (fun (c, _) -> Hashtbl.add env.globalTIds (cr c) (c, TcCtorE f)) cl
		| UnionTD cl ->
			List.iter (fun (c, _, _) -> Hashtbl.add env.globalTIds (cr c) (c, TcCtorU f)) cl
		| StructTD _ | ExternTD -> ()
	in att_aux td

let builtin_tenv (dl: g_virt_bind list): type_env =
	let env = {
		curDir = None;
		globalFIds = Hashtbl.create 50;
		globalTIds = Hashtbl.create 50;
		globalIds = Hashtbl.create 50;
		globalAttrs = Hashtbl.create 10;
		localIds = StringMap.empty;
		guardMap = StringMap.empty;
		boxCount = ref 0
	} in List.iter (fun (f, vd, _) -> match vd with
		SymVD(s, tau_f) -> add_fun_tenv env f (s, tau_f)
		| TDefVD td -> add_tdef_tenv env f td
	) dl; env

let with_dir_tenv (env: type_env) (dir: string): type_env = { env with curDir = Some dir }

let get_box_id_tenv (env: type_env): int =
	let i = !(env.boxCount) in env.boxCount := i + 1; i

let lookup_fun_tenv (env: type_env) (f: canon_name) (tau_o: g_type option): (canon_name * sym_fun_type) option = match Hashtbl.find_opt env.globalFIds (cr f) with
	None -> None (* this case should theoretically never come up *)
	| Some (_f, rho) ->
		let tag = tag_of_type tau_o in (match disambig_ptype rho tag with
			None -> None
			| Some res -> Some (aug_cn ("_" ^ tag) _f, res)
		)

let lookup_fun_tenv_nodis (env: type_env) (f: canon_name): (canon_name * sym_fun_type) option = match Hashtbl.find_opt env.globalFIds (cr f) with
	None -> None (* this case should theoretically never come up *)
	| Some (_f, rho) -> (match rho with
		[(tag, res)] -> Some (aug_cn ("_" ^ tag) _f, res)
		| _ -> None
	)

	(*
		replaces builtin function bindings with type-annotated bindings
	*)

let sym_list_tenv (env: type_env): g_virt_bind list =
	let rho_l = List.of_seq (Hashtbl.to_seq env.globalFIds) in
	List.concat (List.map (fun (_, (f, rho)) ->
		List.map (fun (tag, (s, tau_f)) -> (aug_cn ("_" ^ tag) f, SymVD(s, tau_f), Lexing.dummy_pos)) rho
	) rho_l)

let tc_complete_builtins (env: type_env) (symList: g_virt_bind list): g_virt_bind list =
	(List.filter (fun (_, vd, _) -> match vd with SymVD(_, _) -> false | _ -> true) symList) @ sym_list_tenv env

	(*
		function context:
			stores important meta-information about the function being compiled
	*)

type fun_cont = {
	f: string;
	lf: lin_flag;
}

let nonLinCont (cont: fun_cont): fun_cont = { cont with lf = Fn }