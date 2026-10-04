open Parser.Dusk_type

	(*
		import_origin - half of a binding after it has been imported, which
			stores disambiguating information
		* local - declared (or overloaded) locally in the module
		* import - imported with handle
		* strictly scoped - handle MUST be used (currently only used for globals)
			(local flag, strict scope handle)
	*)

type import_origin =
	LocalOr
	| ImportOr of string
	| StrictOr of bool * string

let origin_handle (ox: import_origin): string option = match ox with
	LocalOr -> None
	| ImportOr handle -> Some handle
	| StrictOr(_, h) -> Some h

	(* overload_list - provides a list of defined/imported bindings + their canonical names *)

type overload_list = (import_origin * canon_name) list

	(* - filtering *)

type ol_filter = (import_origin * canon_name) -> bool

let filter_overload_list (ol: overload_list) (fl: ol_filter list): overload_list =
	let rec fol_rec ol fl = match fl with
		[] -> ol
		| f :: ft ->
			let ol' = List.filter f ol in
			if List.length ol' = 0 then ol
			else if List.length ol' = 1 then ol'
			else fol_rec ol' ft
	in if List.length ol > 1 then fol_rec ol fl else ol

	(* -- overload list filters *)

let not_strict_handle ((ox, _): import_origin * 'a): bool =
	match ox with StrictOr _ -> false | _ -> true
	
let only_local_handle ((ox, _): import_origin * 'a): bool =
	match ox with LocalOr -> true | _ -> false

let match_handle (handle: string option) ((ox, _): import_origin * 'a): bool =
	handle = origin_handle ox

	(* - uniqueness *)

let unique_overload_list (l: overload_list): canon_name list =
	let rec uol_rec l cl = match l with
		[] -> cl
		| (_, x) :: t ->
			if List.exists (fun y -> cr x = cr y) cl then uol_rec t cl
			else uol_rec t (x :: cl) 
	in uol_rec l []

	(* overload_env - maps raw bindings into overload options + their canonical names *)

type overload_env = (string, overload_list) Hashtbl.t
type canon_fun = import_origin -> string -> canon_name

	(* - has local *)

let has_local_oenv (env: overload_env) (QN(_, x): qual_name): bool = match Hashtbl.find_opt env x with
	None -> false
	| Some ol -> List.exists (fun (ox, _) -> ox = LocalOr) ol

	(* - lookup, automatically applies handle *)

let lookup_oenv (env: overload_env) (QN(p, x): qual_name): (import_origin * canon_name) list = match p with
	Some prefix -> (match Hashtbl.find_opt env x with
		None -> []
		| Some xl -> List.filter (match_handle (Some prefix)) xl)
	| None -> (match Hashtbl.find_opt env x with
		None -> []
		| Some xl -> List.filter not_strict_handle xl)

	(* - lookup w/ handle + full disambiguation *)

let lookup_oenv_disambig (env: overload_env) (q: qual_name): (import_origin * canon_name) list =
	filter_overload_list (lookup_oenv env q) [only_local_handle]

	(* - adds overload, will fail if handle already exists *)

let add_oenv (env: overload_env) (cf: canon_fun) (ox: import_origin) (QN(_, x): qual_name): canon_name option = match Hashtbl.find_opt env x with
	None ->
		let x' = cf ox x in
		Hashtbl.add env x [(ox, x')]; Some x'
	| Some ol ->
		let rl = List.filter (match_handle (origin_handle ox)) ol in
		if List.length rl > 0 then None
		else
			let x' = cf ox x in
			(Hashtbl.replace env x ((ox, x') :: ol); Some x')

let add_oenv_direct (env: overload_env) (x: string) (cn: canon_name): unit option = match Hashtbl.find_opt env x with
	None -> Hashtbl.add env x [(LocalOr, cn)]; Some ()
	| Some ol ->
		let rl = List.filter (match_handle (origin_handle LocalOr)) ol in
		if List.length rl > 0 then None
		else (Hashtbl.replace env x ((LocalOr, cn) :: ol); Some ())
