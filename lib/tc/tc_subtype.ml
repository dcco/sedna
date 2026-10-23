open Commons.Try_log
open Parser.Lex_token
open Parser.Dusk_type
open Codegen.Fin_type
open Tc_type
open Tc_err


	(*
		##############################
		## simple subtyping/solving ##
		##############################
	*)

	(*
		** type variable constraints
		- s <: _
		- _ :=: s
	*)

type cmp_type = LeqCmp of lhs_type | EqCmp of g_type

type t_crn = Crn of cmp_type * string

	(*
		** generic type equality / subtyping
		- produces tvar constraints (solving is deferred)
	*)

let cmp_zero_flag (c: cmp_type) (zf1: bool) (zf2: bool): bool = match c with
	EqCmp _ -> zf1 = zf2
	| LeqCmp _ -> not zf1 || zf2

let cmp_valid (b: bool): (t_crn list) opt_res = if b then Valid [] else Error ()

let rec cmp_type_raw (c: cmp_type) (s: g_type) (t: g_type): (t_crn list) opt_res = match (s, t) with
	(BotTy, _) -> Valid []
	| (PrimTy s', PrimTy t') -> cmp_valid (s' = t')
	| (IntTy(u', s'), IntTy(v', t')) -> cmp_valid (u' = v' && s' = t')
		(* - type arguments must usually be identical (invariance of data) *)
	| (NamedTy(s', _sl), NamedTy(t', _tl)) ->
		if List.length _sl <> List.length _tl || cr s' <> cr t' then Error ()
		else fold_try_res (fun crnz (s, t) ->
			let* crnt = cmp_type_raw (EqCmp t) s t in Valid (crnz @ crnt)
		) [] (List.combine _sl _tl) 
	| (ArrayTy(i, s'), ArrayTy(j, t')) -> if i <> j then Error () else cmp_type_raw (EqCmp t') s' t'
	| (TagOfTy s, TagOfTy t) -> cmp_valid (s = t)
	| (CPtrTy s, CPtrTy t) -> cmp_type_raw (EqCmp t) s t
	| (TValTy s, TValTy t) -> cmp_type_raw (EqCmp t) s t
		(* - tuples preserve subtyping *)
	| (TupleTy(zf1, _sl), TupleTy(zf2, _tl)) ->
		if List.length _sl <> List.length _tl || not (cmp_zero_flag c zf1 zf2) then Error ()
		else fold_try_res (fun crnz (s, t) ->
			let* crnt = cmp_type_raw c s t in Valid (crnz @ crnt)
		) [] (List.combine _sl _tl) 
		(* - nullable type case *)
	| (NullableTy s', NullableTy t') -> cmp_type_raw c s' t'
	| (_, NullableTy t') -> (match c with
		EqCmp _ -> Error () | LeqCmp _ -> cmp_type_raw c s t'
	)
		(*
			- fn argument type presumes equality (placing an upper bound) [this is a concession]
			- fn return type preserves subtyping
		*)
	| (FunTy(s_pl, s_r), FunTy(t_pl, t_r)) ->
		let* crn_pl = fold_try_res (fun crnz (s, t) ->
			let* crnt = cmp_type_raw (EqCmp t) s t in Valid (crnz @ crnt)
		) [] (List.combine s_pl t_pl) in
		let* crn_r = cmp_type_raw c s_r t_r in Valid (crn_pl @ crn_r)
		(* - variable constraint *)
	| (_, VarTy a) -> (match c with
		EqCmp _ -> Valid [Crn(EqCmp s, a)]
		| LeqCmp _ -> Valid [Crn(LeqCmp (LT s), a)]
	)
	| (_, BotTy) | (_, PrimTy _) | (_, IntTy _) | (_, NamedTy _)
	| (_, ArrayTy _) | (_, TagOfTy _) | (_, CPtrTy _) | (_, TValTy _)
	| (_, TupleTy _) | (_, FunTy _) -> Error ()

let rec cmp_type (c: cmp_type) (t: g_type): (t_crn list) opt_res = match (c, t) with
	(_, VarTy a) -> Valid [Crn(c, a)]
	| (EqCmp s, _) -> cmp_type_raw c s t
	| (LeqCmp (LT s), _) -> cmp_type_raw c s t
	| (LeqCmp NullLT, t) -> if nullable_type (LT t) then Valid [] else Error ()
	| (LeqCmp (RawTupleLT _sl), TupleTy(_, _tl)) ->
		if List.length _sl <> List.length _tl then Error ()
		else fold_try_res (fun crnz (s, t) ->
			let* crnt = cmp_type (LeqCmp s) t in Valid (crnz @ crnt)
		) [] (List.combine _sl _tl)
	| (LeqCmp (RawTupleLT _), _) -> Error ()

	(*
		** simple constraint solving
		- assumes none of the type variables are fresh (requires exact matches)
	*)

let simp_solve_crn (Crn(c, a): t_crn): bool = match c with
	EqCmp (VarTy b) -> a = b
	| LeqCmp (LT (VarTy b)) -> a = b
	| LeqCmp (LT BotTy) -> true
	| _ -> false

let rec simp_solve_crn_list (crn: t_crn list): bool = match crn with
	[] -> true
	| crz :: crt -> simp_solve_crn crz && simp_solve_crn_list crt 

	(*
		** type join
		- assumes type variables are NOT fresh
		- important for complex constraint solving
	*)

let rec join_type_raw (s: g_type) (t: g_type): g_type opt_res = match (s, t) with
	(_, BotTy) -> Valid s
	| (BotTy, _) -> Valid t
		(* - nullable is folded in to the type *)
	| (NullableTy s', NullableTy t') ->
		let* u' = join_type_raw s' t' in Valid (NullableTy u')
	| (_, NullableTy t') -> let* u' = join_type_raw s t' in Valid (NullableTy u')
	| (NullableTy s', _) -> let* u' = join_type_raw s' t in Valid (NullableTy u')
		(* - tuple type, set zero flag taken from union *)
	| (TupleTy(zf1, _sl), TupleTy(zf2, _tl)) ->
		if List.length _sl <> List.length _tl then Error ()
		else let* ul = map_try_res (fun (s, t) -> join_type_raw s t) (List.combine _sl _tl) in
			Valid (TupleTy(zf1 || zf2, ul))
	| (_, TupleTy _) -> Error ()
	| (TupleTy _, _) -> Error ()
		(* - function return types may be folded in [argument types require equality, which IS a concession] *)
	| (FunTy(s_pl, s_r), FunTy(t_pl, t_r)) ->
		if List.length s_pl <> List.length t_pl then Error ()
		else let* b = (fold_try_res (fun b (s, t) ->
			let* crn = cmp_type (EqCmp s) t in Valid (b && simp_solve_crn_list crn)
		) true (List.combine s_pl t_pl)) in
		if not b then Error ()
		else let* u_r = join_type_raw s_r t_r in Valid (FunTy(s_pl, u_r))
	| (_, FunTy _) -> Error ()
	| (FunTy _, _) -> Error ()
		(* - all other types are assessed by strict equality *)
	| _ ->
		let* crn = cmp_type (EqCmp s) t in
		if simp_solve_crn_list crn then Valid s else Error ()

let rec _join_type_l (s: lhs_type) (t: g_type): g_type opt_res = match (s, t) with
	(_, BotTy) -> failwith "BUG: tc_type.ml - BotTy case should be handled by callee."
	| (LT s', _) -> join_type_raw s' t
	| (NullLT, NullableTy _) -> Valid t
	| (NullLT, CPtrTy _) -> Valid t
	| (NullLT, NamedTy _) -> Valid (NullableTy t)
	| (NullLT, _) -> Error ()
	| (RawTupleLT _sl, TupleTy(zf, _tl)) ->
		if List.length _sl <> List.length _tl then Error ()
		else let* _ul = map_try_res (fun (s, t) -> _join_type_l s t) (List.combine _sl _tl) in
			Valid (TupleTy(zf, _ul))
	| (RawTupleLT _, _) -> Error ()

let join_type (s: lhs_type) (t: lhs_type): lhs_type opt_res = match (s, t) with
	(_, LT BotTy) -> Valid s
	| (LT BotTy, _) -> Valid t
	| (LT s', _) -> let* u = _join_type_l t s' in Valid (LT u)
	| (_, LT t') -> let* u = _join_type_l t t' in Valid (LT u)
	| (NullLT, NullLT) -> Valid NullLT
	| _ -> Error () 

	(*
		** constraint conjunction
		- fundamental step of constraint solving, combines two constraints into a new one
			(assuming that they are compatible)
	*)

let rec conj_crn (crn: t_crn) (crn': t_crn): t_crn opt_res = match (crn, crn') with
	(Crn(LeqCmp s, a), Crn(LeqCmp t, _)) ->
		let* u = join_type s t in Valid (Crn(LeqCmp u, a))
	| (Crn(EqCmp _, _), Crn(LeqCmp _, _)) -> conj_crn crn' crn
	| (Crn(c, _), Crn(EqCmp t, _)) ->
		let* _crn = cmp_type c t in
		if simp_solve_crn_list _crn then Valid crn else Error ()

	(*
		###############################################
		## complex subtyping (type variable solving) ##
		###############################################
	*)

	(*
		** type variable substitution
	*)

type tvar_env = (string, t_crn) Hashtbl.t

let new_sol (): tvar_env = Hashtbl.create 10

let gen_sol (xl: string list) (tau_l: g_type list): tvar_env =
	let sol = new_sol () in
	List.fold_left (fun _ (a, tau) ->
		Hashtbl.add sol a (Crn(EqCmp tau, a))
	) () (List.combine xl tau_l); sol

let rec apply_sol (sol: tvar_env) (t: g_type): g_type = match t with
	NamedTy(x, _tl) -> NamedTy(x, List.map (apply_sol sol) _tl)
	| TupleTy(zFlag, _tl) -> TupleTy(zFlag, List.map (apply_sol sol) _tl)
	| ArrayTy(i, t) -> ArrayTy(i, apply_sol sol t)
	| NullableTy t -> NullableTy (apply_sol sol t)
	| FunTy(t_pl, t_r) -> FunTy(List.map (apply_sol sol) t_pl, apply_sol sol t_r)
	| CPtrTy t -> CPtrTy (apply_sol sol t)
	| TValTy t -> TValTy (apply_sol sol t)
	| VarTy a -> (match Hashtbl.find_opt sol a with
		Some (Crn(EqCmp t, _)) -> t
		| Some (Crn _) ->  failwith "BUG: tc_subtype.ml - Indefinite type variable in solution application."
		| _ -> failwith "BUG: tc_subtype.ml - Failed lookup of type variable in solution application."
	)
	| BotTy | PrimTy _ | IntTy _ | TagOfTy _ -> t

	(*
		** standard constraint solving
		- incremenetally builds a type variable substitution
	*)

let solve_crn (sol: tvar_env) (crn: t_crn): unit opt_res =
	let Crn(_, a) = crn in match Hashtbl.find_opt sol a with
		None -> Hashtbl.add sol a crn; Valid ()
		| Some crn' ->
			let* crnx = conj_crn crn crn' in
			Hashtbl.replace sol a crnx; Valid ()  

let rec solve_crn_list (sol: tvar_env) (crn: t_crn list): unit opt_res = match crn with
	[] -> Valid ()
	| crz :: crt ->
		let* _ = solve_crn sol crz in solve_crn_list sol crt

	(*
		#################################
		## subtyping w/ error handling ##
		#################################
	*)

	(*
		** type-checking for subtyping
	*)

let simp_subtype (s: lhs_type) (t: g_type): bool = match cmp_type (LeqCmp s) t with
	Error _ -> false
	| Valid crn -> simp_solve_crn_list crn

let tc_simp_subtype (info: tc_info) (s: lhs_type) (t: g_type) (p: l_pos): unit tc_res = 
	let res =
		let* crn = cmp_type (LeqCmp s) t in
		cmp_valid (simp_solve_crn_list crn)
	in match res with
		Valid _ -> Valid ()
		| Error _ -> Error (BadType_Err(s, t, info, p))

let tc_subtype (sol: tvar_env) (info: tc_info) (s: lhs_type) (t: g_type) (p: l_pos): unit tc_res = 
	let res =
		let* crn = cmp_type (LeqCmp s) t in
		solve_crn_list sol crn
	in match res with
		Valid _ -> Valid ()
		| Error _ -> Error (BadType_Err(s, t, info, p))

	(*
		** type-checking for subtyping w/ lists
	*)

let tc_type_list (sol: tvar_env) (info: tc_info_stub) (arg_l: lhs_type list) (_tl: g_type list) (p: l_pos): unit tc_res =
	if List.length arg_l <> List.length _tl then
		Error (MismatchedArgNum_Err(List.length arg_l, List.length _tl, index_stub info None, p))
	else let rec tctl_rec _al _tl ix = match (_al, _tl) with
		([], []) -> Valid ()
		| (s :: st, t :: tt) ->
			let* _ = tc_subtype sol (index_stub info (Some ix)) s t p in
			tctl_rec st tt (ix + 1)
			(*let* _ = (match (e, t) with
				(SizeExpC s', KindTy a) -> (match Hashtbl.find_opt sol a with
					None -> Hashtbl.add sol a s'; Valid ()
					| Some t' -> tc_type sol (index_stub info (Some ix)) s' t' p 
				)
				| (_, KindTy _) -> failwith "BUG: tc_exp.ml - Bad value for kind value in type-checking."
				| _ -> Valid ()
			) in tctl_rec st tt (ix + 1)*)
		| _ -> failwith "BUG: tc_exp.ml - Type-checking for mismatched arguments reached unexpected location."
	in tctl_rec arg_l _tl 0

	(*
		** type-checking to join elements of a list
	*)

let tc_type_join (info: tc_info_stub) (_tl: lhs_type list) (p: l_pos): lhs_type tc_res =
	let rec tctj_rec s _tl ix = match _tl with
		[] -> Valid s
		| t :: tt -> (match join_type s t with
			Valid u -> tctj_rec u tt (ix + 1)
			| Error _ ->
				Error (BadJoin_Err(s, t, index_stub info (Some ix), p)) 
		)
	in tctj_rec (LT BotTy) _tl 0

	(*
		#######################
		## type "completion" ##
		#######################
	*)

let complete_type (tau: lhs_type) (p: l_pos): g_type tc_res =
	let rec ct_rec t = match t with
		LT BotTy | NullLT -> Error (IncompleteType_Err(tau, p))
		| LT tau' -> Valid tau'
		| RawTupleLT tau_l ->
			let* tau_l' = map_try_res ct_rec tau_l in
			Valid (TupleTy(false, tau_l'))
	in ct_rec tau

let complete_sol (sol: tvar_env) (p: l_pos): unit tc_res =
	let kl = Hashtbl.fold (fun k _ l -> k :: l) sol [] in
	let* _ = map_try_res (fun a -> match Hashtbl.find sol a with
		Crn(EqCmp _, _) -> Valid ()
		| Crn(LeqCmp t, _) ->
			let* t' = complete_type t p in
			Hashtbl.replace sol a (Crn(EqCmp t', a)); Valid ()
	) kl in Valid ()

let extract_sol (sol: tvar_env) (xl: string list): g_type list =
	try	List.map (fun x -> match Hashtbl.find sol x with
		Crn(EqCmp t, _) -> t
		| Crn(LeqCmp _, _) -> failwith "BUG: tc_subtype.ml - Attempted to extract from incomplete type solution."
	) xl
	with _ -> failwith "BUG: tc_subtype.ml - Could not find assignment for type argument while inferring type."

	(*
		** constraint conjunction
	*)
(*
let conj_crn (crn: t_crn) (crn2: t_crn): t_crn = match crn with
	(Crn)

	(*
		** type variable substitution
	*)

type tvar_env = (string, t_crn) Hashtbl.t

let new_sol (): tvar_env = Hashtbl.create 10

	(*
		** constraint solving
	*)

let solve_crn (sol: tvar_env) (crn: t_crn): tvar_env = match Hashtbl.find_opt sol i with
	None -> Hashtbl.add sol i crn; true
		(* if a constraint exists, combine the constraints *)
	| Some crnx -> Hashtbl.replace sol i (conj_crn crn crnx)
	
let rec solve_crn_list (sol: tvar_env) (crl: t_crn list): tvar_env = match crl with
	[] -> sol
	| crn :: crt -> solve_crn_list (solve_crn sol crn) crt

*)
	
	(*
		** type join
		returns the SUM of two "compatible" types (types that have the same memory layout)
	*)
(*
let rec join_type (s: g_type) (t: g_type): g_type opt_res = match (s, t) with
	(BotTy, _) -> t
	| (_, BotTy) -> s
	| (PrimTy s', PrimTy t') -> if s' = t' then Valid s else Error ()
	| (IntTy(u', s'), IntTy(v', t')) -> if u' = v' && s' = t' then Valid s else Error ()
	| (NamedTy(s', _sl), NamedTy(t', _tl)) ->
		if cr s' <> cr t' || List.length _sl <> List.length _tl then Error ()
		else map_try_res (List.combine _sl _tl)

	(*
		** type equality
	*)

let rec eq_type (s: g_type) (t: g_type): bool = match (s, t) with
	(BotTy, BotTy) -> true
	| (PrimTy s', PrimTy t') -> s' = t'
	| (IntTy(u', s'), IntTy(v', t')) -> u' = v' && s' = t'
	| (NamedTy(s', _sl), NamedTy(t', _tl)) ->
		if List.length _sl <> List.length _tl then false
		else List.for_all (fun (s, t) -> eq_type s t) (List.combine _sl _tl)
			&& cr s' = cr t'
	| (TupleTy(zf1, _sl), TupleTy(zf2, _tl)) ->
		if List.length _sl <> List.length _tl then false
		else if zf1 && not zf2 then false 
		else List.for_all (fun (s, t) -> eq_type s t) (List.combine _sl _tl)
	| (ArrayTy(i, s'), ArrayTy(j, t')) -> i = j && eq_type s' t'
	| (TagOfTy s', TagOfTy t') -> eq_type s' t'
	| (NullableTy s', NullableTy t') -> eq_type s' t'
	| (FunTy(s_pl, s_r), FunTy(t_pl, t_r)) ->
		(List.for_all (fun (s, t) -> eq_type s t) (List.combine s_pl t_pl)) && (eq_type s_r t_r)
	| (CPtrTy s', CPtrTy t') -> eq_type s' t'

	(*
		** subtyping definition
	*)

let rec is_subtype (sol: tvar_env) (s: g_type) (t: g_type): bool = match (s, t) with
	(BotTy, _) -> true
	| (PrimTy s', PrimTy t') -> s' = t'
	| (IntTy(u', s'), IntTy(v', t')) -> u' = v' && s' = t'
	| (NamedTy(s', _sl), NamedTy(t', _tl)) ->
		if List.length _sl <> List.length _tl then false
		else List.for_all (fun (s, t) -> is_subtype sol s t) (List.combine _sl _tl)
			&& cr s' = cr t'
	| (TupleTy(zf1, _sl), TupleTy(zf2, _tl)) ->
		if List.length _sl <> List.length _tl then false
		else if zf1 && not zf2 then false 
		else List.for_all (fun (s, t) -> is_subtype sol s t) (List.combine _sl _tl)
	| (ArrayTy(i, s'), ArrayTy(j, t')) -> i = j && is_subtype sol s' t'
	| (TagOfTy s', TagOfTy t') -> is_subtype sol s' t'
	| (NullableTy s, NullableTy t) -> is_subtype sol s t
	| (s, NullableTy t) -> is_subtype sol s t
	| (FunTy(s_pl, s_r), FunTy(t_pl, t_r)) ->
		(List.for_all (fun (s, t) -> is_subtype sol s t) (List.combine s_pl t_pl)) && (is_subtype sol s_r t_r)
	| (CPtrTy s', CPtrTy t') -> is_subtype sol s' t'
	(*| (VarTy _, _) -> failwith "BUG: tc_exp.ml - Variable type found in left-hand position."*)
	| (_, VarTy i) -> (match Hashtbl.find_opt sol i with
		None -> Hashtbl.add sol i s; true
		| Some t' -> is_subtype sol s t' 
	)
	| (KindTy _, KindTy _) -> true
	| (_, BotTy) | (_, PrimTy _) | (_, IntTy _) | (_, NamedTy _)
	| (_, TupleTy _) | (_, ArrayTy _) | (_, TagOfTy _)
	| (_, FunTy _) | (_, CPtrTy _) | (_, KindTy _) -> false
*)
	(*
		** join definition
	*)
(*
let rec join_type (info: tc_info) (p: l_pos) (s: g_type) (t: g_type): g_type tc_res = match (s, t) with
	(BotTy, _) -> t
	| (PrimTy s', PrimTy t') ->
		if s' = t' then Valid t else Error (Invalid(s, t, info, p))
	| (IntTy(u, s'), IntTy(v', t')) ->
		if u' = v' && s' = t' then Valid t else Error (Invalid(s, t, info, p))
	| (NamedTy(s', _sl), NamedTy(t', _tl)) ->
*)

(*	
	| (TagTupleTy(s', _), NamedTy(t', _)) -> cr s' = cr t'
	| (NullTy, NullTy) -> true
	| (NullTy, NullableTy _) -> true
	| (NullTy, CPtrTy _) -> true
*)