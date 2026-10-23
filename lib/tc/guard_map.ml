
module StringMap = Map.Make(String)

	(*
		** (null only) guard set
		[is null, isnt null]
	*)

type guard_set = GuardSet of bool * bool

let null_guard_set (b: bool): guard_set = if b then GuardSet(true, false) else GuardSet(false, true)

let neg_guard_set (GuardSet(a, b): guard_set): guard_set = GuardSet(not a, not b)

let conj_guard_set (GuardSet(a1, b1): guard_set) (GuardSet(a2, b2): guard_set): guard_set = GuardSet(a1 && a2, b1 && b2)

let disj_guard_set (GuardSet(a1, b1): guard_set) (GuardSet(a2, b2): guard_set): guard_set = GuardSet(a1 || a2, b1 || b2) 

let disj_guard_set_opt (g: guard_set option) (h: guard_set option): guard_set option = match (g, h) with
	(Some g, Some h) -> Some (disj_guard_set g h)
	| _ -> None

	(*
		** guard map
	*)

type guard_map = guard_set StringMap.t

let new_guard_map (x: string) (g: guard_set): guard_map = StringMap.singleton x g

let neg_guard_map (g: guard_map): guard_map = StringMap.map neg_guard_set g

let conj_guard_map (g: guard_map) (h: guard_map): guard_map = 
	StringMap.union (fun _ g h -> Some (conj_guard_set g h)) g h

let disj_guard_map (g: guard_map) (h: guard_map): guard_map = 
	StringMap.merge (fun _ g h -> disj_guard_set_opt g h) g h

let try_narrow_guard_map (g: guard_map) (x: string): bool option = match StringMap.find_opt x g with
	Some (GuardSet(true, false)) -> Some true
	| Some (GuardSet(false, true)) -> Some false
	| _ -> None