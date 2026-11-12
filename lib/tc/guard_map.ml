
module StringMap = Map.Make(String)

	(*
		** guard set
		[partial set / complete set]
	*)

type guard_set = GuardSet of string list * string list

let null_guard_set (b: bool): guard_set =
	if b then GuardSet(["null"], ["null"; "valid"]) else GuardSet(["valid"], ["null"; "valid"])

let neg_guard_set (GuardSet(a, b): guard_set): guard_set =
	GuardSet(List.filter (fun x -> not (List.mem x a)) b, b)

let conj_guard_set (GuardSet(a1, b): guard_set) (GuardSet(a2, _): guard_set): guard_set =
	GuardSet(List.filter (fun x -> List.mem x a1 && List.mem x a2) b, b)

let disj_guard_set (GuardSet(a1, b): guard_set) (GuardSet(a2, _): guard_set): guard_set =
	GuardSet(List.filter (fun x -> List.mem x a1 || List.mem x a2) b, b)

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

let try_narrow_guard_map (g: guard_map) (x: string): string option = match StringMap.find_opt x g with
	Some (GuardSet([x], _)) -> Some x
	| _ -> None