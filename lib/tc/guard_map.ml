
	(*
		** guard index / guard symbol
		symbolic representations of variables / constant indices into variables (array indices, tuple locations)
		- used as keys to store identifying information about variables (null/non-null, tag test results, etc)
	*)
(*
type guard_index = 
	NoIndex
	| ConstIndex of int
		(* variable + multiplier >> dividend >> offset *)
	| LinearIndex of string * int * int * int

let gi_cmp i1 i2 = match (i1, i2) with
	(NoIndex, NoIndex) -> 0
	| (NoIndex, _) -> -1
	| (ConstIndex i, ConstIndex j)

type guard_symbol = string * guard_index

module GuardSymbol = struct
	type t = guard_symbol

end

module GIMap = Map.Make(Guard_symbol)

	(*
		** guard set
		tracks [possible tags / all possible tags]
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
	| _ -> None*)