
let (let>) (x: 'a option) (f: 'a -> 'b option): 'b option =
	match x with None -> None | Some v -> f v

	(* generic type for functions / calculations that may return an error result *)

type ('a, 'b) try_res =
	Valid of 'a
	| Error of 'b

let (let*) (x: ('a, 'c) try_res) (f: 'a -> ('b, 'c) try_res): ('b, 'c) try_res =
	match x with Error e -> Error e | Valid v -> f v

let opt_try_res (f: 'a -> ('b, 'c) try_res) (o: 'a option): ('b option, 'c) try_res = match o with
	None -> Valid None
	| Some v ->	let* v' = f v in Valid (Some v')

let rec map_try_res (f: 'a -> ('b, 'c) try_res) (l: 'a list): ('b list, 'c) try_res = match l with
	[] -> Valid []
	| v :: t ->
		let* v' = f v in
		let* t' = map_try_res f t in Valid (v' :: t')

let map_try_resi (f: 'a -> int -> ('b, 'c) try_res) (l: 'a list): ('b list, 'c) try_res =
	let rec mtri l i = match l with
		[] -> Valid []
		| v :: t ->
			let* v' = f v i in
			let* t' = mtri t (i + 1) in Valid (v' :: t')
	in mtri l 0

let rec fold_try_res (f: 'b -> 'a -> ('b, 'c) try_res) (z: 'b) (l: 'a list): ('b, 'c) try_res = match l with
	[] -> Valid z
	| v :: t -> let* z' = f z v in fold_try_res f z' t 

type 'a opt_res = ('a, unit) try_res

	(* type for (possible) error results + logging state *)

type 'a try_log_res = LogRes of 'a option * string list

let tryWithErrLog (f: 'b -> string) (x: ('a, 'b) try_res): 'a try_log_res =
	match x with Error e -> LogRes(None, [f e]) | Valid v -> LogRes(Some v, [])

let (let*!) (x: 'a try_log_res) (f: 'a -> 'b try_log_res): 'b try_log_res = match x with
	LogRes(Some v, lx) -> let LogRes(r, ly) = f v in LogRes(r, lx @ ly)
	| LogRes(None, lx) -> LogRes(None, lx)

let validLog (v: 'a): 'a try_log_res = LogRes(Some v, [])

let failLog (x: string): 'a try_log_res = LogRes(None, [x])

let endLog (): 'a try_log_res = LogRes(None, [])

let printLogRes (LogRes(_, lx): 'a try_log_res) =
	List.map (fun x -> print_string (x ^ "\n")) lx

let hookLogRes (err: string -> unit) (LogRes(v, lx): 'a try_log_res): unit = match v with
	None -> err (String.concat "\n" lx)
	| _ -> ()

let rec mapLogRes (f: 'a -> 'b try_log_res) (l: 'a list): ('b list) try_log_res = match l with
	[] -> LogRes(Some [], [])
	| v :: t ->
		let*! v' = f v in
		let*! t' = mapLogRes f t in LogRes (Some (v' :: t'), [])