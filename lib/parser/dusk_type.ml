
	(*
		identifier types:
		* qualified - raw, module-prefixed identifier taken from parsing
		* canon - identifier after canonization (also contains pre-canonized name for debugging)
	*)

type qual_name = QN of string option * string
type canon_name = CN of string * string list

let qn x = QN(None, x)
let cn (QN(xo, x)) x' = match xo with
	None -> CN(x', [x])
	| Some p -> CN(x', [p; x])
 
let cr (CN(x, _)) = x

(*
type qual_tag = QT of string option
type canon_tag = CT*)

	(*
		dusk types:
		> 'm: used to determine the type of "identifier used" (raw names vs canonical names) 
		- primitive -- Unit, Float, Bool, String
		- named type
		- tuple type -- (tau, ...)
		- array type -- 1d[tau], 2d[_], etc
	*)

type bit_width = S8 | S16 | S32 | S64

type 'm raw_type =
		(* first level types *)
	PrimTy of string
	| IntTy of bool * bit_width
	| NamedTy of 'm * 'm raw_type list
		(* - zero-able flag *)
	| TupleTy of bool * 'm raw_type list
	| ArrayTy of int * 'm raw_type
	| TagOfTy of 'm
	| FunTy of 'm raw_type list * 'm raw_type
	| NullableTy of 'm raw_type
	| TValTy of 'm raw_type
	| BotTy
		(* polymorphism types *)
	| VarTy of string
		(* special types *)
	| CPtrTy of 'm raw_type
		(* instance types
	| TagTupleTy of 'm * 'm raw_type list
	| NullTy *)
type 'm fun_type = 'm raw_type list * 'm raw_type

type m_type = qual_name raw_type

	(* string functions *)

let string_of_iType (u: bool) (s: bit_width): string =
	if not u && s = S32 then "Int"
	else (let p = if u then "U" else "I" in (match s with
		S8 -> p ^ "8"
		| S16 -> p ^ "16"
		| S32 -> p ^ "32"
		| S64 -> p ^ "64"
	))

let rec string_of_type (f: 'm -> string) (tau: 'm raw_type): string = match tau with
	| PrimTy x -> x
	| IntTy(u, s) -> string_of_iType u s
	| NamedTy(x, []) -> f x
	| NamedTy(x, tau_l) -> f x ^ "[" ^ String.concat ", " (List.map (string_of_type f) tau_l) ^ "]"
	| TupleTy(false, tau_l) -> "(" ^ String.concat ", " (List.map (string_of_type f) tau_l) ^ ")"
	| TupleTy(true, tau_l) -> "(" ^ String.concat " ?? " (List.map (string_of_type f) tau_l) ^ ")"
	| ArrayTy(i, tau) -> (string_of_int i) ^ "d[" ^ (string_of_type f tau) ^ "]"
	| TagOfTy x -> f x ^ ".t"
	| FunTy(tau_pl, tau_r) -> string_of_fun_type f (tau_pl, tau_r)
	| NullableTy tau -> (string_of_type f tau) ^ "?"
	| TValTy tau -> "TYPE[" ^ (string_of_type f tau) ^ "]"
	| BotTy -> "BOT"

	| VarTy a -> a

	| CPtrTy tau -> "CPtr[" ^ (string_of_type f tau) ^ "]"
	
and string_of_fun_type (f: 'm -> string) ((tau_pl, tau_r): 'm fun_type): string =
	"Fn(" ^ (String.concat ", " (List.map (string_of_type f) tau_pl)) ^ ") " ^ (string_of_type f tau_r)

	(* - auxiliary function, used to find the "first" argument of a function type *)

let hd_opt (l: 'm list): 'm option = match l with
	[] -> None
	| v :: _ -> Some v

	(* primitive types *)

let primTy x = PrimTy x
let namedTy x = NamedTy (QN(None, x), [])

let unitTy = primTy "Unit"
let floatTy = primTy "Float"
let stringTy = primTy "String"
let boolTy = primTy "Bool"

let intTy = IntTy(false, S32)
let i8Ty = IntTy(false, S8)
let i16Ty = IntTy(false, S16)
let i32Ty = intTy
let i64Ty = IntTy(false, S64)
let u8Ty = IntTy(true, S8)
let u16Ty = IntTy(true, S16)
let u32Ty = IntTy(true, S32)
let u64Ty = IntTy(true, S64)

(*let keyTy = primTy "Key"*)

	(*
		user-defined types:
		- enum
	*)

type enum_back = NoEB | IntEB of int | GlobalEB of string

type 'm field_list = (string * 'm raw_type) list

type 'm enum_case = string * 'm * enum_back
type 'm union_case = string * 'm * 'm raw_type list * enum_back

type 'm raw_tdef =
	StructTD of string list * 'm field_list
	| EnumTD of 'm enum_case list
	| UnionTD of ('m union_case) list
	| ExternTD

type m_field_list = qual_name field_list
type m_tdef = qual_name raw_tdef