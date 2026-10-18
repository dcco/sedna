open Lex_token
open Dusk_type

	(*
		######################
		## main AST definition
		######################
	*)

type const =
	IConst of Int64.t * bool * bit_width
	| FConst of float
	| SConst of string
	| BConst of bool
	| NullConst

let i_const i = IConst(Int64.of_int i, false, S32)

type rw = RR | WW

	(* functions parameterized by something other than a pure value *)
type x_op =
		(* previously, ElemOp *)
	TupleIndexOp of int
	| StructFieldOp of rw * string
	| ArrayIndexOp of rw
	| TupleTagOp
	| EnumRawOp
	| MeasureOp
	| ArrayAddOp
	(*| ArrayRemoveOp*)

type ('m, 'ann) exp =
	ConstExp of const * 'ann
	| TConstExp of 'm raw_type * 'ann
		(* selectors *)
	| VarExp of 'm * 'ann
	| OpExp of x_op * 'ann
		(* ctors *)
	| AtCtorExp of 'm * 'ann
	| TupleExp of 'm option * ('m, 'ann) exp list * 'ann
		(* - arity, type annotation, static dimensions, data *)
	| DataArrayExp of int * ('m raw_type) option * int list * ('m, 'ann) exp list * 'ann
		(* - arity, dynamic dimensions, initializer *)
	| FormatArrayExp of int * ('m, 'ann) exp list * ('m, 'ann) exp * 'ann
	| ZeroArrayExp of int * ('m, 'ann) exp list * 'm raw_type * 'ann
	| NewStructExp of 'm * ('m, 'ann) field_init * 'ann
		(* selectors *)
	(*| IsExp of ('m, 'ann) exp * 'm option * 'ann*)
		(* function call *)
	| AppExp of ('m, 'ann) exp * ('m, 'ann) exp list * 'ann
and ('m, 'ann) field_init = (string * ('m, 'ann) exp) list

type pat =
	VarPat of string
	| ListPat of (string option) list 

type range_type = LtRange | LeqRange | ListRange

type ('m, 'ann) stmt =
	EvalStmt of ('m, 'ann) exp * 'ann
	| AssignStmt of 'm * ('m, 'ann) exp * 'ann
	| ReturnStmt of ('m, 'ann) exp option * 'ann
	| PatStmt of pat * ('m, 'ann) exp * 'ann
	| IfStmt of ('m, 'ann) exp * ('m, 'ann) stmt list * ('m, 'ann) stmt list * 'ann
	| WhileStmt of ('m, 'ann) exp * ('m, 'ann) stmt list * 'ann
	| ForStmt of string * range_type * ('m, 'ann) exp * ('m, 'ann) stmt list * 'ann
	| GCCollectStmt of 'ann

	(*
		######################
		## position annotation
		######################
	*)

type m_field_init = (qual_name, l_pos) field_init
type m_exp = (qual_name, l_pos) exp
type m_stmt = (qual_name, l_pos) stmt

	(* annotation reader *)

let ann_exp e = match e with
	ConstExp(_, a) -> a
	| TConstExp(_, a) -> a
	| OpExp(_, a) -> a
	| VarExp(_, a) -> a
	| AtCtorExp(_, a) -> a
	| TupleExp(_, _, a) -> a
	| DataArrayExp(_, _, _, _, a) -> a
	| FormatArrayExp(_, _, _, a) -> a
	| ZeroArrayExp(_, _, _, a) -> a
	| NewStructExp(_, _, a) -> a
	(*| IsExp(_, _, a) -> a*)
	| AppExp(_, _, a) -> a

let ann_stmt s = match s with
	EvalStmt(_, a) -> a
	| AssignStmt(_, _, a) -> a
	| ReturnStmt(_, a) -> a
	| PatStmt(_, _, a) -> a
	| IfStmt(_, _, _, a) -> a
	| WhileStmt(_, _, a) -> a
	| ForStmt(_, _, _, _, a) -> a
	| GCCollectStmt a -> a

	(*
		######################
		## module declarations
		######################
	*)

type lin_flag = Fn | Lin

type ('m, 'ann) met =
	Method of lin_flag * 'm * (string * 'm raw_type) list * 'm raw_type * ('m, 'ann) stmt list

(*type ('m, 'ann) attr_case = 'm enum_case * ('m, 'ann) field_init*)
type ('m, 'ann) attr_case = 'm * (('m, 'ann) exp list)

type ('m, 'ann) dec =
	FunDec of ('m, 'ann) met * 'ann
	| TDefDec of 'm * 'm raw_tdef * 'ann
	| AttrsDec of 'm * 'm field_list * ('m, 'ann) attr_case list * 'ann
	(*| ExtendsDec of 'm * 'm field_list * ('m, 'ann) attr_case list * 'ann*)
	| ConstDec of 'm * ('m, 'ann) exp * 'ann
	| GlobalsDec of 'm * 'm option * ('m * ('m, 'ann) exp) list * 'ann

type 'ann req =
	ShortRefReq of string list * string option * 'ann
	| LongRefReq of string list * string list * 'ann

type ('m, 'ann) section =
	Section of 'ann req list * ('m, 'ann) dec list

let ann_req r = match r with
	ShortRefReq(_, _, a) -> a
	| LongRefReq(_, _, a) -> a

	(* table of contents *)

type ('m, 'ann) fun_header =
	FunHeader of (string * 'm raw_type) list * 'm raw_type * 'ann

type ('m, 'ann) mod_unit =
	TypeDefMU of string * 'ann
(*	| IfaceDefMU of string * (string * ('m, 'ann) fun_header) list * 'ann*)

type ('m, 'ann) _mod =
	Module of string * 'ann req list * ('m, 'ann) mod_unit list * 'ann

type ('m, 'ann) toc =
	Toc of ('m, 'ann) _mod list

type m_met = (qual_name, l_pos) met
type m_attr_case = (qual_name, l_pos) attr_case
type m_dec = (qual_name, l_pos) dec
type m_req = l_pos req
type m_section = (qual_name, l_pos) section

type m_fun_header = (qual_name, l_pos) fun_header
type m_mod_unit = (qual_name, l_pos) mod_unit
type m_mod = (qual_name, l_pos) _mod
type m_toc = (qual_name, l_pos) toc