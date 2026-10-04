open Lex_token
open Dusk_type

type arg_mod = PlainArg | OutArg

type ext_dec =
	LinkerExt of string list * l_pos
	| TypeExt of string * l_pos
		(* ptr flag, lang binding, ext binding, parameter list, return type *)
	| FnExt of bool * string * string option * (string * arg_mod * m_type) list * m_type * l_pos