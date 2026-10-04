open Parser.Dusk_type
open Builtin.Builtin_core

	(*
		types for generation
	*)

type g_type = canon_name raw_type
type g_tdef = canon_name raw_tdef

type g_virt_bind = (canon_name, canon_name) virt_bind
(*
type deref_type = TypeDeref of g_type | CtorDeref of string*)