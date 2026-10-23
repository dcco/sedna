
open Dusk_type

	(* int bool is TRUE when UNSIGNED *)
type raw_token = INT of Int64.t * bool * bit_width | FLOAT of float | TRUE | FALSE | NULL
	| STRLIT of string | KLIT of string | T_INT of bool * bit_width
	| ID of string | TID of string | VID of string | CID of string | DIM of int | T_TYPE | T_FN | T_OUT
	| REFERENCES | MODULE | MODULES | AS | IFACE | FTOR | REQUIRES | IMPL | IMPLEMENTS | WITH | END
	| L_LINKER
	| TYPE | STRUCT | ENUM | EXTENDS | ATTRS | UNION | CONST | GLOBALS
	| FN | FNPTR | LIN | VAR | NEW | BY | IF | THEN | ELSIF | ELSE | IS | ISNT
	| LOOP | WHILE | DO | FOR | IN | RETURN
	| MATCH | CASE | OWISE
	| GC_COLLECT | UNDERSCORE
	| EQ | DOT | ELLIP | LPAREN | RPAREN | COMMA | TILDE | QMARK | QQ | AT
	| LBRACE | RBRACE | BAR | LBRACK | RBRACK
	| NEQ | LANGLE | RANGLE | LEQ | GEQ | AND | OR | EXCLAM
	| PLUS | DASH | STAR | SLASH | FLDIV | PERC | EXPO
	| AMPERSAND | CARET | LSHIFT | RSHIFT 
	| PLUS_EQ | SLASH_EQ | EOF

let u64_to_string (i: Int64.t): string =
	Unsigned.UInt64.to_string (Unsigned.UInt64.of_int64 i)

let string_of_xint (i: Int64.t) (u: bool) (bw: bit_width): string =
	let s = if u then u64_to_string i else Int64.to_string i in match bw with
	S32 -> s
	| S8 -> s ^ "b"
	| S16 -> s ^ "s"
	| S64 -> s ^ "l"

let string_of_raw_token tk = match tk with
	INT(i, u, bw) -> string_of_xint i u bw
	| FLOAT f -> string_of_float f
	| STRLIT s -> "\"" ^ (String.escaped s) ^ "\""
	| KLIT s -> "^" ^ s
	| DIM i -> (string_of_int i) ^ "d"
	(*| VDIM -> "1v"*)
	| T_INT(u, s) -> string_of_iType u s
	| T_TYPE -> "TYPE"
	| T_FN -> "Fn"
	| T_OUT -> "Out"
	| L_LINKER -> "_linker"
	| TRUE -> "true"
	| FALSE -> "false"
	| NULL -> "null"
	| ID x -> "id:" ^ x
	| TID x -> "tid:" ^ x
	| VID x -> "vid:" ^ x
	| CID x -> "cid:" ^ x
	| REFERENCES -> "references"
	| MODULE -> "module"
	| MODULES -> "modules"
	| AS -> "as"
	| IFACE -> "iface"
	| FTOR -> "ftor"
	| REQUIRES -> "requires"
	| IMPL -> "impl"
	| IMPLEMENTS -> "implements"
	| WITH -> "with"
	| END -> "end"
	| TYPE -> "type"
	| STRUCT -> "struct"
	| ENUM -> "enum"
	| EXTENDS -> "extends"
	| ATTRS -> "attrs"
	| UNION -> "union"
	| CONST -> "const"
	| GLOBALS -> "globals"
	| FN -> "fn"
	| FNPTR -> "fnPtr"
	| LIN -> "lin"
	| VAR -> "var"
	| NEW -> "new"
	| BY -> "by"
	| IF -> "if"
	| THEN -> "then"
	| ELSIF -> "elsif"
	| ELSE -> "else"
	| IS -> "is"
	| ISNT -> "isnt"
	| LOOP -> "loop"
	| WHILE -> "while"
	| DO -> "do"
	| FOR -> "for"
	| IN -> "in"
	| MATCH -> "match"
	| CASE -> "case"
	| OWISE -> "owise"
	| RETURN -> "return"
	| GC_COLLECT -> "gc_collect"
	| UNDERSCORE -> "_"
	| EQ -> "="
	| DOT -> "."
	| ELLIP -> ".."
	| LPAREN -> "("
	| RPAREN -> ")"
	| COMMA -> ","
	| TILDE -> "~"
	| QMARK -> "?"
	| QQ -> "??"
	| AT -> "@"
	| LBRACE -> "["
	| RBRACE -> "]"
	| BAR -> "|"
	| LBRACK -> "{"
	| RBRACK -> "}"
	| NEQ -> "!="
	| LANGLE -> "<"
	| RANGLE -> ">"
	| LEQ -> "<="
	| GEQ -> ">="
	| AND -> "&&"
	| OR -> "||"
	| EXCLAM -> "!"
	| PLUS -> "+"
	| DASH -> "-"
	| STAR -> "*"
	| SLASH -> "/"
	| FLDIV -> "/."
	| PERC -> "%"
	| EXPO -> "**"
	| AMPERSAND -> "&"
	| CARET -> "^"
	| LSHIFT -> "<<"
	| RSHIFT -> ">>"
	| PLUS_EQ -> "+="
	| SLASH_EQ -> "/="
	| EOF -> "EOF"

type token = raw_token * Lexing.position

	(* lexer position *)

type l_pos = Lexing.position

let string_of_pos (pos: l_pos) =
	"line " ^ (string_of_int pos.pos_lnum) ^ ", column " ^ (string_of_int (pos.pos_cnum - pos.pos_bol))