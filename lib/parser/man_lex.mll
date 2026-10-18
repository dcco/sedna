{
	open Lexing
	open Dusk_type
	open Lex_token

		(* lexer auxiliary functions *)

	let lexWrap lexbuf t = (t, lexeme_start_p lexbuf)

	let asciiHexLit h = int_of_string ("0" ^ h)

	let stringOfASCII c = String.make 1 (Char.chr c)

	(*let lexSizeChar (size: string): (bit_width * bool) =
		let size' =
			if String.get size 0 = '_' then
				String.sub size 1 ((String.length size) - 1)
			else size
		in let (uc, bc) =
			if String.length size' = 2 then
				(String.get size' 0, String.get size' 1)
			else ('\0', String.get size' 0)
		in let s = match bc with
			"b" | "B" -> S8
			| "s" | "S" -> S16
			| "l" | "L" -> S64
			| _ -> failwith "BUG: man_lex.ml - Bad size token for int used in lexer."
		in (s, uc = 'u' || uc = 'U')

		we're gonna put the 'u' in front for now (as part of the "sign" string)
	*)

	let lexSizeChar (size: string): bit_width =
		let sStrip = (try 
			if String.get size 0 = '_' then String.sub size 1 1 else size
		with Invalid_argument _ ->
			failwith ("BUG: man_lex.mll - Bad size token for int \"" ^ size ^ "\" used in lexer.")
		) in match sStrip with
			"b" | "B" -> S8
			| "s" | "S" -> S16
			| "l" | "L" -> S64
			| _ -> failwith ("BUG: man_lex.mll - Bad size token for int \"" ^ sStrip ^ "\" used in lexer.")

	let full_int_of_string (sign: string) (defU: bool) (iStr: string) (size: string): raw_token =
		let s = if size = "" then S32 else lexSizeChar size in
		let (u, neg) = match sign with
			"" -> (defU, false)
			| "+" -> (false, false)
			| "-" -> (false, true)
			| "_" -> (true, false)
			| _ -> failwith ("BUG: man_lex.ml - Bad sign token for int \"" ^ sign ^ "\" used in lexer.")
		in let i = Int64.of_string iStr
		in INT((if neg then Int64.neg i else i), u, s)
}

let idChar = ['a'-'z' 'A'-'Z' '0'-'9' '_']
let numChar = ['0'-'9']
let hexChar = ['a'-'f' 'A'-'F' '0'-'9']
let sizeChar = ['b''B''s''S''l''L']

	(*| "1v" { lexWrap lexbuf VDIM }*)
	
	(*
	| ("-"? "0x" hexChar+) as h { lexWrap lexbuf (INT (int_of_string h)) }
	| ("-"? numChar+) as i { lexWrap lexbuf (INT (int_of_string i)) }
	| ((numChar+) as b) ("b" | "B") { lexWrap lexbuf (U8 (int_of_string b)) }
	| ((numChar+) as l) ("l" | "L") { lexWrap lexbuf (LONG (Int64.of_string l)) }
	*)

rule token = parse
	| "\r\n" | "\r" | "\n" { new_line lexbuf; token lexbuf }
	| "(*" { comment 1 lexbuf }
	| "--" { comment_line lexbuf }
	| "Fn" { lexWrap lexbuf T_FN }
	| "Out" { lexWrap lexbuf T_OUT }
	| "TYPE" { lexWrap lexbuf T_TYPE }
	| "_linker" { lexWrap lexbuf L_LINKER }
	| "references" { lexWrap lexbuf REFERENCES }
	| "module" { lexWrap lexbuf MODULE }
	| "modules" { lexWrap lexbuf MODULES }
	| "as" { lexWrap lexbuf AS }
	| "iface" { lexWrap lexbuf IFACE }
	| "ftor" { lexWrap lexbuf FTOR }
	| "requires" { lexWrap lexbuf REQUIRES }
	| "impl" { lexWrap lexbuf IMPL }
	| "implements" { lexWrap lexbuf IMPLEMENTS }
	| "with" { lexWrap lexbuf WITH }
	| "end" { lexWrap lexbuf END }
	| "type" { lexWrap lexbuf TYPE }
	| "struct" { lexWrap lexbuf STRUCT }
	| "enum" { lexWrap lexbuf ENUM }
	| "extends" { lexWrap lexbuf EXTENDS }
	| "attrs" { lexWrap lexbuf ATTRS }
	| "union" { lexWrap lexbuf UNION }
	| "const" { lexWrap lexbuf CONST }
	| "globals" { lexWrap lexbuf GLOBALS }
	| "fn" { lexWrap lexbuf FN }
	| "fnPtr" { lexWrap lexbuf FNPTR }
	| "lin" { lexWrap lexbuf LIN }
	| "var" { lexWrap lexbuf VAR }
	| "new" { lexWrap lexbuf NEW }
	| "by" { lexWrap lexbuf BY }
	| "if" { lexWrap lexbuf IF }
	| "then" { lexWrap lexbuf THEN }
	| "elsif" { lexWrap lexbuf ELSIF }
	| "else" { lexWrap lexbuf ELSE }
	| "is" { lexWrap lexbuf IS }
	| "isnt" { lexWrap lexbuf ISNT } 
	| "loop" { lexWrap lexbuf LOOP }
	| "while" { lexWrap lexbuf WHILE }
	| "do" { lexWrap lexbuf DO }
	| "for" { lexWrap lexbuf FOR }
	| "in" { lexWrap lexbuf IN }
	| "return" { lexWrap lexbuf RETURN }
	| "false" { lexWrap lexbuf FALSE }
	| "true" { lexWrap lexbuf TRUE }
	| "null" { lexWrap lexbuf NULL }
	| "gc_collect" { lexWrap lexbuf GC_COLLECT }

	| "I8" { lexWrap lexbuf (T_INT(false, S8)) }
	| "I16" { lexWrap lexbuf (T_INT(false, S16)) }
	| "I32" { lexWrap lexbuf (T_INT(false, S32)) }
	| "I64" { lexWrap lexbuf (T_INT(false, S64)) }
	| "U8" { lexWrap lexbuf (T_INT(true, S8)) }
	| "U16" { lexWrap lexbuf (T_INT(true, S16)) }
	| "U32" { lexWrap lexbuf (T_INT(true, S32)) }
	| "U64" { lexWrap lexbuf (T_INT(true, S64)) }

	| "\"" { strlit (lexeme_start_p lexbuf) "" lexbuf }
	| (['A'-'Z']) as x { lexWrap lexbuf (VID (String.make 1 x)) }
	| ("_"? ['a'-'z'] idChar*) as x { lexWrap lexbuf (ID x) }
	| ("_" ['A'-'Z''_']['A'-'Z''_''0'-'9']*) as x { lexWrap lexbuf (CID x) }
	| ("_"? ['A'-'Z'] idChar*) as x { lexWrap lexbuf (TID x) }
	| ((numChar+) as i) "d" { lexWrap lexbuf (DIM (int_of_string i)) }

	| (("+" | "-")? as s) (("0x" hexChar+) as h) (("_" sizeChar)? as b)
		{ lexWrap lexbuf (full_int_of_string s true h b) }
	| (("+" | "-" | "_")? as s) (numChar+ as i) (sizeChar? as b)
		{ lexWrap lexbuf (full_int_of_string s false i b) }
	
	| ("-"? numChar+ "." numChar+) as f { lexWrap lexbuf (FLOAT (float_of_string f)) }

	| "^" (['a'-'z']+ as k) { lexWrap lexbuf (KLIT k) }
	| "_" { lexWrap lexbuf UNDERSCORE }
	| ".." { lexWrap lexbuf ELLIP }
	| "." { lexWrap lexbuf DOT }
	| "=" { lexWrap lexbuf EQ }
	| "!=" { lexWrap lexbuf NEQ }
	| "<" { lexWrap lexbuf LANGLE }
	| ">" { lexWrap lexbuf RANGLE }
	| "<=" { lexWrap lexbuf LEQ }
	| ">=" { lexWrap lexbuf GEQ }
	| "&&" { lexWrap lexbuf AND }
	| "||" { lexWrap lexbuf OR }
	| "!" { lexWrap lexbuf EXCLAM }
	| "+=" { lexWrap lexbuf PLUS_EQ }
	| "/=" { lexWrap lexbuf SLASH_EQ }
	| "+" { lexWrap lexbuf PLUS }
	| "-" { lexWrap lexbuf DASH }
	| "**" { lexWrap lexbuf EXPO }
	| "*" { lexWrap lexbuf STAR }
	| "/" { lexWrap lexbuf SLASH }
	| "/." { lexWrap lexbuf FLDIV }
	| "%" { lexWrap lexbuf PERC }
	| "&" { lexWrap lexbuf AMPERSAND }
	| "^" { lexWrap lexbuf CARET }
	| "<<" { lexWrap lexbuf LSHIFT }
	| ">>" { lexWrap lexbuf RSHIFT }
	| "(" { lexWrap lexbuf LPAREN }
	| ")" { lexWrap lexbuf RPAREN }
	| "[" { lexWrap lexbuf LBRACE }
	| "]" { lexWrap lexbuf RBRACE }
	| "|" { lexWrap lexbuf BAR }
	| "{" { lexWrap lexbuf LBRACK }
	| "}" { lexWrap lexbuf RBRACK }
	| "," { lexWrap lexbuf COMMA }
	| "~" { lexWrap lexbuf TILDE }
	| "??" { lexWrap lexbuf QQ }
	| "?" { lexWrap lexbuf QMARK }
	| "@" { lexWrap lexbuf AT }
	| eof { lexWrap lexbuf EOF }
	| _ { token lexbuf }
and strlit p x = parse
	| "\r\n" | "\r" | "\n" { new_line lexbuf; token lexbuf }
	| "\"" { (STRLIT x, p) }
	| "\\0" { strlit p (x ^ "\x00") lexbuf }
	| "\\a" { strlit p (x ^ "\x07") lexbuf }
	| "\\b" { strlit p (x ^ "\b") lexbuf }
	| "\\t" { strlit p (x ^ "\t") lexbuf }
	| "\\n" { strlit p (x ^ "\n") lexbuf }
	| "\\v" { strlit p (x ^ "\x0B") lexbuf }
	| "\\f" { strlit p (x ^ "\x0C") lexbuf }
	| "\\r" { strlit p (x ^ "\r") lexbuf }
	| "\\\"" { strlit p (x ^ "\"") lexbuf }
	| "\\'" { strlit p (x ^ "'") lexbuf }
	| "\\\\" { strlit p (x ^ "\\") lexbuf }
	| ("\\x" hexChar hexChar) as h { strlit p ((stringOfASCII (asciiHexLit h)) ^ x) lexbuf}
	| _ as c { strlit p (x ^ (String.make 1 c)) lexbuf }
and comment i = parse
	| "\r\n" | "\r" | "\n" { new_line lexbuf; comment i lexbuf }
	| "(*" { comment (i + 1) lexbuf }
	| "*)" { if i = 1 then token lexbuf else comment (i - 1) lexbuf }
	| _ { comment i lexbuf }
and comment_line = parse
	| "\r\n" | "\r" | "\n" { new_line lexbuf; token lexbuf }
	| _ { comment_line lexbuf }