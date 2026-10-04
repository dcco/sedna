open Commons.Try_log
open Lex_token
open Dusk_type

	(* parse results *)

type parse_err =
	EOF_Err of string
	| BadToken_Err of token * string
	| BadLValue_Err of token
	| NonIntExp_Err of l_pos
	| BadAttrs_Err of l_pos

type 'a parse_res = ('a, parse_err) try_res

let string_of_parse_err e = match e with
	EOF_Err x -> "End of file reached while parsing " ^ x
	| BadToken_Err((tk, pos), x) ->
		"Bad token `" ^ (string_of_raw_token tk) ^ "` while parsing " ^ x ^ " at " ^ (string_of_pos pos)  ^ "."
	| BadLValue_Err(_, pos) ->
		"Bad lvalue while parsing assignment at " ^ (string_of_pos pos) ^ "."
	| NonIntExp_Err pos ->
		"Expected integer constant for static array initializer dimensions while parsing at " ^ (string_of_pos pos) ^ "."
	| BadAttrs_Err pos ->
		"Unexpected attributes defined for enum without attribute definitions at " ^ (string_of_pos pos) ^ "."

let string_of_parse_res sf r = match r with
	Valid v -> sf v
	| Error e -> string_of_parse_err e

type 'a parser = token list -> ('a * token list) parse_res

	(*
		generic parse combinators
	*)

	(* [] *)

let parseNone (tkList: token list): (unit * token list) parse_res = Valid ((), tkList)

	(* [e e ...] *)

let rec parseList (pf: 'a parser) (chkEnd: raw_token -> bool): 'a list parser = fun tkList -> match tkList with
	(tk, _) :: _ ->
		if chkEnd tk then Valid ([], tkList)
		else let* (vx, tkRemX) = pf tkList
			in let* (vt, tkRem2) = parseList pf chkEnd tkRemX
			in Valid (vx :: vt, tkRem2)
	| _ -> Valid ([], tkList)

	(* [e <sep> e ...] *)

let rec parseSepList (pf: 'a parser) (chkSep: raw_token -> bool): 'a list parser = fun tkList ->
	let* (vx, tkRem) = pf tkList
	in (match tkRem with
		[] -> Valid ([vx], tkRem)
		| (tkX, _) :: tkRem2 -> if not (chkSep tkX) then Valid ([vx], tkRem)
			else let* (vt, tkRem2) = parseSepList pf chkSep tkRem2
				in Valid (vx :: vt, tkRem2)
	)

	(* [e [<sep>] e ...] *)

let rec parseSepListFull (pf: 'a parser) (readSep: raw_token -> 'b option): ('a * ('a * 'b * l_pos) list) parser = fun tkList ->
	let* (vx, tkRem) = pf tkList
	in (match tkRem with
		[] -> Valid ((vx, []), tkRem)
		| (tkX, p) :: tkRem2 -> (match readSep tkX with
			None -> Valid ((vx, []), tkRem)
			| Some xOp ->
				let* ((vx2, vt), tkRem3) = parseSepListFull pf readSep tkRem2 in
				Valid ((vx, (vx2, xOp, p) :: vt), tkRem3)
		)
	)

	(* [e] | [] <end> *)

let parseOpt (pf: 'a parser) (chkAlt: raw_token -> bool): 'a option parser = fun tkList -> match tkList with
	(tk, _) :: _ ->
		if chkAlt tk then Valid (None, tkList)
		else let* (v, tkRem) = pf tkList in Valid (Some v, tkRem) 
	| _ -> Valid (None, tkList)
	
	(* [e ...] | [] <end> *)

let parseOrEmpty (pf: 'a list parser) (chkEnd: raw_token -> bool): 'a list parser = fun tkList -> match tkList with
	(tk, _) :: _ -> if chkEnd tk then Valid ([], tkList) else pf tkList
	| _ -> pf tkList

	(*
		generic parse functions
	*)

let matchTk (tk1: raw_token) (tk2: raw_token): bool = match (tk1, tk2) with
	(ID _, ID _) -> true
	| (INT _, INT _) -> true
	| (STRLIT _, STRLIT _) -> true
	| _ -> tk1 = tk2

let parseTk (tk: raw_token) (x: string): l_pos parser = fun tkList -> match tkList with
	(tkX, pos) :: tkRem -> if matchTk tk tkX then Valid (pos, tkRem) else Error (BadToken_Err((tkX, pos), x))
	| _ -> Error (EOF_Err x)

let parseTkMulti (f: raw_token -> 'a option) (x: string): ('a * l_pos) parser = fun tkList -> match tkList with
	(tk, pos) :: tkRem -> (match f tk with
		None -> Error (BadToken_Err((tk, pos), x))
		| Some v -> Valid ((v, pos), tkRem)
	)
	| _ -> Error (EOF_Err x)
(*
let parseId (debug: string): string parser = fun tkList -> match tkList with
	(ID x, _) :: tkRem -> Valid (x, tkRem)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug)

let parseTId (debug: string): string parser = fun tkList -> match tkList with
	(TID x, _) :: tkRem -> Valid (x, tkRem)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug)

let parseCId (debug: string): string parser = fun tkList -> match tkList with
	(CID x, _) :: tkRem -> Valid (x, tkRem)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug)
*)

let parseBaseId (debug: string): string parser = fun tkList -> match tkList with
	(ID x, _) :: tkRem -> Valid (x, tkRem)
	| (CID x, _) :: tkRem -> Valid (x, tkRem)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug)

let parseDeclTId (debug: string): string parser = fun tkList -> match tkList with
	(TID x, _) :: tkRem -> Valid (x, tkRem)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug)

let parseBaseTId = parseDeclTId

let parseVId (debug: string): string parser = fun tkList -> match tkList with
	(VID x, _) :: tkRem -> Valid (x, tkRem)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug)

let parseDerefId (debug: string): qual_name parser = fun tkList -> match tkList with
	(ID x, _) :: tkRem -> Valid (qn x, tkRem)
	| (CID x, _) :: tkRem -> Valid (qn x, tkRem)
	| (TID q, _) :: tkRem ->
		let* (_, tkRem2) = parseTk DOT debug tkRem in 
		let* (x, tkRem3) = parseBaseId debug tkRem2 in Valid (QN(Some q, x), tkRem3)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug)

let parseDerefTId (debug: string): qual_name parser = fun tkList ->
	let* (q, tkRem) = parseBaseTId debug tkList in (match tkRem with
		(DOT, _) :: tkRem2 ->
			let* (x, tkRem3) = parseBaseTId debug tkRem2 in Valid (QN(Some q, x), tkRem3)
		| _ -> Valid (qn q, tkRem)
	)

type any_id = ParseId of qual_name * l_pos | ParseTId of qual_name * l_pos

let parseDerefXId (debug: string): any_id parser = fun tkList -> match tkList with
	(ID x, p) :: tkRem -> Valid (ParseId(qn x, p), tkRem)
	| (CID x, p) :: tkRem -> Valid (ParseId(qn x, p), tkRem)
	| (TID q, p) :: tkRem -> (match tkRem with
		(DOT, _) :: tkRem2 -> (match tkRem2 with
			(ID y, _) :: tkRem3 -> Valid (ParseId(QN(Some q, y), p), tkRem3)
			| (TID y, _) :: tkRem3 -> Valid (ParseTId(QN(Some q, y), p), tkRem3)
			| tk :: _ -> Error (BadToken_Err(tk, debug))
			| _ -> Error (EOF_Err debug)
		)
		| _ -> Valid (ParseTId(qn q, p), tkRem)
	)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug)

let parseDeclId (debug: string): string parser = fun tkList -> match tkList with
	(ID x, _) :: tkRem -> Valid (x, tkRem)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug)

let parseDeclCId (debug: string): string parser = fun tkList -> match tkList with
	(CID x, _) :: tkRem -> Valid (x, tkRem)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug) 

let parseStrLit (debug: string): string parser = fun tkList -> match tkList with
	(STRLIT x, _) :: tkRem -> Valid (x, tkRem)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug)

	(*
		bracket parse functions
	*)

let parseParenWrap (pf: 'a parser) (x: string): 'a parser = fun tkList ->
	let* (_, tkRem) = parseTk LPAREN x tkList in
	let* (v, tkRem2) = pf tkRem in
	let* (_, tkRem3) = parseTk RPAREN x tkRem2 in
	Valid (v, tkRem3)

let parseBrackWrap (pf: 'a parser) (x: string): 'a parser = fun tkList ->
	let* (_, tkRem) = parseTk LBRACK x tkList in
	let* (v, tkRem2) = pf tkRem in
	let* (_, tkRem3) = parseTk RBRACK x tkRem2 in
	Valid (v, tkRem3)

let parseBraceWrap (pf: 'a parser) (x: string): 'a parser = fun tkList ->
	let* (_, tkRem) = parseTk LBRACE x tkList in
	let* (v, tkRem2) = pf tkRem in
	let* (_, tkRem3) = parseTk RBRACE x tkRem2 in
	Valid (v, tkRem3)

let parseAngleWrap (pf: 'a parser) (x: string): 'a parser = fun tkList ->
	let* (_, tkRem) = parseTk LANGLE x tkList in
	let* (v, tkRem2) = pf tkRem in
	let* (_, tkRem3) = parseTk RANGLE x tkRem2 in
	Valid (v, tkRem3)