open Commons.Try_log
open Lex_token
open Dusk_type
open Dusk_ext_lib
open Parse_commons
open Parse_exp

let parseSpecType: (arg_mod * m_type) parser = fun tkList -> match tkList with
	(T_OUT, _) :: tkRem -> let* (t, tkRem2) = parseType tkRem in Valid ((OutArg, t), tkRem2)
	| _ -> let* (t, tkRem) = parseType tkList in Valid ((PlainArg, t), tkRem)
	
let parseSpecParam: (string * arg_mod * m_type) parser = fun tkList ->
	let* ((a, t), tkRem) = parseSpecType tkList in
	let* (x, tkRem2) = parseDeclId "External Binding Parameter" tkRem in
	Valid ((x, a, t), tkRem2)

let parseSpecParamList: (string * arg_mod * m_type) list parser = fun tkList -> match tkList with
	(RPAREN, _) :: _ -> Valid ([], tkList)
	| _ -> parseSepList parseSpecParam chkComma tkList

let parseFnRename: string option parser = fun tkList -> match tkList with
	(AS, _) :: tkRem ->
		let* (x, tkRem2) = parseDeclId "External Function Rename" tkRem in
		Valid (Some x, tkRem2)
	| _ -> Valid (None, tkList)

let parseStrLit (debug: string): string parser = fun tkList -> match tkList with
	(STRLIT s, _) :: tkRem -> Valid (s, tkRem)
	| tk :: _ -> Error (BadToken_Err(tk, debug))
	| _ -> Error (EOF_Err debug)
	
let parseFnContent (ptrFlag: bool) (p: l_pos): ext_dec parser = fun tkList ->
	let* (f, tkRem) = parseDeclId "External Function Binding" tkList in
	let* (pl, tkRem2) = parseParenWrap parseSpecParamList "External Binding Parameter List" tkRem in
	let* (tau_r, tkRem3) = parseRetTy tkRem2 in
	let* (rf, tkRem4) = parseFnRename tkRem3 in
	Valid (FnExt(ptrFlag, f, rf, pl, tau_r, p), tkRem4)

let parseExtDec: ext_dec parser = fun tkList -> match tkList with
	(L_LINKER, p) :: tkRem ->
		let* (_, tkRem2) = parseTk REFERENCES "Linker Info" tkRem in
		let* (sl, tkRem3) = parseList (parseStrLit "Linker String") chkPureEnd tkRem2 in
		let* (_, tkRem4) = parseTk END "Linker Info" tkRem3 in
		Valid (LinkerExt(sl, p), tkRem4)
	| (TYPE, p) :: tkRem ->
		let* (x, tkRem2) = parseDeclTId "External Type" tkRem in Valid (TypeExt(x, p), tkRem2)
	| (FN, p) :: tkRem -> parseFnContent false p tkRem
	| (FNPTR, p) :: tkRem -> parseFnContent true p tkRem
	| tk :: _ -> Error (BadToken_Err(tk, "External Lib Dec"))
	| _ -> Error (EOF_Err "External Lib Dec")

let parseExtIface (tkList: token list): (ext_dec list) parse_res =
	let* (dList, _) = (parseList parseExtDec neverEnd) tkList in Valid dList