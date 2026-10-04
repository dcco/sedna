open Parser.Lex_token
open Parser.Dusk_type
open Parser.Dusk_ast
open Commons.Try_log
open Codegen.Fin_type
open Codegen.Fin_ast
open Tc_err
open Tc_cont

	(*
		value coercion functions
	*)

let as_int (e: gen_exp): Int64.t = match e with
	ConstExpC (IConst(i, _, _)) -> i
	| _ -> failwith "BUG: calc_exp.ml - Found unexpected non-integer value during constant calculation."

let as_float (e: gen_exp): float = match e with
	ConstExpC (FConst f) -> f
	| _ -> failwith "BUG: calc_exp.ml - Found unexpected non-float value during constant calculation."

let as_bool (e: gen_exp): bool = match e with
	ConstExpC (BConst b) -> b
	| _ -> failwith "BUG: calc_exp.ml - Found unexpected non-i64 value during constant calculation."

let read_usize (e: gen_exp): (bool * bit_width) = match e with
	ConstExpC (IConst(_, u, s)) -> (u, s)
	| _ -> (false, S32)

	(*
		compile-time constant expression calculation
	*)

let rec calc_exp (env: type_env) (p: l_pos) (e: gen_exp): gen_exp tc_res = match e with
	ConstExpC c -> Valid (ConstExpC c)
	| EnumExpC tag -> Valid (EnumExpC tag)
	| VarExpC x -> (match Hashtbl.find_opt env.globalIds x with
		Some (_, _, cOpt) -> (match cOpt with
			None -> Error (NonCVar_Err(x, p))
			| Some c -> Valid c
		)
		| _ -> failwith "BUG: calc_exp.ml - Failed variable lookup during type-checking phase."
	)
	| BinExpC(xOp, e1, e2) ->
		let* v1 = calc_exp env p e1 in
		let* v2 = calc_exp env p e2 in
		let (u, s) = read_usize v1 in
		let vf = (match xOp with
			"xadd" -> IConst(Int64.add (as_int v1) (as_int v2), u, s)
			| "xsub" -> IConst(Int64.sub (as_int v1) (as_int v2), u, s)
			| "xmul" -> IConst(Int64.mul (as_int v1) (as_int v2), u, s)
			| "idiv" -> IConst(Int64.div (as_int v1) (as_int v2), u, s)
			| "imod" -> IConst(Int64.rem (as_int v1) (as_int v2), u, s)
			| "fadd" -> FConst((as_float v1) +. (as_float v2))
			| "fsub" -> FConst((as_float v1) -. (as_float v2))
			| "fmul" -> FConst((as_float v1) *. (as_float v2))
			| "fdiv" -> FConst((as_float v1) /. (as_float v2))
			| "fmod" -> FConst(Float.rem (as_float v1) (as_float v2))
			| "xeq" -> BConst((as_int v1) = (as_int v2))
			| "xneq" -> BConst((as_int v1) <> (as_int v2))
			| "ileq" -> BConst((as_int v1) <= (as_int v2))
			| "ilt" -> BConst((as_int v1) < (as_int v2))
			| "igeq" -> BConst((as_int v1) >= (as_int v2))
			| "igt" -> BConst((as_int v1) > (as_int v2))
			| "feq" -> BConst((as_float v1) = (as_float v2))
			| "fneq" -> BConst((as_float v1) <> (as_float v2))
			| "fleq" -> BConst((as_float v1) <= (as_float v2))
			| "flt" -> BConst((as_float v1) < (as_float v2))
			| "fgeq" -> BConst((as_float v1) >= (as_float v2))
			| "fgt" -> BConst((as_float v1) > (as_float v2))
			| "bit_and" -> IConst(Int64.logand (as_int v1) (as_int v2), u, s)
			| "bit_or" -> IConst(Int64.logor (as_int v1) (as_int v2), u, s)
			| "bit_xor" -> IConst(Int64.logxor (as_int v1) (as_int v2), u, s)
			(*
			| "band" -> BConst((as_bool v1) && (as_bool v2))
			| "bor" -> BConst((as_bool v1) || (as_bool v2))
			| "ui64add" -> LConst(Int64.add (as_long v1) (as_long v2))
			| "ui64sub" -> LConst(Int64.sub (as_long v1) (as_long v2))
			| "ui64mul" -> LConst(Int64.mul (as_long v1) (as_long v2))
			| "ui64div" -> LConst(Int64.div (as_long v1) (as_long v2))
			| "ui64mod" -> LConst(Int64.rem (as_long v1) (as_long v2))
			| "tag_eq" -> failwith "UNIMPLEMENTED calc_exp.ml - tag literal constants"
			| "ptr_eq" -> failwith "UNIMPLEMENTED calc_exp.ml - pointer literal constants?"
			| "ifdiv" -> FConst((float_of_int (as_int v1)) /. (float_of_int (as_int v2)))*)
			| _ -> failwith ("BUG: calc_exp.ml - Unexpected operator \"" ^ xOp ^ "\" encountered during constant evaluation.")
		) in Valid (ConstExpC vf)
	| NewArrayExpC(dim_l, el, tau) ->
		let* dim_l' = map_try_res (calc_exp env p) dim_l in
		let dims = List.map (fun v -> Int64.to_int (as_int v)) dim_l' in
		let* el' = map_try_res (calc_exp env p) el in
		Valid (ConstArrayExpC(dims, el', tau))
	| _ -> failwith "UNIMPLEMENTED: calc_exp.ml - Constant expression."

let calc_cfun (env: type_env) (f: string) (el: gen_exp list) (tau: g_type) (p: l_pos): gen_exp tc_res = match (f, el) with
	("cLoad", [ConstExpC (SConst s)]) -> (match env.curDir with
		Some dir -> 
			let fname = dir ^ "/" ^ s in
			if not (Sys.file_exists fname) then Error (BadCLoad_Err(fname, p))
			else (try
				let fc = open_in fname in
				let len = in_channel_length fc in
				let text = really_input_string fc len in
				close_in fc; Valid (ConstExpC (SConst text))
				with _ -> Error (FailCLoad_Err p)
			)
		| _ -> failwith "BUG: calc_exp.ml - Constant expression cLoad with unspecified directory."
	)
	| ("cBox", [e]) -> Valid (BoxExpC(get_box_id_tenv env, e, tau))
	| ("cRead", [e]) -> Valid (MemoryFieldExpC(RC(None, tau), e, Some 0))
	| _ -> failwith "UNIMPLEMENTED: calc_exp.ml - Constant expression cfun failure."