open Parser.Lex_token
open Commons.Tree_map
open Parser.Dusk_type
open Parser.Dusk_ext_lib

	(*
		virtual declarations: special declarations to "compile" builtin functions / types
		* symbols: < builtin functions, and what they should compile to >
		-- binary expression ASM
		-- internal bindings
			< miscellaneous special function that executes at compile-time >
		-- external bindings
			< int list determines which parameters are "outside" >
		-- user-defined: < not a builtin function >
		* type definition: < builtin types w/ a concrete definition (mostly ADTs) >
	*)

type raw_bind =
	PrimBind of string
	| RawBind of string

let pb x = PrimBind x
let rb x = RawBind x

type sym =
	UnaryASMSym of string
	| BinaryASMSym of string
	| InternalSym of string
	| ExternalSym
		(* binding name, function ptr flag, argument modifiers *)
	| ExternalSym2 of string * bool * arg_mod list
	| UserDefSym

type 'm virt_dec =
	SymVD of sym * 'm fun_type
	| TDefVD of 'm raw_tdef

type ('b, 'm) virt_bind = 'b * 'm virt_dec * l_pos

type m_virt_bind = (raw_bind, qual_name) virt_bind

	(*
		builtins
	*)

let toVirtList (rawList: (string * sym * m_type list * m_type) list): m_virt_bind list =
	List.map (fun (x, v, tau_pl, tau_r) -> (rb x, SymVD(v, (tau_pl, tau_r)), Lexing.dummy_pos)) rawList

let cStringTy = CPtrTy u8Ty

let anyIntCoreList intTy = [
	("neg", UnaryASMSym "xneg", [intTy], intTy);
	("add", BinaryASMSym "xadd", [intTy; intTy], intTy);
	("sub", BinaryASMSym "xsub", [intTy; intTy], intTy);
	("mul", BinaryASMSym "xmul", [intTy; intTy], intTy);
	("eq", BinaryASMSym "xeq", [intTy; intTy], boolTy);
	("neq", BinaryASMSym "xneq", [intTy; intTy], boolTy);

	("bitNeg", UnaryASMSym "bit_neg", [intTy], intTy);
	("bitAnd", BinaryASMSym "bit_and", [intTy; intTy], intTy);
	("bitOr", BinaryASMSym "bit_or", [intTy; intTy], intTy);
	("bitXor", BinaryASMSym "bit_xor", [intTy; intTy], intTy);

	("toRawOffset", UnaryASMSym "xtoPtr", [intTy], CPtrTy u8Ty);
]

let signIntCoreList intTy = [
	("div", BinaryASMSym "idiv", [intTy; intTy], intTy);
	("mod", BinaryASMSym "imod", [intTy; intTy], intTy);
	("flDiv", BinaryASMSym "ifdiv", [intTy; intTy], floatTy);
	("leq", BinaryASMSym "ileq", [intTy; intTy], boolTy);
	("lt", BinaryASMSym "ilt", [intTy; intTy], boolTy);
	("geq", BinaryASMSym "igeq", [intTy; intTy], boolTy);
	("gt", BinaryASMSym "igt", [intTy; intTy], boolTy);

	("toFloat", UnaryASMSym "itof", [intTy], floatTy);
]

let unsignIntCoreList intTy = [
	("div", BinaryASMSym "udiv", [intTy; intTy], intTy);
	("mod", BinaryASMSym "umod", [intTy; intTy], intTy);
	("leq", BinaryASMSym "uileq", [intTy; intTy], boolTy);
	("lt", BinaryASMSym "ult", [intTy; intTy], boolTy);
	("geq", BinaryASMSym "ugeq", [intTy; intTy], boolTy);
	("gt", BinaryASMSym "ugt", [intTy; intTy], boolTy);

	("toFloat", UnaryASMSym "utof", [intTy], floatTy);
]

let varTy x = VarTy x

let builtinList =
	anyIntCoreList i8Ty @
	anyIntCoreList i16Ty @
	anyIntCoreList i32Ty @
	anyIntCoreList i64Ty @
	anyIntCoreList u8Ty @
	anyIntCoreList u16Ty @
	anyIntCoreList u32Ty @
	anyIntCoreList u64Ty @
	signIntCoreList i8Ty @
	signIntCoreList i16Ty @
	signIntCoreList i32Ty @
	signIntCoreList i64Ty @
	unsignIntCoreList u8Ty @
	unsignIntCoreList u16Ty @
	unsignIntCoreList u32Ty @
	unsignIntCoreList u64Ty @
	[
		(* float point ops *)
	("neg", UnaryASMSym "fneg", [floatTy], floatTy);
	("add", BinaryASMSym "fadd", [floatTy; floatTy], floatTy);
	("sub", BinaryASMSym "fsub", [floatTy; floatTy], floatTy);
	("mul", BinaryASMSym "fmul", [floatTy; floatTy], floatTy);
	("mod", BinaryASMSym "fmod", [floatTy; floatTy], floatTy);
	("flDiv", BinaryASMSym "fdiv", [floatTy; floatTy], floatTy);

	("eq", BinaryASMSym "feq", [floatTy; floatTy], boolTy);
	("neq", BinaryASMSym "fneq", [floatTy; floatTy], boolTy);
	("leq", BinaryASMSym "fleq", [floatTy; floatTy], boolTy);
	("lt", BinaryASMSym "flt", [floatTy; floatTy], boolTy);
	("geq", BinaryASMSym "fgeq", [floatTy; floatTy], boolTy);
	("gt", BinaryASMSym "fgt", [floatTy; floatTy], boolTy);

		(* 
			int down-casting ops
			- unsigned/int downcast into anything the same way
		*)
	("toU8", UnaryASMSym "xtox8_d", [u16Ty], u8Ty);
	("toU8", UnaryASMSym "xtox8_d", [i16Ty], u8Ty);
	("toU8", UnaryASMSym "xtox8_d", [u32Ty], u8Ty);
	("toU8", UnaryASMSym "xtox8_d", [i32Ty], u8Ty);
	("toU8", UnaryASMSym "xtox8_d", [u64Ty], u8Ty);
	("toU8", UnaryASMSym "xtox8_d", [i64Ty], u8Ty);

	("toI8", UnaryASMSym "xtox8_d", [u16Ty], i8Ty);
	("toI8", UnaryASMSym "xtox8_d", [i16Ty], i8Ty);
	("toI8", UnaryASMSym "xtox8_d", [u32Ty], i8Ty);
	("toI8", UnaryASMSym "xtox8_d", [i32Ty], i8Ty);
	("toI8", UnaryASMSym "xtox8_d", [u64Ty], i8Ty);
	("toI8", UnaryASMSym "xtox8_d", [i64Ty], i8Ty);

	("toU16", UnaryASMSym "xtox16_d", [u32Ty], u16Ty);
	("toU16", UnaryASMSym "xtox16_d", [i32Ty], u16Ty);
	("toU16", UnaryASMSym "xtox16_d", [u64Ty], u16Ty);
	("toU16", UnaryASMSym "xtox16_d", [i64Ty], u16Ty);

	("toI16", UnaryASMSym "xtox16_d", [u32Ty], i16Ty);
	("toI16", UnaryASMSym "xtox16_d", [i32Ty], i16Ty);
	("toI16", UnaryASMSym "xtox16_d", [u64Ty], i16Ty);
	("toI16", UnaryASMSym "xtox16_d", [i64Ty], i16Ty);

	("toU32", UnaryASMSym "xtox32_d", [u64Ty], u32Ty);
	("toU32", UnaryASMSym "xtox32_d", [i64Ty], u32Ty);

	("toInt", UnaryASMSym "xtox32_d", [u64Ty], i32Ty);
	("toInt", UnaryASMSym "xtox32_d", [i64Ty], i32Ty);

		(*
			int up-casting ops
			- unsigned ints can upcast to either unsigned OR signed
			- signed ints can only upcast to signed
		*)
	("toU64", UnaryASMSym "utox64_u", [u8Ty], u64Ty);
	("toU64", UnaryASMSym "utox64_u", [u16Ty], u64Ty);
	("toU64", UnaryASMSym "utox64_u", [u32Ty], u64Ty);
	("toI64", UnaryASMSym "utox64_u", [u8Ty], i64Ty);
	("toI64", UnaryASMSym "utox64_u", [u16Ty], i64Ty);
	("toI64", UnaryASMSym "utox64_u", [u32Ty], i64Ty);

	("toU32", UnaryASMSym "utox32_u", [u8Ty], u32Ty);
	("toU32", UnaryASMSym "utox32_u", [u16Ty], u32Ty);
	("toInt", UnaryASMSym "utox32_u", [u8Ty], i32Ty);
	("toInt", UnaryASMSym "utox32_u", [u16Ty], i32Ty);

	("toU16", UnaryASMSym "utox16_u", [u8Ty], u16Ty);
	("toI16", UnaryASMSym "utox16_u", [u8Ty], i16Ty);

	("toI64", UnaryASMSym "itoi64_u", [i8Ty], i64Ty);
	("toI64", UnaryASMSym "itoi64_u", [i16Ty], i64Ty);
	("toI64", UnaryASMSym "itoi64_u", [i32Ty], i64Ty);

	("toInt", UnaryASMSym "itoi32_u", [i8Ty], i32Ty);
	("toInt", UnaryASMSym "itoi32_u", [i16Ty], i32Ty);

	("toI16", UnaryASMSym "itoi16_u", [i8Ty], i16Ty);

		(*
			int (same size) signed-unsigned conversion
		*)
	("toI8", UnaryASMSym "nop", [u8Ty], i8Ty);
	("toI16", UnaryASMSym "nop", [u16Ty], i16Ty);
	("toInt", UnaryASMSym "nop", [u32Ty], i32Ty);
	("toI64", UnaryASMSym "nop", [u64Ty], i64Ty);

	("toU8", UnaryASMSym "nop", [i8Ty], u8Ty);
	("toU16", UnaryASMSym "nop", [i16Ty], u16Ty);
	("toU32", UnaryASMSym "nop", [i32Ty], u32Ty);
	("toU64", UnaryASMSym "nop", [i64Ty], u64Ty);

		(* float casting ops *)
	("toInt", UnaryASMSym "ftoi", [floatTy], intTy);

		(* boolean ops *)
	("not", UnaryASMSym "bnot", [boolTy], boolTy);
	("and", BinaryASMSym "band", [boolTy; boolTy], boolTy);
	("or", BinaryASMSym "bor", [boolTy; boolTy], boolTy);

		(* string ops *)
	("lookup", ExternalSym, [stringTy; intTy], u8Ty);
	("add", ExternalSym, [stringTy; stringTy], stringTy);
	("toString", ExternalSym, [intTy], stringTy);
	("toString", ExternalSym, [floatTy], stringTy);
	("measure", ExternalSym, [stringTy], intTy);
	("eq", ExternalSym, [stringTy; stringTy], boolTy);

		(* math ops *)
	("floor", ExternalSym, [floatTy], intTy);
	("ceil", ExternalSym, [floatTy], intTy);

	("expo", ExternalSym, [floatTy; floatTy], floatTy);
	("sqrt", ExternalSym, [floatTy], floatTy);
	("ln", ExternalSym, [floatTy], floatTy);
	("abs", ExternalSym, [intTy], intTy);
	("abs", ExternalSym, [floatTy], floatTy);
	
	("sin", ExternalSym, [floatTy], floatTy);
	("cos", ExternalSym, [floatTy], floatTy);
	("toRadians", ExternalSym, [intTy], floatTy);

	("color", ExternalSym, [u8Ty; u8Ty; u8Ty], u32Ty);
	("rgb", ExternalSym, [u32Ty], u32Ty);

	("cLoad", InternalSym "cLoad", [stringTy], stringTy);

		(* misc *)
	("panic", ExternalSym, [stringTy], BotTy);

		(* polymorphic functions *)
	("insert", ExternalSym, [ArrayTy(1, varTy "A"); varTy "A"], unitTy);
	("remove", ExternalSym, [ArrayTy(1, varTy "A"); intTy], unitTy);
	("flush", ExternalSym, [ArrayTy(1, varTy "A")], unitTy);
	("clear", ExternalSym, [ArrayTy(1, varTy "A")], unitTy);

		(* byte buffer functions *)
	("addFloat", ExternalSym, [ArrayTy(1, varTy "A"); floatTy], unitTy);
	("addU32", ExternalSym, [ArrayTy(1, varTy "A"); u32Ty], unitTy);
	("addInt", ExternalSym, [ArrayTy(1, varTy "A"); intTy], unitTy);

		(* FFI functions *)
	("cString", ExternalSym, [stringTy], cStringTy);
	("toString", ExternalSym, [cStringTy], stringTy);

		(* FFI polymorphic functions *)
	("cBox", InternalSym "cBox", [varTy "A"], CPtrTy (varTy "A"));
	("cRead", InternalSym "cRead", [CPtrTy (varTy "A")], varTy "A");
	("cAlloc", ExternalSym, [TValTy (varTy "A"); intTy], CPtrTy (varTy "A"));

	("toCPtr", ExternalSym, [ArrayTy(1, varTy "A")], CPtrTy (varTy "A"));
	("toRawPtr", ExternalSym, [ArrayTy(1, varTy "A")], CPtrTy u8Ty);
	("toRawPtr", UnaryASMSym "nop", [CPtrTy (varTy "A")], CPtrTy u8Ty)
]

let prngTy = primTy "PRNG"

let osList = [
	("print", ExternalSym, [stringTy], unitTy);
	("print", ExternalSym, [cStringTy], unitTy);
	
	("randomInt", ExternalSym, [intTy], intTy);
	("randomFloat", ExternalSym, [], floatTy);

	("newPRNG", ExternalSym, [intTy], prngTy);
	("randomInt", ExternalSym, [prngTy; intTy], intTy);
	("randomFloat", ExternalSym, [prngTy], floatTy);
	
	("time", ExternalSym, [], u64Ty);
	("timeNS", ExternalSym, [], u64Ty);
]

	(*
		builtin tree map
	*)

let builtinTreeMap (): (m_virt_bind list) tree_map =
	let m1 = single_tree ["builtin"] (toVirtList builtinList) in
	let m2 = add_tree m1 ["Sys"; "Os"] (toVirtList osList) in
	m2

let extractSymbols (symList: (raw_bind, qual_name) virt_bind list): raw_bind list =
	List.concat (List.map (fun (f, vd, _) -> match vd with
		TDefVD (EnumTD cl) -> f :: (List.map (fun (c, _, _) -> RawBind c) cl)
		| TDefVD (UnionTD cl) -> f :: (List.map (fun (c, _, _, _) -> RawBind c) cl)
		| _ -> [f]
	) symList)