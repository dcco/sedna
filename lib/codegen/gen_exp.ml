open Llvm

open Parser.Dusk_ast
open Fin_type
open Fin_ast
open Gen_cont
open Gen_type

	(*
		### CONSTANT GENERATION ###	
	*)

	(* string literal generation *)

let genStrLit (cont: llvm_cont) (env: dusk_env) (s: string): dusk_val =
		(* create (pointer to) string constant data *)
	let i = genRef cont in
	let strVal = const_string context (s ^ "\x00") in
	let structVal = const_struct context
		[| const_int iType (String.length s); strVal |] in
	let structRef = define_global ("_sz" ^ (string_of_int i)) structVal cont.llmod in
	Hashtbl.add env (DStrLit s) (DVal (structRef, LitVT)); (structRef, HeapPtrDT dummyInnerType)

	(* expression generation *)

let genConst (cont: llvm_cont) (env: dusk_env) (c: const): dusk_val = match c with
	IConst(i, u, s) ->
		let t = match s with
			S8 -> i8Type
			| S16 -> i16Type
			| S32 -> iType
			| S64 -> i64Type
		in (const_of_int64 t i (not u), PrimDT t)
	| FConst f -> (const_float fType f, PrimDT fType)
	| BConst b -> (const_int bType (if b then 1 else 0), PrimDT bType)
	| SConst s -> (match Hashtbl.find_opt env (DStrLit s) with
		Some (DVal(v, LitVT)) -> (v, HeapPtrDT dummyInnerType)
		| _ -> genStrLit cont env s
	)
	| NullConst -> (const_null _ptrType, PrimDT _ptrType)
	(*| KConst k -> (match Hashtbl.find_opt env (DKeyLit k) with
		Some (DVal (v, _)) -> (build_load kType v "_kT" cont.builder, PrimDT kType)
		| _ ->
			let v = declare_global kType ("K_" ^ k) cont.llmod in
			Hashtbl.add env (DKeyLit k) (DVal(v, VarVT (PrimDT kType)));
			(build_load kType v "_kT" cont.builder, PrimDT kType)
	)*)

	(*
		### VARIABLE GENERATION ###
	*)

let genLoadVar (cont: llvm_cont) (env: dusk_env) (k: dusk_key) (debugName: string): dusk_val = match Hashtbl.find_opt env k with
	(*Some (DFunVal (v, t)) -> (v, t)
	| *)
	Some (DVal (v, FunVT(t, tr))) -> (v, FunDT(t, tr))
	| Some (DVal (v, FunPtrVT(t, tr))) ->
		(build_load _ptrType v debugName cont.builder, FunDT(t, tr))
	| Some (DVal (v, VarVT t)) ->
		(*print_endline ((string_of_llvalue v) ^ " :: " ^ (string_of_dtype t));*)
		(build_load (genType t) v debugName cont.builder, t)
	| Some _ -> failwith ("BUG: gen_exp.ml - Variable \"" ^ debugName ^ "\" resolved to non-value in generation phase.")
	| None -> failwith ("BUG: gen_exp.ml - Unexpected variable \"" ^ debugName ^ "\" encountered in generation phase.")

	(*
		### BOX USAGE ###
	*)

let lookupBox (debug: string) (env: dusk_env) (boxId: int): llvalue * store_type =
	match Hashtbl.find_opt env (DBox boxId) with
		Some (DBoxVal(vb, tb)) -> (vb, tb)
		| _ -> failwith ("BUG: gen_exp.ml - Ungenerated box " ^ (string_of_int boxId) ^ " encountered in generation phase. " ^ debug)

let genGetBox (debug: string) (env: dusk_env) (boxId: int): dusk_val =
	let (vb, tb) = lookupBox debug env boxId in
	let tb' = storeToBoxType debug tb in (vb, tb')

let genStoreBox (debug: string) (cont: llvm_cont) (env: dusk_env) (boxId: int) (vx: llvalue): dusk_val =
	let (vb, tb) = lookupBox debug env boxId in
	let tb' = storeToBoxType debug tb in
	let alignOpt = alignOfBoxType tb' in
	let vs = build_store vx vb cont.builder in
	Option.iter (fun align -> set_alignment align vs) alignOpt; (vb, tb')

let genStoreRet (debug: string) (cont: llvm_cont) (env: dusk_env) (vx: llvalue): dusk_val =
	let (vb, tb) = (match Hashtbl.find_opt env DRetVar with
		Some (DBoxVal(vb, tb)) -> (vb, tb)
		| _ -> failwith "BUG: gen_exp.ml - No return variable allocated for boxed return."
	) in
	let tb' = storeToBoxType debug tb in
	let alignOpt = alignOfBoxType tb' in
	let vs = build_store vx vb cont.builder in
	Option.iter (fun align -> set_alignment align vs) alignOpt; (vb, tb')

	(*
		### GENERAL POINTER FUNCTIONS ###
	*)

let genPtrLoad (name: string) (debug: string) (cont: llvm_cont) (env: dusk_env)
	((vp, t): store_val) (boxOpt: int option): dusk_val =
	let v = build_load (genStoreType t) vp name cont.builder in
	let t' = storeToValType debug env t in (match (t', boxOpt) with
		(StackPtrDT _, Some boxId) ->
			(*let t_inner' = fst (genInnerType t_inner) in
			let v_inner = build_load t_inner' v ("_inner_" ^ name) cont.builder in*)
			genStoreBox debug cont env boxId v
		| (StackPtrDT _, None) ->
			failwith ("BUG: gen_exp.ml - Attempted to load from pointer that must be boxed without a generated box. " ^ debug)
		| _ -> (v, t')
	)

let toStoreVal (debug: string) (cont: llvm_cont) ((v, t): dusk_val): store_val = match t with
	StackPtrDT t_inner ->
		let t_inner' = fst (genInnerType t_inner) in
		(build_load t_inner' v "_innerT" cont.builder, valToStoreType debug t)
	| _ -> (v, valToStoreType debug t)

let genPtrStore (debug: string) (cont: llvm_cont) (env: dusk_env) ((vp, t): store_val) (vv: llvalue): unit =
		(* - uses the same code as toStoreVal, but we skip generating the store type) *)
	let t' = storeToValType debug env t in (match t' with
		StackPtrDT t_inner ->
			let t_inner' = fst (genInnerType t_inner) in
			let v_inner = build_load t_inner' vv "_innerT" cont.builder in
			ignore (build_store v_inner vp cont.builder)
		| _ -> ignore (build_store vv vp cont.builder)
	)

let genPtrArithInc (name: string) (cont: llvm_cont) ((vp, t): raw_dusk_val) (i: int): llvalue =
	build_gep t vp [|const_int iType i|] name cont.builder

	(*
		### STRUCT FUNCTIONS ###
	*)

let genStructLit (debug: string) (cont: llvm_cont) (vl: dusk_val list): llvalue * store_type array =
	let svl = List.map (toStoreVal debug cont) vl in
	let tau_s = structType (List.map (fun (_, t) -> genStoreType t) svl) in
	let (sVal, _) = List.fold_left (fun (sVal, i) (v, _) ->
		let tempName = "_stInit_" ^ (string_of_int i) ^ "T" in
		let sVal' = build_insertvalue sVal v i tempName cont.builder in (sVal', i + 1)
	) (undef tau_s, 0) svl in (sVal, Array.of_list (List.map snd svl))

let genStructIndexGEP (debug: string) (cont: llvm_cont) ((v, t): dusk_val) (i: int): store_val =
	let t_a = innerValType debug t in
	let tempName = "_slot" ^ (string_of_int i) ^ "PT" in
	let t_s = struct_type context (Array.map genStoreType t_a) in
	(build_gep t_s v [|const_int iType 0; const_int iType i|] tempName cont.builder, t_a.(i))

let rawGenStructIndexGEP (name: string) (cont: llvm_cont) ((v, t): raw_dusk_val) (i: int): llvalue =
	(build_gep t v [|const_int iType 0; const_int iType i|] name cont.builder)

	(*
		### ARRAY FUNCTIONS ###
	*)

let rec genProduct (cont: llvm_cont) (vl: llvalue list): llvalue = match vl with
	[] -> failwith ("BUG: gen_exp.ml - Attempted to multiply empty list of values.")
	| [v] -> v
	| v :: vt -> let vt' = genProduct cont vt in build_mul v vt' "_mulT" cont.builder

let genIndexProd (cont: llvm_cont) (va: llvalue) (vl: llvalue list) (dim: int): llvalue =
	let dimsPtr = genPtrArithInc "_dimsPT" cont (va, gcArrType) 1 in
	let rec gip_rec vl i = match vl with
		[] -> failwith ("BUG: gen_exp.ml - Empty index list found while generating index product.")
		| [v] -> v
		| v :: vt ->
				(* recurse + load dim *)
			let vt' = gip_rec vt (i + 1) in
			let sx = "_dim" ^ (string_of_int i) in
			let sizePtr = rawGenStructIndexGEP (sx ^ "PT") cont (dimsPtr, gcDimsType dim) i in
			let v_size = build_load iType sizePtr (sx ^ "T") cont.builder in
				(* multiply + add *)
			let vm = build_mul vt' v_size "_mulT" cont.builder in
			build_add v vm "_addT" cont.builder
	in gip_rec vl 0

let genArrayIndexGEP (debug: string) (cont: llvm_cont) ((v, t): dusk_val) (vi: llvalue): store_val =
	let t_e = elemOfValType debug t in
	(build_gep (genStoreType t_e) v [|vi|] "_elemPT" cont.builder, t_e)

	(*
		### GC LAYOUT FUNCTIONS ###
	*)

	(*
		genGCType: takes list of offsets, generates a global representing them
	*)

let genGCType (cont: llvm_cont) (f: string) (offsetList: gc_child list): llvalue =
		(* obtain offsets of each pointer value *)
	let ol = List.map (fun o -> match o with
		DirectChild -> const_int iType 0
		| OffsetChild i -> const_int iType i
	) offsetList in
	let offsets_const = const_array iType (Array.of_list ol) in
	let offsets_global = define_global ("tc_offs_" ^ f) offsets_const cont.llmod in
		(* create type information global *)
	let tc_inner = [const_int iType (List.length ol); offsets_global] in
	define_global ("tc_" ^ f) (const_struct context (Array.of_list tc_inner)) cont.llmod

	(*
		safeGetGCType: takes a type, returns the "layout type" corresponding to it (caching when relevant)
	*)

let safeGetGCType (debug: string) (cont: llvm_cont) (env: dusk_env) (tau: g_type): int * llvalue =
	let gcType = gcElemType debug cont env tau in match gcType with
		[] -> (0, const_null _ptrType)
		| [DirectChild] -> (1, const_null _ptrType)
		| _ -> (match Hashtbl.find_opt env (DTAnon tau) with
			None ->
				let tc_elem = genGCType cont "tup" gcType in
				Hashtbl.add env (DTAnon tau) (DLayout tc_elem); (1, tc_elem)
			| Some (DLayout tc_elem) -> (1, tc_elem)
			| Some _ -> failwith "BUG gen_exp.ml - Unexpected value when looking up type layout global."
		)

	(*
		### EXTERNAL ALLOC CALLS ###
	*)

let genAlloc (cont: llvm_cont) (env: dusk_env) (tName: string) (tau_inner: inner_type): dusk_val =
		(* calculate size *)
	let v_size = const_int iType (size_of_type cont (fst (genInnerType tau_inner))) in
		(* lookup type information global *)
	let gc_layout_elem = (match Hashtbl.find_opt env (DTName tName) with
		Some (DTDef (StructTD_C(_, tc))) -> tc
		| _ -> failwith "BUG: gen_exp.ml - Bad type for struct initialization encountered in generation phase."
	) in
		(* heap allocate *)
	let (alloc_fun, alloc_type) = !(cont.gc).gc_alloc in
	let mPtr = build_call alloc_type alloc_fun (Array.of_list [v_size; gc_layout_elem]) "_stPT" cont.builder in
	(mPtr, HeapPtrDT tau_inner)

let genNewArray (cont: llvm_cont) (env: dusk_env) (vSize: llvalue) (dim: int) (tau: g_type): dusk_val =
		(* calculate elem size *)
	let tau_store = toStoreType "(New Array)" env tau in
	let e_size = const_int iType (size_of_type cont (genStoreType tau_store)) in
		(* calc dim space + gc layout type *)
	let dim_size = const_int iType (if dim <= 1 then 0 else size_of_type cont (gcDimsType dim)) in
	let (nest_flag, gc_layout_elem) = safeGetGCType "(New Array)" cont env tau in
		(* gc array alloc call *)
	let (new_arr, new_arr_type) = !(cont.gc).new_array in
	let arrPtr = build_call new_arr_type new_arr
		(Array.of_list [e_size; vSize; dim_size; const_int i8Type nest_flag; gc_layout_elem]) "_arrPT" cont.builder in
	(arrPtr, gcArrValType tau_store)

	(*
		### EXPRESSION GENERATION ###
	*)

let voidVal: dusk_val = (const_int iType 0, PrimDT voidType)

let _revType (t: dusk_type): lltype = match t with
	PrimDT t -> t
	| _ -> iType

let rec genExp (cont: llvm_cont) (env: dusk_env) (e: gen_exp): dusk_val = let bx = cont.builder in match e with
	ConstExpC c -> genConst cont env c
	| VarExpC x -> genLoadVar cont env (DVar x) x 
	| UnaryExpC(xOp, e) ->
		let (v, _tv) = genExp cont env e in
		let tv = _revType _tv in
		let (vf, t) = (match xOp with
			"nop" -> (v, tv)
			| "xneg" -> (build_neg v "_negT" bx, tv)
			| "fneg" -> (build_fneg v "_negT" bx, tv)
			| "bnot" -> (build_not v "_notT" bx, bType)
				(* integer downcasts *)
			| "xtox8_d" -> (build_trunc v i8Type "_castT" bx, i8Type)
			| "xtox16_d" -> (build_trunc v i8Type "_castT" bx, i16Type)
			| "xtox32_d" -> (build_trunc v i8Type "_castT" bx, iType)
				(* integer upcasts *)
			| "utox16_u" -> (build_zext v i16Type "_castT" bx, i16Type)
			| "utox32_u" -> (build_zext v iType "_castT" bx, iType)
			| "utox64_u" -> (build_zext v i64Type "_castT" bx, i64Type)
			| "itoi16_u" -> (build_sext v i16Type "_castT" bx, i16Type)
			| "itoi32_u" -> (build_sext v iType "_castT" bx, iType)
			| "itoi64_u" -> (build_sext v i64Type "_castT" bx, i64Type)
				(* float casts *)
			| "ftoi" -> (build_fptosi v iType "_castT" bx, iType)
			| "itof" -> (build_sitofp v fType "_castT" bx, fType)
			| "utof" -> (build_uitofp v fType "_castT" bx, fType)
				(* misc casts *)
			| "xtoPtr" -> (build_inttoptr v _ptrType "_castT" bx, _ptrType)
			| _ -> failwith ("BUG: gen_exp.ml - Unexpected operator \"" ^ xOp ^ "\" encountered in generation phase.")
		) in (vf, PrimDT t)
	| BinExpC(xOp, e1, e2) ->
		let (v1, _tv) = genExp cont env e1 in
		let tv = _revType _tv in
		let (v2, _) = genExp cont env e2 in
		let (vf, t) = (match xOp with
				(* generic int ops *)
			"xadd" -> (build_add v1 v2 "_addT" bx, tv)
			| "xsub" -> (build_sub v1 v2 "_subT" bx, tv)
			| "xmul" -> (build_mul v1 v2 "_mulT" bx, tv)
			| "xeq" -> (build_icmp Icmp.Eq v1 v2 "_cmpT" bx, bType)
			| "xneq" -> (build_icmp Icmp.Ne v1 v2 "_cmpT" bx, bType)
				(* signed int ops *)
			| "idiv" -> (build_sdiv v1 v2 "_divT" bx, tv)
			| "imod" -> (build_srem v1 v2 "_modT" bx, tv)
			| "ileq" -> (build_icmp Icmp.Sle v1 v2 "_cmpT" bx, bType)
			| "ilt" -> (build_icmp Icmp.Slt v1 v2 "_cmpT" bx, bType)
			| "igeq" -> (build_icmp Icmp.Sge v1 v2 "_cmpT" bx, bType)
			| "igt" -> (build_icmp Icmp.Sgt v1 v2 "_cmpT" bx, bType)
			| "ifdiv" ->
				let v1' = build_sitofp v1 fType "_castAT" bx in
				let v2' = build_sitofp v2 fType "_castBT" bx in
				(build_fdiv v1' v2' "_divT" bx, fType)
				(* unsigned int ops *)
			| "udiv" -> (build_udiv v1 v2 "_divT" bx, tv)
			| "umod" -> (build_urem v1 v2 "_modT" bx, tv)
			| "uleq" -> (build_icmp Icmp.Ule v1 v2 "_cmpT" bx, bType)
			| "ult" -> (build_icmp Icmp.Ult v1 v2 "_cmpT" bx, bType)
			| "ugeq" -> (build_icmp Icmp.Uge v1 v2 "_cmpT" bx, bType)
			| "ugt" -> (build_icmp Icmp.Ugt v1 v2 "_cmpT" bx, bType)
				(* float ops *)
			| "fadd" -> (build_fadd v1 v2 "_addT" bx, tv)
			| "fsub" -> (build_fsub v1 v2 "_subT" bx, tv)
			| "fmul" -> (build_fmul v1 v2 "_mulT" bx, tv)
			| "fdiv" -> (build_fdiv v1 v2 "_divT" bx, tv)
			| "fmod" -> (build_frem v1 v2 "_modT" bx, tv)
			| "feq" -> (build_fcmp Fcmp.Oeq v1 v2 "_cmpT" bx, bType)
			| "fneq" -> (build_fcmp Fcmp.One v1 v2 "_cmpT" bx, bType)
			| "fleq" -> (build_fcmp Fcmp.Ole v1 v2 "_cmpT" bx, bType)
			| "flt" -> (build_fcmp Fcmp.Olt v1 v2 "_cmpT" bx, bType)
			| "fgeq" -> (build_fcmp Fcmp.Oge v1 v2 "_cmpT" bx, bType)
			| "fgt" -> (build_fcmp Fcmp.Ogt v1 v2 "_cmpT" bx, bType)
				(* boolean ops *)
			| "band" -> (build_and v1 v2 "_andT" bx, bType)
			| "bor" -> (build_or v1 v2 "_orT" bx, bType)
				(* enum/ptr ops *)
			| "tag_eq" -> (build_icmp Icmp.Eq v1 v2 "_isT" bx, bType)
			| "ptr_eq" -> (build_icmp Icmp.Eq v1 v2 "_isT" bx, bType)
				(* bitwise ops *)
			| "bit_and" -> (build_and v1 v2 "_bitAndT" bx, tv)
			| "bit_or" -> (build_or v1 v2 "_bitOrT" bx, tv)
			| "bit_xor" -> (build_xor v1 v2 "_bitXorT" bx, tv)
			| _ -> failwith ("BUG: gen_exp.ml - Unexpected operator \"" ^ xOp ^ "\" encountered in generation phase.")
		) in (vf, PrimDT t)
	| CallExpC(boxOpt, ef, el, _) ->
			(* compile sub-expressions, read return type *)
		let (vf, tf) = genExp cont env ef in
		let vl = List.map (fun e -> fst (genExp cont env e)) el in
		let tr = (match tf with
			FunDT(_, tr) -> storeToValType "(Function Call)" env tr
			| _ -> failwith ("BUG: gen_exp.ml - Attempted to perform function call on non-function value in generation phase.")
			(* prepare "box" if return type is stack ptr type *)
		) in (match (tr, boxOpt) with
			(StackPtrDT _, Some boxId) -> 
				let (vb, tb) = genGetBox "(Function Call)" env boxId in
				ignore (build_call (genType tf) vf (Array.of_list (vb :: vl)) "" cont.builder); (vb, tb)
			| (StackPtrDT _, None) ->
				failwith ("BUG: gen_exp.ml - Ungenerated box for boxed function return value.")
			| _ -> (build_call (genType tf) vf (Array.of_list vl) "" cont.builder, tr)
		)
	| BoxExpC(boxId, e, _) ->
		let (v, _) = genExp cont env e in
		genStoreBox "(Boxed Value)" cont env boxId v
	| TagExpC e ->
		let (v, _) = genExp cont env e in
		(build_trunc v tagType "_dropT" bx, PrimDT tagType)
	| EnumExpC tag ->
		let tagLit = (match Hashtbl.find_opt env (DCtor tag) with
			Some (DEnum (IntEV i)) -> const_int tagType i
			| Some (DEnum (GlobalEV vp)) -> build_load tagType vp "_G" bx
			| Some _ -> failwith ("BUG: gen_exp.ml - Enum constructor \"" ^ tag ^ "\" resolved to non-enum constructor.")
			| None -> failwith ("BUG: gen_exp.ml - Unexpected enum \"" ^ tag ^ "\" encountered in generation phase.")
		) in (tagLit, PrimDT tagType)
	| EnumRawExpC e -> 
		let (v, _) = genExp cont env e in
		(build_sext v iType "_liftT" bx, PrimDT iType)
	| TupleExpC(boxId, _, el) ->
		 	(* compile the sub-expressions *)
		let vl = List.map (fun e -> genExp cont env e) el in
		genStoreBox "(Tuple Init)" cont env boxId (fst (genStructLit "(Tuple Init)" cont vl))
		(* RW flag, main expression, struct index, underlying type *)
	| MemoryFieldExpC(rw, e, iOpt) ->
			(* generate sub-expresion *)
		let vp = genExp cont env e in
		let i = (match iOpt with Some i -> i | None -> 0) in
		let vp_i = genStructIndexGEP "(Field Operator)" cont vp i in
		(match rw with
			RC(boxOpt, _) ->
				let loadName = "_elem" ^ (string_of_int i) ^ "T" in 
				genPtrLoad loadName "(Field Operator)" cont env vp_i boxOpt
			| WC ev ->
				let (vv, _) = genExp cont env ev in
				genPtrStore "(Field Operator)" cont env vp_i vv; voidVal
		)
	| NewArrayExpC(dim_l, el, tau) ->
			(* calculate size + dimensions *)
		let res_l = List.map (genExp cont env) dim_l in
		let dim = List.length res_l in
		let v_size = genProduct cont (List.map fst res_l) in
			(* allocate new array *)
		let arrPtr = genNewArray cont env v_size dim tau in 
			(* initialize dimensions *)
		(if dim <= 1 then () else
			let dimsPtr = genPtrArithInc "_dimsPT" cont (fst arrPtr, gcArrType) 1 in
			List.iteri (fun i vd ->
				let dx = "_dim" ^ (string_of_int i) ^ "PT" in
				let dimPtr = build_gep (gcDimsType dim) dimsPtr
					(Array.of_list [const_int iType 0; const_int iType i]) dx bx in
				ignore (build_store vd dimPtr bx)
			) (List.map fst res_l)
		);
			(* calculate array index pointer *)
		let dataSlot = genStructIndexGEP "(New Array Data)" cont arrPtr 3 in
		let dataPtr = genPtrLoad "_dataPT" "(New Array Data)" cont env dataSlot None in
			(* store each value *)
		List.iteri (fun i e ->
			let vPtr = genArrayIndexGEP "(New Array Index)" cont dataPtr (const_int iType i) in
			let (vv, _) = genExp cont env e in
			genPtrStore "(New Array Index)" cont env vPtr vv
		) el; arrPtr
	| ArrayIndexExpC(rw, ea, ix) ->
			(* calculate index *)
		let va = genExp cont env ea in
		let vi = (match ix with
			RawIndexC e -> fst (genExp cont env e)
			| FullIndexC el ->
				let vl = List.map (fun e -> fst (genExp cont env e)) el in
				let dim = List.length vl in
				if dim = 1 then List.hd vl else genIndexProd cont (fst va) vl dim
		) in
			(* calculate array index pointer *)
		let dataSlot = genStructIndexGEP "(Array RW Data)" cont va 3 in
		let dataPtr = genPtrLoad "_dataPT" "(Array RW Data)" cont env dataSlot None in
		let vPtr = genArrayIndexGEP "(Array RW Index)" cont dataPtr vi in
			(* read / write to index *)
		(match rw with
			RC(boxOpt, _) ->
				genPtrLoad "_elemT" "(Array RW Index)" cont env vPtr boxOpt
			| WC ev ->
				let (vv, _) = genExp cont env ev in
				genPtrStore "(Array RW Index)" cont env vPtr vv; (const_int iType 0, PrimDT voidType)
		)
	| ArrayAddExpC(ea, ev) ->
			(* calculate length (final index) *)
		let va = genExp cont env ea in
		let sizePtr = genStructIndexGEP "(Array Addition)" cont va 2 in
		let (vSize, _) = genPtrLoad "_sizeT" "(Array Addition)" cont env sizePtr None in
			(* array grow call *)
		let (arr_grow, grow_type) = !(cont.gc).array_grow in
		ignore (build_call grow_type arr_grow (Array.of_list [fst va]) "" bx);
			(* write to new index *)
		let dataSlot = genStructIndexGEP "(Array Addition)" cont va 3 in
		let dataPtr = genPtrLoad "_dataPT" "(Array Addition)" cont env dataSlot None in
		let vPtr = genArrayIndexGEP "(Array Addition)" cont dataPtr vSize in
		let (vv, _) = genExp cont env ev in
		genPtrStore "(Array Addition)" cont env vPtr vv; voidVal
	| ArrayLengthExpC ea ->
		let (va, _) = genExp cont env ea in
		let sizePtr = rawGenStructIndexGEP "_sizePT" cont (va, gcArrType) 2 in
		genPtrLoad "_sizeT" "(Array Length)" cont env (sizePtr, PrimST iType) None
	| ArrayDimsExpC(i, ea) ->
		let (va, _) = genExp cont env ea in
		let dimsPtr = genPtrArithInc "_dimsPT" cont (va, gcArrType) 1 in
		(dimsPtr, gcDimsValType i)
	| NewStructExpC(tx, el) ->
			(* generate struct value *)
		let res_l = List.map (genExp cont env) el in
		let (sVal, tau_sl) = genStructLit "(Struct Init)" cont res_l in
			(* heap allocate + initialize *)
		let sPtr = genAlloc cont env tx (StructIDT tau_sl) in
		ignore (build_store sVal (fst sPtr) bx); sPtr
	| SizeExpC t ->
		let tau_store = toStoreType "(Size of Type)" env t in
		let size = size_of_type cont (genStoreType tau_store) in
		(const_int i64Type size, PrimDT i64Type)
	| GCNewRootExpC e ->
		let (v, t) = genExp cont env e in
		let (new_root_fun, new_root_type) = !(cont.gc).gc_new_root in
		ignore (build_call new_root_type new_root_fun (Array.of_list [v]) "" bx); (v, t)
	| ConstArrayExpC _ ->
		failwith "BUG: gen_exp.ml - Wrong generation function used for constant-only expression."

	(* special expression generation that only gives constants *)

let rec genConstExp (cont: llvm_cont) (env: dusk_env) (e: gen_exp): dusk_val = (*let bx = cont.builder in*) match e with
	ConstExpC c -> genConst cont env c
	| EnumExpC tag ->
		let tagLit = (match Hashtbl.find_opt env (DCtor tag) with
			Some (DEnum (IntEV i)) -> const_int tagType i
			| Some (DEnum (GlobalEV _)) ->
				failwith ("UNIMPLEMENTED: gen_exp.ml - Enum constructor \"" ^ tag ^ "\" resolved to external (non-constant) constructor.") 
			| Some _ -> failwith ("BUG: gen_exp.ml - Enum constructor \"" ^ tag ^ "\" resolved to non-enum constructor.")
			| None -> failwith ("BUG: gen_exp.ml - Unexpected enum \"" ^ tag ^ "\" encountered in generation phase.")
		) in (tagLit, PrimDT tagType)
	| ConstArrayExpC(dims, el, tau) ->
		let size = List.fold_left (fun i v -> i * v) 1 dims in
		let tau_store = toStoreType "(Constant Array)" env tau in
		let t' = genStoreType tau_store in
			(* define array data vector *)
		let res_l = List.map (genConstExp cont env) el in
		let aVal = const_array t' (Array.of_list (List.map fst res_l)) in
		let rVal = define_global "_rawC" aVal cont.llmod in
			(* define array global *)
		let sVal = const_struct context (Array.of_list ([
			const_int iType (size_of_type cont t');
			const_int iType size;
			const_int iType size;
			rVal] @ (List.map (const_int iType) dims)
		)) in
		let xVal = define_global "_arrC" sVal cont.llmod in
		(xVal, gcArrValType tau_store)
	| _ -> failwith "BUG: gen_exp.ml - Non-constant initializer for global declaration encountered in generation phase."
