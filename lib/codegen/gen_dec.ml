open Llvm
open Llvm_analysis
open Llvm_target

open Parser.Dusk_type
open Builtin.Builtin_core
open Fin_type
open Fin_ast
open Gen_cont
open Gen_type
open Gen_exp
open Gen_stmt

	(*
		pre-function allocation generation
	*)

let genParamList (cont: llvm_cont) (env: dusk_env) (pl: (string * g_type) list) (tau_r: g_type) (v: llvalue): dusk_env =
	let env' = Hashtbl.copy env in
	let va = params v in
	let rec gpl_rec pl i = match pl with
		[] -> ()
		| (x, tau) :: pt ->
				(* read type + alignment *)
			let tx = toValType "Parameter List" env tau in
			let alignOpt = alignOfBoxType tx in
				(* store the actual value passed in into a variable for the alloca *)
			let vx = build_alloca (genType tx) ("_" ^ x) cont.builder in
			let vs = build_store (Array.get va i) vx cont.builder in
				(* align + add to env *)
			Option.iter (fun align -> set_alignment align vx; set_alignment align vs) alignOpt;
			Hashtbl.add env' (DVar x) (DVal (vx, VarVT tx)); gpl_rec pt (i + 1)
	in let startId =
		let tau_store = toStoreType "(Parameter List Return)" env tau_r in
		(match storeToValType "(Parameter List Return)" env tau_store with
			StackPtrDT _ ->
				let vp = DBoxVal(Array.get va 0, tau_store) in
				Hashtbl.add env' DRetVar vp; 1
			| _ -> 0
		)
	in try 
		gpl_rec pl startId; env'
	with Invalid_argument _ ->
		failwith ("BUG: gen_dec.ml - OOB parameter list access.")

let genPreAlloc (cont: llvm_cont) (env: dusk_env) (b: gen_stmt list): unit =
	let varList = collect_var_body b in
	List.iter (fun (x, tau) ->
		let tx = toValType "(Variable Alloc)" env tau in
		let vx = build_alloca (genType tx) ("_" ^ x) cont.builder in
		Hashtbl.add env (DVar x) (DVal(vx, VarVT tx))
	) varList;
	let boxList = collect_box_body b in
	List.iter (fun (i, t_b) -> (match t_b with
		VBoxTy tau ->
			let tau_store = toStoreType "(Box Alloc)" env tau in
			let v = build_alloca (genStoreType tau_store) "_boxT" cont.builder in
			Option.iter (fun align -> set_alignment align v) (alignOfStoreType tau_store);
			Hashtbl.add env (DBox i) (DBoxVal (v, tau_store))
	)) boxList

	(*
		type definition generation
	*)

let genStructTD (cont: llvm_cont) (env: dusk_env) (f: string) (fl: (string * g_type) list): unit =
		(* add temp type w/out layout for recursive type generation *)
	let tau_l = List.map snd fl in
	Hashtbl.add env (DTName f) (DTDef (StructTD_C(Array.of_list tau_l, const_null _ptrType)));
		(* build layout struct *)
	let offsetList = gcElemTypeList "(Struct Type Dec)" cont env 0 tau_l in
	let tc_struct = (match offsetList with
		[] -> const_null _ptrType
		| [DirectChild] -> const_null _ptrType
		| _ -> genGCType cont f offsetList
	) in
		(*
			add struct w/ layout type
			- ignores alignment, values must be copied out
		*)
	Hashtbl.replace env (DTName f) (DTDef (StructTD_C(Array.of_list tau_l, tc_struct)))

let rec genEnumTD (cont: llvm_cont) (env: dusk_env) (i: int) (cl: (canon_name union_case) list): unit = match cl with
	[] -> ()
	| (name, _, ext_o) :: ct ->
		(* - ignores alignment, value must be copied out *)
		let (v, i') = (match ext_o with
			NoEB -> (DEnum (IntEV i), i + 1)
			| IntEB j -> (DEnum (IntEV j), j + 1)
			| GlobalEB ext -> (DEnum (GlobalEV (declare_global tagType ext cont.llmod)), i + 1)
		) in
		Hashtbl.add env (DCtor (cr name)) v;
		genEnumTD cont env i' ct

let genUnionTD (cont: llvm_cont) (env: dusk_env) (f: string) (cl: (canon_name union_case) list): unit =
	let zero_size = size_of_type cont tagType in
	let max_size = List.fold_left max zero_size (List.map (fun (_, tau_l, _) ->
		size_of_type cont (genTagCaseType env tau_l)
	) cl) in
	let max_align = List.fold_left max zero_size (List.map (fun (_, tau_l, _) ->
		align_of_type cont (genTagCaseType env tau_l)
	) cl) in
	Hashtbl.add env (DTName f) (DTDef (OpaqueTD_C(max_size, max_align)));
	genEnumTD cont env 0 cl

let rec genTDef (cont: llvm_cont) (env: dusk_env) (f: string) (td: g_tdef): unit = match td with
	TFunTD(_, td') -> genTDef cont env f td'
	| StructTD fl -> genStructTD cont env f fl
	| EnumTD cl ->
		Hashtbl.add env (DTName f) (DTDef EnumTD_C);
			(* - filler datatypes for data-less enums *)
		genEnumTD cont env 0 (List.map (fun (x, ext) -> (x, [], ext)) cl)
	| UnionTD cl -> genUnionTD cont env f cl
	| ExternTD -> Hashtbl.add env (DTName f) (DTDef UnknownTD_C)

	(*
		declaration generation
	*)

let genDec (cont: llvm_cont) (env: dusk_env) (initFun: llvalue) (f: string) (d: gen_dec): unit = match d with
	FunDecC (MethodC(pl, tau_r, b)) ->
			(* generate function type, declare function *)
		let fType = genFunType "(Function Dec)" env (List.map snd pl) tau_r in
		let fVal = declare_function f fType cont.llmod in
			(* begin generation *)
		let block = append_block context "entry" fVal in
		position_at_end block cont.builder;
			(* - insert call to global init if inside MAIN *)
		(if f = "_none_main" then
			let fType = function_type voidType (Array.of_list []) in
			ignore (build_call fType initFun (Array.of_list []) "" cont.builder)
		else ());
			(* - add recursive reference to function handle *)
		let tau_r' = toStoreType "(Return Type)" env tau_r in
		Hashtbl.add env (DVar f) (DVal(fVal, FunVT(fType, tau_r')));
			(* generate function *)
		let env' = genParamList cont env pl tau_r fVal in
		genPreAlloc cont env' b;
		ignore (genBody cont env' (1, fVal) b)
	| TDefDecC td -> genTDef cont env f td
	(*| TDefDecC (TFunTD(_, td)) -> genDec cont env initFun f (TDefDecC td)
	| TDefDecC (StructTD fl) -> genStructTD cont env f fl
	| TDefDecC (EnumTD cl) ->
		Hashtbl.add env (DTName f) (DTDef EnumTD_C);
			(* - filler datatypes for data-less enums *)
		genEnumTD cont env 0 (List.map (fun (x, ext) -> (x, [], ext)) cl)
	| TDefDecC (UnionTD cl) -> genUnionTD cont env f cl
	| TDefDecC ExternTD -> Hashtbl.add env (DTName f) (DTDef UnknownTD_C);*)
	| ConstDecC e ->
		let (v, t) = genConstExp cont env e in
		let cVal = define_global f v cont.llmod in
		Llvm.set_global_constant true cVal;
		Hashtbl.add env (DVar f) (DVal(cVal, VarVT t))
	| GlobalDecC tau ->
		let t = toValType "(Global Dec)" env tau in
		let gVal = define_global f (const_null (genType t)) cont.llmod in
		Hashtbl.add env (DVar f) (DVal(gVal, VarVT t))
	| InitDecC _ -> ()

let genDecList (cont: llvm_cont) (env: dusk_env) (initFun: llvalue) (dl: (string * gen_dec) list): unit =
	List.iter (fun (f, d) -> genDec cont env initFun f d) dl

let genInitFun (cont: llvm_cont) (env: dusk_env) (dl: (string * gen_dec) list): unit =
	let fType = function_type voidType (Array.of_list []) in
	let fVal = declare_function "init_globals" fType cont.llmod in
	let block = append_block context "entry" fVal in
	position_at_end block cont.builder;
	ignore (List.fold_left (fun blockInfo (_, d) -> match d with
		InitDecC b -> 
			genPreAlloc cont env b;
			genBody cont env blockInfo b
		| _ -> blockInfo
	) (1, fVal) dl);
	ignore (build_ret_void cont.builder)

	(*
		external generation
	*)

let genGC (cont: llvm_cont): unit =
	let new_arr_type = function_type _ptrType (Array.of_list [iType; iType; iType; i8Type; _ptrType]) in
	let new_arr = declare_function "gc_alloc_array" new_arr_type cont.llmod in
	let grow_type = function_type _ptrType (Array.of_list [_ptrType]) in
	let arr_grow = declare_function "array_grow" grow_type cont.llmod in
	let alloc_type = function_type _ptrType (Array.of_list [iType; _ptrType]) in
	let gc_alloc = declare_function "gc_alloc" alloc_type cont.llmod in
	let new_root_type = function_type voidType (Array.of_list [_ptrType]) in
	let gc_new_root = declare_function "gc_new_root" new_root_type cont.llmod in
	let collect_type = function_type voidType (Array.of_list []) in
	let gc_collect = declare_function "gc_collect" collect_type cont.llmod in
	cont.gc := {
		new_array = (new_arr, new_arr_type);
		array_grow = (arr_grow, grow_type);
		gc_alloc = (gc_alloc, alloc_type);
		gc_new_root = (gc_new_root, new_root_type);
		gc_collect = (gc_collect, collect_type);
	}

let extLoadType (ext: string): int = match ext with
	"png" -> 0
	| "ttf" -> 1
	| "sprite" -> 10
	| _ -> failwith ("BUG: Bad resource file extension \"" ^ ext ^ "\" encountered in generation phase.")

(* let grListTypeLL = structType [iType; _ptrType] *)
let srTypeLL = structType [tagType; iType; _ptrType; _ptrType]
let crTypeLL = structType [tagType; iType; _ptrType; _ptrType; _ptrType]

let genGlobal (cont: llvm_cont) (privateFlag: bool) (g: string) (v: llvalue): llvalue =
	let g = define_global g v cont.llmod in
	set_global_constant true g;
	(if privateFlag then set_linkage Linkage.Private g else ()); g

let genExternals (cont: llvm_cont) (env: dusk_env) (symList: g_virt_bind list): unit =
		(*
			iterate virtual declarations
			- generate external enum/function handles
		*)
	List.iter (fun (f, vd, _) -> match vd with
		SymVD (ExternalSym, (tau_pl, tau_r)) ->
			let fType = genFunType "(External Function Dec)" env tau_pl tau_r in
			let tr = toStoreType "(External Function Dec)" env tau_r in
			let v = declare_function (cr f) fType cont.llmod in
			Hashtbl.add env (DVar (cr f)) (DVal(v, FunVT(fType, tr)))
		| SymVD (ExternalSym2(ff, ptrFlag, _), (tau_pl, tau_r)) ->
			let fType = genFunType "(External Function Dec)" env tau_pl tau_r in
			let tr = toStoreType "(External Function Dec)" env tau_r in
			if ptrFlag then
				let v = declare_global _ptrType ff cont.llmod in
				Hashtbl.add env (DVar (cr f)) (DVal(v, FunPtrVT(fType, tr)))
			else
				let v = declare_function ff fType cont.llmod in
				Hashtbl.add env (DVar (cr f)) (DVal(v, FunVT(fType, tr)))
		| SymVD _ -> ()
		| TDefVD td -> genTDef cont env (cr f) td
		(*| TDefVD (StructTD fl) -> genStructTD cont env (cr f) fl
		| TDefVD (EnumTD cl) ->
			Hashtbl.add env (DTName (cr f)) (DTDef EnumTD_C);
			(* - filler datatypes for data-less enums *)
			genEnumTD cont env 0 (List.map (fun (x, ext) -> (x, [], ext)) cl)
		| TDefVD (UnionTD cl) -> genUnionTD cont env (cr f) cl
		| TDefVD ExternTD -> Hashtbl.add env (DTName (cr f)) (DTDef UnknownTD_C)*)
	) symList

	(*
		code generation hook
		- pre-initializes context data structures so LLVM content doesn't end up as a dependency outside the library
	*)

let printAllTargets (): unit =
	let targetList = Target.all () in
	ignore (List.map (fun t -> print_string ((Target.name t) ^ " -- " ^ (Target.description t) ^ "\n")) targetList)

let genTarget (targetArg: string option) (optimizeFlag: bool): (llvm_cont * TargetMachine.t) =
	let newCont = Gen_cont.newLCont () in
		(* get target *)
	let target = (match targetArg with None -> Target.default_triple () | Some x -> x) in
	let ttx = Target.by_triple target in
	(*print_endline ("target: " ^ target);*)
	set_target_triple target newCont.llmod;
		(* create target machine *)
	let level = if optimizeFlag then CodeGenOptLevel.Aggressive else CodeGenOptLevel.None in
	let tm = TargetMachine.create ~triple:target ~cpu:"generic" ~features:"" ~level:level
		~reloc_mode:RelocMode.Default ~code_model:CodeModel.Default ttx in
		(* get data layout from target machine *)
	let layout = TargetMachine.data_layout tm in
	let cont = { newCont with data_layout = layout } in
	set_data_layout (DataLayout.as_string layout) (cont.llmod); (cont, tm)

let genFinalize (cont: llvm_cont) (tm: TargetMachine.t) (fname: string): unit =
	let oc = open_out "log.ll" in
	output_string oc ("\n" ^ (string_of_llmodule cont.llmod));
	close_out oc; assert_valid_module cont.llmod;
	TargetMachine.emit_to_file cont.llmod (CodeGenFileType.ObjectFile) (fname ^ ".o") tm;
	TargetMachine.emit_to_file cont.llmod (CodeGenFileType.AssemblyFile) (fname ^ ".xx") tm

let genProgramHook (targetArg: string option) (binDir: string) (optimizeFlag: bool)
	(symList: g_virt_bind list) (dl: (string * gen_dec) list): unit =
	let (cont, tm) = genTarget targetArg optimizeFlag in
	let env = Hashtbl.create 50 in
	genGC cont;
	genExternals cont env symList;
	let vInit = declare_function "init_globals" (function_type voidType (Array.of_list [])) cont.llmod in
	genDecList cont env vInit dl;
	genInitFun cont env dl;
	genFinalize cont tm (binDir ^ "/main");;