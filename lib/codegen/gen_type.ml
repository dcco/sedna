open Llvm
open Llvm_target

open Parser.Dusk_type
open Fin_type
open Gen_cont

	(*
		LLVM types
		- basic types
	*)

let voidType = void_type context
let i8Type = i8_type context
let tagType = i16_type context
let iType = i32_type context
let i16Type = i16_type context
let i64Type = i64_type context
let fType = float_type context
let f64Type = double_type context
let bType = i1_type context
let _ptrType = pointer_type context

	(* - complex types *)

let structType tau_l = struct_type context (Array.of_list tau_l)

let gcArrType = struct_type context (Array.of_list [iType; iType; iType; _ptrType])
let gcDimsType n = struct_type context (Array.of_list (List.init n (fun _ -> iType)))

	(*
		qualified basic types
	*)

let dummyInnerType = StructIDT [||]

let gcArrValType tau = HeapPtrDT (StructIDT [|
		PrimST iType; PrimST iType; PrimST iType; ArrayPtrST tau
	|])

let gcArrStoreType tau = StructPtrST [|
		ExplDST (PrimST iType);
		ExplDST (PrimST iType);
		ExplDST (PrimST iType);
		ExplDST (ArrayPtrST tau)
	|]

let gcDimsValType n = HeapPtrDT (StructIDT (Array.of_list
		(List.init n (fun _ -> PrimST iType))
	))

(*
let gcArrType tau = HeapPtrDT (StructIDT [|
		PrimST iType; PrimST iType; PrimST iType;
		ArrayPtrST tau
	|])*)

(*let gcArrType = struct_type context (Array.of_list [iType; iType; iType; ptrType]);;

let gcDimsType n = struct_type context (Array.of_list (List.init n (fun _ -> iType)));;
*)

	(*
		// SCRAP
		genType: gives the "main" type for a datatype
			(the one handled in expressions / used in arguments)
	*)

	(*
		genType: gives the final llvm type for a datatype
	*)

let genType (tau: dusk_type): lltype = match tau with	
	PrimDT t -> t
	| FunDT _ -> _ptrType
	| StackPtrDT _ -> _ptrType
	| HeapPtrDT _ -> _ptrType

let genCallType (tau: dusk_type): lltype = match tau with
	FunDT(t, _) -> t
	| _ -> failwith "BUG: Attempted to extract function type from non-function value."

let alignOfBoxType (tau: dusk_type): int option = match tau with
	StackPtrDT (OpaqueIDT(_, i)) -> Some i
	| _ -> None

	(*
		- final llvm types for storage / inside of a pointer type
	*)

let rec genStoreType (tau: store_type): lltype = match tau with
	PrimST t -> t
	| TupleST tau_a -> struct_type context (Array.map genStoreType tau_a)
	| TagTupleST(t, _) -> t
	| StructPtrST _ -> _ptrType
	| ArrayPtrST _ -> _ptrType
	| FunPtrST _ -> _ptrType

let genInnerType (tau: inner_type): lltype * int option = match tau with
	OpaqueIDT(t, i) -> (t, Some i)
	| StructIDT tau_a -> (struct_type context (Array.map genStoreType tau_a), None)
	| ArrayIDT tau -> (genStoreType tau, None)

let alignOfStoreType (tau: store_type): int option = match tau with
	TagTupleST(_, i) -> Some i
	| _ -> None

	(*
		toStoreType: converts TC type into type used for internal storage
	*)

let rec toStoreType (debug: string) (env: dusk_env) (tau: g_type): store_type = match tau with
	PrimTy "Unit" -> PrimST voidType
	| IntTy(_, s) -> (match s with
		S8 -> PrimST i8Type
		| S16 -> PrimST i16Type
		| S32 -> PrimST iType
		| S64 -> PrimST i64Type
	)
	| PrimTy "Float" -> PrimST fType
	| PrimTy "F64" -> PrimST f64Type
	| PrimTy "Bool" -> PrimST bType
	| PrimTy "String" -> PrimST _ptrType
	| PrimTy "PRNG" -> PrimST _ptrType
	| PrimTy "VPtr" -> PrimST _ptrType
	| PrimTy x -> failwith ("BUG: gen_type.ml - Non-existent primitive type \"" ^ x ^ "\". " ^ debug)
	| NamedTy(t, _) -> _namedStoreType debug env t
	| TupleTy(_, tau_l) -> TupleST (Array.of_list (List.map (toStoreType debug env) tau_l))
	(*| TagTupleTy(t, _) -> _namedStoreType debug env t*)
	| ArrayTy(_, tau) -> gcArrStoreType (toStoreType debug env tau)
	| TagOfTy _ -> PrimST tagType
	| FunTy(tau_pl, tau_r) ->
		let tau_f = genFunType debug env tau_pl tau_r in
		(*failwith ("generated fun type: " ^ debug ^ "_" ^ (string_of_lltype tau_f))*)
		FunPtrST(tau_f, toStoreType debug env tau_r)
	(*| FunTy(_, _) -> PrimST _ptrType*)
	| CPtrTy t -> StructPtrST [| ExplDST (toStoreType debug env t) |]
	| NullableTy tau -> toStoreType debug env tau
	| BotTy -> PrimST iType
	(*| NullTy -> failwith ("BUG: gen_type.ml - Null-only type encountered while generating storage type.")*)
		(* this case only comes up as a filler for array functions *)
	| VarTy _ -> PrimST _ptrType
		(* the way a "type value" is actually passed in is as the size of the underlying datatype *)
	| TValTy _ -> PrimST i64Type
		(*failwith ("BUG: gen_type.ml - Variable type encountered while generating storage type.")*)
and _namedStoreType (debug: string) (env: dusk_env) (t: canon_name): store_type =
	match Hashtbl.find_opt env (DTName (cr t)) with
	Some (DTDef td) -> (match td with
		EnumTD_C -> PrimST tagType
		| OpaqueTD_C(i, align) -> TagTupleST(array_type i8Type i, align)
		| StructTD_C(tau_l, _) -> StructPtrST (Array.map (fun t -> ImplDST t) tau_l)
		| UnknownTD_C -> PrimST _ptrType
		(*| StructTD_C(tau_l, _) -> StructPtrST tau_l*)
	) 
	| Some v -> failwith ("BUG: gen_type.ml - Invalid type \"" ^ (cr t) ^
		"\" mapped to unexpected value " ^ (string_of_dval v) ^ " while generating storage type. " ^ debug)
	| None -> failwith ("BUG: gen_type.ml - Invalid type \"" ^ (cr t) ^ "\" encountered while generating storage type." ^ debug)
	
	(*
		storeToValType: converts storage type into its "main" type
			(the one handled in expressions / used in arguments)
			- notably, this involves "boxing" tuple/tag tuple types
			> mutually recursive to support fun type generation
	*)

and storeToValType (debug: string) (env: dusk_env) (tau: store_type): dusk_type = match tau with
	PrimST t -> PrimDT t
	| TupleST tau_a -> StackPtrDT (StructIDT tau_a)
	| TagTupleST(t, align) -> StackPtrDT (OpaqueIDT(t, align))
	| StructPtrST tau_a ->
		let tau_a' = Array.map (fun tau -> match tau with
			ExplDST t -> t | ImplDST t -> toStoreType debug env t
		) tau_a in
		HeapPtrDT (StructIDT tau_a')
	| ArrayPtrST tau -> HeapPtrDT (ArrayIDT tau)
	| FunPtrST(tf, tau_r) -> FunDT(tf, tau_r)

and toValType (debug: string) (env: dusk_env) (tau: g_type): dusk_type =
	storeToValType debug env (toStoreType debug env tau)

and genFunType (debug: string) (env: dusk_env) (tau_pl: g_type list) (tau_r: g_type): lltype =
	let tau_pl' = List.map (fun tau -> genType (toValType debug env tau)) tau_pl in
	match toValType debug env tau_r with
		StackPtrDT _ -> function_type voidType (Array.of_list (_ptrType :: tau_pl'))
		| tau_r' -> function_type (genType tau_r') (Array.of_list tau_pl')

	(*
		valToStoreType: converts a value type into its corresponding storage type
	*)

let valToStoreType (debug: string) (tau: dusk_type): store_type = match tau with
	PrimDT t -> PrimST t
	| FunDT(tf, tau_r) -> FunPtrST(tf, tau_r)
	| HeapPtrDT (StructIDT tau_l) -> StructPtrST (Array.map (fun t -> ExplDST t) tau_l)
	| HeapPtrDT _->
		failwith ("BUG: gen_type.ml - Encountered invalid memory type stored in heap pointer type. " ^ debug)
	| StackPtrDT (OpaqueIDT(t, i)) -> TagTupleST(t, i)
	| StackPtrDT (StructIDT tau_l) -> TupleST tau_l
	| StackPtrDT (ArrayIDT _ ) ->
		failwith ("BUG: gen_type.ml - Encountered direct usage of array stored in stack pointer type. " ^ debug)

	(*
		storeToBoxType: boxes a storage type into its "main" type
	*)

let storeToBoxType (_: string) (tau: store_type): dusk_type = match tau with
	TupleST tau_a -> StackPtrDT (StructIDT tau_a)
	| TagTupleST(t, align) -> StackPtrDT (OpaqueIDT(t, align))
	| _ -> StackPtrDT (StructIDT [| tau |])
	(*| _ -> failwith ("BUG: gen_type.ml - Attempting to box type that should not be boxed. " ^ debug)*)
	(*
	PrimST t -> PrimDT t
	| StructPtrST tau_a -> StackPtrDT (StructIDT (Array.map (toStoreType debug env) tau_a))
	| GCArrayPtrST tau -> StackPtrDT (ArrayIDT (toStoreType debug env tau))*)

	(*
		auxiliary type reading functions
	*)

let innerValType (debug: string) (tau: dusk_type): store_type array =
	let ivt_aux tau_inner = match tau_inner with
		StructIDT tau_a -> tau_a
		| _ -> failwith ("BUG: gen_type.ml - Attempted to index non-struct type in generation phase. " ^ debug)
	in match tau with
		StackPtrDT tau_inner -> ivt_aux tau_inner
		| HeapPtrDT tau_inner -> ivt_aux tau_inner
		| _ -> failwith ("BUG: gen_type.ml - Attempted to index non-struct type in generation phase. " ^ debug)

(*let indexOfValType (debug: string) (tau: dusk_type) (i: int): store_type =
	let iovt_aux tau_inner = match tau_inner with
		StructIDT tau_a ->
			if i >= Array.length tau_a then failwith ("BUG: gen_type.ml - OOB indexed memory access. " ^ debug)
			else tau_a.(i)
		| _ -> failwith ("BUG: gen_type.ml - Attempted to index non-struct type in generation phase. " ^ debug)
	in match tau with
		StackPtrDT tau_inner -> iovt_aux tau_inner
		| HeapPtrDT tau_inner -> iovt_aux tau_inner
		| _ -> failwith ("BUG: gen_type.ml - Attempted to index non-struct type in generation phase. " ^ debug)*)

let elemOfValType (debug: string) (tau: dusk_type): store_type =
	let eovt_aux tau_inner = match tau_inner with
		ArrayIDT tau_a -> tau_a
		| _ -> failwith ("BUG: gen_type.ml - Attempted to read element of non-array type in generation phase. " ^ debug)
	in match tau with
		StackPtrDT tau_inner -> eovt_aux tau_inner
		| HeapPtrDT tau_inner -> eovt_aux tau_inner
		| _ -> failwith ("BUG: gen_type.ml - Attempted to read element of non-array type in generation phase. " ^ debug)

	(*
		miscellaneous type generation functions
	*)

let genTagCaseType (env: dusk_env) (tau_l: g_type list): lltype =
	let tau_l' = List.map (toStoreType "(Tag Tuple)" env) tau_l in
	let tlf = List.map genStoreType tau_l' in
	struct_type context (Array.of_list (tagType :: tlf))

	(*
		garbage collection layout type
		- gcElemType: gives the gc layout for an array element (given as a list of search criterion)
			- direct: searches directly through the given pointer
			- offset: searches at the given offset
			X (DEPRECATED, we're simply not allowing variant offsets) variant: looks up offsets using the variant tag
	*)

type gc_child = DirectChild | OffsetChild of int

let offsetChildList (childList: gc_child list) (offset: int): gc_child list =
	List.map (fun c -> match c with
		DirectChild -> OffsetChild offset
		| OffsetChild i -> OffsetChild (offset + i)
	) childList

let rec gcElemType (debug: string) (cont: llvm_cont) (env: dusk_env) (tau: g_type): gc_child list = match tau with
	NamedTy(t, _) -> (match Hashtbl.find_opt env (DTName (cr t)) with
		Some (DTDef td) -> (match td with
			StructTD_C(_, _) -> [DirectChild]
			| OpaqueTD_C(_, _) -> []
			| _ -> []
		) 
		| _ -> failwith ("BUG: gen_type.ml - Invalid type \"" ^ (cr t) ^ "\" encountered while constructing GC layout for type.")
	)
	| PrimTy "String" -> [DirectChild]
	| ArrayTy(_, _) -> [DirectChild]
	| TupleTy(_, tau_l) -> gcElemTypeList debug cont env 0 tau_l
	(*| ValArrayTy _ -> failwith ("BUG: gen_type.ml - Value-arrays cannot be stored in other data structures.")*)
	| _ -> []
and gcElemTypeList (debug: string) (cont: llvm_cont) (env: dusk_env) (fieldOffset: int) (tau_l: g_type list): gc_child list =
	let tau_s = struct_type context (Array.of_list (List.map (fun t -> genStoreType (toStoreType debug env t)) tau_l)) in
	let childList = ref [] in
	List.iteri (fun i tau ->
		let offset = Int64.to_int (DataLayout.offset_of_element tau_s (i + fieldOffset) cont.data_layout) in
		let childElem = offsetChildList (gcElemType debug cont env tau) offset in
		childList := !childList @ childElem
	) tau_l; !childList

	(*
		size/alignment of a type
	*)

let align_of_type (cont: llvm_cont) (t: lltype): int = DataLayout.abi_align t cont.data_layout

let align_rup (offset: int) (align: int): int = ((offset + align - 1) / align) * align

let size_of_type (cont: llvm_cont) (t: lltype): int = Int64.to_int (DataLayout.abi_size t cont.data_layout)
