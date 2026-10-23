open Llvm
open Llvm_target

open Parser.Dusk_type
open Fin_type

	(* LLVM initialization *)

let context = global_context ();;

install_fatal_error_handler (fun x -> failwith (x ^ "\n"));;
Llvm_all_backends.initialize ();;

	(*
		garbage collector interface
	*)

type gc_iface = {
	new_array: llvalue * lltype;
	array_grow: llvalue * lltype;
	gc_alloc: llvalue * lltype;
	gc_new_root: llvalue * lltype;
	gc_collect: llvalue * lltype;
}

	(*
		special LLVM builder context
	*)

type llvm_cont = {
	llmod: llmodule;
	data_layout: DataLayout.t;
	builder: llbuilder;
	gc: gc_iface ref;
	uid: int ref;
}

let newLCont (): llvm_cont =
	let m = create_module context "sedna" in
	let ptrType = pointer_type context in {
		llmod = m;
		data_layout = DataLayout.of_string (data_layout m);
		builder = builder context;
		gc = ref {
			new_array = (const_null ptrType, ptrType);
			array_grow = (const_null ptrType, ptrType);
			gc_alloc = (const_null ptrType, ptrType);
			gc_new_root = (const_null ptrType, ptrType);
			gc_collect = (const_null ptrType, ptrType);
		};
		uid = ref 0;
	}

let genRef (cont: llvm_cont): int = cont.uid := !(cont.uid) + 1; !(cont.uid) - 1

	(*
		dusk compilation type definitions:
			- enum: raw enum value
			- opaque: opaque array of bytes used for unions
				(size, alignment, GC type layout)
			- struct: heap-allocated struct + GC type layout
	*)

type dusk_tdef =
	EnumTD_C
	| OpaqueTD_C of int * int
	| StructTD_C of g_type array * llvalue
	| UnknownTD_C

	(*
		dusk type: type of an llvm value augmented w/ the "inner" structure of pointer values
			(assumed to be either a storage struct, or an "opqaue" set of bytes)
		- fun: includes ll function type + detailed return type
		- stack ptr: includes alignment when applicable

		store type: similar, but types for "stored" values (instead of top-level values)
	*)

type store_type =
	PrimST of lltype
	| TupleST of store_type array
	| TagTupleST of lltype * int
	| ArrayPtrST of store_type
	| StructPtrST of deref_type array
	| FunPtrST of lltype * store_type
and deref_type =
	ExplDST of store_type
	| ImplDST of g_type

	(*| StructPtrST of store_type array
	| ArrayPtrST of store_type*)

type dusk_type =
	PrimDT of lltype
	| FunDT of lltype * store_type
	| StackPtrDT of inner_type
	| HeapPtrDT of inner_type
and inner_type =
	OpaqueIDT of lltype * int
	| StructIDT of store_type array
	| ArrayIDT of store_type

let _stringify_arr (f: 'a -> string) (a: 'a array): string =
	String.concat ", " (List.map f (Array.to_list a))

let rec string_of_store_type (t: store_type): string = match t with
	PrimST t -> string_of_lltype t
	| TupleST a -> "(" ^ (_stringify_arr string_of_store_type a) ^ ")"
	| TagTupleST(t, i) -> (string_of_lltype t) ^ " (" ^ (string_of_int i) ^ ")"
	| ArrayPtrST t -> "[" ^ (string_of_store_type t) ^ "]"
	| StructPtrST _ -> "_struct_ptr_type_"
	| FunPtrST _ -> "_fun_ptr_type_"

let string_of_inner_type (t: inner_type): string = match t with
	OpaqueIDT(t, i) -> (string_of_lltype t) ^ " (" ^ (string_of_int i) ^ ")"
	| StructIDT a -> "{" ^ (_stringify_arr string_of_store_type a) ^ "}"
	| ArrayIDT t -> "[" ^ (string_of_store_type t) ^ "]"

let string_of_dtype (t: dusk_type): string = match t with
	PrimDT t -> string_of_lltype t
	| FunDT(t, _) -> "fun< " ^ string_of_lltype t ^ " >"
	| StackPtrDT t -> "stack< " ^ (string_of_inner_type t) ^ " >"
	| HeapPtrDT t -> "heap< " ^ string_of_inner_type t ^ " >"

	(* var type: wraps variables - ensures that a load is done to obtain the underlying type
		a regular variable is always a pointer to a dusk_type, so we treat it accordingly
		- fun: stores the LLVM function type + storage return type
	*)

type var_type =
	VarVT of dusk_type
	| LitVT
	| FunVT of lltype * store_type
	| FunPtrVT of lltype * store_type

	(*
		code generation environment
	*)

type dusk_val = llvalue * dusk_type
type raw_dusk_val = llvalue * lltype
type store_val = llvalue * store_type

type dusk_enum_val = IntEV of int | GlobalEV of llvalue

type dusk_fval =
	(*DVal of llvalue * var_type
	| DGlobal of llvalue * var_type*)
	DVal of llvalue * var_type
	| DBoxVal of llvalue * store_type
	| DTDef of dusk_tdef
	| DEnum of dusk_enum_val
	| DLayout of llvalue

type dusk_key =
	DVar of string
	| DRetVar
	| DStrLit of string
	| DKeyLit of string
	| DBox of int
	| DTName of string
	| DTAnon of g_type
	| DCtor of string
[@@deriving equal, hash]

type dusk_env = (dusk_key, dusk_fval) Hashtbl.t

	(* - TEST fun: used to dump *)

let string_of_dkey (k: dusk_key): string = match k with
	DVar x -> "VAR " ^ x
	| DRetVar -> "RET"
	| DStrLit s -> "STRLIT " ^ s
	| DKeyLit k -> "KLIT " ^ k
	| DBox i -> "BOX " ^ (string_of_int i)
	| DTName t -> "TNAME " ^ t
	| DTAnon t -> "TANON " ^ (string_of_type (fun (CN(x, _)) -> x) t)
	| DCtor c -> "CTOR " ^ c

let string_of_dval (v: dusk_fval): string = match v with
	DVal(_, VarVT _) -> "VAL"
	| DVal(_, LitVT) -> "LIT"
	| DVal(_, FunVT _) -> "FUNC"
	| DVal(_, FunPtrVT _) -> "FPTR"
	| DBoxVal _ -> "BOX"
	(*| DGlobal _ -> "GLOBAL"
	| DFunVal(_, _) -> "FUNC"*)
	| DTDef _ -> "TYPE DEF"
	| DEnum _ -> "ENUM"
	| DLayout _ -> "GC LAYOUT TYPE"

let dump_denv (env: dusk_env): unit =
	print_string "#CODEGEN_ENV {\n";
	Hashtbl.iter (fun k v ->
		print_string ((string_of_dkey k) ^ ": " ^ (string_of_dval v));
		print_string "\n"
	) env;
	print_string "}\n";;