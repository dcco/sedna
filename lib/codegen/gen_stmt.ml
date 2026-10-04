open Llvm

open Fin_ast
open Gen_cont
open Gen_type
open Gen_exp

	(* statement generation *)

type blockInfo = int * llvalue

let addBlock ((i, fVal): blockInfo) (prefix: string): (llbasicblock * blockInfo) =
	(append_block context (prefix ^ "_" ^ (string_of_int i)) fVal, (i + 1, fVal))

let genAssign (cont: llvm_cont) (env: dusk_env) (x: string) (e: gen_exp): unit =
	let (ve, _) = genExp cont env e in
	(match Hashtbl.find_opt env (DVar x) with
		Some (DVal (vx, tt)) -> (match tt with
			VarVT tau ->
				let alignOpt = alignOfBoxType tau in
				let vs = build_store ve vx cont.builder in
				Option.iter (fun align -> set_alignment align vs) alignOpt
			| _ -> failwith "BUG: gen_stmt.ml - Unexpected assignment to variable of non-value type."
		)
		| Some _ -> failwith "BUG: gen_stmt.ml - Unexpected assignment to non-variable."
		| None -> failwith "BUG: gen_stmt.ml - Unexpected assignment to undeclared variable."
	)

let rec genStmt (cont: llvm_cont) (env: dusk_env) (b: blockInfo) (s: gen_stmt): blockInfo = match s with
	EvalStmtC e -> let _ = genExp cont env e in b
	| AssignStmtC(x, e) -> genAssign cont env x e; b
	| VarStmtC(x, e, _) -> genAssign cont env x e; b
	| ReturnStmtC rv -> let _ = (match rv with
		None -> build_ret_void cont.builder
		| Some e ->
			let (ve, tau_r) = genExp cont env e in
			(match tau_r with
				StackPtrDT tau_inner ->
					let vx = build_load (fst (genInnerType tau_inner)) ve "_retCopy" cont.builder in
					ignore (genStoreRet "(Return Stmt)" cont env vx); build_ret_void cont.builder
				| _ -> build_ret ve cont.builder
			)
	) in b
	| UnreachableStmtC -> ignore (build_unreachable cont.builder); b
	| IfStmtC(ec, body, term1, elseBody, term2) ->
		let (vc, _) = genExp cont env ec in
			(* create branch statement *)
		let (block1, b1) = addBlock b "body" in
		let (block2, b2) = addBlock b1 "else_body" in
		let _ = build_cond_br vc block1 block2 (cont.builder) in
			(* stub out final block when necessary *)
		let (blockF, bx) = if not (term1 && term2) then addBlock b2 "join" else (block2, b2) in
			(* generate block 1 + 2, join when relevant *)
		position_at_end block1 (cont.builder);
		let bx' = genBody cont env bx body in
		if not term1 then ignore (build_br blockF (cont.builder)) else ();
		position_at_end block2 (cont.builder);
		let bf = genBody cont env bx' elseBody in
		if not term2 then ignore (build_br blockF (cont.builder)) else ();
			(* re-position at final join *)
		position_at_end blockF (cont.builder); bf
	| WhileStmtC(ec, body) ->
			(* create loop starting block *)
		let (block1, b1) = addBlock b "cond" in
		ignore (build_br block1 (cont.builder));
		position_at_end block1 (cont.builder);
		let (vc, _) = genExp cont env ec in
			(* create branch statement *)
		let (block2, b2) = addBlock b1 "body" in 
		let (blockF, b3) = addBlock b2 "end" in 
		let _ = build_cond_br vc block2 blockF (cont.builder) in
			(* generate main block, branch to start *)
		position_at_end block2 (cont.builder);
		let bf = genBody cont env b3 body in
		ignore (build_br block1 (cont.builder));
		position_at_end blockF (cont.builder); bf
	| GCCollectStmtC ->
		let (collect_fun, collect_type) = !(cont.gc).gc_collect in
		ignore (build_call collect_type collect_fun (Array.of_list []) "" cont.builder); b

and genBody (cont: llvm_cont) (env: dusk_env) (b: blockInfo) (body: gen_stmt list): blockInfo = match body with
	[] -> b
	| s :: st -> let b' = genStmt cont env b s in genBody cont env b' st
