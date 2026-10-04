open Yojson.Safe

open Commons.Try_log
open Commons.Tree_map
open Parser
open Parser.Dusk_ast
open Parser.Dusk_ext_lib
open Parser.Parse_commons
open Parser.Parse_exp
open Parser.Parse_ext_lib
open Builtin
open Resolve
open Resolve.Res_cont
open Resolve.Res_exp
open Tc
open Tc.Tc_err
open Tc.Tc_exp
open Codegen.Fin_ast
open Codegen.Gen_dec

	(*
		preproc phase (incremental steps):
		- handles the compilation steps that happen incrementally (parsing, name resolution)
	*)

let load_token_list (fname: string): (Lex_token.token list) try_log_res =
	if not (Sys.file_exists fname) then failLog ("Could not find file " ^ fname)
	else let fc = open_in fname in
		let lexbuf = Lexing.from_channel fc in
		let rec lex_iter partList = 
			let tk = Man_lex.token lexbuf in
				if fst tk = Lex_token.EOF then List.rev partList
				else lex_iter (tk :: partList) in
		let tkList = lex_iter [] in
		(close_in fc; validLog tkList);;

	(*
		compiler context:
			datatype that determines what compilers to use	
	*)

type compiler_cont = {
	c_compiler: string ref;
	link_libs: (string, unit) Hashtbl.t;
	link_syms: (string, unit) Hashtbl.t;
	link_srcs: (string * string, unit) Hashtbl.t;
}

let init_compiler_cont (winFlag: bool): compiler_cont =
	let comp = if winFlag then "x86_64-w64-mingw32-gcc" else "gcc" in
	{
		c_compiler = ref comp;
		link_libs = Hashtbl.create 10;
		link_syms = Hashtbl.create 10;
		link_srcs = Hashtbl.create 10;
	}

	(*
		library loading:
			loads external C libraries
			- returns external declarations + linker requirements
	*)

let load_ext_lib (cont: compiler_cont) (work_dir: string) (l: string): ext_dec list try_log_res =
	print_string ("Pre-loading external library: " ^ l ^ "\n");
		(* parsing *)
	let*! tkList = load_token_list (work_dir ^ "/" ^ l ^ "/" ^ l ^ ".sdi") in
	let*! dList = tryWithErrLog string_of_parse_err (parseExtIface tkList) in
		(* store linker reqs *)
	Hashtbl.replace cont.link_libs (work_dir ^ "/" ^ l) ();
	List.iter (fun d -> match d with
		LinkerExt(sl, _) -> List.iter (fun s ->
				(* dont link .c files *)
			if Filename.check_suffix s ".c" then
				Hashtbl.replace cont.link_srcs (l, Filename.chop_suffix s ".c") ()
			else Hashtbl.replace cont.link_syms s ()
		) sl
		| _ -> ()
	) dList; validLog dList

(*	Unix.create_process !(cont.c_compiler) [|
		!(cont.c_compiler);
		"-c"; work_dir ^ "/_lib/" ^ l ^ "/" ^ l ^ ".h";
		"-o"; main_dir ^ "/bin/" ^ l ^ ".o"
	|] Unix.stdin Unix.stdout Unix.stderr
*)

(*	*)

	(*
		file context: contextual information about what file is being compiled
			- toplevel
			- external lib: (library directory, file name)
			- library: (directory, file name)
	*)

type file_context =
	TopLevelFC
	| ExtLibFC of string * string
	| LibFC of string * string

let full_name_fc (main_dir: string) (fc: file_context): string = match fc with
	TopLevelFC -> main_dir ^ "/main.sm"
	| ExtLibFC(lib_dir, f) -> lib_dir ^ "/" ^ f
	| LibFC(dir, f) -> main_dir ^ "/" ^ dir ^ "/" ^ f

let full_dir_fc (main_dir: string) (fc: file_context): string = match fc with
	TopLevelFC -> main_dir
	| ExtLibFC(lib_dir, _) -> lib_dir
	| LibFC(dir, _) -> main_dir ^ "/" ^ dir

let is_ext_lib_fc (fc: file_context): bool = match fc with
	ExtLibFC _ -> true
	| _ -> false

	(* pre-comp auxiliaries *)

let mod_req_list (m: m_mod): m_req list = match m with
	Module(_, rl, _, _) -> rl

	(*
		pre-compilation:
			does compilation up to codegen (incrementally).
	*)

type pre_comp_res = (string * gen_dec) list

let print_lib_alert (l: string) (parent: string option): unit = match parent with
	None -> print_string ("Loading library: " ^ l ^ "\n")
	| Some p -> print_string ("Loading library: " ^ l ^ " (Requested by " ^ p ^ ")\n")

let rec pre_compile_lib (resEnv: Res_cont.res_env) (typeEnv: Tc_cont.type_env)
	(main_dir: string) (parent: string option) (libName: string): (pre_comp_res list) try_log_res =
		(* - lex / parse the library TOC *)
	print_lib_alert libName parent;
	let*! tkList = load_token_list (main_dir ^ "/" ^ libName ^ "/" ^ "toc.dt") in
	let*! Toc ml = tryWithErrLog string_of_parse_err (parseToc tkList) in
		(* - load un-compiled libraries *)
	let*! res_pre_ll = mapLogRes (fun m ->
		let rl = mod_req_list m in
		let missingLibList = pre_check_req_list resEnv rl in
		let*! res_pre_ll = mapLogRes (pre_compile_lib resEnv typeEnv main_dir parent) missingLibList
		in validLog (List.concat res_pre_ll)
	) ml in
		(* - compile modules *)
	print_string ("Compiling library: " ^ libName ^ "\n");
	let*! res_l = mapLogRes (fun m -> match m with
		Module(m, rl, xl, _) ->
			print_string ("- Module: " ^ m ^ "\n");
				(* - resolve requirements (freeze imports) *)
			let resEnv' = Res_cont.freeze_env resEnv [libName; m] in
			let*! _ = tryWithErrLog string_of_rs_err (resolve_req_list resEnv' rl) in
				(* - compile individual files *)	
			let*! res_m = mapLogRes (fun mu ->
				pre_compile_mod_unit resEnv' typeEnv main_dir (libName ^ "/" ^ m) mu
			) xl in
			save_local_dec_renv resEnv' [libName; m]; validLog res_m
	) ml in validLog ((List.concat res_pre_ll) @ (List.concat res_l))
		(* codegen for a module unit *)
and pre_compile_mod_unit (resEnv: Res_cont.res_env) (typeEnv: Tc_cont.type_env)
	(main_dir: string) (mod_dir: string) (mu: m_mod_unit): pre_comp_res try_log_res = match mu with
	TypeDefMU(x, _) ->
		print_string ("-- " ^ x ^ "\n");
		let lfc = LibFC (mod_dir, x ^ ".sm") in
		let typeEnv' = Tc_cont.with_dir_tenv typeEnv mod_dir in
		let*! res_f = pre_compile_file resEnv typeEnv' main_dir lfc
		in validLog (List.concat res_f)
		(* codegen for an individual file *)
and pre_compile_file (resEnv: Res_cont.res_env) (typeEnv: Tc_cont.type_env)
	(main_dir: string) (fc: file_context): (pre_comp_res list) try_log_res =
		(* PHASE 1. lexing / parsing *)
	(match fc with
		TopLevelFC -> print_string "Loading top-level\n"
		| ExtLibFC(lib_dir, _) -> print_string ("Compiling external library: \"" ^ lib_dir ^ "\"\n")
		| _ -> ()
	);
	let*! tkList = load_token_list (full_name_fc main_dir fc) in
	let*! rawAst = tryWithErrLog string_of_parse_err (parseMain tkList) in
		(* PHASE 2. namespace resolution
			- for top-level, we must pre-load all the requirements
			- for not top-level, we have to save all the bindings
		*)
	let*! (res_pre_l, canonAst) = (match fc with
		TopLevelFC ->
				(* - load un-compiled libraries *)
			let Section(rl, _) = rawAst in
			let missingLibList = pre_check_req_list resEnv rl in
			let*! res_pre_ll = mapLogRes (pre_compile_lib resEnv typeEnv main_dir None) missingLibList in
				(* - file resolution *)
			print_string "Compiling top-level\n";
			let resEnv' = Res_cont.freeze_env resEnv [] in
			let*! canonAst = tryWithErrLog string_of_rs_err (resolve_section resEnv' true rawAst) in
			validLog (List.concat res_pre_ll, canonAst)
		| _ ->
			let*! canonAst = tryWithErrLog string_of_rs_err (resolve_section resEnv (is_ext_lib_fc fc) rawAst) in
			validLog ([], canonAst)
	) in
		(* PHASE 3. type-checking *)
	let typeEnv' = Tc_cont.with_dir_tenv typeEnv (full_dir_fc main_dir fc) in
	let*! res_f = tryWithErrLog string_of_tc_err (tc_section typeEnv' canonAst) in
	validLog (res_pre_l @ [res_f])
		(*
			codegen for an individual file + adds its bindings to an existing library
				(used for external libraries)
		*)
and ext_compile_file (resEnv: Res_cont.res_env) (typeEnv: Tc_cont.type_env)
	(modPath: string list) (libDir: string) (f: string): (pre_comp_res list) try_log_res =
	(if Sys.file_exists (libDir ^ "/" ^ f) then
		let resEnv' = Res_cont.freeze_env resEnv modPath in
		let*! _ = tryWithErrLog string_of_rs_err (add_import_renv resEnv' Lexing.dummy_pos modPath "Main") in
		let*! res_f = pre_compile_file resEnv' typeEnv "_unused" (ExtLibFC(libDir, f)) in
		save_ext_dec_renv resEnv' modPath; validLog res_f
	else validLog [])

	(* command line argument state *)

let usage_msg = "dusk <directory>"

let main_arg = ref ""
let out_arg = ref ""
let win_arg = ref false
let target_arg = ref ""
let runtime_arg = ref ""
let lib_arg = ref ""

	(* system commands [TO REPLACE] *)

let fail_simple str = (print_string (str ^ "\n"); exit 1)

(*let run_command s e =
	let r = Sys.command s in if r <> 0 then fail_simple e else ()*)

	(* configuration info *)

type dusk_config = {
	lib: string list ref
}

let def_config (): dusk_config = {
	lib = ref []
}

let read_config (path: string): dusk_config =
	let cfg = def_config () in
	if not (Sys.file_exists (path ^ "/config.json")) then cfg
	else let json = Yojson.Safe.from_file (path ^ "/config.json") in
	(match Util.member "lib" json with
		| `List l -> let ll = List.map (fun j -> match j with
			`String s -> s | _ -> fail_simple "Invalid JSON for library name in configuration file."
		) l in cfg.lib := ll
		| _ -> fail_simple "Invalid JSON for library list in configuration file."
	); cfg;;
(*
let read_config (path: string): dusk_config =
	let cfg = def_config () in
	if not (Sys.file_exists (path ^ "/config.json")) then cfg
	else let json = Yojson.Safe.from_file (path ^ "/config.json") in
	(match Util.member "size" json with
		`Null -> ()
		| `List [`Int w; `Int h] -> cfg.size := (w, h)
		| _ -> fail_simple "Invalid JSON for size in configuration file."
	); (match Util.member "shaderDir" json with
		`Null -> ()
		| `String s ->
			cfg.shaderFlag := true;
			cfg.shaderDir := Some s
		| _ -> fail_simple "Invalid JSON for shader directory in configuration file."
	); cfg;;*)

	(* main program *)

let program _ =
		(* parse arguments from command line *)
	(*let binDir = Array.get Sys.argv 0 in*)
	Arg.parse [
		("-o", Arg.Set_string out_arg,
			"Name of the output executable.");
		("-w", Arg.Set win_arg,
			"Sets compilation to compile with mingw and target Windows.");
		("-t", Arg.Set_string target_arg,
			"Specifies a target architecture for the executable (other than the default).");
		("-r", Arg.Set_string runtime_arg,
			"The directory in which the compiler's runtime is stored (if not the default).");
		("-l", Arg.Set_string lib_arg,
			"The directory to look for locally declared libraries (if not the default).");
	] (fun name -> main_arg := name) usage_msg;
		(* main compilation *)
	if !main_arg = "" then failLog "No file / directory name given."
	else let main_dir = !main_arg in (
		print_string ("Source directory: " ^ main_dir ^ "\n");
		let cfg = read_config main_dir in
			(* load library bindings *)
		let c_cont = init_compiler_cont !win_arg in
		let work_dir = if !lib_arg = "" then main_dir ^ "/_lib" else !lib_arg in
		let*! lib_l = mapLogRes (fun l ->
			let*! dl = load_ext_lib c_cont work_dir l in validLog (l, dl)
		) !(cfg.lib) in
			(* build virtual bindings from builtin + lib *)
		let virtTree = Builtin_core.builtinTreeMap () in
		let virtTree' = List.fold_left (fun tree (l, dl) ->
			Builtin_ext_lib.addExtTreeMap tree l dl
		) virtTree lib_l in
		let virtBindings = try (List.map (fun (path, vdl) ->
			(List.nth path 0, List.map (fun vd -> (path, vd)) vdl)
		) (flatten_tree virtTree'))
		with Invalid_argument _ -> failwith "BUG: main.ml - Empty path for virtual binding." in
			(* build environments from virtual bindings *)
		let resEnv = builtin_env virtTree' in
		let*! canonBindings = tryWithErrLog string_of_rs_err (
			let* resBindings = map_try_res (fun (l, subBindings) ->
				Res_type.resolve_virt_bindings resEnv l Lexing.dummy_pos subBindings
			) virtBindings in Valid (List.concat resBindings)
		) in
		let typeEnv = Tc_cont.builtin_tenv canonBindings in
		let tcBuiltins = Tc_cont.tc_complete_builtins typeEnv canonBindings in
			(* PHASE 0. compile extra external library source files *)
		let*! extAstList = mapLogRes (fun l ->
			ext_compile_file resEnv typeEnv [l; "Main"]	(work_dir ^ "/" ^ l) (l ^ ".sm")
		) !(cfg.lib) in
			(* PHASES 1-3. incremental resolution *)
		let*! typedAstList = pre_compile_file resEnv typeEnv main_dir TopLevelFC in
		let typedAst = (List.concat (List.concat extAstList)) @ (List.concat typedAstList) in
			(* PHASE 4. code generation *)
		let bin_dir = main_dir ^ "/bin" in
		(if not (Sys.file_exists bin_dir) then Unix.mkdir bin_dir 0o755);
		let targetArch =
			if !target_arg <> "" then Some !target_arg
			else if !win_arg then Some "x86_64-pc-windows-gnu" else None in
		genProgramHook targetArch bin_dir false tcBuiltins typedAst;
			(* PHASE 5. linking *)
		let runTarget = if !win_arg then "main.exe" else "main" in
		let outFile = if !out_arg = "" then runTarget else !out_arg in
			(* - compile external source files *)
		let libSrcList = Hashtbl.fold (fun k _ l -> k :: l) c_cont.link_srcs [] in
		let lExtArgs = List.map (fun (l, x) ->
			let libOutFile = bin_dir ^ "/" ^ x ^ ".o" in
			let pid = Unix.create_process !(c_cont.c_compiler) [|
				!(c_cont.c_compiler);
				"-c"; (work_dir ^ "/" ^ l ^ "/" ^ x ^ ".c");
				"-o"; libOutFile;
			|] Unix.stdin Unix.stdout Unix.stderr in
			let _ = Unix.waitpid [] pid in libOutFile
		) libSrcList in
			(* - collect linker flags *)
		let libDirList = Hashtbl.fold (fun k _ l -> k :: l) c_cont.link_libs [] in
		let libSymList = Hashtbl.fold (fun k _ l -> k :: l) c_cont.link_syms [] in
		let ldArgs = List.flatten (List.map (fun x -> ["-L"; x]) libDirList) in
		let lsArgs = List.flatten (List.map (fun x -> ["-l"; x]) libSymList) in
		let allArgs = [
				(* C compiler *)
			!(c_cont.c_compiler);
				(* main file + runtime *)
			"-o"; outFile;
			bin_dir ^ "/main.o";
			"./_runtime/runtime.o"
		] @ lExtArgs @ ["-pthread"] @ ldArgs @ lsArgs in
		(*List.iter (Printf.printf "[%s]\n") allArgs;*)
		let pid = Unix.create_process !(c_cont.c_compiler)
			(Array.of_list allArgs) Unix.stdin Unix.stdout Unix.stderr in
		let (_, status) = Unix.waitpid [] pid in (match status with
			Unix.WEXITED 0 -> endLog ()
			| Unix.WEXITED code -> failLog ("Compiler exited with code: " ^ (string_of_int code))
			| Unix.WSIGNALED s -> failLog ("Compiler killed by signal: " ^ (string_of_int s))
			| Unix.WSTOPPED s -> failLog ("Compiler stopped by signal: " ^ (string_of_int s))
		)
			(* PHASE 5. linking *)(*
		let runDir = if !runtime_arg = "" then binDir ^ "/_runtime" else !runtime_arg in
			(* -- copy test object file to runtime directory *)
		run_command (Printf.sprintf "cp -f %s/test.o %s/j_out.o" main_dir runDir)
			("Failed to copy test binary to runtime directory\n  " ^ runDir ^ "");
			(* -- run makefile in runtime directory, copy output to output directory *)
		let runTarget = if !win_arg then "main.exe" else "main" in
		run_command (Printf.sprintf ("cd %s; make %s") runDir runTarget) "Failed MAKE for runtime.";
		let outFile = if !out_arg = "" then runTarget else !out_arg in
		run_command (Printf.sprintf "cp %s/%s %s" runDir runTarget outFile)
			"Failed to copy final binary to output directory.";
		endLog ()*)
	);;

printLogRes (program ())