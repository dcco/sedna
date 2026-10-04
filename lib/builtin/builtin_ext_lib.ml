open Commons.Tree_map
open Builtin_core
open Parser.Dusk_type
open Parser.Dusk_ext_lib

let extDecVirtBind (d: ext_dec): m_virt_bind list = match d with
	LinkerExt _ -> []
	| TypeExt(x, p) -> [(rb x, TDefVD ExternTD, p)]
	| FnExt(ptrFlag, f, rf, pl, tau_r, p) ->
		let al = List.map (fun (_, a, _) -> a) pl in
		let tau_pl = List.map (fun (_, _, t) -> t) pl in
		let f' = (match rf with None -> f | Some f' -> f') in
		[(rb f, SymVD(ExternalSym2(f', ptrFlag, al), (tau_pl, tau_r)), p)]

let addExtTreeMap (m: (m_virt_bind list) tree_map) (l: string) (dl: ext_dec list): (m_virt_bind list) tree_map =
	add_tree m [l; "Main"] (List.flatten (List.map extDecVirtBind dl))
