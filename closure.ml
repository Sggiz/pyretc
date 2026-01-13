
open Typed_ast
open Closure_ast

module Smap = Map.Make(String)

exception VarUndef of string

(* Varibales globales *)
let (genv : (string, unit) Hashtbl.t) = Hashtbl.create 17
let add_genv s = Hashtbl.add genv s ()

(* Les fonctions introduites par explicitation des fermetures *)
let gfuns : (string * int * c_block) list ref = ref []
let add_gfun gf = gfuns := gf :: !gfuns
let curr_fun_id = ref 0
let get_fun_name () =
    let n = !curr_fun_id in incr curr_fun_id;
    Format.sprintf ".fun_%d" n

(* Variables locales *)
type local_env = int Smap.t
let fp_init = -8
(* Arguments de fonctions : 24, 32, 40, ...
   Variables locales : -8, -16, -24, ...*)

(* Variables de fermeture *)
type fvars = int Smap.t
let clos = ref 0
(* Variables de fermeture : 16, 24, 32, ... *)

let reset () =
    Hashtbl.reset genv;
    List.iter add_genv
        ["nothing";"num-modulo";"empty";"link";"print";"each"];
(*  ["nothing";"num-modulo";"empty";"link";"print";"raise";"each";"fold"]; *)
    gfuns := [];
    curr_fun_id := 0;
    clos := 0

let correct_name name = if name = "num-modulo" then "num_modulo" else name


(* Down : env, fpcur, fvars, typed_ast *)
(* Up: c_ast, fpnew, fvars *)

let rec closure_block env fpcur fvars b =
    let csl, fpnew, fvars = closure_fold_block env fpcur fvars b.block in
    {desc=csl; t=b.t}, fpnew, fvars

and closure_fold_block env fpcur fvars = function
        | [] -> [], fpcur, fvars
        | stmt :: q ->
            let cs, fpnew, newfvars, defined =
                closure_stmt env fpcur fvars stmt in
            let fpnext, newenv = begin match defined with
                | None -> fpcur, env
                | Some x -> fpcur-8, Smap.add x fpcur env
            end in
            let csl, fpmin, newfvars2 =
                closure_fold_block newenv fpnext newfvars q in
            cs :: csl, min fpnew fpmin, newfvars2

and closure_stmt env fpcur fvars s = match s.stmt with
    | TSbexpr be ->
        let cbe, fpnew, newfvars =
            closure_bexpr env fpcur fvars be in
        {desc=CSbexpr cbe; t=s.t}, fpnew, newfvars, None
    | TSdef(_, x, be) ->
        let cbe, fpnew, newfvars =
            closure_bexpr env fpcur fvars be in
        {desc=CSdef(fpcur, cbe); t=s.t}, fpnew, newfvars,
        Some x
    | TSredef(x, be) ->
        let cbe, fpnew, newfvars =
            closure_bexpr env fpcur fvars be in
        let pos = try Smap.find x env with Not_found -> raise (VarUndef x) in
        {desc=CSdef(pos, cbe); t=s.t}, fpnew, newfvars, None
    | TSfun(f, _, (arg_l, _, b)) ->
        let save_clos = !clos in
        clos := 0;
        let funbody_env, _ =
            List.fold_left
                (fun (env, pos) arg -> Smap.add arg pos env, pos+8)
                (Smap.empty, 24)
                arg_l
        in
        let cb, fpnew, newfvars =
            closure_block funbody_env fp_init Smap.empty b in
        let gfun_name = get_fun_name () in
        add_gfun (gfun_name, fpnew, cb);
(*         add_genv gfun_name; *)
        let pos_array = Array.make !clos (Vlocal 0) in
        clos := save_clos;
        let new_ext_fvars = Smap.fold (fun x clos_pos fv ->
                let v, nfv = (
                if x = f then Vlocal 0, fv
                else if Hashtbl.mem genv x then Vglobal (correct_name x), fv
                else if Smap.mem x env then Vlocal (Smap.find x env), fv
                else if Smap.mem x fvars then Vclos (Smap.find x fvars), fv
                else (
                    let res = Vclos !clos, Smap.add x !clos fv in
                    clos := !clos + 1; res
                )) in
                pos_array.(clos_pos) <- v; nfv
            ) newfvars fvars
        in
        let cf = {desc=CSfun(fpcur, gfun_name, pos_array); t=s.t} in
        cf, fpcur, new_ext_fvars, Some f

and closure_bexpr env fpcur fvars { bexpr = e, op_list; t=t } =
    let expr_list = e :: (List.map snd op_list) in
    let cexprl, fpmin, newfvars =
        closure_fold_bexpr env fpcur fvars expr_list in
    let new_op_list = List.combine (List.map fst op_list) (List.tl cexprl) in
    { desc= List.hd cexprl, new_op_list; t=t}, fpmin, newfvars

and closure_fold_bexpr env fpcur fvars = function
    | [] -> [], fpcur, fvars
    | expr :: q ->
        let cexpr, fpnew, newfvars =
            closure_expr env fpcur fvars expr in
        let cexprl, fpmin, newfvars2 =
            closure_fold_bexpr env fpcur newfvars q in
        cexpr :: cexprl, min fpnew fpmin, newfvars2

and closure_expr env fpcur fvars e = match e.expr with
    (* renvoie (cexpr, closmap, fpnew, closnew) *)
    | TTrue -> {desc=CTrue; t=e.t}, fpcur, fvars
    | TFalse -> {desc=CFalse; t=e.t}, fpcur, fvars
    | TEint n -> {desc=CEint n; t=e.t}, fpcur, fvars
    | TEstring s -> {desc=CEstring s; t=e.t}, fpcur, fvars
    | TEident x ->
        let v, newfvars = (
            if Hashtbl.mem genv x then Vglobal (correct_name x), fvars
            else if Smap.mem x env then Vlocal (Smap.find x env), fvars
            else if Smap.mem x fvars then Vclos (Smap.find x fvars), fvars
            else (
                let res = Vclos !clos, Smap.add x !clos fvars in
                clos := !clos + 1; res
            )
        ) in
        {desc=CEvar v; t=e.t}, fpcur, newfvars
    | TEbexpr be ->
        let cbe, fpnew, newfvars = closure_bexpr env fpcur fvars be in
        {desc=CEbexpr cbe; t=e.t}, fpnew, newfvars
    | TEblock b ->
        let cb, fpnew, newfvars = closure_block env fpcur fvars b in
        {desc=CEblock cb; t=e.t}, fpnew, newfvars
    | TEcond(if_bexpr, _, if_block, elif_list, else_block_option) ->
        let cbexpr1, fp1, fvars1 = closure_bexpr env fpcur fvars if_bexpr in
        let cblock2, fp2, fvars2 = closure_block env fpcur fvars1 if_block in
        let (fp3, fvars3), clist3 = List.fold_left_map
            (fun (fp, fv) (be, b) ->
                let cbe, fp1, fv1 = closure_bexpr env fpcur fv be in
                let cb, fp2, fv2 = closure_block env fpcur fv1 b in
                (fp |> min fp1 |> min fp1, fv2), (cbe, cb)
            )
            (fpcur, fvars2) elif_list
        in
        let coption4, fp4, fvars4 = begin match else_block_option with
            | None -> None, fpcur, fvars3
            | Some b -> let cb, fp, fv = closure_block env fpcur fvars3 b in
                Some cb, fp, fv
        end in
        {desc=CEcond(cbexpr1, cblock2, clist3, coption4); t=e.t},
        fp1 |> min fp2 |> min fp3 |> min fp4, fvars4
    | TEcall(c, be_list) ->
        let cc, fpnew, newfvars = closure_caller env fpcur fvars c in
        let cbe_list, fpmin, newfvars2 =
            closure_fold_args env fpcur newfvars be_list in
        {desc=CEcall(cc, cbe_list); t=e.t}, min fpnew fpmin, newfvars2
    | TElam(arg_l, _, b) ->
        let save_clos = !clos in
        clos := 0;
        let funbody_env, _ =
            List.fold_left
                (fun (env, pos) arg -> Smap.add arg pos env, pos+8)
                (Smap.empty, 24)
                arg_l
        in
        let cb, fpnew, newfvars =
            closure_block funbody_env fp_init Smap.empty b in
        let gfun_name = get_fun_name () in
        add_gfun (gfun_name, fpnew, cb);
        let pos_array = Array.make !clos (Vlocal 0) in
        clos := save_clos;
        let new_ext_fvars = Smap.fold (fun x clos_pos fv ->
                let v, nfv = (
                if Hashtbl.mem genv x then Vglobal (correct_name x), fv
                else if Smap.mem x env then Vlocal (Smap.find x env), fv
                else if Smap.mem x fvars then Vclos (Smap.find x fvars), fv
                else (
                    let res = Vclos !clos, Smap.add x !clos fv in
                    clos := !clos + 1; res
                )) in
                pos_array.(clos_pos) <- v; nfv
            ) newfvars fvars
        in
        let cf = {desc=CElam(gfun_name, pos_array); t=e.t} in
        cf, fpcur, new_ext_fvars
    | TEcases(be, _, [("empty", None, b1);("link", (Some [x;y]), b2)]) ->
        let cbe, fp0, fvars0 = closure_bexpr env fpcur fvars be in
        let cb1, fp1, fvars1 = closure_block env fpcur fvars0 b1 in
        let envx, fpx, pos_x = if x="_" then env, fpcur, None else
            Smap.add x fpcur env, fpcur-8, Some fpcur in
        let next_env, fpnext, pos_y = if y="_" then envx, fpx, None else
            Smap.add y fpx envx, fpx-8, Some fpx in
        let cb2, fp2, fvars2 = closure_block next_env fpnext fvars1 b2 in
        {desc=CEcases(cbe, cb1, pos_x, pos_y, cb2); t=e.t},
        fp0 |> min fp1 |> min fp2, fvars2

    | _ -> failwith "A faire [closure_expr]"

and closure_fold_args env fpcur fvars = function
    | [] -> [], fpcur, fvars
    | expr :: q ->
        let cexpr, fpnew, newfvars =
            closure_bexpr env fpcur fvars expr in
        let cexprl, fpmin, newfvars2 =
            closure_fold_args env fpcur newfvars q in
        cexpr :: cexprl, min fpnew fpmin, newfvars2

and closure_caller env fpcur fvars c = match c.caller with
    | TCident f ->
        let v, newfvars = (
            if Hashtbl.mem genv f then Vglobal (correct_name f), fvars
            else if Smap.mem f env then Vlocal (Smap.find f env), fvars
            else if Smap.mem f fvars then Vclos (Smap.find f fvars), fvars
            else (
                let res = Vclos !clos, Smap.add f !clos fvars in
                clos := !clos + 1; res
            )
        ) in
        {desc=CCvar v; t=c.t}, fpcur, newfvars
    | TCcall(c0, be_list) ->
        let cc0, fpnew, newfvars = closure_caller env fpcur fvars c0 in
        let cbe_list, fpmin, newfvars2 =
            closure_fold_args env fpcur newfvars be_list in
        {desc=CCcall(cc0, cbe_list); t=c.t}, min fpnew fpmin, newfvars2


let closure_file file =
    reset ();
    let cb, fp, fvars =
        closure_fold_block Smap.empty fp_init Smap.empty file.file in
    Smap.iter (fun s _ -> raise (VarUndef s)) fvars;
    ({desc=cb; t=file.t}, fp, !gfuns : c_file)


