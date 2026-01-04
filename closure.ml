
open Typed_ast
open Closure_ast

let (genv : (string, unit) Hashtbl.t) = Hashtbl.create 17

module Smap = Map.Make(String)

type local_env = var Smap.t
let union = Smap.union (fun s a b -> Some a)
(* Il n'y a pas de conflits en pratique *)

let curr_fun_id = ref 0
let get_fun_id = let n = !curr_fun_id in incr curr_fun_id; n

let rec closure_block env fpcur closcur b =
    let csl, closmap, fpmax, closnew =
        closure_fold_block env fpcur closcur b.block in
    {desc=csl; t=b.t}, closmap, fpmax, closnew

and closure_fold_block env fpcur closcur = function
        | [] -> [], Smap.empty, fpcur, closcur
        | stmt :: q ->
            let cs, closmap, fpnew, closnew =
                closure_stmt env fpcur closcur stmt in
            let newenv = union env closmap in
            let csl, closmapl, fpmax, closnew2 =
                closure_fold_block newenv fpcur closnew q in
            cs :: csl, union closmap closmapl, max fpnew fpmax, closnew2

and closure_stmt env fpcur closcur s = match s.stmt with
    | TSbexpr be ->
        let cbe, closmap, fpnew, closnew =
            closure_bexpr env fpcur closcur be in
        {desc=CSbexpr cbe; t=s.t}, closmap, fpnew, closnew
(*     | TSdef(x, be) -> *)
(*     | TSredef(x, be) -> *)
(*     | TSfun(f, _, (arg_l, _, b)) -> *)
    | _ -> failwith "A faire [closure_stmt]"

and closure_bexpr env fpcur closcur { bexpr = e, op_list; t=t } =
    let expr_list = e :: (List.map snd op_list) in
    let rec closure_fold env fpcur closcur = function
        | [] -> [], Smap.empty, fpcur, closcur
        | expr :: q ->
            let cexpr, closmap, fpnew, closnew =
                closure_expr env fpcur closcur expr in
            let newenv = union env closmap in
            let cexprl, closmapl, fpmax, closnew2 =
                closure_fold newenv fpcur closnew q in
            cexpr :: cexprl, union closmap closmapl, max fpnew fpmax, closnew2
    in
    let cexprl, closmapl, fpmax, closnew =
        closure_fold env fpcur closcur expr_list in
    let new_op_list = List.combine (List.map fst op_list) (List.tl cexprl) in
    { desc= List.hd cexprl, new_op_list; t=t}, closmapl, fpmax, closnew

and closure_expr env fpcur closcur e = match e.expr with
    (* renvoie (cexpr, closmap, fpnew, closnew) *)
    | TTrue -> {desc=CTrue; t=e.t}, Smap.empty, fpcur, closcur
    | TFalse -> {desc=CFalse; t=e.t}, Smap.empty, fpcur, closcur
    | TEint n -> {desc=CEint n; t=e.t}, Smap.empty, fpcur, closcur
    | TEstring s -> {desc=CEstring s; t=e.t}, Smap.empty, fpcur, closcur
    | TEident x ->
        begin try
            {desc=CEvar(Smap.find x env); t=e.t}, Smap.empty, fpcur, closcur
        with Not_found->
            if Hashtbl.mem genv x then
                {desc=CEvar(Vglobal x); t=e.t}, Smap.empty, fpcur, closcur
            else
                {desc=CEvar(Vclos closcur); t=e.t},
                Smap.singleton x (Vclos (closcur + 1)), fpcur, closcur + 1
        end
    | TEbexpr be ->
        let cbe, closmap, fpnew, closnew=closure_bexpr env fpcur closcur be in
        {desc=CEbexpr cbe; t=e.t}, closmap, fpnew, closnew
    | TEblock b ->
        let cb, closmap, fpnew, closnew=closure_block env fpcur closcur b in
        {desc=CEblock cb; t=e.t}, closmap, fpnew, closnew
    | TEcall(caller, bexpr_list) ->
        
    | _ -> failwith "A faire [closure_expr]"


let closure_file file =
    let cb, _, _, _ = closure_fold_block Smap.empty 8 0 file.file in
    {desc=cb; t=file.t}




