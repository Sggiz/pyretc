
open Typed_ast
open Closure_ast

module Smap = Map.Make(String)

exception VarUndef of string

(* Varibales globales *)
let (genv : (string, unit) Hashtbl.t) = Hashtbl.create 17
let add_genv s = Hashtbl.add genv s ()

(* Dont les fonctions introduites par explicitation des fermetures *)
let gfuns : (string * c_block) list ref = ref []
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
        ["nothing"];
(*  ["nothing";"num-modulo";"empty";"link";"print";"raise";"each";"fold"]; *)
(* pas besoin d'ajouter "print" *)
    gfuns := [];
    curr_fun_id := 0;
    clos := 0




(* Down : env, fpcur, fvars, typed_ast *)
(* Up: c_ast, fpnew, fvars *)

let rec closure_block env fpcur fvars b =
    let csl, fpnew, fvars = closure_fold_block env fpcur fvars b.block in
    {desc=csl; t=b.t}, fpnew, fvars

and closure_fold_block env fpcur fvars = function
        | [] -> [], fpcur, Smap.empty
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
        add_gfun (gfun_name, cb);
        let pos_array = Array.make !clos (Vlocal 0) in
        Smap.iter (fun x clos_pos ->
                let v = (
                if Hashtbl.mem genv x then Vglobal x
                else if Smap.mem x env then Vlocal (Smap.find x env)
                else if Smap.mem x fvars then Vclos (Smap.find x env)
                else raise (VarUndef x)
                ) in
                pos_array.(clos_pos) <- v
            ) newfvars;
        let cf = {desc=CSfun(fpcur, gfun_name, pos_array, fpnew); t=s.t} in
        clos := save_clos;
        cf, fpcur, fvars, Some f

and closure_bexpr env fpcur fvars { bexpr = e, op_list; t=t } =
    let expr_list = e :: (List.map snd op_list) in
    let cexprl, fpmin, newfvars =
        closure_fold_bexpr env fpcur fvars expr_list in
    let new_op_list = List.combine (List.map fst op_list) (List.tl cexprl) in
    { desc= List.hd cexprl, new_op_list; t=t}, fpmin, newfvars

and closure_fold_bexpr env fpcur fvars = function
    | [] -> [], fpcur, Smap.empty
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
            if Hashtbl.mem genv x then Vglobal x, fvars
            else if Smap.mem x env then Vlocal (Smap.find x env), fvars
            else if Smap.mem x fvars then Vclos (Smap.find x env), fvars
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
    | TEcall({caller=TCident "print"; t=_} , [be]) ->
        let cbe, fpnew, newfvars = closure_bexpr env fpcur fvars be in
        {desc=CEprint cbe; t=e.t}, fpnew, newfvars
    | TEcall(c, be_list) ->
        let cc, fpnew, newfvars = closure_caller env fpcur fvars c in
        let cbe_list, fpmin, newfvars2 =
            closure_fold_args env fpcur newfvars be_list in
        {desc=CEcall(cc, cbe_list); t=e.t}, min fpnew fpmin, newfvars2

    | _ -> failwith "A faire [closure_expr]"

and closure_fold_args env fpcur fvars = function
    | [] -> [], fpcur, Smap.empty
    | expr :: q ->
        let cexpr, fpnew, newfvars =
            closure_bexpr env fpcur fvars expr in
        let cexprl, fpmin, newfvars2 =
            closure_fold_args env fpcur newfvars q in
        cexpr :: cexprl, min fpnew fpmin, newfvars2

and closure_caller env fpcur fvars c = match c.caller with
    | TCident f ->
        let v, newfvars = (
            if Hashtbl.mem genv f then Vglobal f, fvars
            else if Smap.mem f env then Vlocal (Smap.find f env), fvars
            else if Smap.mem f fvars then Vclos (Smap.find f env), fvars
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
    {desc=cb; t=file.t}, fp


