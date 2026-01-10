
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
let get_fun_name =
    let n = !curr_fun_id in incr curr_fun_id;
    Format.sprintf ".fun_%d" n

(* Variables locales *)
type local_env = int Smap.t
(* Arguments de fonctions : 24, 32, 40, ...
   Variables locales : -8, -16, -24, ...*)

(* Variables de fermeture *)
type fvars = int Smap.t
let clos = ref 16
(* Variables de fermeture : 16, 24, 32, ... *)

let reset () =
    Hashtbl.reset genv;
    List.iter add_genv
        ["nothing"];
(*  ["nothing";"num-modulo";"empty";"link";"print";"raise";"each";"fold"]; *)
(* pas besoin d'ajouter "print" *)
    gfuns := [];
    curr_fun_id := 0;
    clos := 16




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
        {desc=Csredef(pos, cbe); t=s.t}, fpnew, newfvars, None
(*     | TSfun(f, _, (arg_l, _, b)) -> *)
    | _ -> failwith "A faire [closure_stmt]"

and closure_bexpr env fpcur fvars { bexpr = e, op_list; t=t } =
    let expr_list = e :: (List.map snd op_list) in
    let rec closure_fold env fpcur fvars = function
        | [] -> [], fpcur, Smap.empty
        | expr :: q ->
            let cexpr, fpnew, newfvars =
                closure_expr env fpcur fvars expr in
            let cexprl, fpmin, newfvars2 =
                closure_fold env fpcur newfvars q in
            cexpr :: cexprl, min fpnew fpmin, newfvars2
    in
    let cexprl, fpmin, newfvars =
        closure_fold env fpcur fvars expr_list in
    let new_op_list = List.combine (List.map fst op_list) (List.tl cexprl) in
    { desc= List.hd cexprl, new_op_list; t=t}, fpmin, newfvars

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
                clos := !clos + 8; res
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
    | _ -> failwith "A faire [closure_expr]"


let closure_file file =
    reset ();
    let cb, fp, fvars =
        closure_fold_block Smap.empty (-8) Smap.empty file.file in
    Smap.iter (fun s _ -> raise (VarUndef s)) fvars;
    {desc=cb; t=file.t}, fp




