
(* Algo W *)

open Ast
open Typed_ast

exception UnificationFailure of typ * typ

exception Message_terr of string
let raise_mess_terr s = raise (Message_terr s)

exception Wrong_terr of typ * typ
let wrong_type t1 t2 = raise (Wrong_terr(t1, t2))

let rec head = function
    | Tvar { id = _; def = Some t } -> head t
    | t -> t

let rec canon t =
    match head t with
    | Tlist t -> Tlist(canon t)
    | Tfun(tl, t) -> Tfun(List.map canon tl, canon t)
    | t' -> t'

let unification_error t1 t2 = raise (UnificationFailure (canon t1, canon t2))

let rec occur tv t =
    match head t with
    | Tvar tv' -> V.equal tv tv'
    | Tlist t' -> occur tv t'
    | Tfun(tl, t') -> List.exists (occur tv) tl || occur tv t'
    | _ -> false

let rec unify t1 t2 =
    match head t1, head t2 with
    | Tany, Tany
    | Tnoth, Tnoth
    | Tbool, Tbool
    | Tint, Tint
    | Tstr, Tstr -> ()
    | Tlist(t1'), Tlist(t2') -> unify t1' t2'
    | Tfun(tla, ta), Tfun(tlb, tb) -> 
        if List.length tla <> List.length tlb then
            unification_error t1 t2
        else List.iter2 unify tla tlb; unify ta tb
    | Tvar v1 , Tvar v2  ->
        if not @@ V.equal v1 v2 then unification_error t1 t2
    | t, Tvar v
    | Tvar v, t ->
        if occur v t then unification_error t1 t2
        else ( v.def <- Some t )
    | _ -> unification_error t1 t2


module Vset = Set.Make(V)

let rec fvars t =
    match head t with
    | Tvar v -> Vset.singleton v
    | Tlist t' -> fvars t'
    | Tfun(tl, t') ->
        List.fold_left (fun s t -> Vset.union s @@ fvars t) (fvars t') tl
    | _ -> Vset.empty

type schema = { vars : Vset.t; typ : typ }

module Smap = Map.Make(String)

type env = { bindings : schema Smap.t; fvars : Vset.t }

let empty = { bindings = Smap.empty; fvars = Vset.empty }

let update_fvars s =
    Vset.fold (fun v s -> Vset.union (fvars (Tvar v)) s) s Vset.empty

let add s t e =
    let new_vars = fvars t in
    let new_schema = { vars = Vset.empty; typ = t } in {
        bindings = Smap.add s new_schema e.bindings;
        fvars = Vset.union e.fvars new_vars
    }

let add_gen s t e =
    let new_vars = fvars t in
    let updated_env_fvars = update_fvars e.fvars in
    let free_vars =
        Vset.filter (fun tv -> not @@ Vset.mem tv updated_env_fvars) new_vars
    in
    let new_schema = { vars = free_vars; typ = t } in {
        bindings = Smap.add s new_schema e.bindings;
        fvars = e.fvars
    }

module Vmap = Map.Make(V)

let find s e =
    let schema = Smap.find s e.bindings in

    let rec constr_new_type vmap t =
        match head t with
        | Tvar var ->
            if Vset.mem var schema.vars then
            let new_var = (
                try Vmap.find var vmap
                with Not_found -> V.create ()
            ) in
            Vmap.add var new_var vmap, Tvar(new_var)
            else vmap, Tvar(var)
        | Tlist t' ->
            let vmap', nt' = constr_new_type vmap t' in
            vmap', Tlist(nt')
        | Tfun(tl, t') ->
            let rec vmap_fold = function
                | [] -> vmap, []
                | t::q ->
                    let vm, tl = vmap_fold q in 
                    let vm2, nt = constr_new_type vm t in
                    vm2, nt :: tl
            in
            let vm, ntl = vmap_fold tl in
            let vm2, nt = constr_new_type vm t' in
            vm2, Tfun(ntl, nt)
        | _ -> vmap, t
    in

    let _, t = constr_new_type Vmap.empty schema.typ in t



(* Algorithme W appliqué à notre ast de pyret *)

let init_env = empty
    |> add_gen "nothing" Tnoth
    |> add_gen "num-modulo" (Tfun([Tint; Tint], Tint))
    |> add_gen "empty" (Tlist(Tvar(V.create ())))
    |> add_gen "link" ( let v = V.create () in 
        Tfun([Tvar(v); Tlist(Tvar(v))], Tlist(Tvar(v))) )
    |> add_gen "print" ( let v = V.create () in
        Tfun([Tvar(v)], Tvar(v)) )
    |> add_gen "raise" ( let v = V.create () in
        Tfun([Tstr], Tvar(v)) )
    |> add_gen "each" (let a, b = V.create (), V.create () in
        Tfun([Tfun([Tvar(a)], Tvar(b)); Tlist(Tvar(a)) ], Tnoth) )
    |> add_gen "fold" ( let a, b = V.create (), V.create () in
Tfun([Tfun([Tvar(a); Tvar(b)], Tvar(a)) ;Tvar(a) ; Tlist(Tvar(b))], Tvar(a)) )

let check_type t1 t2 = if t1 <> t2 then wrong_type t1 t2

let check_binop t1 bin t2 = match bin with
    | Add -> begin match t1, t2 with
        | Tint, t | t, Tint -> check_type t Tint; Tint
        | Tstr, t | t, Tstr -> check_type t Tstr; Tstr
        | _ -> wrong_type t1 Tint end
    | Sub | Mul | Div -> check_type t1 Tint; check_type t2 Tstr; Tstr
    | Eq | Neq -> Tbool
    | Lneq | Leq | Gneq | Geq ->
        check_type t1 Tint; check_type t2 Tint; Tbool
    | And | Or ->
        check_type t1 Tbool; check_type t2 Tbool; Tbool

let rec w_block e = function
    | [] -> { block = []; t = Tnoth }
    | [s] -> let _, ts = w_stmt e s in
        { block = [ts]; t = ts.t }
    | s::q -> let new_env, ts = w_stmt e s in let tb = w_block new_env q in
        { block = ts::tb.block; t = tb.t }

and w_stmt e = function
    | Sbexpr be -> let tbe = w_bexpr e be in
        e, { t = tbe.t; stmt = TSbexpr(tbe) }
    | _ -> raise_mess_terr "This statement type is not yet implemented"

and w_bexpr e = function
    | exp, [] -> let texp = w_expr e exp in
        { bexpr = (texp, []); t = texp.t }
    | exp1, [bin, exp2] -> let texp1, texp2 = w_expr e exp1, w_expr e exp2 in
        { bexpr = (texp1, [bin, texp2]); t = check_binop texp1.t bin texp2.t }
    | exp1, (bin, exp2)::q ->
        let {bexpr=(te2, l);t=t} = w_bexpr e (exp2, q) in
        let texp1 = w_expr e exp1 in
        if bin <> Eq && bin <> Neq then check_type texp1.t te2.t;
        { bexpr = (texp1, (bin, te2)::l); t=t}

and w_expr e = function
    | True -> { t = Tbool; expr = TTrue }
    | False -> { t = Tbool; expr = TFalse }
    | Eint k -> { t = Tint; expr = TEint k }
    | Estring s -> { t = Tstr; expr = TEstring s }
    | _ -> raise_mess_terr "This expression type is not yet implemented"

let w_file e f = let tb = w_block e f in { file = tb.block; t = tb.t }

let type_file f = w_file init_env f

