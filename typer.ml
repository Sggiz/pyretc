
(* Algo W *)

open Ast
open Typed_ast

type loc = Lexing.position * Lexing.position

exception Message_terr of loc * string
let raise_mess_terr l s = raise (Message_terr(l, s))

exception Unification_alert of typ * typ
exception Unification_terr of loc * typ * typ * typ * typ

exception ST_alert of typ * typ
exception ST_terr of loc * typ * typ * typ * typ

exception Wrong_type_terr of loc * typ * typ

exception Not_a_fun_terr of caller
exception Arg_nb_terr of caller

exception Var_not_def of loc * string
exception Invalid_annot_terr of ty
exception Redef_terr of loc * string
exception Shadow_terr of loc * string

exception BF_alert
exception BF_terr of ty

exception Case_terr of expr

let rec head = function
    | Tvar { id = _; def = Some t } -> head t
    | t -> t

let rec canon t =
    match head t with
    | Tlist t -> Tlist(canon t)
    | Tfun(tl, t) -> Tfun(List.map canon tl, canon t)
    | t' -> t'

let rec occur tv t =
    match head t with
    | Tvar tv' -> V.equal tv tv'
    | Tlist t' -> occur tv t'
    | Tfun(tl, t') -> List.exists (occur tv) tl || occur tv t'
    | _ -> false

module Vset = Set.Make(V)

let rec fvars t =
    match head t with
    | Tvar v -> Vset.singleton v
    | Tlist t' -> fvars t'
    | Tfun(tl, t') ->
        List.fold_left (fun s t -> Vset.union s @@ fvars t) (fvars t') tl
    | _ -> Vset.empty

type schema = { vars : Vset.t; typ : typ; is_var : bool }

module Smap = Map.Make(String)

type env = {
    bindings : schema Smap.t;
    fvars : Vset.t;
    selfdef_map : tvar Smap.t
}

let empty = { bindings=Smap.empty; fvars=Vset.empty; selfdef_map=Smap.empty }

let update_fvars s =
    Vset.fold (fun v s -> Vset.union (fvars (Tvar v)) s) s Vset.empty

let add s t is_var e =
    let new_vars = fvars t in
    let new_schema = { vars = Vset.empty; typ = t; is_var = is_var } in
    {
        bindings = Smap.add s new_schema e.bindings;
        fvars = Vset.union e.fvars new_vars;
        selfdef_map = e.selfdef_map
    }

let add_gen s t e =
    let new_vars = fvars t in
    let updated_env_fvars = update_fvars e.fvars in
    let free_vars =
        Vset.filter (fun tv -> not @@ Vset.mem tv updated_env_fvars) new_vars
    in
    let new_schema = { vars = free_vars; typ = t; is_var = false} in
    {
        bindings = Smap.add s new_schema e.bindings;
        fvars = e.fvars;
        selfdef_map = e.selfdef_map
    }

let add_selfdef e s =
    let newvar = V.create true in
    {
        bindings = e.bindings;
        fvars = Vset.add newvar e.fvars;
        selfdef_map = Smap.add s newvar e.selfdef_map
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
                with Not_found -> V.create false
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



(* Fonctions de vérification de types *)

let rec rec_unify t1 t2 = match head t1, head t2 with
    | Tany, _ | _, Tany
    | Tnoth, Tnoth | Tbool, Tbool | Tint, Tint | Tstr, Tstr ->
        ()
    | Tlist ta, Tlist tb -> rec_unify ta tb
    | Tfun(tla, ta), Tfun(tlb, tb) ->
        List.iter2 rec_unify tla tlb; rec_unify ta tb
    | Tvar v1, Tvar v2 ->
        if V.equal v1 v2 then ()
        else if v1.is_selfdef && v2.is_selfdef then
            raise (Unification_alert(head t1, head t2))
        else if v1.is_selfdef then v2.def <- Some (Tvar v1)
        else v1.def <- Some (Tvar v2)
    | t, Tvar v | Tvar v, t ->
        if v.is_selfdef then raise (Unification_alert(t, Tvar v))
        else v.def <- Some t
    | ta, tb -> raise (Unification_alert(ta, tb))


let unify loc t1 t2 =
    try rec_unify t1 t2 with Unification_alert(ta, tb) ->
    raise (Unification_terr(loc, t1, t2, ta, tb))


let rec st_verif m t1 t2 = match head t1, head t2 with
    | _, Tany
    | Tnoth, Tnoth | Tbool, Tbool | Tint, Tint | Tstr, Tstr ->
        m
    | Tlist(ta), Tlist(tb) -> st_verif m ta tb
    | Tfun(tl1, ta), Tfun(tl2, tb) ->
        if (List.length tl1) <> (List.length tl2) then
            raise (ST_alert(t1, t2));
        let m' = st_verif m ta tb in
        List.fold_left2 st_verif m' tl2 tl1
    | Tvar v1, Tvar v2 ->
        if V.equal v1 v2 then m
        else if Vmap.mem v1 m then st_verif m (Vmap.find v1 m) (Tvar v2)
        else if Vmap.mem v2 m then st_verif m (Tvar v1) (Vmap.find v2 m)
        else if v1.is_selfdef && v2.is_selfdef then
            raise (ST_alert(Tvar v1, Tvar v2))
        else if v1.is_selfdef then Vmap.add v2 (Tvar v1) m
        else Vmap.add v1 (Tvar v2) m
    | ht, Tvar v ->
        if Vmap.mem v m then st_verif m ht (Vmap.find v m)
        else if v.is_selfdef then
            raise (ST_alert(ht, Tvar v))
        else Vmap.add v ht m
    | Tvar v, ht ->
        if Vmap.mem v m then st_verif m (Vmap.find v m) ht
        else if v.is_selfdef then
            raise (ST_alert(Tvar v, ht))
        else Vmap.add v ht m
    | t1, t2 ->
        raise (ST_alert(t1, t2))

let try_sous_type loc t1 t2 = 
    try
        st_verif Vmap.empty t1 t2
    with ST_alert(unif_t1, unif_t2) ->
        raise (ST_terr(loc, t1, t2, unif_t1, unif_t2))

let lock_bindings m =
    let f (var, t) = var.def <- Some t in
    List.iter f (Vmap.bindings m)

let sous_type loc t1 t2 =
    let m = try_sous_type loc t1 t2 in
    lock_bindings m

let sous_type_list loc_typ_list t =
    let ml = 
        List.map (fun (loc, typ) -> try_sous_type loc typ t) loc_typ_list
    in
    List.iter lock_bindings ml


let eq_type loc1 t1 loc2 t2 = 
    sous_type loc1 t1 t2;
    sous_type loc2 t2 t1

let rec eq_type_list = function
    | [] | [_] -> ()
    | (loc1, t1) :: (loc2, t2) :: q ->
        eq_type loc1 t1 loc2 t2; eq_type_list ((loc2, t2) :: q)


let check_binop loc_typ_list = function
    | Add ->
        let is_clue (_, t) = match t with |Tint|Tstr-> true |_-> false in
        begin try
            let _, t = List.find is_clue loc_typ_list in
            sous_type_list loc_typ_list t; t
        with Not_found ->
            begin try
                sous_type_list loc_typ_list Tstr; Tstr
            with ST_terr _ ->
                sous_type_list loc_typ_list Tint; Tint
        end end
    | Sub | Mul | Div -> sous_type_list loc_typ_list Tint; Tint
    | Eq | Neq -> Tbool
    | Lneq | Leq | Gneq | Geq -> sous_type_list loc_typ_list Tint; Tbool
    | And | Or -> sous_type_list loc_typ_list Tbool; Tbool


let rec bf e t =
    match head t with
    | Tvar v -> if not @@ Vset.mem v e.fvars then raise BF_alert
    | Tlist t -> bf e t
    | Tfun(tl, t) -> List.iter (bf e) tl; bf e t
    | _ -> ()

let check_bf e (annot, t) =
    try bf e t with BF_alert ->
    raise (BF_terr annot)

let rec read_type e t = match t.desc with
    | Tannot("Any", None) -> Tany
    | Tannot("Nothing", None) -> Tnoth
    | Tannot("Boolean", None) -> Tbool
    | Tannot("Number", None) -> Tint
    | Tannot("String", None) -> Tstr
    | Tannot("List", Some([t])) -> Tlist (read_type e t)
    | Tfun(tyl, rt) -> 
        let Rtype(t) = rt.desc in
        Tfun(List.map (read_type e)tyl, read_type e t)
    | Tannot(x, None) ->
        begin try
            Tvar(Smap.find x e.selfdef_map)
        with Not_found -> raise (Invalid_annot_terr t) end
    | _ -> raise (Invalid_annot_terr t)

let check_valid_selfdef e loc s = match s with
    | "Any" | "Nothing" | "Boolean" | "Number" | "String" | "List" ->
        raise (Shadow_terr(loc, s))
    | _ -> if Smap.mem s e.selfdef_map then raise (Shadow_terr(loc, s))


(* Algo W construisant l'AST typé *)

let init_env = empty
    |> add_gen "nothing" Tnoth
    |> add_gen "num-modulo" (Tfun([Tint; Tint], Tint))
    |> add_gen "empty" (Tlist(Tvar(V.create true)))
    |> add_gen "link" ( let v = V.create true in 
        Tfun([Tvar(v); Tlist(Tvar(v))], Tlist(Tvar(v))) )
    |> add_gen "print" ( let v = V.create true in
        Tfun([Tvar(v)], Tvar(v)) )
    |> add_gen "raise" ( let v = V.create true in
        Tfun([Tstr], Tvar(v)) )
    |> add_gen "each" (let a, b = V.create true, V.create true in
        Tfun([Tfun([Tvar(a)], Tvar(b)); Tlist(Tvar(a)) ], Tnoth) )
    |> add_gen "fold" ( let a, b = V.create true, V.create true in
Tfun([Tfun([Tvar(a); Tvar(b)], Tvar(a)) ;Tvar(a) ; Tlist(Tvar(b))], Tvar(a)) )

let ping () = Format.printf "ping@."
let pingarg f a = Format.printf "ping : %a@." f a

let rec w_block e b = match b.desc with
    | [] -> { block = []; t = Tnoth }
    | [s] -> let _, ts = w_stmt e s in
        { block = [ts]; t = ts.t }
    | s::q -> 
        let new_env, ts = w_stmt e s in
        let tb = w_block new_env { desc = q; loc = b.loc } in
        { block = ts::tb.block; t = tb.t }

and w_stmt e s = match s.desc with
    | Sfun(f, targl, fb) ->
        let (paraml, rt, ub ,b) = fb.desc in
        let idl, annotl = List.split (List.map peel paraml) in
        let new_env = List.fold_left add_selfdef e targl in

        let tl, t = begin
            List.map (read_type new_env) annotl,
            read_type new_env (let Rtype(t') = rt.desc in t')
        end in

        List.iter (check_bf new_env) (List.combine annotl tl);

        if Smap.mem f e.bindings then raise (Shadow_terr(s.loc, f));
        List.iter (check_valid_selfdef e s.loc) targl;
        List.iter (fun p -> let id = fst p.desc in
            if Smap.mem (fst p.desc) e.bindings then
            raise (Shadow_terr(p.loc, id))) paraml;

        let sch = {
            vars = List.fold_left
                (fun s id -> Vset.add (Smap.find id new_env.selfdef_map) s)
                Vset.empty targl;
            typ = Tfun(tl, t);
            is_var = false 
        } in
        let inner_env = List.fold_left 
            (fun e (s,t) -> add s t false e)
            new_env (List.combine idl tl)
        in
        let rec_env = {
            bindings = Smap.add f sch inner_env.bindings;
            fvars = inner_env.fvars;
            selfdef_map = inner_env.selfdef_map
        } in
        let tb = w_block rec_env b in
        sous_type b.loc tb.t t;
        let next_env = {
            bindings = Smap.add f sch e.bindings;
            fvars = e.fvars;
            selfdef_map = e.selfdef_map
        } in
        next_env, { stmt = TSfun(f, targl, (idl, ub, tb)); t = Tfun(tl, t) }


    | Sdef(b, id, tyo, be) ->
        if Smap.mem id e.bindings then raise (Shadow_terr(s.loc, id)) else
        let tbe = w_bexpr e be in
        begin match tyo with 
            | None->()
            | Some(t)-> sous_type be.loc tbe.t (read_type e t)
        end;
        begin if b then add id tbe.t true e else add_gen id tbe.t e end,
        { stmt = TSdef(b, id, tbe); t = tbe.t }
    | Sredef(id, be) ->
        begin try
            let sch = Smap.find id e.bindings in
            if not sch.is_var then
                raise (Redef_terr(s.loc,id))
            else let t = find id e in
            let tbe = w_bexpr e be in
            sous_type be.loc tbe.t t;
            e, { stmt = TSredef(id, tbe); t = Tnoth }
        with Not_found -> raise (Var_not_def(s.loc, id)) end
    | Sbexpr be -> let tbe = w_bexpr e be in
        e, { t = tbe.t; stmt = TSbexpr tbe }

and w_bexpr e be = match be.desc with
    | exp, [] -> let texp = w_expr e exp in
        ({ bexpr = (texp, []); t = texp.t } : t_bexpr)
    | exp1, (bin, exp2)::q ->
        let expl = exp2 :: List.map snd q in
        let locl = exp1.loc :: List.map (fun exp -> exp.loc) expl in
        let texp1, texpl =
            w_expr e exp1, List.map (w_expr e) expl
        in
        let tl = texp1.t :: List.map (fun (texp: t_expr) -> texp.t) texpl in
        let t = check_binop (List.combine locl tl) bin in

        let tbe = texp1, List.map (fun texp -> (bin, texp)) texpl in
        { bexpr = tbe; t = t }

and w_expr e exp = match exp.desc with
    | True -> { expr = TTrue; t = Tbool }
    | False -> { t = Tbool; expr = TFalse }
    | Eint k -> { t = Tint; expr = TEint k }
    | Estring s -> { t = Tstr; expr = TEstring s }
    | Eident id -> begin try
        let t = find id e in
        { expr = TEident id; t = t }
        with Not_found -> raise (Var_not_def(exp.loc,id)) end

    | Ebexpr be -> let tbe = w_bexpr e be in
        { t = tbe.t; expr = TEbexpr tbe }

    | Eblock b -> let tb = w_block e b in
        { t = tb.t; expr = TEblock tb }

    | Econd(be, ub, b, bebl, bo) ->
        let tbe = w_bexpr e be in
        let tb = w_block e b in
        let bel, bl = List.split bebl in
        let tbel = List.map (w_bexpr e) bel in
        let tbl = List.map (w_block e) bl in
        let tbo = Option.map (w_block e) bo in
        unify be.loc tbe.t Tbool;
        List.iter2
            (fun be (tbe: t_bexpr) -> unify be.loc tbe.t Tbool)
            bel tbel;
        let tl = tb.t :: List.map (fun (tb : t_block) -> tb.t) tbl in
        let tl' = (try (Option.get tbo).t ::tl with Invalid_argument _-> tl) in
        let locl = b.loc :: List.map (fun b -> b.loc) bl in
        let locl' = 
            (try (Option.get bo).loc :: locl with Invalid_argument _ -> locl)
        in
        begin try
            eq_type_list (List.combine locl' tl');
            { expr = TEcond(tbe, ub, tb, List.combine tbel tbl, tbo); t=tb.t }
        with ST_alert _ -> raise_mess_terr exp.loc
            "Toutes les branches conditionnelles doivent avoir le même type."
        end

    | Ecall(caller, bel) -> begin
        let tcaller = w_caller e caller in
        let tbel = List.map (w_bexpr e) bel in
        match tcaller.t with
        | Tfun(tl, t) ->
            if List.length tl <> List.length tbel then
                raise (Arg_nb_terr caller)
            else List.iter2
                (fun (tbe:t_bexpr) t -> sous_type caller.loc tbe.t t) tbel tl;
            { expr = TEcall(tcaller, tbel); t = t }
        | _ -> raise (Not_a_fun_terr caller)
        end

    | Elam fb ->
        let (pl, rt, ub, b) = fb.desc in
        let Rtype annot = rt.desc in
        let peeled_pl = List.map peel pl in
        let sl = List.map fst peeled_pl in
        let stl = List.map 
            (fun (id, annot) -> let t = read_type e annot in bf e t; id, t)
            peeled_pl
        in
        let e' = List.fold_left (fun e (id, t) -> add id t false e) e stl in
        let tb = w_block e' b in
        let t = read_type e annot in
        sous_type b.loc tb.t t;
        { expr = TElam(sl, ub, tb); t = Tfun(List.map snd stl, t) }

    | Ecases(
        { desc = Tannot("List",Some([t])); loc = _ } as lt, be, ub,
        [{ desc = ("empty", None, b1); loc = _ };
         { desc = ("link", (Some [x;y]), b2); loc = loc2 }])
    | Ecases(
        { desc = Tannot("List",Some([t])); loc = _ } as lt, be, ub,
        [{ desc = ("link", (Some [x;y]), b2); loc = loc2 };
         { desc = ("empty", None, b1); loc = _ }]) ->

        if Smap.mem x e.bindings then raise (Shadow_terr(loc2, x)) else
        if Smap.mem y e.bindings || (x = y && x <> "_") then
            raise (Shadow_terr(loc2,y)) else

        let tbe = w_bexpr e be in sous_type be.loc tbe.t (read_type e lt);
        let tb1 = w_block e b1  in

        let e_x = if x = "_" then e else add x (read_type e t) false e in
        let e' = if y = "_" then e_x else add y (read_type e_x lt) false e_x in
        let tb2 = w_block e' b2 in
        eq_type b1.loc tb1.t b2.loc tb2.t;
        { expr = TEcases(tbe, ub,
            [("empty", None, tb1);("link", (Some [x;y]), tb2)]);
          t = tb1.t }
    | Ecases _ -> raise (Case_terr exp)

    (* Désucrage de la boucle for *)
    | Eloop(c, froml, rt, ub, b) ->
        let paraml, bexpl = List.split (List.map peel froml) in
        let lam = {
            desc = {
                desc = Elam { desc = (paraml, rt, ub, b); loc = exp.loc };
                loc = exp.loc }, [];
            loc = exp.loc
        } in
        let ecall = { desc = Ecall(c, lam :: bexpl); loc = exp.loc } in
        w_expr e ecall

and w_caller e c = match c.desc with
    | Cident id -> let texp = w_expr e { desc = Eident id; loc = c.loc } in
        begin match texp with
        | { expr = TEident s; t = t } -> 
            ({ caller = TCident s; t = t } : t_caller )
        | _ -> exit 2 end
    | Ccall(caller, bel) ->
        let texp = w_expr e { desc = Ecall(caller, bel); loc = c.loc } in
        begin match texp with
        | { expr = TEcall(c, b); t = t } -> { caller = TCcall(c, b); t = t }
        | _ -> exit 2 end

let w_file e f = let tb = w_block e f in { file = tb.block; t = tb.t }

let type_file f = w_file init_env f

