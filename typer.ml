
(* Algo W *)

open Ast
open Typed_ast

exception Message_terr of string
let raise_mess_terr s = raise (Message_terr s)

exception Wrong_terr of typ * typ
let wrong_type t1 t2 = raise (Wrong_terr(t1, t2))

exception Not_a_fun_terr of caller
exception Arg_nb_terr of caller

exception Var_not_def of string
exception Invalid_annot_terr of ty
exception Redef_terr of string
exception Shadow_terr of string
exception BF_terr
exception Case_terr

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

type env = { bindings : schema Smap.t; fvars : Vset.t; varmap : tvar Smap.t }

let empty = { bindings = Smap.empty; fvars = Vset.empty; varmap = Smap.empty }

let update_fvars s =
    Vset.fold (fun v s -> Vset.union (fvars (Tvar v)) s) s Vset.empty

let add s t is_var e =
    let new_vars = fvars t in
    let new_schema = { vars = Vset.empty; typ = t; is_var = is_var } in
    {
        bindings = Smap.add s new_schema e.bindings;
        fvars = Vset.union e.fvars new_vars;
        varmap = e.varmap
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
        varmap = e.varmap
    }

let add_var e s =
    let newvar = V.create () in
    {
        bindings = e.bindings;
        fvars = Vset.add newvar e.fvars;
        varmap = Smap.add s newvar e.varmap
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

let check_type t1 t2 = if canon t1 <> canon t2 then wrong_type t1 t2


let sous_type t1 t2 =
    let rec verif m t1 t2 =
        match head t1, head t2 with
        | _, Tany -> m
        | Tlist(ta), Tlist(tb) -> verif m ta tb
        | Tfun(tl1, ta), Tfun(tl2, tb) ->
            if (List.length tl1) <> (List.length tl2) then wrong_type t1 t2;
            let m' = verif m ta tb in
            List.fold_left2 verif m' tl2 tl1
        | (Tvar v1 as ht1), Tvar v2 ->
            if V.equal v1 v2 then m else begin
            try let t = Vmap.find v2 m in verif m ht1 t
            with Not_found -> Vmap.add v2 ht1 m
        end
        | ht1, Tvar v2 -> begin
            try let t = Vmap.find v2 m in verif m ht1 t
            with Not_found -> Vmap.add v2 ht1 m
        end
        | Tvar v1, ht2 -> begin
            try let t = Vmap.find v1 m in verif m t ht2
            with Not_found -> Vmap.add v1 ht2 m
        end
        | _, _ -> check_type t1 t2; m
    in
    let m = verif Vmap.empty t1 t2 in
    let f (var, t) = var.def <- Some t in
    List.iter f (Vmap.bindings m)

let check_binop t1 bin t2 = match bin with
    | Add -> begin match t1, t2 with
        | Tint, t | t, Tint -> sous_type t Tint; Tint
        | Tstr, t | t, Tstr -> sous_type t Tstr; Tstr
        | _ -> wrong_type t1 Tint end
    | Sub | Mul | Div -> sous_type t1 Tint; sous_type t2 Tstr; Tstr
    | Eq | Neq -> Tbool
    | Lneq | Leq | Gneq | Geq ->
        sous_type t1 Tint; sous_type t2 Tint; Tbool
    | And | Or ->
        sous_type t1 Tbool; sous_type t2 Tbool; Tbool

let eq_type t1 t2 = sous_type t1 t2; sous_type t2 t1

let rec eq_type_list = function
    | [] | [_] -> ()
    | t1 :: t2 :: q -> eq_type t1 t2; eq_type_list (t2 :: q)

let rec bf e t =
    match head t with
    | Tvar v -> if not @@ Vset.mem v e.fvars then raise BF_terr
    | Tlist t -> bf e t
    | Tfun(tl, t) -> List.iter (bf e) tl; bf e t
    | _ -> ()

let rec read_type e = function
    | Tannot("Any", None) -> Tany
    | Tannot("Nothing", None) -> Tnoth
    | Tannot("Boolean", None) -> Tbool
    | Tannot("Number", None) -> Tint
    | Tannot("String", None) -> Tstr
    | Tannot("List", Some([t])) -> Tlist (read_type e t)
    | Tfun(tyl, Rtype(t)) -> Tfun(List.map (read_type e)tyl, read_type e t)
    | Tannot(x, None) as t ->
        begin try
            Tvar(Smap.find x e.varmap)
        with Not_found -> raise (Invalid_annot_terr t) end
    | _ as t -> raise (Invalid_annot_terr t)

let ping () = Format.printf "ping@."
let pingarg f a = Format.printf "ping : %a@." f a

let rec w_block e = function
    | [] -> { block = []; t = Tnoth }
    | [s] -> let _, ts = w_stmt e s in
        { block = [ts]; t = ts.t }
    | s::q -> let new_env, ts = w_stmt e s in let tb = w_block new_env q in
        { block = ts::tb.block; t = tb.t }

and w_stmt e = function
    | Sfun(f, targl, (paraml, rt, ub ,b)) ->
        let idl, annotl = List.split paraml in
        let new_env = List.fold_left add_var e targl in

        let tl, t = begin
            match read_type new_env (Tfun(annotl, rt)) with
            | Tfun(tl, t) -> tl, t
            | _ -> raise (Message_terr "Erreur de lecture de type d'une fonction.")
        end in

        List.iter (bf new_env) tl;

        let sch = { 
            vars = List.fold_left
                (fun s id -> Vset.add (Smap.find id new_env.varmap) s)
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
            varmap = inner_env.varmap
        } in
        let tb = w_block rec_env b in
        sous_type tb.t t;
        let next_env = {
            bindings = Smap.add f sch e.bindings;
            fvars = e.fvars;
            varmap = e.varmap
        } in
        next_env, { stmt = TSfun(f, targl, (idl, ub, tb)); t = Tfun(tl, t) }


    | Sdef(b, id, tyo, be) ->
        if Smap.mem id e.bindings then raise (Shadow_terr id) else
        let tbe = w_bexpr e be in
        begin match tyo with 
            | None->()
            | Some(t)-> sous_type tbe.t (read_type e t)
        end;
        begin if b then add id tbe.t true e else add_gen id tbe.t e end,
        { stmt = TSdef(b, id, tbe); t = tbe.t }
    | Sredef(id, be) ->
        begin try
            let sch = Smap.find id e.bindings in
            if not sch.is_var then
                raise (Redef_terr id)
            else let t = find id e in
            let tbe = w_bexpr e be in
            sous_type tbe.t t;
            e, { stmt = TSredef(id, tbe); t = Tnoth }
        with Not_found -> raise (Var_not_def id) end
    | Sbexpr be -> let tbe = w_bexpr e be in
        e, { t = tbe.t; stmt = TSbexpr tbe }

and w_bexpr e = function
    | exp, [] -> let texp = w_expr e exp in
        ({ bexpr = (texp, []); t = texp.t } : t_bexpr)
    | exp1, [bin, exp2] -> let texp1, texp2 = w_expr e exp1, w_expr e exp2 in
        { bexpr = (texp1, [bin, texp2]); t = check_binop texp1.t bin texp2.t }
    | exp1, (bin, exp2)::q ->
        let {bexpr=(te2, l);t=t} = w_bexpr e (exp2, q) in
        let texp1 = w_expr e exp1 in
        if bin <> Eq && bin <> Neq then check_type texp1.t te2.t;
        { bexpr = (texp1, (bin, te2)::l); t=t}

and w_expr e = function
    | True -> { expr = TTrue; t = Tbool }
    | False -> { t = Tbool; expr = TFalse }
    | Eint k -> { t = Tint; expr = TEint k }
    | Estring s -> { t = Tstr; expr = TEstring s }
    | Eident id -> begin try
        let t = find id e in
        { expr = TEident id; t = t }
        with Not_found -> raise (Var_not_def id) end

    | Ebexpr be -> let tbe = w_bexpr e be in
        { t = tbe.t; expr = TEbexpr tbe }

    | Eblock b -> let tb = w_block e b in
        { t = tb.t; expr = TEblock tb }

    | Econd(be, ub, b, bebl, bo) ->
        let tbe = w_bexpr e be
        and tb = w_block e b
        and tbebl = List.map (fun (be,b) -> (w_bexpr e be, w_block e b)) bebl
        and tbo = Option.map (w_block e) bo in
        check_type tbe.t Tbool;
        List.iter (fun ((tbe : t_bexpr), _) -> check_type tbe.t Tbool) tbebl;
        let tl = tb.t :: List.map (fun (_,(tb : t_block)) -> tb.t) tbebl in
        let tl' = (try (Option.get tbo).t ::tl with Invalid_argument _-> tl) in
        eq_type_list tl';
        { expr = TEcond(tbe, ub, tb, tbebl, tbo); t = tb.t }

    | Ecall(caller, bel) -> begin
        let tcaller = w_caller e caller in
        let tbel = List.map (w_bexpr e) bel in
        match tcaller.t with
        | Tfun(tl, t) ->
            if List.length tl <> List.length tbel then
                raise (Arg_nb_terr caller)
            else List.iter2 (fun (tbe:t_bexpr) t -> sous_type tbe.t t) tbel tl;
            { expr = TEcall(tcaller, tbel); t = t }
        | _ -> raise (Not_a_fun_terr caller) end

    | Elam (pl, (Rtype annot), ub, b) ->
        let sl = List.map fst pl in
        let stl = List.map 
            (fun (id, annot) -> let t = read_type e annot in bf e t; id, t) pl
        in
        let e' = List.fold_left (fun e (id, t) -> add id t false e) e stl in
        let tb = w_block e' b in
        let t = read_type e annot in
        sous_type tb.t t;
        { expr = TElam(sl, ub, tb); t = Tfun(List.map snd stl, t) }

    | Ecases((Tannot("List",Some([t])) as lt), be, ub,
        [("empty", None, b1);("link", (Some [x;y]), b2)])
    | Ecases((Tannot("List",Some([t])) as lt), be, ub,
        [("link",(Some [x;y]), b2);("empty",None,b1)]) ->

        if Smap.mem x e.bindings then raise (Shadow_terr x) else
        if Smap.mem y e.bindings || x = y then raise (Shadow_terr y) else

        let tbe = w_bexpr e be in sous_type tbe.t (read_type e lt);
        let tb1 = w_block e b1  in
        let e' = e 
            |> add x (read_type e t) false
            |> add y (read_type e lt) false
        in
        let tb2 = w_block e' b2 in
        eq_type tb1.t tb2.t;
        { expr = TEcases(tbe, ub,
            [("empty", None, tb1);("link", (Some [x;y]), tb2)]);
          t = tb1.t }
    | Ecases _ -> raise Case_terr

    (* Désucrage de la boucle for *)
    | Eloop(c, froml, rt, ub, b) ->
        let paraml, bexpl = List.split froml in
        let lam = Elam (paraml, rt, ub, b),[] in
        let ecall = Ecall(c, lam :: bexpl) in
        w_expr e ecall

and w_caller e = function
    | Cident id -> let texp = w_expr e (Eident id) in
        begin match texp with
        | { expr = TEident s; t = t } -> 
            ({ caller = TCident s; t = t } : t_caller )
        | _ -> exit 2 end
    | Ccall(caller, bel) -> let texp = w_expr e (Ecall(caller, bel)) in
        begin match texp with
        | { expr = TEcall(c, b); t = t } -> { caller = TCcall(c, b); t = t }
        | _ -> exit 2 end

let w_file e f = let tb = w_block e f in { file = tb.block; t = tb.t }

let type_file f = w_file init_env f

