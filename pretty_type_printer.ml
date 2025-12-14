
open Typed_ast
open Format

let binop_assoc = Ast.(
    [Eq,"=="; Neq,"<>"; Lneq,"<"; Leq,"<="; Gneq,">"; Geq,">=";
    Add,"+"; Sub,"-"; Mul,"*"; Div,"/"; And,"and"; Or,"or"] )

let pp_list sep pp fmt l = if l <> [] then begin
    pp fmt @@ List.hd l;
    List.iter (fprintf fmt "%s@ %a" sep pp) @@ List.tl l
    end

let rec tp_typ fmt t = match t with
    | Tvar { id = _; def = Some t' } -> tp_typ fmt t'
    | Tvar v -> fprintf fmt "V%d" v.id
    | Tany -> fprintf fmt "Any"
    | Tnoth -> fprintf fmt "Nothing"
    | Tbool -> fprintf fmt "Bool"
    | Tint -> fprintf fmt "Number"
    | Tstr -> fprintf fmt "String"
    | Tlist t -> fprintf fmt "List<%a>" tp_typ t
    | Tfun(tl, t) -> fprintf fmt "(%a -> %a)" (pp_list "," tp_typ) tl tp_typ t


let rec tp_stmt fmt ts = match ts.stmt with
    | TSbexpr tb -> fprintf fmt "@[%a@]" tp_bexpr tb
    | TSdef(bool, id, tbe) ->
        fprintf fmt "@[%s%s :: %a@]" (if bool then "var " else "") id
            tp_typ tbe.t
    | TSredef(id, tbe) ->
        fprintf fmt "@[redef (%s :: %a) :: %a@]" id tp_typ tbe.t tp_typ ts.t
    | TSfun(f, targl, _) ->
        fprintf fmt "@[%s<%a> :: %a@]"
            f (pp_list "," (fun fmt s -> fprintf fmt "%s" s)) targl tp_typ ts.t

and tp_bexpr fmt tbe = match tbe.bexpr with
    | e, [] -> fprintf fmt "%a" tp_expr e
    | e1, (bin, e2)::q -> fprintf fmt "%a :: @[%a@]" tp_typ tbe.t
        (pp_list (" "^(List.assoc bin binop_assoc)) tp_expr)
        (e1 :: List.map snd ((bin,e2)::q))

and tp_expr fmt te = match te.expr with
    | _ -> fprintf fmt "%a" tp_typ te.t

let tp_file fmt tf =
    fprintf fmt "types : %a {@ %a}"
        tp_typ tf.t
        (fun fmt f -> List.iteri (fun i ->
            fprintf fmt "%d: @[<v>%a@]@ " i tp_stmt) f) tf.file


let tprint_file f = printf "@[<v>%a@]@." tp_file f

