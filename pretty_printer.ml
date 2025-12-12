
open Ast
open Format

let binop_assoc = [Eq,"=="; Neq,"<>"; Lneq,"<"; Leq,"<="; Gneq,">"; Geq,">=";
    Add,"+"; Sub,"-"; Mul,"*"; Div,"/"; And,"and"; Or,"or"]

let pp_list sep pp fmt l = if l <> [] then begin
    pp fmt @@ List.hd l;
    List.iter (fprintf fmt "%s@ %a" sep pp) @@ List.tl l
    end

let pp_ident fmt id = fprintf fmt "%s" id

let pp_ublock fmt ub = fprintf fmt "%s"
    (match ub.desc with Colon->":" |BlockColon->"block:")

let rec pp_type fmt t = match t.desc with
    | Tannot(s, None) ->
        fprintf fmt "%s" s
    | Tannot(s, Some tl) ->
        fprintf fmt "%s<@[%a@]>" s (pp_list "," pp_type) tl
    | Tfun(tl, rt) ->
        fprintf fmt "(@[%a@] @[%a@])"
            (pp_list "," pp_type) tl
            pp_rtype rt

and pp_rtype fmt rt = let Rtype t = rt.desc in
    fprintf fmt "-> %a" pp_type t


let rec pp_stmt fmt s = match s.desc with
    | Sfun(f, [], fb) ->
        fprintf fmt "fun %s%a" f pp_funbody fb
    | Sfun(f, idl, fb) ->
        fprintf fmt "fun %s<%a>%a"
            f
            (pp_list "," pp_ident) idl
            pp_funbody fb
    | Sdef(bvar, id, None, bexpr) ->
        fprintf fmt "%s%s = @[%a@]"
            (if bvar then "var " else "")
            id
            pp_bexpr bexpr
    | Sdef(bvar, id, Some ty, bexpr) ->
        fprintf fmt "%s%s :: %a = @[%a@]"
            (if bvar then "var " else "")
            id
            pp_type ty
            pp_bexpr bexpr
    | Sredef(id, bexpr) ->
        fprintf fmt "%s := @[%a@]" id pp_bexpr bexpr
    | Sbexpr b ->
        fprintf fmt "@[%a@]" pp_bexpr b

and pp_funbody fmt fb = let (param_list, rt, ub, b) = fb.desc in
    fprintf fmt "(%a) %a %a@   @[<v>%a@]@ end"
        (pp_list "," pp_param) param_list
        pp_rtype rt
        pp_ublock ub
        pp_block b

and pp_param fmt p = let (id, t) = p.desc in
    fprintf fmt "%s :: %a" id pp_type t

and pp_block fmt b = let sl = b.desc in
    pp_stmt fmt @@ List.hd sl;
    List.iter (fun s -> fprintf fmt "@ %a" pp_stmt s) @@ List.tl sl

and pp_bexpr fmt be = match be.desc with
    | e, [] -> 
        fprintf fmt "%a" pp_expr e
    | e, (b,e')::q -> 
        fprintf fmt "%a@ %s@ %a"
            pp_bexpr { desc = (e, []); loc = be.loc }
            (List.assoc b binop_assoc)
            pp_bexpr { desc = (e', q); loc = be.loc }

and pp_expr fmt e = match e.desc with
    | True -> fprintf fmt "true"
    | False -> fprintf fmt "false"
    | Eint n -> fprintf fmt "%d" n
    | Estring s -> fprintf fmt "\"%s\"" @@ String.escaped s
    | Eident s -> fprintf fmt "%s" s
    | Ebexpr bexpr ->
        fprintf fmt "(@[%a@])" pp_bexpr bexpr

    | Eblock block ->
        fprintf fmt "@[<v>block:@   @[<v>%a@]@]" pp_block block

    | Econd(cond, ub, b, elifl, elo) ->
        open_vbox 0;
        fprintf fmt "if @[%a@] %a@   @[<v>%a@]@ " 
            pp_bexpr cond 
            pp_ublock ub
            pp_block b;
        List.iter (fun (cond, b) ->
            fprintf fmt "else if @[%a@] :@   @[<v>%a@]@ " 
            pp_bexpr cond pp_block b)
        elifl;
        begin match elo with
        | None -> fprintf fmt "end"
        | Some b -> fprintf fmt "else:@   @[<v>%a@]@ end" pp_block b
        end;
        close_box ()


    | Ecall(caller, bexp_list) ->
        fprintf fmt "%a(@[%a@])"
            pp_caller caller
            (pp_list "," pp_bexpr) bexp_list

    | Elam fb -> fprintf fmt "lam%a" pp_funbody fb

    | Ecases(t, be, ub, bl) ->
        fprintf fmt "@[<v>@[<v 2>cases (%a) @[%a@] %a@ %a@]@ end@]"
            pp_type t
            pp_bexpr be
            pp_ublock ub
            (pp_list "" pp_branch) bl

    | Eloop(c, fl, rt, ub, b) ->
        fprintf fmt "@[<v>for %a(%a) %a %a@ @[<v>%a@]@ end@]"
            pp_caller c
            (pp_list "," pp_from) fl
            pp_rtype rt
            pp_ublock ub
            pp_block b

and pp_from fmt f = let (p, be) = f.desc in
    fprintf fmt "%a from %a" pp_param p pp_bexpr be

and pp_caller fmt c = match c.desc with
    | Cident s -> fprintf fmt "%s" s
    | Ccall(caller, bexp_list) ->
            pp_expr fmt { desc = Ecall(caller, bexp_list); loc = c.loc }

and pp_branch fmt b = match b.desc with
    | (id, None, b) -> fprintf fmt "| %s => @[<v>%a@]" id pp_block b
    | (id, Some(pl), b) ->
        fprintf fmt "| %s(@[%a@]) => @[<v>%a@]"
            id (pp_list "," pp_ident) pl pp_block b


let pp_file fmt f =
    fprintf fmt "file {@ %a}"
        (fun fmt f -> List.iteri (fun i ->
            fprintf fmt "%d: @[<v>%a@]@ " i pp_stmt) f) f.desc


let print_file f = printf "@[<v>%a@]@." pp_file f

