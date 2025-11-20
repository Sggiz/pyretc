
open Ast
open Format

let binop_assoc = [Eq,"=="; Neq,"<>"; Lneq,"<"; Leq,"<="; Gneq,">"; Geq,">=";
    Add,"+"; Sub,"-"; Mul,"*"; Div,"/"; And,"and"; Or,"or"]


let rec pp_type fmt = function
    | Tannot(s, None) ->
        fprintf fmt "%s" s
    | Tannot(s, Some tl) ->
        fprintf fmt "%s<@[%a%a@]>"
            s
            pp_type (List.hd tl)
            (fun fmt tl -> List.iter (fprintf fmt ",@ %a" pp_type) tl)
                (List.tl tl)
    | Tfun([], rt) ->
        fprintf fmt "(-> @[%a@])" pp_rtype rt
    | Tfun(tl, rt) ->
        fprintf fmt "(@[%a%a@]@ -> @[%a@])"
            pp_type (List.hd tl)
            (fun fmt tl -> List.iter (fprintf fmt ",@ %a" pp_type) tl)
                (List.tl tl)
            pp_rtype rt

and pp_rtype fmt = function | Rtype t -> pp_type fmt t


let rec pp_stmt fmt = function
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
        fprintf fmt "%a" pp_bexpr b
    | _ -> fprintf fmt "@[statement@]"

and pp_block fmt sl =
    pp_stmt fmt @@ List.hd sl;
    List.iter (fun s -> fprintf fmt "@ %a" pp_stmt s) @@ List.tl sl

and pp_bexpr fmt = function
    | e, [] -> 
        fprintf fmt "%a" pp_expr e
    | e, (b,e')::q -> 
        fprintf fmt "%a@ %s@ %a"
            pp_bexpr (e, [])
            (List.assoc b binop_assoc)
            pp_bexpr (e', q)

and pp_expr fmt = function
    | True -> fprintf fmt "true"
    | False -> fprintf fmt "false"
    | Eint n -> fprintf fmt "%d" n
    | Estring s | Eident s -> fprintf fmt "Str(@[%s@])" s
    | Ebexpr bexpr ->
        fprintf fmt "(@[%a@])" pp_bexpr bexpr

    | Econd(cond, ub, b, elifl, elo) ->
        fprintf fmt "if %a :@   @[<v>%a@]@ " pp_bexpr cond pp_block b;
        List.iter (fun (cond, b) ->
            fprintf fmt "else if %a :@   @[<v>%a@]@ " pp_bexpr cond pp_block b)
        elifl;
        begin match elo with
        | None -> fprintf fmt "end"
        | Some b -> fprintf fmt "else:@   @[<v>%a@]@ end" pp_block b
        end


    | Ecall(caller, bexp_list) ->
        pp_caller fmt caller;
        fprintf fmt "(";
        if not (bexp_list = []) then begin
            pp_bexpr fmt (List.hd bexp_list);
            List.iter (fun bexp -> fprintf fmt ",@ %a" pp_bexpr bexp)
                (List.tl bexp_list)
        end;
        fprintf fmt ")"
    | _ -> fprintf fmt "expr@ "

and pp_caller fmt = function
    | Cident s -> fprintf fmt "%s" s
    | Ccall(caller, bexp_list) -> pp_expr fmt (Ecall(caller, bexp_list))

let pp_file fmt f =
    fprintf fmt "file {@ %a}"
        (fun fmt f -> List.iteri (fun i ->
            fprintf fmt "%d: @[<v>%a@]@ " i pp_stmt) f) f


let print_file f = printf "@[<v>%a@]@." pp_file f

