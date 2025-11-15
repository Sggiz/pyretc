
open Ast
open Format

let binop_assoc = []


let rec pp_bexpr fmt = function
    | e, [] -> pp_expr fmt e
    | _ -> fprintf fmt "bexpr@ "

and pp_expr fmt = function
    | True -> fprintf fmt "true"
    | False -> fprintf fmt "false"
    | Eint n -> fprintf fmt "%d" n
    | Estring s -> fprintf fmt "%s" s
    | Ecall(caller, bexp_list) ->
        pp_caller fmt caller;
        fprintf fmt "(";
        if not (bexp_list = []) then begin
            pp_bexpr fmt (List.hd bexp_list);
            List.iter (fun bexp ->
                fprintf fmt ",@ ";
                pp_bexpr fmt bexp)
                (List.tl bexp_list)
        end;
        fprintf fmt ")"
    | _ -> fprintf fmt "expr@ "

and pp_caller fmt = function
    | Cident s -> fprintf fmt "%s" s
    | Ccall(caller, bexp_list) -> pp_expr fmt (Ecall(caller, bexp_list))

let pp_stmt fmt = function
    | Sbexpr b -> 
        fprintf fmt ": @[";
        pp_bexpr fmt b;
        fprintf fmt "@]@."
    | _ -> fprintf fmt ": @[statement@]@?"

let pp_file fmt f =
    fprintf fmt "@[<v>file {@.";
    List.iter (pp_stmt fmt) f;
    fprintf fmt "}@]"


let print_file f = printf "@[%a@]@." pp_file f

