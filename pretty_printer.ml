
open Ast
open Format

let pp_stmt fmt = function
    | _ -> fprintf fmt "-> @[statement@]@?"

let pp_file fmt f =
    fprintf fmt "@[<v>file {@?";
    List.iter (pp_stmt fmt) f;
    fprintf fmt "}@]"


let print_file f = printf "@[%a@]@." pp_file f

