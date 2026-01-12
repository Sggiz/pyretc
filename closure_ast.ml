
(* Ast avec les fermetures et portées *)

type binop = Ast.binop
type typ = Typed_ast.typ

type var =
    | Vglobal of string
    | Vlocal of int
    | Vclos of int

type 'a c_ast = { desc : 'a ; t : typ }

type c_block = cc_block c_ast
and cc_block = c_stmt list

and c_stmt = cc_stmt c_ast
and cc_stmt =
    | CSfun of int * string * var array
    | CSdef of int * c_bexpr
    | CSbexpr of c_bexpr

and c_bexpr = cc_bexpr c_ast
and cc_bexpr = c_expr * (binop * c_expr) list

and c_expr = cc_expr c_ast
and cc_expr =
    | CTrue
    | CFalse
    | CEint of int
    | CEstring of string
    | CEvar of var
    | CEbexpr of c_bexpr
    | CEblock of c_block
    | CEcond of c_bexpr * c_block * (c_bexpr * c_block) list
        * c_block option
    | CEprint of c_bexpr
    | CEcall of c_caller * c_bexpr list
    | CEcases of c_bexpr * c_block * int option * int option * c_block
        (* cas empty puis cas link *)

and c_caller = cc_caller c_ast
and cc_caller =
    | CCvar of var
    | CCcall of c_caller * c_bexpr list

type c_file = cc_file c_ast * int * (string * int * c_block) list
and cc_file = c_stmt list


