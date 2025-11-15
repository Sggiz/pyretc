
(* Syntaxe abstraite pour le langage Pyret *)

type file = stmt list

and block = stmt list (* non vide *)

and stmt =
    | Sfun of string * string list * funbody
    | Sbind of bool * string * ty option * bexpr (* bool <=> var *)
    | Srebind of string * bexpr
    | Sbexpr of bexpr

and funbody = param list * rty * ublock * block

and param = string * ty

and rty = Rtype of ty

and ublock = Colon | BlockColon

and ty =
    | Tannot of string * ty list option
    | Tfun of ty list * rty

and bexpr = expr * (binop * expr) list

and expr =
    | True
    | False
    | Eint of int
    | Estring of string
    | Eident of string
    | Ebexpr of bexpr
    | Eblock of block
    | Econd of bexpr * ublock * block * (bexpr * block) list * block option
    | Ecall of caller * bexpr list
    | Elam of funbody
    | Ecases of ty * bexpr * ublock * branch list
    | Eloop of caller * from list * rty * ublock * block

and caller =
    | Cident of string
    | Ccall of caller * bexpr list

and branch = string * string list option * block

and from = param * bexpr

and binop = Eq | Neq | Lneq | Leq | Gneq | Geq | Add | Sub | Mul | Div
    | And | Or

