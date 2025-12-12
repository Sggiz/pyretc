
(* Syntaxe abstraite pour le langage Pyret *)

exception Block_perr
exception Message_perr of string


type binop = Eq | Neq | Lneq | Leq | Gneq | Geq | Add | Sub | Mul | Div
    | And | Or

type 'a ast = { desc : 'a; loc : Lexing.position * Lexing.position }

let peel (a : 'a ast) = a.desc

type ty = a_ty ast
and a_ty =
    | Tannot of string * ty list option
    | Tfun of ty list * rty

and rty = a_rty ast
and a_rty = Rtype of ty

type ublock = a_ublock ast
and a_ublock = Colon | BlockColon

type block = a_block ast
and a_block = stmt list

and stmt = a_stmt ast
and a_stmt =
    | Sfun of string * string list * funbody
    | Sdef of bool * string * ty option * bexpr (* bool <=> var *)
    | Sredef of string * bexpr
    | Sbexpr of bexpr

and funbody = a_funbody ast
and a_funbody = param list * rty * ublock * block

and param = a_param ast
and a_param = string * ty

and bexpr = a_bexpr ast
and a_bexpr = expr * (binop * expr) list

and expr = a_expr ast
and a_expr =
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

and caller = a_caller ast
and a_caller =
    | Cident of string
    | Ccall of caller * bexpr list

and branch = a_branch ast
and a_branch = string * string list option * block

and from = a_from ast
and a_from = param * bexpr

type file = a_file ast
and a_file = stmt list

