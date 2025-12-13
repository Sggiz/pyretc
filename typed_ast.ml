
open Ast

type typ =
    | Tvar of tvar
    | Tany
    | Tnoth
    | Tbool
    | Tint
    | Tstr
    | Tlist of typ
    | Tfun of typ list * typ

and tvar =
    { id : int;
      mutable def : typ option;
      is_selfdef : bool }

module V = struct
    type t = tvar
    let compare v1 v2 = Stdlib.compare v1.id v2.id
    let equal v1 v2 = v1.id = v2.id
    let create = let r = ref 0 in fun b ->
        incr r; { id = !r; def = None; is_selfdef = b }
end

(* Ast augmenté avec les types *)

type t_block = { block : tt_block; t : typ }
and tt_block = t_stmt list

and t_stmt = { stmt : tt_stmt; t : typ }
and tt_stmt =
    | TSfun of string * string list * t_funbody
    | TSdef of bool * string * t_bexpr (* bool <=> var *)
    | TSredef of string * t_bexpr
    | TSbexpr of t_bexpr

and t_funbody = string list * ublock * t_block

and t_bexpr = { bexpr : tt_bexpr; t : typ }
and tt_bexpr = t_expr * (binop * t_expr) list

and t_expr = { expr : tt_expr; t : typ }
and tt_expr =
    | TTrue
    | TFalse
    | TEint of int
    | TEstring of string
    | TEident of string
    | TEbexpr of t_bexpr
    | TEblock of t_block
    | TEcond of t_bexpr * ublock * t_block * (t_bexpr * t_block) list
        * t_block option
    | TEcall of t_caller * t_bexpr list
    | TElam of t_funbody
    | TEcases of t_bexpr * ublock * tt_branch list
    | TEloop of t_caller * t_from list * ublock * t_block

and t_caller = { caller : tt_caller; t : typ }
and tt_caller =
    | TCident of string
    | TCcall of t_caller * t_bexpr list

and tt_branch = string * string list option * t_block

and t_from = string * t_bexpr


type t_file = { file : tt_file; t : typ }
and tt_file = t_stmt list

