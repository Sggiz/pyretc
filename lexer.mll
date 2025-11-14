
(* Analyseur lexical pour Pyret *)

{
    open Lexing
    open Parser

    exception Lexing_error of char

    let kwd_tbl = []
    let id_or_kwd s = try List.assoc s kwd_tbl with _ -> IDENT s

}

rule token = parse
    | eof       { EOF }
    | _ as c    { raise (Lexing_error c) }
