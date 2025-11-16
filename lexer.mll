
(* Analyseur lexical pour Pyret *)

{
    open Lexing
    open Parser
    exception Char_lerr of char
    exception Message_lerr of string


    let kwd_tbl = ["and",AND; "block",BLOCK; "cases",CASES; "else",ELSE;
        "end",END; "false",FALSE; "for",FOR; "from",FROM; "fun",FUN;
        "if",IF; "lam",LAM; "or",OR; "true",TRUE; "var",VAR]
    let id_or_kwd s = try List.assoc s kwd_tbl with _ -> IDENT s

    let binop_tbl = ["==",EQ; "<>",NEQ; "<",LNEQ; "<=",LEQ; ">",GNEQ; ">=",GEQ;
        "+",PLUS; "-",MINUS; "*",TIMES; "/",DIV; "and",AND; "or",OR]
}

let digit = ['0'-'9']
let letter = ['a'-'z' 'A' - 'Z' '_']
let ident = letter ('-'* (letter | digit)+)*
let integer = ('-' | '+')? (digit)+
let blank = [' ' '\t' '\n']
let binoperator = ("=="|"<>"|"<"|"<="|">"|">="|"+"|"-"|"*"|"/"|"and"|"or")

rule token = parse
    | '\n'
        { new_line lexbuf; NL }

    (* commentaires et espaces *)
    | "#|"
        { comment 0 lexbuf }
    | '#' [^'|'] [^'\n']*
        { token lexbuf }
    | ' ' | '\t'
        { token lexbuf }

    (* caracteres atomiques *)
    | ")("  { DP }
    | '('   { LP }
    | ')'   { RP }
    | ','   { COMMA }
    | '='   { DEF }
    | ":="  { REDEF }
    | "::"  { DCOL }
    | "->"  { LARR }

    (* operateurs *)
    | blank+ (binoperator as binop) blank+
        { List.assoc binop binop_tbl }

    | integer as s
        { INTEGER(int_of_string s) }
    | ('"' | '\'') as c
        { string c [] lexbuf }

    | (ident as s) '('
        { CALL s }
    | ident as s
        { id_or_kwd s }
    | eof       { EOF }
    | _ as c    { raise (Char_lerr c) }

and comment n = parse
    | "#|"
        { comment (n+1) lexbuf }
    | "|#"
        { if n = 0 then token lexbuf else comment (n-1) lexbuf}
    | eof
        { raise (Message_lerr "commentaire non fermé") }
    | _ { comment n lexbuf }

and string c sl = parse
    | '\n' | eof
        { raise (Message_lerr "chaîne de caractère qui pendouille") }
    | '\'' | '"' as c'
        { if c = c' then STRING (String.concat "" @@ List.rev sl)
        else string c (String.make 1 c' :: sl) lexbuf }
    | [^'\n' '\\' '\'' '"']* as s
        { string c (s :: sl) lexbuf }
    | '\\' ([ '"' '\'' '\\' ] as c')
        { string c (String.make 1 c' :: sl) lexbuf }
    | "\\t"
        { string c ("\t" :: sl) lexbuf }
    | "\\n"
        { string c ("\n" :: sl) lexbuf }
    | _ { raise (Message_lerr
        "Erreur d'échappement dans la chaîne de caractère") }

