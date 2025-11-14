
(* Analyseur lexical pour Pyret *)

{
    open Lexing
    open Parser
    type tlerr =
        | Charlerr of char
        | Message of string
    exception Lexing_error of tlerr


    let kwd_tbl = ["and",AND; "block",BLOCK; "cases",CASES; "else",ELSE;
        "end",END; "false",FALSE; "for",FOR; "from",FROM; "fun",FUN;
        "if",IF; "lam",LAM; "or",OR; "true",TRUE; "var",VAR]
    let id_or_kwd s = try List.assoc s kwd_tbl with _ -> IDENT s

}

let digit = ['0'-'9']
let letter = ['a'-'z' 'A' - 'Z' '_']
let ident = letter ('-'* (letter | digit)+)*
let integer = ('-' | '+')? (digit)+

rule token = parse
    | '\n'      { new_line lexbuf; token lexbuf }

    | "#|"      { comment 0 lexbuf }
    | '#' [^'|'] [^'\n']*
                { token lexbuf }
    | ident as s
        { id_or_kwd s }
    | eof       { EOF }
    | _ as c    { raise (Lexing_error(Charlerr c)) }

and comment n = parse
    | "#|"      { comment (n+1) lexbuf }
    | "|#"      { if n = 0 then token lexbuf else comment (n-1) lexbuf}
    | eof
        { raise (Lexing_error (Message "commentaire non fermé")) }
    | _         { comment n lexbuf }

and string c sl = parse
    | '\n' | eof
                { raise (Lexing_error(Message
                "chaîne de caractère qui pendouille")) }
    | '\'' | '"' as c'
                { if c = c' then STRING (String.concat "" sl)
                else string c (String.make 1 c :: sl) lexbuf }
    | [^'\n' '\\' '\'' '"']* as s
                { string c (s :: sl) lexbuf }
    | '\\' [ '"' '\'' '\\' ] as s
                { string c (String.make 1 (s.[1]) :: sl) lexbuf }
    | "\\t"     { string c ("\t" :: sl) lexbuf }
    | "\\n"     { string c ("\n" :: sl) lexbuf }
    | _         { raise (Lexing_error (Message
                "Erreur d'échappement dans la chaîne de caractère : \\")) }

