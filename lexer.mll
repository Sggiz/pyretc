
(* Analyseur lexical pour Pyret *)

{
    open Lexing
    open Parser
    exception Char_lerr of char
    exception Message_lerr of string
    exception BinopSpace_lerr


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
    (* commentaires et espaces *)
    | "#|"
        { comment 0 lexbuf }
    | '#' [^'|'] [^'\n']*
        { token lexbuf }
    | ' ' | '\t'
        { token lexbuf }
    | '\n'
        { new_line lexbuf; token lexbuf}

    (* caracteres atomiques *)
    | ")("  { DP }
    | '('   { LP }
    | ')'   { RP }
    | ','   { COMMA }
    | '='   { DEF }
    | ":="  { REDEF }
    | ":"   { COL }
    | "|"   { BAR }
    | blank+ "::" blank+  { DCOL }
    | "->"  { LARR }
    | '<'   { LANG }
    | '>'   { RANG }
    | ">("  { RANGLP }
    | "=>"  { CARR }
    | "else:"   { ELSEC }
    | "block:"  { BLOCK }

    (* operateurs *)
    | blank+ (binoperator as binop) blank+
        { List.assoc binop binop_tbl }

    (* entiers *)
    | integer as s
        { INTEGER(int_of_string s) }
    (* cas problematique : l'assemblage maladif de statement n'est pas permis*)
    | integer blank* binoperator integer
        { raise BinopSpace_lerr }

    | ('"' | '\'') as c
        { string c [] lexbuf }

    (* appel *)
    | (ident as id) '('
        { match id with
            | "lam" -> LAM
            | "cases" -> raise (Message_lerr
                "Il manque un espace entre 'cases' et son type associé.")
            | _ -> CALL id }
    (* cas problématique d'appel *)
        (* 'if (true)' est illicite ici *)
    | (ident as id) blank+ '('
        { match id with
            | "cases" -> CASES
            | _ -> raise (Message_lerr
        "Il ne doit pas y avoir d'espace entre une fonction et sa paranthèse.")}

    | ident as s
        { match id_or_kwd s with
        |BLOCK -> raise (Message_lerr
            "Le mot-clé 'block' doit être suivi de ':'")
        | AND | OR -> raise BinopSpace_lerr
        | _ as t -> t }
    | eof       { EOF }
    | _ as c    { raise (Char_lerr c) }

and comment n = parse
    | "#|"
        { comment (n+1) lexbuf }
    | "|#"
        { if n = 0 then token lexbuf else comment (n-1) lexbuf}
    | '\n'
        { new_line lexbuf; comment n lexbuf }
    | eof
        { raise (Message_lerr "Commentaire non fermé.") }
    | _ { comment n lexbuf }

and string c sl = parse
    | '\n' | eof
        { raise (Message_lerr "Chaîne de caractère qui pendouille.") }
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
        "Erreur d'échappement dans la chaîne de caractère.") }

