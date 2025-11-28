
(* Fichier principal du compilateur pyretc *)

open Format
open Lexing

(* Option de comilation, pour s'arrêter à l'issue du parser/typeur *)
let parse_only = ref false
let type_only = ref false


(* Noms des fichiers source et cible *)
let ifile = ref ""
let ofile = ref ""

let set_file f s = f := s

(* Les options du compilateur que l'on affiche en tapant pyretc --help *)
let options = [
    "--parse-only", Arg.Set parse_only,
    "  Pour ne faire uniquement que la phase d'analyse syntaxique";
    "--type-only", Arg.Set type_only,
    "  Pour ne faire que la phase d'analyse syntaxique et sémantique";
    "-o", Arg.String (set_file ofile),
    "<file>  Pour indiquer le nom du fichier de sortie"]

let usage = "usage: pyretc [option] file.arr"

(* localise une erreur en indiquant la ligne et la colonne *)
let localisation pos =
    let l = pos.pos_lnum in
    let c = pos.pos_cnum - pos.pos_bol + 1 in
    eprintf "File \"%s\", line %d, characters %d-%d:\n" !ifile l (c-1) c

let () =
    (* Parsing de la ligne de commande *)
    Arg.parse options (set_file ifile) usage;

    (* On vérifie que le nom du fichier a bien été indiqué *)
    if !ifile="" then begin eprintf "Aucun fichier à compiler\n@?";exit 1 end;

    (* Ce fichier doit avoir l'extension .arr *)
    if not (Filename.check_suffix !ifile ".arr") then begin
        eprintf "Le fichier d'entrée doit avoir l'extension .arr\n@?";
        Arg.usage options usage;
        exit 1
    end;

    (* Défault : le nom du fichier cible correspond au fichier source *)
    if !ofile="" then ofile := Filename.chop_suffix !ifile ".arr" ^ ".s";

    (* Ouverture du fichier source en lecture *)
    let f_in = open_in !ifile in

    (* Création d'un tampon d'analyse lexicale *)
    let buf = Lexing.from_channel f_in in

    let ping_loc () = localisation (Lexing.lexeme_start_p buf) in

    try
        let f = Parser.file Lexer.token buf in
        close_in f_in;

        if !parse_only then (Pretty_printer.print_file f; exit 0);

        if !type_only then (
            Pretty_printer.print_file f;
            Pretty_type_printer.tprint_file @@ Typer.type_file f;
            exit 0);

        Compile.compile_file f !ofile;

        ignore (ping_loc)
    with
        | Lexer.Char_lerr c ->
            ping_loc ();
            eprintf "Erreur dans l'analyse lexicale au caractère: '%s'@."
                (Char.escaped c);
            exit 1
        | Lexer.Message_lerr s ->
            ping_loc ();
            eprintf "%s@." s;
            exit 1
        | Lexer.BinopSpace_lerr ->
            ping_loc ();
            eprintf "Un opérateur binaire doit être encadré d'espaces.";
            exit 1

        | Parser.Error ->
            ping_loc ();
            eprintf "Erreur dans l'analyse syntaxique@.";
            exit 1

        | Typer.Message_terr s ->
            eprintf "%s@." s;
            exit 1

        | Compile.VarUndef s ->
            eprintf "Erreur de compilation: la variable %s n'est pas définie@."
            s;
            exit 1

        | _ -> eprintf "Erreur ???@."; exit 1

