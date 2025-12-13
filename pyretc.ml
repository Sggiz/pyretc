
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

let localisation2 (p1, p2) =
    let l1, l2 = p1.pos_lnum, p2.pos_lnum in
    if l1 = l2 then
        let c1 = p1.pos_cnum - p1.pos_bol + 1 in
        let c2 = p2.pos_cnum - p2.pos_bol + 1 in
        eprintf "File \"%s\", line %d, characters %d-%d:\n" !ifile l1 (c1-1) c2
    else
        eprintf "File \"%s\", lines %d-%d:\n" !ifile l1 l2


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
            eprintf "Un opérateur binaire doit être encadré d'espaces.@.";
            exit 1


        | Parser.Error ->
            ping_loc ();
            eprintf "Erreur dans l'analyse syntaxique@.";
            exit 1
        | Ast.Block_perr ->
            ping_loc ();
            eprintf "Erreur d'utilisation du block.@.";
            exit 1
        | Ast.Message_perr s ->
            ping_loc ();
            eprintf "%s@." s;
            exit 1


        | Typer.Message_terr(loc, s) ->
            localisation2 loc;
            eprintf "%s@." s;
            exit 1
        | Typer.Unification_terr(loc, t1, t2, ut1, ut2) -> Pretty_type_printer.(
            localisation2 loc;
            eprintf "Erreur de type : Unification\n";
            eprintf "Cette expression a le type %a, " tp_typ t1;
            eprintf "mais devrait être de type %a.\n" tp_typ t2;
            eprintf "(Erreur d'unification sur %a et %a)@."
                tp_typ ut1 tp_typ ut2;
            exit 1)
        | Typer.ST_terr(loc, t1, t2, ut1, ut2) -> Pretty_type_printer.(
            localisation2 loc;
            eprintf "Erreur de type : Sous-typage\n";
            eprintf "Cette expression a le type %a, " tp_typ t1;
            eprintf "mais devrait être un sous-type de %a.\n" tp_typ t2;
            eprintf "(Erreur de sous-typage sur %a et %a)@."
                tp_typ ut1 tp_typ ut2;
            exit 1)
        | Typer.Wrong_type_terr(loc, t1, t2) -> Pretty_type_printer.(
            localisation2 loc;
            eprintf "Erreur de type :\n";
            eprintf "Cette expression a le type %a, " tp_typ t1;
            eprintf "mais devrait être de type %a." tp_typ t2;
            exit 1)
        | Typer.Not_a_fun_terr c ->
            localisation2 c.loc;
            eprintf "Erreur de type : %a n'est pas une fonction.@."
                Pretty_printer.pp_caller c;
            exit 1
        | Typer.Arg_nb_terr c ->
            localisation2 c.loc;
            eprintf
                "Erreur d'arité : %a n'a pas reçu le bon nombre d'arguments.@."
                Pretty_printer.pp_caller c;
            exit 1
        | Typer.Var_not_def(loc, id) ->
            localisation2 loc;
            eprintf "La variable %s n'est pas définie.@." id;
            exit 1
        | Typer.Invalid_annot_terr ty ->
            localisation2 ty.loc;
            eprintf "L'annotation %a ne correspond pas à un type valide.@."
                Pretty_printer.pp_type ty;
            exit 1
        | Typer.Redef_terr(loc, id) ->
            localisation2 loc;
            eprintf "La variable %s ne peut être redéfinie.@." id;
            exit 1
        | Typer.Shadow_terr(loc, id) ->
            localisation2 loc;
            eprintf
            "La variable %s a déjà été introduite et ne peut être écrasée.@."
                id;
            exit 1
        | Typer.BF_terr annot ->
            localisation2 annot.loc;
            eprintf "Le type annoté %a n'est pas bien formé.@."
                Pretty_printer.pp_type annot;
            exit 1
        | Typer.Case_terr exp ->
            localisation2 exp.loc;
            eprintf "Mauvaise utilisation de l'expression 'cases'.@.";
            exit 1


        | Compile.VarUndef s ->
            eprintf "Erreur de compilation: la variable %s n'est pas définie@."
            s;
            exit 1

