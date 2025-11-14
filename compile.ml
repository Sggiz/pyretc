
(* Production de code pour le langage Pyret *)

open Format
open X86_64
open Ast

(* Exception à lever quand une variable est mal utilisée *)
exception VarUndef of string

(* Taille du tableau d'activation *)
let frame_size = ref 0

(* Table d'association pour la position par rapport à %rbp (en octets)
   des variables locales *)
module StrMap = Map.Make(String)

(* Raccourci pour ajouter des sauts de ligne dans le code assembleur produit *)
let newline = inline "\n"

(* Compilation ... *)



(* Compile le fichier f et enregistre le code dans le fichier ofile *)
let compile_file f ofile =
    let code = nop in
    if !frame_size mod 16 = 8 then frame_size := 8 + !frame_size;
    let p =
        { text =
            globl "main" ++ label "main" ++
            (* alignement de la pile *)
            pushq !%rbp ++
            movq !%rsp !%rbp ++
            newline ++
            (* reservation de l'espace pour les variables locales *)
            subq (imm !frame_size) !%rsp ++
            newline ++

            code ++

            leave ++
            ret ++
            newline ++

            label "print_int" ++
            pushq !%rbp ++ (* assure notamment l'alignement *)
            movq !%rdi !%rsi ++
            leaq (lab ".Sprint_int") rdi ++
            movq (imm 0) !%rax ++
            call "printf" ++
            popq rbp ++
            ret ++
            newline;

          data =
            label ".Sprint_int" ++ string "%d\n"
        }
    in
    let f_out = open_out ofile in
    let fmt = formatter_of_out_channel f_out in
    X86_64.print_program fmt p;
    (* on "flush" le buffer afin de s'assurer que tout y a été écrit
       avant de le fermer *)
    fprintf fmt "@?";
    close_out f_out

