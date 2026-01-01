
(* Production de code pour le langage Pyret *)

open Format
open X86_64
open Typed_ast

(* Exception à lever quand une variable est mal utilisée *)
exception VarUndef of string

(* Taille du tableau d'activation *)
let frame_size = ref 0

(* Table d'association pour la position par rapport à %rbp (en octets)
   des variables locales *)
module StrMap = Map.Make(String)

(* Table d'association pour les string de l'utilisateur *)
let string_data_count = ref 0
let string_data_table = Hashtbl.create 5
let string_data_n = Format.sprintf "string_data_%d"

(* Raccourci pour ajouter des sauts de ligne dans le code assembleur produit *)
let newline = inline "\n"

(* Fonctions d'allocation de mémoire *)

let call_my_malloc nb_bytes =
    movq (imm nb_bytes) !%rdi ++
    call "my_malloc"

let my_malloc_code =
    label "my_malloc" ++
    pushq !%rbp ++
    movq !%rsp !%rbp ++
    andq (imm (-16)) !%rsp ++
    call "malloc" ++
    movq !%rbp !%rsp ++
    popq rbp ++
    ret


let prealloc_data =
    label "pre_nothing" ++
    dquad [0] ++
    label "pre_false" ++
    dquad [0] ++
    label "pre_true" ++
    dquad [0]

let prealloc_init =
    comment "Preallocations" ++

    call_my_malloc 1 ++
    movb (imm 0) (ind rax) ++
    movq !%rax (lab "pre_nothing") ++

    call_my_malloc 2 ++
    movb (imm 1) (ind rax) ++
    movb (imm 0) (ind ~ofs:1 rax) ++
    movq !%rax (lab "pre_false") ++

    call_my_malloc 2 ++
    movb (imm 1) (ind rax) ++
    movb (imm 1) (ind ~ofs:1 rax) ++
    movq !%rax (lab "pre_true")

(* Fonctions d'affichage *)

let print_int_code =
    label "print_int" ++
    pushq !%rbp ++
    movq !%rsp !%rbp ++
    andq (imm (-16)) !%rsp ++
    movq !%rdi !%rsi ++
    leaq (lab ".Sprint_int") rdi ++
    call "printf" ++
    movq !%rbp !%rsp ++
    popq rbp ++
    ret

let print_bool_code =
    label "print_bool" ++
    pushq !%rbp ++
    movq !%rsp !%rbp ++
    andq (imm (-16)) !%rsp ++
    testb !%dil !%dil ++
    jne "1f" ++
    leaq (lab ".Sprint_false") rdi ++
    jmp "2f" ++
    label "1" ++
    leaq (lab ".Sprint_true") rdi ++
    label "2" ++
    call "printf" ++
    movq !%rbp !%rsp ++
    popq rbp ++
    ret

let print_str_code =
    label "print_str" ++
    pushq !%rbp ++
    movq !%rsp !%rbp ++
    andq (imm (-16)) !%rsp ++
    movq !%rdi !%rsi ++
    leaq (lab ".Sprint_str") rdi ++
    call "printf" ++
    movq !%rbp !%rsp ++
    popq rbp ++
    ret

let call_print = function
    | Tnoth -> nop
    | Tbool ->
        movb (ind ~ofs:1 rdi) !%dil ++
        call "print_bool"
    | Tint ->
        movq (ind ~ofs:1 rdi) !%rdi ++
        call "print_int"
    | Tstr ->
        incq !%rdi ++
        call "print_str"
    | _ -> failwith "A faire [call_print]"

(* Fonctions de manipulation de chaîne *)

let copy_string_code =
    (* Copier la chaîne dans rdi vers celle dans rsi *)
    label "copy_string" ++
    movb (ind rdi) !%r8b ++
    movb  !%r8b (ind rsi) ++
    testb !%r8b !%r8b ++
    je "1f" ++
    incq !%rdi ++
    incq !%rsi ++
    jmp "copy_string" ++
    label "1" ++
    ret

let len_string_code =
    (* Calcule la taille de rdi, dans rax *)
    label "len_string" ++
    movq (imm 0) !%rax ++
    label "1" ++
    movb (ind rdi) !%r8b ++
    testb !%r8b !%r8b ++
    je "2f" ++
    incq !%rax ++
    incq !%rdi ++
    jmp "1b" ++
    label "2" ++
    ret


let concat_string_code =
    (* Concatène la valeur rsi derrière la valeur rdi, résultat dans rax *)
    label "concat_string" ++
    pushq !%rsi ++
    pushq !%rdi ++

    incq !%rdi ++
    call "len_string" ++
    movq !%rax !%r8 ++

    leaq (ind ~ofs:1 rsi) rdi ++
    call "len_string" ++
    movq !%rax !%r9 ++

    movq !%r8 !%rdi ++
    addq !%r9 !%rdi ++
    addq (imm 2) !%rdi ++
    call "my_malloc" ++

    movb (imm 3) (ind rax) ++

    leaq (ind ~ofs:1 rax) rsi ++
    popq rdi ++
    incq !%rdi ++
    call "copy_string" ++

    popq rdi ++
    incq !% rdi ++
    call "copy_string" ++

    ret



(* Compilation ... *)

let rec compile_bexpr tbexpr = match tbexpr.bexpr with
    | texpr, [] -> compile_expr texpr
    | texpr1, (Add, texpr2) :: q ->
        if texpr1.t = Tstr then (
            compile_expr texpr1 ++
            pushq !%rax ++
            compile_bexpr ({bexpr = (texpr2, q); t=tbexpr.t}) ++
            movq !%rax !%rsi ++
            popq rdi ++
            call "concat_string"
        )
        else (
            failwith "A faire [compile_bexpr]"
        )
    | _ -> failwith "A faire [compile_bexpr]"

and compile_expr texpr = match texpr.expr with
    | TFalse -> movq (lab "pre_false") !%rax
    | TTrue -> movq (lab "pre_true") !%rax
    | TEint d ->
        call_my_malloc 9 ++
        movq (imm 2) (ind rax) ++
        movq (imm d) (ind ~ofs:1 rax)
    | TEstring s ->
        if not (Hashtbl.mem string_data_table s) then (
            Hashtbl.add string_data_table s !string_data_count;
            incr string_data_count
        );
        let n, len = Hashtbl.find string_data_table s, String.length s in
        call_my_malloc (1 + len + 1) ++
        movq (imm 3) (ind rax) ++
        movq (ilab (string_data_n n)) !%rdi ++
        movq !%rax !%rsi ++
        incq !%rsi ++
        call "copy_string"
    | TEcall({caller=TCident "print";t=_}, [tbexpr]) ->
        compile_bexpr tbexpr ++
        movq !%rax !%rdi ++
        call_print tbexpr.t
    | _ -> failwith "A faire [compile_expr]"

and compile_stmt (codefun, code) i t_stmt =
    let comment_line =
        if i = -1 then nop else 
        comment (Format.sprintf "global stmt number %d" i)
    in
    match t_stmt.stmt with
    | TSbexpr tbexpr ->
        let tbexpr_code = compile_bexpr tbexpr in
        (codefun, code ++ comment_line ++ tbexpr_code ++ newline)
    | _ -> failwith "A faire [compile_stmt]"


(* Compile le fichier f et enregistre le code dans le fichier ofile *)
let compile_file (f: t_file) ofile =
    let codefun, code = fst @@
        List.fold_left (fun (c, i) stmt -> compile_stmt c i stmt, i+1) 
            ((nop, nop), 0) f.file
    in
    let p =
        { text =
            globl "main" ++
            label "main" ++
            pushq !%rbp ++
            movq !%rsp !%rbp ++
            newline ++

            prealloc_init ++
            newline ++

            code ++

            popq rbp ++
            movq (imm 0) !%rax ++ (* exit *)
            ret ++

            newline ++
            newline ++

            my_malloc_code ++
            print_int_code ++
            print_bool_code ++
            print_str_code ++
            copy_string_code ++
            len_string_code ++
            concat_string_code ++
            codefun ++

            newline;

          data =
            label ".Sprint_false" ++ string "false" ++
            label ".Sprint_true" ++ string "true" ++
            label ".Sprint_int" ++ string "%d" ++
            label ".Sprint_str" ++ string "%s" ++
            prealloc_data ++
            (Hashtbl.fold
                (
                    fun s n text ->
                        text ++
                        label (string_data_n n) ++
                        string s
                )
                string_data_table nop
            )
        }
    in
    let f_out = open_out ofile in
    let fmt = formatter_of_out_channel f_out in
    X86_64.print_program fmt p;
    (* on "flush" le buffer afin de s'assurer que tout y a été écrit
       avant de le fermer *)
    fprintf fmt "@?";
    close_out f_out

