
(* Production de code pour le langage Pyret *)

open Format
open X86_64
open Closure_ast
open Closure

(* Table d'association pour les string de l'utilisateur *)
let string_data_count = ref 0
let string_data_table = Hashtbl.create 5
let string_data_n = Format.sprintf ".string_data_%d"

(* Table pour la distinction des étiquettes *)
let label_table = Hashtbl.create 5
let get_new_label s =
    try
        let n = Hashtbl.find label_table s in
        Hashtbl.replace label_table s (n+1);
        Format.sprintf "%s_%d" s n
    with Not_found ->
        Hashtbl.add label_table s 1;
        Format.sprintf "%s_%d" s 0

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
    label ".pre_nothing" ++
    dquad [0] ++
    label ".pre_false" ++
    dquad [0] ++
    label ".pre_true" ++
    dquad [0] ++
    label ".pre_empty" ++
    dquad [0]

let prealloc_init =
    comment "Preallocations" ++

    call_my_malloc 1 ++
    movb (imm 0) (ind rax) ++
    movq !%rax (lab ".pre_nothing") ++

    call_my_malloc 2 ++
    movb (imm 1) (ind rax) ++
    movb (imm 0) (ind ~ofs:1 rax) ++
    movq !%rax (lab ".pre_false") ++

    call_my_malloc 2 ++
    movb (imm 1) (ind rax) ++
    movb (imm 1) (ind ~ofs:1 rax) ++
    movq !%rax (lab ".pre_true") ++

    call_my_malloc 1 ++
    movb (imm 4) (ind rax) ++
    movq !%rax (lab ".pre_empty")

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
    | Typed_ast.Tnoth -> nop
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

let rec compile_bexpr bexpr = match bexpr.desc with
    | expr, [] -> compile_expr expr
    | expr, op_list ->
    begin let op = fst @@ List.hd op_list in match bexpr.t, op with
    | Tint, _ -> (* opération arithmétique *)
        pushq !%r12 ++
        compile_expr expr ++
        movq (ind ~ofs:1 rax) !%r12 ++
        compile_bexpr_int_arith op_list ++
        call_my_malloc 9 ++
        movq (imm 2) (ind rax) ++
        movq !%r12 (ind ~ofs:1 rax) ++
        popq r12
    | Tstr, Ast.Add -> compile_bexpr_str bexpr
    | _ (* Tbool *), Lneq | _, Leq | _, Gneq | _, Geq ->
        compile_bexpr_int_cmp expr op (snd (List.hd op_list))
    | _, Eq | _, Neq ->
        compile_bexpr_poly_cmp expr op (snd (List.hd op_list))
    | _, And | _, Or ->
        let t, nt = (
            if op = And then ".pre_false", ".pre_true"
            else ".pre_true", ".pre_false"
        ) in
        let l = get_new_label "bool_op_term" in
        compile_bexpr_bool  l t nt (expr :: (List.map snd op_list))
    | _ -> failwith "A faire [compile_bexpr]" end

and compile_bexpr_bool l t nt = function
    | [] -> nop
    | [e] ->
        compile_expr e ++
        label l
    | hd :: tl ->
        compile_expr hd ++
        cmpq !%rax (lab t) ++
        je l ++
        compile_bexpr_bool l t nt tl

and compile_bexpr_int_arith = function
    (* agit sur la valeur dans r12 *)
    | [] -> nop
    | (Ast.Div, expr) :: q ->
        compile_expr expr ++
        movq (ind ~ofs:1 rax) !%r8 ++
        movq !%r12 !%rax ++ cqto ++
        idivq !%r8 ++
        movq !%rax !%r12 ++
        compile_bexpr_int_arith q
    | (op , expr) :: q ->
        compile_expr expr ++
        movq (ind ~ofs:1 rax) !%r8 ++
        (match op with
            | Add -> addq
            | Sub -> subq
            | Mul -> imulq
            | _ -> failwith "A faire [compile_bexpr_int]"
        ) !%r8 !%r12 ++
        compile_bexpr_int_arith q

and compile_bexpr_int_cmp e1 op e2 =
    compile_expr e1 ++
    pushq (ind ~ofs:1 rax) ++
    compile_expr e2 ++
    movq (ind ~ofs:1 rax) !%r9 ++
    popq r8 ++
    subq !%r9 !%r8 ++
    (match op with
        | Ast.Lneq -> jl
        | Leq -> jle
        | Gneq -> jg
        | Geq -> jge
        | _ -> failwith "A faire [compile_bexpr_int]"
    ) "1f" ++
    movq (lab ".pre_false") !%rax ++
    jmp "2f" ++
    label "1" ++
    movq (lab ".pre_true") !%rax ++
    label "2"

and compile_bexpr_poly_cmp (e1 : c_expr) op (e2 : c_expr) =
    let res_eq, res_neq = match op with
        | Ast.Eq -> movq (lab ".pre_true") !%rax, movq (lab ".pre_false") !%rax
        | Ast.Neq -> movq (lab ".pre_false") !%rax, movq (lab ".pre_true") !%rax
        | _ -> failwith "A faire [compile_bexpr_poly_cmp]"
    in
    if e1.t <> e2.t then
        res_neq
    else match e1.t with
    | Tint ->
        compile_expr e1 ++
        pushq (ind ~ofs:1 rax) ++
        compile_expr e2 ++
        movq (ind ~ofs:1 rax) !%r8 ++
        popq r9 ++
        cmpq !%r8 !%r9 ++
        je "1f" ++ res_neq ++ jmp "2f" ++ label "1" ++ res_eq ++ label "2"
    | Tbool ->
        compile_expr e1 ++
        pushq !%rax ++
        compile_expr e2 ++
        popq r8 ++
        cmpq !%rax !%r8 ++
        je "1f" ++ res_neq ++ jmp "2f" ++ label "1" ++ res_eq ++ label "2"
    | Tstr ->
        pushq !%r12 ++ pushq !%r13 ++
        compile_expr e1 ++
        movq !%rax !%r12 ++
        compile_expr e2 ++
        movq !%rax !%r13 ++
        label "1" ++
        incq !%r12 ++ incq !%r13 ++
        movb (ind r12) !%r8b ++
        movb (ind r13) !%r9b ++
        cmpb !%r8b !%r9b ++
        jne "2f" ++
        testb !%r8b !%r8b ++
        jne "1b" ++
        res_eq ++
        jmp "3f" ++
        label "2" ++
        res_neq ++
        label "3" ++
        popq r13 ++ popq r12

    | _ -> failwith "A faire [compile_bexpr_poly_cmp]"

and compile_bexpr_str bexpr = match bexpr.desc with
    | texpr, [] -> compile_expr texpr
    | texpr1, (Ast.Add, texpr2) :: q ->
        compile_expr texpr1 ++
        pushq !%rax ++
        compile_bexpr ({desc = (texpr2, q); t=bexpr.t}) ++
        movq !%rax !%rsi ++
        popq rdi ++
        call "concat_string"
    | _ -> failwith "A faire [compile_bexpr_str]"

and compile_expr expr = match expr.desc with
    | CFalse -> movq (lab ".pre_false") !%rax
    | CTrue -> movq (lab ".pre_true") !%rax
    | CEint d ->
        call_my_malloc 9 ++
        movq (imm 2) (ind rax) ++
        movq (imm d) (ind ~ofs:1 rax)
    | CEstring s ->
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
    | CEvar(Vglobal x) ->
        movq (lab x) !%rax
    | CEvar(Vlocal pos) ->
        movq (ind ~ofs:pos rbp) !%rax
    | CEvar(Vclos pos) ->
        movq (ind ~ofs:16 rbp) !%rax ++
        movq (ind ~ofs:pos rax) !%rax
    | CEbexpr bexpr -> compile_bexpr bexpr
(*     | CEcall({desc=CCvar (Vglobal "print");t=_}, [bexpr]) *)
    | CEprint bexpr ->
        compile_bexpr bexpr ++
        pushq !%rax ++
        movq !%rax !%rdi ++
        call_print bexpr.t ++
        popq rax
    | _ -> failwith "A faire [compile_expr]"

and compile_stmt (codefun, code) i stmt =
    let comment_line =
        if i = -1 then nop else 
        comment (Format.sprintf "global stmt number %d" i)
    in
    match stmt.desc with
    | CSbexpr bexpr ->
        let bexpr_code = compile_bexpr bexpr in
        (codefun, code ++ comment_line ++ bexpr_code ++ newline)
    | CSdef(pos, bexpr) ->
        let bexpr_code = compile_bexpr bexpr in
        (codefun,
            code ++ comment_line ++ bexpr_code ++
            movq !%rax (ind ~ofs:pos rbp)
        )
    | _ -> failwith "A faire [compile_stmt]"


(* Compile le fichier f et enregistre le code dans le fichier ofile *)
let compile_file (f: Typed_ast.t_file) ofile =
    let cf, fp = closure_file f in
    let codefun, code = fst @@
        List.fold_left (fun (c, i) stmt -> compile_stmt c i stmt, i+1) 
            ((nop, nop), 0) cf.desc
    in
    let p =
        { text =
            globl "main" ++
            label "main" ++
            pushq !%rbp ++
            movq !%rsp !%rbp ++
            addq (imm fp) !%rsp ++

            newline ++

            prealloc_init ++
            newline ++

            code ++

            subq (imm fp) !%rsp ++
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

