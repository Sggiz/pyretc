
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
        Format.sprintf ".%s_%d" s n
    with Not_found ->
        Hashtbl.add label_table s 1;
        Format.sprintf ".%s_%d" s 0

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
    label "nothing" ++ dquad [0] ++
    label ".pre_false" ++ dquad [0] ++
    label ".pre_true" ++ dquad [0] ++
    label "empty" ++ dquad [0] ++

    label "link" ++ dquad [0] ++
    label "each" ++ dquad [0] ++
    label "fold" ++ dquad [0] ++
    label "raise" ++ dquad [0]

let prealloc_init =
    comment "Preallocations" ++

    call_my_malloc 1 ++
    movb (imm 0) (ind rax) ++
    movq !%rax (lab "nothing") ++

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
    movq !%rax (lab "empty") ++

    call_my_malloc 9 ++
    movb (imm 6) (ind rax) ++
    movq (ilab "link_code") (ind ~ofs:1 rax) ++
    movq !%rax (lab "link")

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

(* Fonctions primaires *)

let link_code =
    label "link_code" ++ pushq !%rbp ++ movq !%rsp !%rbp ++
    call_my_malloc 17 ++
    movb (imm 5) (ind rax) ++
    movq (ind ~ofs:24 rbp) !%r8 ++ movq !%r8 (ind ~ofs:1 rax) ++
    movq (ind ~ofs:32 rbp) !%r8 ++ movq !%r8 (ind ~ofs:9 rax) ++
    popq rbp ++ ret


(* Fonction d'aide *)

let rec structural_cmp eq neq t1 t2 =
    (* valeurs à comparer dans r12 et r13 *)
    match Typer.head t1, Typer.head t2 with
    | Typed_ast.(Tnoth, Tnoth) -> jmp eq
    | Typed_ast.(Tint, Tint) ->
        movq (ind ~ofs:1 r12) !%r12 ++ movq (ind ~ofs:1 r13) !%r13 ++
        cmpq !%r12 !%r13 ++ je eq ++ jmp neq
    | Typed_ast.(Tbool, Tbool) ->
        cmpq !%r12 !%r13 ++ je eq ++ jmp neq
    | Typed_ast.(Tstr, Tstr) ->
        label "1" ++
        incq !%r12 ++ incq !%r13 ++
        movb (ind r12) !%r8b ++
        movb (ind r13) !%r9b ++
        cmpb !%r8b !%r9b ++ jne neq ++
        testb !%r8b !%r8b ++ jne "1b" ++ jmp eq
    | Typed_ast.(Tlist t1, Tlist t2) ->
        let list_entry = get_new_label "list_entry" in
        let list1_notempty = get_new_label "list1_notempty" in
        let lists = get_new_label "lists" in
        let inter_eq = get_new_label "inter_eq" in
        let inter_neq = get_new_label "inter_neq" in
        label list_entry ++
        cmpq !%r12 (lab "empty") ++ jne list1_notempty ++
        cmpq !%r13 (lab "empty") ++ jne neq ++ jmp eq ++
        label list1_notempty ++
        cmpq !%r13 (lab "empty") ++ jne lists ++ jmp neq ++
        label lists ++
        pushq !%r12 ++ pushq !%r13 ++
        movq (ind ~ofs:1 r12) !%r12 ++ movq (ind ~ofs:1 r13) !%r13 ++
        structural_cmp inter_eq inter_neq t1 t2 ++
        label inter_eq ++
        popq r13 ++ movq (ind ~ofs:9 r13) !%r13 ++
        popq r12 ++ movq (ind ~ofs:9 r12) !%r12 ++
        jmp list_entry ++
        label inter_neq ++
        popq r13 ++ popq r12 ++ jmp neq

(*     | Typed_ast.(Tfun _, Tfun _) -> failwith "Valeurs non comparables" *)

    | _ -> (* comparaison physique *)
        cmpq !%r12 !%r13 ++ je eq ++ jmp neq



(* Compilation ... *)

let rec compile_block b =
    List.fold_left (++) nop @@ List.map (compile_stmt (-1)) b.desc

and compile_var = function
    | Vglobal x ->
        movq (lab x) !%rax
    | Vlocal pos ->
        movq (ind ~ofs:pos rbp) !%rax
    | Vclos pos ->
        movq (ind ~ofs:16 rbp) !%rax ++
        movq (ind ~ofs:(9+8*pos) rax) !%rax

and compile_bexpr bexpr = match bexpr.desc with
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
        | Ast.Neq ->movq (lab ".pre_false") !%rax, movq (lab ".pre_true") !%rax
        | _ -> failwith "A faire [compile_bexpr_poly_cmp]"
    in
    let res_eq_label = get_new_label "res_eq" in
    let res_neq_label = get_new_label "res_neq" in
    pushq !%r12 ++ pushq !%r13 ++
    compile_expr e1 ++ movq !%rax !%r12 ++
    compile_expr e2 ++ movq !%rax !%r13 ++
    structural_cmp res_eq_label res_neq_label e1.t e2.t ++
    label res_eq_label ++ res_eq ++ jmp "1f"++
    label res_neq_label ++ res_neq ++ label "1" ++
    popq r13 ++ popq r12

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
        movb (imm 2) (ind rax) ++
        movq (imm d) (ind ~ofs:1 rax)
    | CEstring s ->
        if not (Hashtbl.mem string_data_table s) then (
            Hashtbl.add string_data_table s !string_data_count;
            incr string_data_count
        );
        let n, len = Hashtbl.find string_data_table s, String.length s in
        call_my_malloc (1 + len + 1) ++
        movb (imm 3) (ind rax) ++
        movq (ilab (string_data_n n)) !%rdi ++
        movq !%rax !%rsi ++
        incq !%rsi ++
        call "copy_string"
    | CEvar v -> compile_var v
    | CEbexpr bexpr -> compile_bexpr bexpr
    | CEblock b ->
        compile_block b
    | CEcond(if_bexpr, if_block, elif_list, else_block_option) ->
        let lout = get_new_label "out" in
        let cond_branch_code (bexpr, block) =
            let next_label = get_new_label "else" in
            compile_bexpr bexpr ++
            movb (ind ~ofs:1 rax) !%al ++
            testb !%al !%al ++
            je next_label ++
            compile_block block ++
            jmp lout ++
            label next_label
        in
        (List.fold_left (++) nop @@ List.map cond_branch_code
            ((if_bexpr, if_block) :: elif_list)) ++
        (match else_block_option with
            | None -> nop
            | Some b -> compile_block b
        ) ++
        label lout

(*     | CEcall({desc=CCvar (Vglobal "print");t=_}, [bexpr]) *)
    | CEprint bexpr ->
        compile_bexpr bexpr ++
        pushq !%rax ++
        movq !%rax !%rdi ++
        call_print bexpr.t ++
        popq rax
    | CEcall(caller, bexpr_list) ->
        (List.fold_left (++) nop @@ List.rev_map
            (fun be -> compile_bexpr be ++ pushq !%rax) bexpr_list) ++
        compile_caller caller ++
        pushq !%rax ++
        call_star (ind ~ofs:1 rax) ++
        addq (imm (8*(1 + List.length bexpr_list))) !%rsp
    | _ -> failwith "A faire [compile_expr]"

and compile_caller c = match c.desc with
    | CCvar v -> compile_var v
    | CCcall(caller, bexpr_list) ->
        (List.fold_left (++) nop @@ List.rev_map
            (fun be -> compile_bexpr be ++ pushq !%rax) bexpr_list) ++
        compile_caller caller ++
        pushq !%rax ++
        call_star (ind ~ofs:1 rax) ++
        addq (imm (8*(1 + List.length bexpr_list))) !%rsp

and compile_stmt i stmt =
    let comment_line =
        if i = -1 then nop else
        comment (Format.sprintf "global stmt number %d" i)
    in
    match stmt.desc with
    | CSbexpr bexpr ->
        comment_line ++
        compile_bexpr bexpr ++
        newline
    | CSdef(pos, bexpr) ->
        comment_line ++
        compile_bexpr bexpr ++
        movq !%rax (ind ~ofs:pos rbp) ++
        newline
    | CSfun(pos, gfun_name, fvars) ->
        let nb_fvars = Array.length fvars in
        comment_line ++
        call_my_malloc (9 + 8*nb_fvars) ++
        movq (imm 6) (ind rax) ++
        movq (ilab gfun_name) (ind ~ofs:1 rax) ++
        (Array.fold_left (++) nop @@ Array.mapi
            (fun k v -> match v with
            | Vglobal x -> nop (* normalement inatteignable *)
            | Vlocal p ->
                if p = 0 then
                    movq !%rax (ind ~ofs:(9 + 8*k) rax)
                else
                    movq (ind ~ofs:p rbp) !%r8 ++
                    movq !%r8 (ind ~ofs:(9 + 8*k) rax)
            | Vclos j ->
                movq (ind ~ofs:16 rbp) !%r8 ++
                movq (ind ~ofs:(9 + 8*j) r8) !%r8 ++
                movq !%r8 (ind ~ofs:(9 + 8*k) rax)
            ) fvars) ++
        movq !%rax (ind ~ofs:pos rbp)


(* Compile le fichier f et enregistre le code dans le fichier ofile *)
let compile_file (f: Typed_ast.t_file) ofile =
    let cf, fp, gfun_list = closure_file f in
    let code = List.fold_left (++) nop @@ List.mapi compile_stmt cf.desc in
    let codefun = List.fold_left (++) nop @@ List.rev_map (
        fun (f, fp, b) ->
            label f ++
            pushq !%rbp ++ movq !%rsp !%rbp ++ addq (imm fp) !%rsp ++ newline++
            compile_block b ++
            subq (imm fp) !%rsp ++ popq rbp ++ ret ++ newline
        ) gfun_list
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

            newline ++

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
            link_code ++
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

