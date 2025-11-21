
/* Analyseur syntaxique pour Pyret */

%{
    open Ast

    exception Block_perr
    exception Message_perr of string

    let rec is_unique_binop = function
        | (b1,_)::((b2,_)::_ as q) -> b1 = b2 && is_unique_binop q
        | _ -> true

    let rec is_valid_block ub = function
        | [Sbexpr _] | [Sredef(_, _)] -> true
        | [] | [_] -> false
        | (Sbexpr _)::q | (Sredef(_, _))::q ->
            begin match ub with
            | Colon -> false
            | BlockColon -> is_valid_block ub q
            end
        | _::q -> is_valid_block ub q

    let valid_blocks ub = List.for_all (is_valid_block ub)

%}

/* Définition des tokens */

%token <int> INTEGER
%token <string> STRING
%token <string> IDENT
%token <string> CALL

%token EOF
%token DP LP RP COMMA DEF REDEF DCOL COL LARR LANG RANG BAR CARR RANGLP

%token EQ NEQ LNEQ LEQ GNEQ GEQ PLUS MINUS TIMES DIV AND OR

%token BLOCK CASES ELSE ELSEC END FALSE FOR FROM FUN IF LAM TRUE VAR


/* Définition des priorités et associativités des tokens */

/* Point d'entrée de la grammaire */
%start file

/* Type des valeurs retournées par l'analyseur syntaxique */
%type <Ast.file> file


%%

file:
| sl = stmt* EOF   { sl }
;

block:
| sl = stmt*
    { (sl : block) }

stmt:
| FUN id = CALL fb = funbody
    { Sfun(id, [], fb) }
| FUN id = IDENT lang idl = separated_nonempty_list(COMMA, i = IDENT { i })
RANGLP fb = funbody
    { Sfun(id, idl, fb) }
| bvar = ioption(VAR) id = IDENT tyo = preceded(DCOL, typerule)?
DEF b = bexpr
    { Sdef( (match bvar with None -> false | Some _ -> true) , id, tyo, b) }
| id = IDENT REDEF b = bexpr
    { Sredef(id, b) }
| b = bexpr
    { Sbexpr b }
;

funbody:
| pl = separated_list(COMMA, param) RP rt = rtype ub = ublock b = block END
    { if not @@ is_valid_block ub b then raise Block_perr
    else ((pl, rt, ub, b): funbody) }
;

param:
| id = IDENT DCOL t = typerule
    { ((id, t): param) }
;

rtype:
| LARR ty = typerule
    { Rtype ty }
;

ublock:
| COL   { Colon }
| BLOCK { BlockColon }

typerule:
| id = IDENT
tlo = delimited(lang,
    separated_nonempty_list(COMMA, typerule), 
    rang)?
    { Tannot(id, tlo) }
| LP tl = separated_list(COMMA, typerule) rt = rtype RP
    { Tfun(tl, rt) }
;

%inline lang: LNEQ {} | LANG {};
%inline rang: GNEQ {} | RANG {};

bexpr:
| e = expr bel = list(b = binop e0 = expr { (b,e0) })
    { if is_unique_binop bel then ((e, bel): bexpr)
    else raise (Message_perr
    "Enchaînement ambigu des opérateurs, veuillez utiliser des paranthèses.") }
;

expr: (* incomplet *)
| TRUE  { True }
| FALSE { False }
| n = INTEGER
    { Eint n }
| s = STRING
    { Estring s }
| id = IDENT
    { Eident id }
| LP b = bexpr RP
    { Ebexpr b }

| BLOCK b = block END
    { if not @@ is_valid_block BlockColon b then raise Block_perr
    else Eblock b }

| IF bex = bexpr ub = ublock b = block
elif = list(ELSE IF be = bexpr COL belif = block { (be, belif) })
elo = option(ELSEC belo = block { belo })
END
    { if elo = None && elif = [] then raise (Message_perr
        "Une expression conditionnelle nécessite un branche else ou else if.")

    else
    let bloc_list = match elo with
        | None -> b :: List.map snd elif
        | Some bel -> b :: bel :: List.map snd elif
    in
    if not @@valid_blocks ub bloc_list then raise Block_perr

    else Econd(bex, ub, b, elif, elo) }

| c = caller bel = separated_list(COMMA, bexpr) RP
    { Ecall(c, bel) }

| LAM fb = funbody
    { Elam fb }

| CASES t = typerule RP be = bexpr ub = ublock bl = branch* END
    { Ecases(t, be, ub, bl) }
;

caller:
|c = caller bel = separated_list(COMMA, bexpr) DP
    { Ccall(c, bel) }
|id = CALL
    { Cident id }
;

branch:
| BAR id = IDENT carr b = block
    { ((id, None, b): branch) }
| BAR id = CALL idl = separated_list(COMMA, p=IDENT{p}) RP carr b = block
    { ((id, Some(idl), b): branch) }
;

carr: CARR | GEQ {};

binop:
| EQ    { Eq }
| NEQ   { Neq }
| LNEQ  { Lneq }
| LEQ   { Leq }
| GNEQ  { Gneq }
| GEQ   { Geq }
| PLUS  { Add }
| MINUS { Sub }
| TIMES { Mul }
| DIV   { Div }
| AND   { And }
| OR    { Or }

