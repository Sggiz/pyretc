
/* Analyseur syntaxique pour Pyret */

%{
    open Ast

    exception Message_perr of string

    let rec is_unique_binop = function
        | (b1,_)::((b2,_)::_ as q) -> b1 = b2 && is_unique_binop q
        | _ -> true
%}

/* Définition des tokens */

%token <int> INTEGER
%token <string> STRING
%token <string> IDENT
%token <string> CALL

%token NL EOF
%token DP LP RP COMMA DEF REDEF DCOL LARR LANG RANG

%token EQ NEQ LNEQ LEQ GNEQ GEQ PLUS MINUS TIMES DIV AND OR

%token BLOCK CASES ELSE END FALSE FOR FROM FUN IF LAM TRUE VAR


/* Définition des priorités et associativités des tokens */

/* Point d'entrée de la grammaire */
%start file

/* Type des valeurs retournées par l'analyseur syntaxique */
%type <Ast.file> file


%%

file:
| NL* sl = stmt* EOF   { sl }
;

stmt: (* incomplet *)
| bvar = boption(VAR) id = IDENT tyo = preceded(DCOL, typerule)?
DEF b = bexpr NL+
    { Sdef(bvar, id, tyo, b) }
| bvar = boption(VAR) id = IDENT REDEF b = bexpr NL+
    { if not bvar then Sredef(id, b)
    else raise (Message_perr
    "Le mot-clé 'var' ne convient pas à une redéfinition de variable.") }
| b = bexpr NL+
    { Sbexpr b }
;

rtype:
| LARR ty = typerule
    { Rtype ty }
;

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

| c = caller bel = separated_list(COMMA, bexpr) RP
    { Ecall(c, bel) }
;

caller:
|c = caller bel = separated_list(COMMA, bexpr) DP
    { Ccall(c, bel) }
|id = CALL
    { Cident id }
;

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

