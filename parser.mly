
/* Analyseur syntaxique pour Pyret */

%{
    open Ast
%}

/* Définition des tokens */

%token <int> INTEGER
%token <string> STRING
%token <string> IDENT
%token NL EOF

%token AND BLOCK CASES ELSE END FALSE FOR FROM FUN IF LAM OR TRUE VAR

%token <string> CALL

%token EQ
%token DP LP RP COMMA


/* Définition des priorités et associativités des tokens */

/* Point d'entrée de la grammaire */
%start file

/* Type des valeurs retournées par l'analyseur syntaxique */
%type <Ast.file> file


%%

file:
| NL* sl = stmt* EOF   { sl }
;

stmt:
| b = bexpr NL+
    { Sbexpr b }
;

bexpr:
| e = expr list(b = binop e0 = expr { (b,e0) })
    { ((e, []): bexpr) }
;

expr: (* incomplet *)
| TRUE  { True }
| FALSE { False }
| n = INTEGER
    { Eint n }
| s = STRING
    { Estring s }
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

