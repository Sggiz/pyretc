
/* Analyseur syntaxique pour Pyret */

%{
    open Ast
%}

/* Définition des tokens */

%token <int> INTEGER
%token <string> STRING
%token <string> IDENT
%token EOF

%token TRUE FALSE EQ
%token LP RP

/* Définition des priorités et associativités des tokens */

/* Point d'entrée de la grammaire */
%start file

/* Type des valeurs retournées par l'analyseur syntaxique */
%type <Ast.file> file


%%

file:
| sl = stmt* EOF   { List.rev sl }
;

stmt:
| b = bexpr
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
;

binop:
| EQ    { Eq }

