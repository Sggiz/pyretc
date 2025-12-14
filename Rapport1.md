# Rapport Partie 1

Max Holemans - Projet de "Langages de programmation et compilation" 2025-2026

## Structure

Les fichiers sources sont:
- `lexer.mll`, `parser.mly` : Lexeur et parseur de pyretc
- `ast.ml` : Définit l'AST construit par le parseur, et introduit quelques
exceptions levées pas le parseur.
- `typer.ml` : Typeur de pyretc qui applique l'algorithme W (typage statique)
à l'AST produit par le parseur.
- `typed_ast.ml` : Définit l'AST augmenté construit par le typeur.
- `pretty_printer.ml`, `pretty_type_printer.ml` : Deux "pretty printer" pour
l'AST et l'AST augmenté respectivement.
- `pyretc.ml` : Programme principal de pyretc.


## Analyse syntaxique

Comme conseillé, j'ai fait le choix de garder un parseur plutôt simple et de
détecter les cas pathologiques avec le lexeur. Par exemple, dans mon
implémentation du compilateur de Mini Pyret différents `stmt` peuvent se
trouver sur la même ligne; mais les lectures ambigües comme `40 +2` sont
rejetées comme des erreurs par le lexeur.
Pour éviter de coder un buffer pour le lexeur, j'ai ajouté quelques lexèmes
qui regroupent plusieurs éléments en un, comme le léxème `CALL` qui représent
un `IDENT` suivi par une paranthèse ouvrante vérifiant les propriétés
d'espacement de Mini Pyret.

Le parseur suit simplement la grammaire donnée. J'ai rencontré assez peu de
conflits; par exemple lors de la définition d'une variable (règle `a_stmt`),
la présence du mot-clé `var` est posé "inline" par la fonction `ioption` de
menhir, pour éviter le conflit généré et éviter le dédoublement de code.
Deux propriétés supplémentaires sont vérifiées par le parseur : l'unicité de
l'opérateur binaure dans une `bexpr`, et les opérations autorisées dans un
`bloc`. Si ces propriétés ne sont pas vérifiées, le parseur lève une
exception (définie dans `ast.ml` car `parser.mli` produit par menhir ne
transporte pas les exceptions définies en entête). Les règles du parseur sont
dédoublées pour transporter les positions des expressions, sans surcharger le
reste du code.


- `ocamllex lexer.mll` : 76 states, 1767 transitions
- `parser.automaton` : 178 états


## Typage statique

Pour le typage, j'ai adapté l'algoritme W codé en TD, et en plus de faire
l'analyse de l'AST, il le reconstruit en le décorant avec des types.
Ce qui était le plus, c'est comprendre la distinction entre les variables
de type introduits par l'algorithme W et les types introduits lors de
l'introduction d'une foncte; puis adapter les fonctions d'unification et de
sous-typage associés.

Pour distinguer ces différentes natures de variables de type, j'associe un
booléen `is_sefldef` à la création d'une variable. Il est faux pour une
variable classique de l'algorithme W; et vraie pour une variable introduite,
qui ne sera pas résolue par unification, mais qui deviendra une variable
calssique lorsqu'on récupère le type de la fonction définie, plus loin dans
le code (avec `find`).


Pour typer une addition, `w_bexpr` recherche d'abord un indice de type
(une expression de type atomique `Tint` ou `Tstr`) et sous-type en conséquence;
et s'il n'y a pas de tel indice, on effectue le sous-typage par `Tstr` puis par
`Tint` s'il échoue. Pour que cela reste correct, j'ai codé des fonctions de
sous-typage délicates, qui ne définissent les variables traitées qu'à la fin
d'un sous-typage réussi.

Le reste du typage est plutôt mécanique, en suivant la structure de l'AST.
Les localisations sont utilisées pour lever les erreurs de typage, mis en forme
dans `pyretc.ml`, même si dans quelques cas la localisation est correcte mais
peu précise : c'est parfois l'expression entière qui est soulignée, même si ce
n'est qu'un élément qui cause l'erreur. La nature du message d'erreur est assez
précise pour identifier les problèmes de type malgré cela.
Les localisations ne sont pas gardées dans l'AST augmenté, mais il y reste tout
de même quelques éléments probablement superflus (comme la nature
d'introduction de bloc, ou la répétition du `binop` dans les `bexpr`).
Les annotations de type sont également retirées dans l'AST augmenté.


Le compilateur passe tous les tests de syntaxe et de typage.

