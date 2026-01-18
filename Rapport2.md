# Rapport Partie 2

Max Holemans - Projet de "Langages de programmation et compilation" 2025-2026

## Structure

Les fichiers sources de la première partie sont :
`lexer.mll`, `parser.mly`, `ast.ml`, `typer.ml`, `typed_ast.ml`,
`pretty_printer.ml`, `pretty_type_printer.ml`

Les fichiers sources de la deuxième partie sont :
- `closure_ast.ml`, `closure.ml` : Explicitation des fermetures et
allocation des variables locales, construction d'un nouvel AST à
partir de l'AST typé.
- `compile.ml`, `compile.mli` : Production de code à partir de l'AST produit
par `closure.ml`. Utilise le programme `x86_64.ml`.

Finalement `pyertc.ml` est le programme principal de pyretc.

## Explicitation des fermetures

J'ai essayé d'appliquer l'explicitation des fermetures proposée dans le cours
sur la compilation des langages fonctionnels, en adaptant quelques points
pour le langage Pyret. Par exemple, une construction de fermeture peut
correspondre à une fonction appelé avec plusieurs arguments.

Comme conseillé dans le sujet, toutes les fonctions passent par cette
explicitation, même les fonctions globales, et (dans la production de code)
les fonctions primaires du langage. Mis à part ces fonctions primaires et les
fonctions assembleur contenant les codes des fermetures, il n'y a en réalité
pas de valeurs globales.

L'explicitation des fermetures et l'allocation des variables se font de
manière conjointe. J'ai pris pour objectif de faire cette construction avec un
unique parcours linéaire de l'AST typé :
- les variables locales allouées descendent l'AST dans un environnement `env`.
- la taille du tableau d'activation est calculée à partir d'une entrée `fpcur`
et remontée jusqu'à la construction d'une fermeture ou la racine du fichier.
- les variables libres traversent l'AST dans un dictionnaire `fvars` qui leur
associe une position dans la fermeture en construction. La référence `clos`
est utilisée pour attribuer une position à une nouvelle variable libre
rencontrée.

J'ai eu du mal à décider comment implémenter ce parcours et quels éléments
propager dans la construction, avant d'arriver à la solution que j'ai
implémentée. Il m'a fallu du temps pour bien comprendre comment introduire les
fermetures.

Quelques éléments présents dans l'AST typé, non nécessaires pour la production
de code, sont retirés pour simplifier la construction; les types sont
conservés.

## Production de code

J'ai suivi le schéma de compilation proposé dans le sujet, à partir de l'AST
des fermetures.

Concernant les conventions x86-64:
- l'alignment de la pile est réservée pour les appels de fonction extérieures,
encapsulées dans de nouvelles fonctions (`my_malloc`, `print_int`, ...)
- les conventions d'appels sont respectées (j'utilise r8/r9 comme registres
temporaires, et r12/r13/r14 comme registres à plus longues portée; r15 est
utilisée pour sauvegarder l'état de le pile pour échouer le programme).

J'ai codé les parties de code assembleur qui ne viennent pas de l'AST à la main
pour garder un code final plus lisible.

Les types sont utilisés pour distinguer l'addition d'entiers de la
concaténation de chaînes de caractères, et pour facilité la comparaison
structurelle.

Cette comparaison structurelle est introduite dans la fonction
`structural_cmp`, mais n'est pas correcte : si les types fournis ne sont pas
assez précis, une comparaison physique est effectuée. Ceci suffit pour passer
le test `equal.arr` (parce que le cas simple `empty` est correct ici), mais
cela pose problème lorsqu'on introduit nos propres types.

J'ai rencontré le même problème pour la fonction polymorphe `print`, rélgé en
utilisant le type inscrit en mémoire au lieu du type donné par le typeur.
La comparaison structurelle peut être réécrite de la même façon, mais ce serait
une fonction assembleur encore plus longue.


Tous les tests fournis passent : les tests de la partie précédente, la
compilation, le code produit, et le comportement du code.

