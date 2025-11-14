
exception VarUndef of string
    (** exception levée pour signaler une variable non déclarée *)

val compile_file : Ast.file -> string -> unit
    (** [compile_program p f] compile le programme [p] et écrit le code x86_64
        correxpondant dans le fichier [f] *)
