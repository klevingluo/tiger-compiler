signature SEMANT =
sig
    type venv
    type tenv
    type expty

    val transProg : Absyn.exp -> unit
    val transVar: venv * tenv * Absyn.var -> expty
    val transExp: venv * tenv * Absyn.exp -> expty
    val transDec:        tenv * Absyn.dec -> {venv: venv, tenv: tenv}
    val transTy:         tenv * Absyn.ty  -> Types.ty
end

structure Semant : SEMANT =
struct

  type venv = Env.enventry IntMapTable.table
  type tenv = Types.ty IntMapTable
  type expty = {exp: Translate.exp, ty: Types.ty}

  fun transProg(exp : Absyn.exp) = ()

end (* structure Semant *)
