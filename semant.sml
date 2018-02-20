signature SEMANT =
sig
    type venv
    type tenv
    type expty

    val transProg : Absyn.exp -> unit
    val transVar: venv * tenv * Absyn.var -> expty
    val transExp: venv * tenv * Absyn.exp -> expty
    val transDec: venv * tenv * Absyn.dec -> {venv: venv, tenv: tenv}
    val transTy:         tenv * Absyn.ty  -> Types.ty
end

structure Semant : SEMANT =
struct

  type venv = Env.enventry Symbol.table
  type tenv = Types.ty Symbol.table
  type expty = {exp: Translate.exp, ty: Types.ty}

  structure S = Symbol
  structure A = Absyn
  structure E = Env
  structure T = Types

  fun transProg(exp : A.exp) = ()

  fun transVar(venv : venv, tenv : tenv, var : A.var) = {exp= (), ty= T.UNIT}

  fun checkInt({exp : A.exp, ty : T.ty}, pos : int) =
      case ty of T.INT => ()
              |  _ => ErrorMsg.error pos "integer required"

  fun actual_ty(ty : T.ty, pos : int) =
      case ty
       of T.NAME(sym, tyref) => (* reference to an optional type *)
          (case (!tyref)
            of SOME(ty) => actual_ty(ty, pos)
             | NONE => (ErrorMsg.error pos ("undefined type " ^ S.name sym);
                        T.NIL))
        | T.ARRAY(ty, uniq) => T.ARRAY(actual_ty(ty, pos), uniq)
        | _ => ty

  fun transExp(venv : venv, tenv : tenv, exp : A.exp) =
      let fun trexp (A.OpExp{left, oper= A.PlusOp, right, pos}) =
              (checkInt(trexp left, pos);
               checkInt(trexp right, pos);
               {exp= (), ty= T.INT})
            | trexp(_) = {exp= (), ty= T.UNIT}
          and trvar (A.SimpleVar(id, pos)) =
              (case S.look(venv, id)
                of SOME(E.VarEntry{ty}) => {exp= (), ty= actual_ty(ty, pos)}
                 | NONE => (ErrorMsg.error pos ("undefined variable " ^ S.name id);
                            {exp= (), ty=T.INT}))
            | trvar (_) = {exp= (), ty=T.UNIT}
      in trexp(exp)
      end

  fun transDec(venv : venv, tenv : tenv, dec : A.dec) = {venv= venv, tenv= tenv}

  fun transTy(tenv : tenv, ty : A.ty) = T.UNIT

end (* structure Semant *)
