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

  fun checkInt({exp : Translate.exp, ty : T.ty}, pos : int) =
      case ty of T.INT => ()
              |  _ => ErrorMsg.error pos "integer required"

  fun checkArgs(param::params : T.ty list, arg::args : T.ty list, pos : int) =
      if param == arg
      then checkArgs(params, args)
      else ErrorMsg.error pos "type mismatch"
    | checkArgs([], arg::args, pos) = ErrorMsg.error pos "too many arguments"
    | checkArgs(param::params, [], pos) = ErrorMsg.error pos "not enough arguments"
    | checkArgs([], [], pos) = ()

  fun checkFields(param::params : (Symbol.symbol * T.ty) list,
                  arg::args : (Symbol.symbol * T.ty * int) list) =
      let fun checkField(param::params : (Symbol.symbol * T.ty) list,
                         argSym : Symbol.symbol, argTy : T.ty, argPos : int) =
              if param[0] == argSym && param[1] == argTy
              then params
              else param :: checkField(params, argSym, argTy, argPos)
            | checkField([], _) = (ErrorMsg.error argPos ("extra field" ^ S.name argSym);
                                   [])
      in checkFields(checkField(params, arg), args)
      end

    | checkFields(param::params, [], pos) = ErrorMsg.error pos ("missing argument" ^ S.name param[0])
    | checkFields([], [], pos) = ()




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
      let fun trexp (A.OpExp{left, oper= oper, right, pos}):expty =
              (checkInt(trexp left, pos);
               checkInt(trexp right, pos);
               {exp= (), ty= T.INT})
            | trexp (A.VarExp{var}) = trvar(var)
            | trexp (A.NilExp) = {exp= (), ty= T.NIL}
            | trexp (A.IntExp) = {exp= (), ty= T.INT}
            | trexp (A.StringExp) = {exp= (), ty= T.STRING}
            | trexp (A.CallExp{func, args, pos}) =
              let val fundec = S.look(venv, func)
              in (case fundec
                   of SOME(E.FunEntry{formals, result}) =>
                      (checkArgs(formals, map(trexp, args), pos);
                       {exp= (), ty= result})
                    | NONE => (ErrorMsg.error pos ("undefined function " ^ S.name func);
                               {exp= (), ty= T.BOTTOM}))
              end
            | trexp (A.RecordExp{args, typ, pos}) =
              let val recdec = S.look(tenv, typ)
                  fun trfield (sym, exp, pos) = (sym, trexp(exp), pos)
              in (case recdec
                   of SOME(T.RECORD(params, unique)) =>
                      (checkFields(fields, map(trfield, args), pos);
                       {exp= (), ty= typ})
                    | NONE => (ErrorMsg.error pos ("undefined record " ^ S.name typ);
                               {exp= (), ty= T.BOTTOM}))
              end
          and trvar (A.SimpleVar(id, pos)) =
              (case S.look(venv, id)
                of SOME(E.VarEntry{ty}) => {exp= (), ty= actual_ty(ty, pos)}
                 | NONE => (ErrorMsg.error pos ("undefined variable " ^ S.name id);
                            {exp= (), ty= T.BOTTOM}))
            | trvar (_) = {exp= (), ty=T.UNIT}
      in trexp(exp)
      end

  fun transDec(venv : venv, tenv : tenv, dec : A.dec) = {venv= venv, tenv= tenv}

  fun transTy(tenv : tenv, ty : A.ty) = T.UNIT

end (* structure Semant *)
