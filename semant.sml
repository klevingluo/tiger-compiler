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

fun transVar(venv : venv, tenv : tenv, var : A.var) = {exp= (), ty= T.UNIT}

fun getTy({exp, ty} : expty) = ty

fun checkInt({exp : Translate.exp, ty : T.ty}, pos : int) =
    case ty of T.INT => ()
            |  _ => ErrorMsg.error pos "integer required"

fun checkArgs(param::params : T.ty list, {exp, ty}::args : expty list, pos : int) =
    if param = ty
    then checkArgs(params, args, pos)
    else ErrorMsg.error pos "type mismatch"
  | checkArgs([], arg::args, pos) = ErrorMsg.error pos "too many arguments"
  | checkArgs(param::params, [], pos) = ErrorMsg.error pos "not enough arguments"
  | checkArgs([], [], pos) = ()

fun checkFields(param::params : (Symbol.symbol * T.ty) list,
                arg::args : (Symbol.symbol * T.ty * int) list,
                pos : int) =
    let fun checkField(param::params : (Symbol.symbol * T.ty) list,
                       argSym : Symbol.symbol,
                       argTy : T.ty,
                       argPos : int) =
            if (#1 param) = argSym andalso (#2 param) = argTy
            then params
            else param :: checkField(params, argSym, argTy, argPos)
          | checkField([], argSym, argTy, argPos) = (ErrorMsg.error argPos ("extra field" ^ S.name argSym);
                                                     [])
    in checkFields(checkField(params, (#1 arg), (#2 arg), pos), args, pos)
    end

  | checkFields(param::params, [], pos) = ErrorMsg.error pos ("missing argument(s) " ^ S.name (#1 param))
  | checkFields([], arg::args, pos) = ErrorMsg.error pos ("extra argument(s) " ^ S.name (#1 arg))
  | checkFields([], [], pos) = ()

fun actual_ty(ty : T.ty, pos : int) =
    case ty
     of T.NAME(sym, tyref) => (* reference to an optional type *)
        (case (!tyref)
          of SOME(ty) => actual_ty(ty, pos)
           | _ => (ErrorMsg.error pos ("undefined type " ^ S.name sym);
                   T.NIL))
      | _ => ty

fun extendEnvs(decs : A.dec list, venv : venv, tenv : tenv) = (venv, tenv)

fun transExp(venv : venv, tenv : tenv, exp : A.exp) =
    let fun trexp (A.OpExp{left, oper= oper, right, pos}):expty =
            (checkInt(trexp left, pos);
             checkInt(trexp right, pos);
             {exp= (), ty= T.INT})
          | trexp (A.VarExp(var)) = trvar(var)
          | trexp (A.NilExp) = {exp= (), ty= T.NIL}
          | trexp (A.IntExp(int)) = {exp= (), ty= T.INT}
          | trexp (A.StringExp(str, pos)) = {exp= (), ty= T.STRING}
          | trexp (A.CallExp{func, args, pos}) =
            let val fundec = S.look(venv, func)
            in (case fundec
                 of SOME(E.FunEntry{formals, result}) =>
                    (checkArgs(formals, map(trexp)(args), pos);
                     {exp= (), ty= result})
                  | _ => (ErrorMsg.error pos ("undefined function " ^ S.name func);
                          {exp= (), ty= T.BOTTOM}))
            end
          | trexp (A.RecordExp{fields = args, typ = typ, pos = pos}) =
            let val recdec = S.look(tenv, typ)
                fun trfield (sym, exp, pos) = (sym, getTy(trexp(exp)), pos)
            in (case recdec
                 of SOME(T.RECORD(params, unique)) =>
                    (checkFields(params, map(trfield)(args), pos);
                     {exp= (), ty= valOf(recdec)})
                  | _ => (ErrorMsg.error pos ("undefined record " ^ S.name typ);
                          {exp= (), ty= T.BOTTOM}))
            end
          | trexp (A.SeqExp(exps)) =
            let fun buildSeqExp((exp, pos) : (A.exp * int), expty : expty) = trexp(exp)
            in foldl(buildSeqExp)({exp= (), ty= T.BOTTOM})(exps)
            end
          | trexp (A.AssignExp{var, exp, pos}) =
            if getTy(trvar(var)) = getTy(trexp(exp))
            then {exp= (), ty= T.BOTTOM}
            else (ErrorMsg.error pos "tycon mismatch";
                  {exp= (), ty= T.BOTTOM})
          | trexp (A.IfExp{test, then', else', pos}) =
            ((if getTy(trexp(test)) <> T.INT
              then ErrorMsg.error pos "test case must be of type bool/int"
              else ());
             (case else'
               of SOME(exp) =>
                  if getTy(trexp(then')) <> getTy(trexp(exp))
                  then ErrorMsg.error pos "branches of if/else must be of equal type"
                  else ()
                | NONE => ());
             trexp(then'))
          | trexp (A.WhileExp{test, body, pos}) =
            ((if getTy(trexp(test)) <> T.INT
              then ErrorMsg.error pos "test case must be of type bool/int"
              else ());
             (if getTy(trexp(body)) <> T.UNIT
              then ErrorMsg.error pos "body must be of type unit"
              else ());
             {exp= (), ty= T.UNIT})
          | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
            ((if getTy(trexp(lo)) <> T.INT orelse getTy(trexp(hi)) <> T.INT
              then ErrorMsg.error pos "low and hi bounds of for expressions must be of type int"
              else ());
             transExp(S.enter(venv, var, Env.VarEntry({ty= T.INT})), tenv, body);
             {exp= (), ty= T.UNIT})
          | trexp (A.BreakExp(pos)) = {exp= (), ty= T.BOTTOM}
          | trexp (A.LetExp{decs, body, pos}) =
            let val envs = extendEnvs(decs, venv, tenv)
            in transExp((#1 envs), (#2 envs), body)
            end
          | trexp (A.ArrayExp{typ, size, init, pos}) =
            ((if getTy(trexp(size)) <> T.INT
              then ErrorMsg.error pos "initial size of array must be of time int"
              else ());
             (case S.look(tenv, typ)
               of SOME(T.ARRAY(ty, unique)) =>
                  ((if actual_ty(ty, pos) <> getTy(trexp(init))
                    then ErrorMsg.error pos ("initial array value must be of type " ^ S.name typ)
                    else ());
                   {exp= (), ty= T.ARRAY(ty, unique)})
                | _ => (ErrorMsg.error pos ("undefined array type " ^ S.name typ);
                        {exp= (), ty= T.BOTTOM})))

        and trvar (A.SimpleVar(id, pos)) =
            (case S.look(venv, id)
              of SOME(E.VarEntry{ty}) => {exp= (), ty= actual_ty(ty, pos)}
               | _ => (ErrorMsg.error pos ("undefined variable " ^ S.name id);
                       {exp= (), ty= T.BOTTOM}))
          | trvar(A.FieldVar(var, id, pos)) =
            let val {exp, ty} = trvar(var)
                fun findFieldType((sym, ty)::fields, id, pos) =
                    if sym = id
                    then actual_ty(ty, pos)
                    else findFieldType(fields, id, pos)
                  | findFieldType([], id, pos) =
                    (ErrorMsg.error pos ("undefined field " ^ S.name id);
                     T.BOTTOM)

            in (case ty
                 of T.RECORD(fields, unique) =>
                    {exp= (), ty=findFieldType(fields, id, pos)}
                  | _ => (ErrorMsg.error pos "no record type at";
                          {exp= (), ty= T.BOTTOM}))
            end
          | trvar(A.SubscriptVar(var, exp, pos)) =
            let val {exp, ty} = trvar(var)
            in (case ty
                 of T.ARRAY(ty, unique) => {exp= (), ty= ty}
                  | _ => (ErrorMsg.error pos "not array";
                          {exp= (), ty= T.BOTTOM}))
            end

    in trexp(exp)
    end

fun transDec(venv : venv, tenv : tenv, dec : A.dec) = {venv= venv, tenv= tenv}

fun transTy(tenv : tenv, ty : A.ty) = T.UNIT

fun transProg(exp : A.exp) =
    let val tenv = Env.base_tenv
        val venv = Env.base_venv
    in
        (transExp(venv, tenv, exp);
         ())
    end

end (* structure Semant *)
