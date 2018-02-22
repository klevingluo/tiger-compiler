signature SEMANT =
sig
    type env
    type expty

    val transProg : Absyn.exp -> unit
    val transExp: env * Absyn.exp -> expty
end

structure Semant : SEMANT =
struct

type env = Env.env
type expty = {exp: Translate.exp, ty: Types.ty}

structure S = Symbol
structure A = Absyn
structure E = Env
structure T = Types

fun getTy({exp, ty} : expty) = ty

fun type2string(T.RECORD(fields, unique)) = 
      let val body = case fields
                       of [] => ""
                        | (sym, ty)::rest => 
                            (Symbol.name(sym) ^ " : " ^ type2string(ty) ^ ", ")
      in
        "{" ^ body ^ "}"
      end
  | type2string(T.NIL) = "nil"
  | type2string(T.INT) = "int"
  | type2string(T.STRING) = "string"
  | type2string(T.ARRAY(ty, unique)) = ("[" ^ type2string(ty) ^ "]")
  | type2string(T.UNIT) = "unit"
  | type2string(T.BOTTOM) = "bottom"
  | type2string(T.NAME(sym, maybe)) = case !maybe 
        of SOME(ty) => (Symbol.name(sym) ^ " AKA " ^ type2string(ty))
         | NONE => "unknown"

fun assertType({exp : Translate.exp, ty : T.ty}, pos, expect) =
    case ty 
      of expect => ()
       (*| _ => ErrorMsg.error pos ("expected type:" ^ type2string(expect) ^ 
         "got type:" ^ type2string(ty))*)

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

fun extendEnvs(decs : A.dec list, env) = ()

fun transExp(env: env, exp : A.exp) =
    let fun trexp (A.OpExp{left, oper= oper, right, pos}):expty =
            (assertType(trexp left, pos, T.INT);
             assertType(trexp right, pos, T.INT);
             {exp= (), ty= T.INT})
          | trexp (A.VarExp(var)) = trvar(var)
          | trexp (A.NilExp) = {exp= (), ty= T.NIL}
          | trexp (A.IntExp(int)) = {exp= (), ty= T.INT}
          | trexp (A.StringExp(str, pos)) = {exp= (), ty= T.STRING}
          | trexp (A.CallExp{func, args, pos}) =
            let val fundec = Env.lookupVar(func, env)
            in (case fundec
                 of SOME(E.FunEntry{formals, result}) =>
                    (checkArgs(formals, map(trexp)(args), pos);
                     {exp= (), ty= result})
                  | _ => (ErrorMsg.error pos ("undefined function " ^ S.name func);
                          {exp= (), ty= T.BOTTOM}))
            end
          | trexp (A.RecordExp{fields = args, typ = typ, pos = pos}) =
            let val recdec = E.lookupTy(typ, env)
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
            (assertType(trexp exp, pos, getTy(trvar var)); 
             {exp= (), ty= T.BOTTOM})
          | trexp (A.IfExp{test, then', else', pos}) =
          (assertType(trexp test, pos, T.INT);
          (case else'
             of SOME(exp) =>
             if getTy(trexp(then')) <> getTy(trexp(exp))
             then ErrorMsg.error pos "branches of if/else must be of equal type"
             else ()
              | NONE => ());
             trexp(then'))
          | trexp (A.WhileExp{test, body, pos}) =
            (assertType(trexp test, pos, T.INT);
             assertType(trexp body, pos, T.UNIT);
             {exp= (), ty= T.UNIT})
          | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
            (assertType(trexp hi, pos, T.INT);
             assertType(trexp lo, pos, T.UNIT);
             Env.openScope(env);
             Env.setTy(var, T.INT, env);
             transExp(env, body);
             {exp= (), ty= T.UNIT})
          | trexp (A.BreakExp(pos)) = {exp= (), ty= T.BOTTOM}
          | trexp (A.LetExp{decs, body, pos}) =
            let val envs = extendEnvs(decs, venv, tenv)
            in transExp((#1 envs), (#2 envs), body)
            end
          | trexp (A.ArrayExp{typ, size, init, pos}) =
            (assertType(trexp size, pos, T.INT);
             (case E.lookupTy(typ, env)
               of SOME(T.ARRAY(ty, unique)) =>
                  (assertType(trexp init, pos, actual_ty(ty,pos));
                   {exp= (), ty= T.ARRAY(ty, unique)})
                | _ => (ErrorMsg.error pos ("undefined array type " ^ S.name typ);
                        {exp= (), ty= T.BOTTOM})))

        and trvar (A.SimpleVar(id, pos)) =
            (case Env.lookupVar(id, env)
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

fun transProg(exp : A.exp) =
    let val env = Env.base_env
    in
        (transExp(env, exp);
         ())
    end

end (* structure Semant *)
