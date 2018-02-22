signature SEMANT =
sig
    type expty

    val transProg : Absyn.exp -> unit
    val transExp: Absyn.exp -> expty
end

structure Semant : SEMANT =
struct

type expty = {exp: Translate.exp, ty: Types.ty}

val env = () (* incoming *)

structure S = Symbol
structure A = Absyn
structure E = Env
structure T = Types

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

fun writeDecs(dec::decs) =
    let fun findTy(sym, pos) =
            case S.lookupTy(env, sym)
             of SOME(ty) => ty
              | _ => (ErrorMsg.error pos ("undefined type " ^ S.name sym);
                      T.BOTTOM)
        and fun writeFunDecs({name, params, result, body, pos}::fundecs) =
                let  val resultTy =
                         case result
                          of SOME((sym, pos)) => findTy(sym, pos)
                           | _ => T.UNIT
                     val paramTys = map(fn ({name, escape, typ, pos}) => findTy(typ, pos))(params)
                in if getTy(transExp(body)) <> resultTy
                   then ErrorMsg.error pos "function signature mismatch"
                   else S.setVar(env, name, E.FunEntry{formals= paramTys, result= resultTy})
                end
              | writeFunDecs([]) = ()
        and fun writeTyDecs({name, ty, pos}::tydecs) =
                (S.setTy(env, name, findTy(ty, pos));
                 writeTyDecs(tydecs))
              | writeTyDecs([]) = ()
    in case dec
        of FunctionDec(decs) => writeFunDecs(decs)
         | VarDec{name, escape, typ, init, pos} =>
           S.setVar(env, name, E.VarEntry{ty= findTy(typ)})
         | TypeDec(decs) => writeTyDecs(decs)
    end
  | writeDecs([]) = ()

fun transExp(exp : A.exp) =
    let fun trexp (A.OpExp{left, oper= oper, right, pos}):expty =
            (checkInt(trexp left, pos);
             checkInt(trexp right, pos);
             {exp= (), ty= T.INT})
          | trexp (A.VarExp(var)) = trvar(var)
          | trexp (A.NilExp) = {exp= (), ty= T.NIL}
          | trexp (A.IntExp(int)) = {exp= (), ty= T.INT}
          | trexp (A.StringExp(str, pos)) = {exp= (), ty= T.STRING}
          | trexp (A.CallExp{func, args, pos}) =
            let val fundec = S.lookupVar(env, func)
            in (case fundec
                 of SOME(E.FunEntry{formals, result}) =>
                    (checkArgs(formals, map(trexp)(args), pos);
                     {exp= (), ty= result})
                  | _ => (ErrorMsg.error pos ("undefined function " ^ S.name func);
                          {exp= (), ty= T.BOTTOM}))
            end
          | trexp (A.RecordExp{fields = args, typ = typ, pos = pos}) =
            let val recdec = S.lookupTy(env, typ)
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
             S.openScope();
             S.setVar(env, var, Env.VarEntry({ty= T.INT}));
             transExp(body);
             S.closeSope();
             {exp= (), ty= T.UNIT})
          | trexp (A.BreakExp(pos)) = {exp= (), ty= T.BOTTOM}
          | trexp (A.LetExp{decs, body, pos}) =
            (S.openScope();
             writeDecs(decs);
             transExp(body);
             S.closeScope())
          | trexp (A.ArrayExp{typ, size, init, pos}) =
            ((if getTy(trexp(size)) <> T.INT
              then ErrorMsg.error pos "initial size of array must be of time int"
              else ());
             (case S.lookupTy(env, typ)
               of SOME(T.ARRAY(ty, unique)) =>
                  ((if actual_ty(ty, pos) <> getTy(trexp(init))
                    then ErrorMsg.error pos ("initial array value must be of type " ^ S.name typ)
                    else ());
                   {exp= (), ty= T.ARRAY(ty, unique)})
                | _ => (ErrorMsg.error pos ("undefined array type " ^ S.name typ);
                        {exp= (), ty= T.BOTTOM})))

        and trvar (A.SimpleVar(id, pos)) =
            (case S.lookupVar(env, id)
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
    (transExp(exp);
     ())

end (* structure Semant *)
