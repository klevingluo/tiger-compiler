signature SEMANT =
sig
    type env
    type expty

    val transProg : Absyn.exp -> unit
    val transExp: Absyn.exp * env -> expty
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

fun isSubType(T.NIL, T.RECORD(fields, unique)) = true
  | isSubType(T.BOTTOM, _) = true
  | isSubType(x,y) = x = y

fun assertType({exp : Translate.exp, ty : T.ty}, pos, expect) =
  if isSubType(ty, expect) 
  then () 
  else ErrorMsg.error pos ("expected type: " ^ type2string(expect) ^ 
    " got type: " ^ type2string(ty))

fun checkArgs(param::params : T.ty list, {exp, ty}::args : expty list, pos : int) =
    if param = ty
    then checkArgs(params, args, pos)
    else ErrorMsg.error pos "type mismatch"
  | checkArgs([], arg::args, pos) = ErrorMsg.error pos "too many arguments"
  | checkArgs(param::params, [], pos) = ErrorMsg.error pos "not enough arguments"
  | checkArgs([], [], pos) = ()

fun checkFields(param::params, arg::args, pos) =
    let fun checkField((sym, ty)::params, (argSym, argTy, argPos)) =
            if sym = argSym andalso isSubType(argTy,ty)
            then params
            else param :: checkField(params, (argSym, argTy, argPos))
          | checkField([], (argSym, argTy, argPos)) = (ErrorMsg.error argPos ("record field not found:" ^ S.name argSym); [])
    in 
      checkFields(checkField(param::params, arg), args, pos)
    end
  | checkFields((sym, ty)::params, [], pos) = 
      ErrorMsg.error pos ("missing argument(s) " ^ S.name sym)
  | checkFields([], (argSym, argTy, argPos)::args, pos) = 
      ErrorMsg.error pos ("extra argument(s) " ^ S.name argSym)
  | checkFields([], [], pos) = ()

fun actual_ty(ty : T.ty, pos : int) =
    case ty
     of T.NAME(sym, tyref) => (* reference to an optional type *)
        (case (!tyref)
          of SOME(ty) => actual_ty(ty, pos)
           | _ => (ErrorMsg.error pos ("undefined type " ^ S.name sym);
                   T.NIL))
      | _ => ty

fun transExp(exp : A.exp, env) =

  let fun absynty2ty(A.NameTy(sym, pos)) = 
          (case E.lookupTy(sym, env)
            of SOME(ty) => T.NAME(sym, (ref (SOME(ty))))
             | NONE => T.NAME(sym, (ref (NONE))))
        | absynty2ty(A.RecordTy(fields)) = 
            let 
              fun transformField({name, typ, escape, pos} : A.field) = 
                (name, fillTy(typ, pos, env))
              val transformedFields = map(transformField)(fields)
            in 
              T.RECORD(transformedFields, ref ())
            end
        | absynty2ty(A.ArrayTy(sym, pos)) = 
          case E.lookupTy(sym, env)
            of SOME(ty) => T.ARRAY(ty, ref ())
             | NONE => (ErrorMsg.error pos ("undefined type " ^ S.name sym);
                    (T.ARRAY(T.BOTTOM, ref ())))
  and fillTy(sym, pos, env) =
                case E.lookupTy(sym, env)
                 of SOME(ty) => T.NAME(sym, (ref (SOME(ty))))
                  | _ => T.NAME(sym, (ref (NONE)))
  and findTy(sym, pos, env) =
                case E.lookupTy(sym, env)
                 of SOME(ty) => ty
                  | _ => (ErrorMsg.error pos ("undefined type " ^ S.name sym); T.BOTTOM)
  and trexp (A.OpExp{left, oper= oper, right, pos}):expty =
            (assertType(trexp left, pos, T.INT);
             assertType(trexp right, pos, T.INT);
             {exp= (), ty= T.INT})
          | trexp (A.VarExp(var)) = trvar(var)
          | trexp (A.NilExp) = {exp= (), ty= T.NIL}
          | trexp (A.IntExp(int)) = {exp= (), ty= T.INT}
          | trexp (A.StringExp(str, pos)) = {exp= (), ty= T.STRING}
          | trexp (A.CallExp{func, args, pos}) =
            let val fundec = E.lookupVar(func, env)
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
                     {exp= (), ty=valOf(recdec)})
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
             (if getTy(trexp(then')) <> getTy(trexp(exp))
              then ErrorMsg.error pos "branches of if/else must be of equal type"
              else ();trexp(exp))
              | NONE => (trexp then')))
          | trexp (A.WhileExp{test, body, pos}) =
            (assertType(trexp test, pos, T.INT);
             assertType(trexp body, pos, T.UNIT);
             {exp= (), ty= T.UNIT})
          | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
            (assertType(trexp hi, pos, T.INT);
             assertType(trexp lo, pos, T.UNIT);
             E.beginScope(env);
             E.setTy(var, T.INT, env);
             transExp(body, env);
             E.endScope(env);
             {exp= (), ty= T.UNIT})
          | trexp (A.BreakExp(pos)) = {exp= (), ty= T.BOTTOM}
          | trexp (A.LetExp{decs, body, pos}) =
            (E.beginScope(env);
             writeDecs(rev(decs), env);
             transExp(body, env);
             E.endScope(env);
             {exp= (), ty= T.BOTTOM})
          | trexp (A.ArrayExp{typ, size, init, pos}) =
            (assertType(trexp size, pos, T.INT);
             (case E.lookupTy(typ, env)
               of SOME(T.ARRAY(ty, unique)) =>
                  (assertType(trexp init, pos, actual_ty(ty,pos));
                   {exp= (), ty= T.ARRAY(ty, unique)})
                | SOME(_) => (ErrorMsg.error pos ("not type array:" ^ S.name typ); {exp= (), ty= T.BOTTOM})
                | _ => (ErrorMsg.error pos ("undefined type " ^ S.name typ); {exp= (), ty= T.BOTTOM})))
        and  writeDecs(dec::restdecs, env) =
        let fun findTy(sym, pos, env) =
                case E.lookupTy(sym, env)
                 of SOME(ty) => ty
                  | _ => (ErrorMsg.error pos ("undefined type " ^ S.name sym); T.BOTTOM)
            fun writeFunDecs({name, params, result, body, pos}::fundecs, env) =
                    let  val resultTy =
                             case result
                              of SOME((sym, pos)) => findTy(sym, pos, env)
                               | _ => T.UNIT
                         val paramTys = map(fn ({name, escape, typ, pos}) => findTy(typ, pos, env))(params)
                    in 
                      (map(fn {name, escape, typ, pos} => E.setVar(name, E.VarEntry{ty=findTy(typ, pos, env)}, env))(params);
                       assertType(transExp(body, env), pos, resultTy);
                       E.setVar(name, E.FunEntry{formals= paramTys, result= resultTy}, env))
                    end
                  | writeFunDecs([], _) = ()
            fun writeTyDecs({name, ty, pos}::tydecs, env) =
                    (E.setTy(name, absynty2ty(ty), env);
                    writeTyDecs(tydecs, env))
                  | writeTyDecs([], _) = ()
        in 
          (case dec
            of A.FunctionDec(decs) => writeFunDecs(decs, env)
             | A.VarDec{name, escape, typ, init, pos} =>
                 (case typ
                   (* the type is declared, so we assign it and check*)
                   of SOME((sym, pos)) => 
                       let val ty = E.lookupTy(sym, env)
                       in
                       case ty
                         of SOME(ty) => (assertType(trexp(init), pos, ty);
                                         E.setVar(name, E.VarEntry{ty=ty}, env))
                            | _ => ErrorMsg.error pos ("undefined type " ^ S.name sym)
                        end
                    (* no type is declared, we infer based on the value *)
                    | _ => E.setVar(name, E.VarEntry{ty=getTy(transExp(init, env))}, env))
             | A.TypeDec(decs) => (writeTyDecs(rev(decs), env));
             writeDecs(restdecs, env))
        end
      | writeDecs([], _) = ()
        and trvar (A.SimpleVar(id, pos)) =
            (case E.lookupVar(id, env)
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
    let val env = Env.base_env()
    in
        (transExp(exp, env);
         ())
    end

end (* structure Semant *)
