signature SEMANT =
sig
  type env
  type expty

  val transProg : Absyn.exp -> Translate.exp
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

fun isSubType(T.NIL, T.RECORD(fields, unique)) = true
  | isSubType(T.BOTTOM, _) = true
  | isSubType(x,y) = x = y

fun actual_ty(ty : T.ty, pos : int) =
    case ty
     of T.NAME(sym, tyref) => (* reference to an optional type *)
        (case (!tyref)
          of SOME(ty) => actual_ty(ty, pos)
           | _ => (ErrorMsg.error pos ("undefined type " ^ S.name sym);
                   T.BOTTOM))
      | _ => ty

fun assertType({exp : Translate.exp, ty : T.ty}, pos, expect) =
    if isSubType(actual_ty(ty, pos), actual_ty(expect, pos))
    then ()
    else ErrorMsg.error pos ("expected type: " ^ T.type2string(expect) ^
    " got type: " ^ T.type2string(ty))

fun checkArgs(param::params : T.ty list, {exp, ty}::args : expty list, pos : int) =
    (assertType({exp=exp, ty=ty}, pos, param);
     checkArgs(params, args, pos))
  | checkArgs([], arg::args, pos) = ErrorMsg.error pos "too many arguments"
  | checkArgs(param::params, [], pos) = ErrorMsg.error pos "not enough arguments"
  | checkArgs([], [], pos) = ()

fun checkFields(param::params, arg::args, pos) =
    let fun checkField((sym, ty)::params, (argSym, argTy, argPos)) =
            if Symbol.name sym = Symbol.name argSym
            then (assertType({exp= (), ty=argTy}, argPos, ty); params)
            else (sym, ty) :: checkField(params, (argSym, argTy, argPos))
          | checkField([], (argSym, argTy, argPos)) = (ErrorMsg.error argPos
             ("record field not found: " ^ S.name argSym); [])
    in
      checkFields(checkField(param::params, arg), args, pos)
    end
  | checkFields((sym, ty)::params, [], pos) =
      ErrorMsg.error pos ("missing argument(s) " ^ S.name sym)
  | checkFields([], (argSym, argTy, argPos)::args, pos) =
      ErrorMsg.error pos ("extra argument(s) " ^ S.name argSym)
  | checkFields([], [], pos) = ()

fun transVar(A.SimpleVar(id, pos), env) =
    (case E.lookupVar(id, env, pos)
      of E.VarEntry{ty} => {exp = (), ty= actual_ty(ty, pos)}
       | _ => (ErrorMsg.error pos ("undefined variable " ^ S.name id);
               {exp= (), ty= T.BOTTOM}))
  | transVar(A.FieldVar(var, id, pos), env) =
    let val {exp, ty} = transVar(var, env)
        fun findFieldType((sym, ty)::fields, id, pos) =
            if sym = id
            then actual_ty(ty, pos)
            else findFieldType(fields, id, pos)
          | findFieldType([], id, pos) =
            (ErrorMsg.error pos ("undefined field " ^ S.name id);
             T.BOTTOM)
    in case actual_ty(ty, pos)
        of T.RECORD(fields, unique) => {exp= (), ty= findFieldType(fields, id, pos)}
         | _ => (ErrorMsg.error pos ("no record type for " ^ T.type2string(ty));
                 {exp= (), ty= T.BOTTOM})
    end
  | transVar(A.SubscriptVar(var, exp, pos), env) =
    let val {exp, ty} = transVar(var, env)
    in case actual_ty(ty, pos)
        of T.ARRAY(ty, unique) => {exp= (), ty= ty}
         | _ => (ErrorMsg.error pos ("no array type for " ^ T.type2string(ty));
                 {exp= (), ty= T.BOTTOM})
    end

fun transExp(exp : A.exp, env) =
  let fun findTy(sym, pos) = E.lookupTy(sym, env, pos)
      and detect_loop(ty, pos, acc) =
          case ty
           of T.NAME(sym, tyref) =>
              (case !tyref
                of SOME(ty2) =>
                   if isSome(List.find(fn ref2 => (tyref = ref2))(acc))
                   then ErrorMsg.error pos ("Unresolved type definition")
                   else detect_loop(ty2, pos, tyref::acc)
                 | NONE => ErrorMsg.error pos ("undefined type" ^ S.name sym))
            | _ => ()
      and trexp(A.OpExp{left, oper= oper, right, pos}):expty =
        (case oper
          of A.EqOp =>
           (assertType(trexp right, pos, getTy(trexp left));
           {exp= (), ty= T.INT})
           | A.NeqOp =>
           (assertType(trexp right, pos, getTy(trexp left));
           {exp= (), ty= T.INT})
           | A.LtOp =>
          (assertType(trexp right, pos, T.INT);
           assertType(trexp left, pos, T.INT);
           {exp= (), ty= T.INT})
           | A.LeOp =>
          (assertType(trexp right, pos, T.INT);
           assertType(trexp left, pos, T.INT);
           {exp= (), ty= T.INT})
           | A.GtOp =>
          (assertType(trexp right, pos, T.INT);
           assertType(trexp left, pos, T.INT);
           {exp= (), ty= T.INT})
           | A.GeOp =>
          (assertType(trexp right, pos, T.INT);
           assertType(trexp left, pos, T.INT);
           {exp= (), ty= T.INT})
           | A.PlusOp =>
          (assertType(trexp right, pos, T.INT);
           assertType(trexp left, pos, T.INT);
           {exp= (), ty= T.INT})
           | A.MinusOp =>
          (assertType(trexp right, pos, T.INT);
           assertType(trexp left, pos, T.INT);
           {exp= (), ty= T.INT})
           | A.TimesOp =>
          (assertType(trexp right, pos, T.INT);
           assertType(trexp left, pos, T.INT);
           {exp= (), ty= T.INT})
           | A.DivideOp =>
          (assertType(trexp right, pos, T.INT);
           assertType(trexp left, pos, T.INT);
           {exp= (), ty= T.INT}))
        | trexp (A.VarExp(var)) = transVar(var, env)
        | trexp (A.NilExp) = {exp= (), ty= T.NIL}
        | trexp (A.IntExp(int)) = {exp= (), ty= T.INT}
        | trexp (A.StringExp(str, pos)) = {exp= (), ty= T.STRING}
        | trexp (A.CallExp{func, args, pos}) =
          (case E.lookupVar(func, env, pos)
           of E.FunEntry{formals, result} =>
                (checkArgs(formals, map(trexp)(args), pos);
                 {exp= (), ty= result})
            | _ => (ErrorMsg.error pos ("undefined function " ^ S.name func);
              {exp= (), ty= T.BOTTOM}))
        | trexp (A.RecordExp{fields = args, typ = typ, pos = pos}) =
          let val recdec = actual_ty(E.lookupTy(typ, env, pos), pos)
              fun trfield (sym, exp, pos) = (sym, getTy(trexp(exp)), pos)
          in (case recdec
               of T.RECORD(params, unique) =>
                  (checkFields(params, map(trfield)(args), pos);
                   {exp= (), ty=recdec})
                | _ => (ErrorMsg.error pos ("undefined record " ^ S.name typ);
                        {exp= (), ty= T.BOTTOM}))
          end
        | trexp (A.SeqExp(exps)) =
          let fun buildSeqExp((exp, pos) : (A.exp * int), expty : expty) = trexp(exp)
          in foldl(buildSeqExp)({exp= (), ty= T.UNIT})(exps)
          end
        | trexp (A.AssignExp{var, exp, pos}) =
          (assertType(trexp exp, pos, getTy(transVar(var, env)));
           {exp= (), ty= T.UNIT})
        | trexp (A.IfExp{test, then', else', pos}) =
          (assertType(trexp test, pos, T.INT);
          (case else'
             of SOME(exp) =>
             (if getTy(trexp(then')) <> getTy(trexp(exp))
              then ErrorMsg.error pos "branches of if/else must be of equal type"
              else ();trexp(exp))
              | NONE => 
                  (assertType(trexp then', pos, T.UNIT);
                  trexp then')))
          | trexp (A.WhileExp{test, body, pos}) =
            (assertType(trexp test, pos, T.INT);
             E.openLoop();
             assertType(trexp body, pos, T.UNIT);
             E.closeLoop();
             {exp= (), ty= T.UNIT})
          | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
            (assertType(trexp hi, pos, T.INT);
             assertType(trexp lo, pos, T.INT);
             E.beginScope(env);
             E.setTy(var, T.INT, env);
             E.openLoop();
             trexp body;
             E.closeLoop();
             E.endScope(env);
             {exp= (), ty= T.UNIT})
          | trexp (A.BreakExp(pos)) =
            (if not(E.inLoop())
             then ErrorMsg.error pos "invalid break expression outside of loop"
             else ();
            {exp= (), ty= T.BOTTOM})
          | trexp (A.LetExp{decs, body, pos}) =
            (E.beginScope(env);
             writeDecs(decs);
             trexp body;
             E.endScope(env);
             {exp= (), ty= T.BOTTOM})
          | trexp (A.ArrayExp{typ, size, init, pos}) =
            (assertType(trexp size, pos, T.INT);
             (case actual_ty(E.lookupTy(typ, env, pos), pos)
               of T.ARRAY(ty, unique) =>
                  (assertType(trexp init, pos, actual_ty(ty,pos));
                   {exp= (), ty= T.ARRAY(ty, unique)})
                | ty => (ErrorMsg.error pos ("undefined array type " ^ S.name typ); {exp= (), ty= T.BOTTOM})))
    and  writeDecs(dec::restdecs) =
        let 
            (* code for processing recursive type declarations *)
            fun addFunDecs({name, params, result, body, pos}::fundecs) =
                    let  val resultTy =
                             case result
                              of SOME((sym, pos)) => findTy(sym, pos)
                               | _ => T.UNIT
                         val paramTys = map(fn ({name, escape, typ, pos}) => findTy(typ, pos))(params)
                    in 
                       (E.setVar(name, E.FunEntry{formals= paramTys, result= resultTy}, env);
                        addFunDecs(fundecs))
                    end
                  | addFunDecs([]) = ()
            fun lookForFunDups(fundecs) =
                  (let 
                    fun findDups({name,params,result,body,pos}::decs, names) =
                      (case List.find(fn x => name = x)names
                        of SOME(nm) => ErrorMsg.error pos "duplicate type declaration"
                         | NONE => findDups(decs, name::names))
                      | findDups(_, _) = ()
                   in 
                     findDups(fundecs, [])
                   end;
                   ())
            fun checkFunDecs({name, params, result, body, pos}::fundecs) =
                    let  val resultTy =
                             case result
                              of SOME((sym, pos)) => findTy(sym, pos)
                               | _ => T.UNIT
                    in 
                      (E.beginScope(env);
                      map(fn {name, escape, typ, pos} => E.setVar(name, E.VarEntry{ty=findTy(typ, pos)}, env))(params);
                      assertType(trexp body, pos, resultTy);
                      E.endScope(env))
                  end
              | checkFunDecs([]) = ()
              and writeFunDecs(decs) =
                  (addFunDecs(decs);
                   lookForFunDups(decs);
                   checkFunDecs(decs))
              (* code for processing recursive type declarations *)
              and transTy(A.NameTy(sym, pos)) = E.lookupTy(sym, env, pos)
                | transTy(A.RecordTy(fields)) =
                  let fun transformField({name, typ, escape, pos}) = (name, findTy(typ, pos))
                      val transformedFields = map(transformField)(fields)
                  in T.RECORD(transformedFields, ref ())
                  end
                | transTy(A.ArrayTy(sym, pos)) = T.ARRAY(findTy(sym, pos), ref ())
              and addTyDecs({name, ty, pos}::tydecs) =
                  (E.setTy(name, T.NAME(name, ref NONE), env);
                   addTyDecs(tydecs))
                | addTyDecs([]) = ()
              and resolveTyDecs({name, ty, pos}::tydecs) =
                  (case E.lookupTy(name, env, pos)
                    of T.NAME(name, refer) => refer := SOME(transTy(ty))
                     | _ => ();
                   resolveTyDecs(tydecs))
                | resolveTyDecs([]) = ()
              and checkTyDecs(tydecs) =
                  (let fun report_loop({name,ty,pos}) =
                           detect_loop(E.lookupTy(name, env, pos), pos, [])
                   in map report_loop tydecs
                   end;
                   ())
              and lookForDups(tydecs) =
                  (let 
                    fun findDups({name,ty,pos}::decs, names) =
                      (case List.find(fn x => name = x)names
                        of SOME(nm) => ErrorMsg.error pos "duplicate type declaration"
                         | NONE => findDups(decs, name::names))
                      | findDups(_, _) = ()
                   in 
                     findDups(tydecs, [])
                   end;
                   ())
              and writeTyDecs(tydecs) =
                  (addTyDecs(tydecs);
                   resolveTyDecs(tydecs);
                   lookForDups(tydecs);
                   checkTyDecs(tydecs))
          in (case dec
               of A.FunctionDec(decs) => writeFunDecs(decs)
                | A.VarDec{name, escape, typ, init, pos} =>
                  (case typ
                     (* the type is declared, so we assign it and check *)
                    of SOME((sym, pos)) =>
                       let val ty = E.lookupTy(sym, env, pos)
                       in (assertType(trexp(init), pos, ty);
                           E.setVar(name, E.VarEntry{ty=ty}, env))
                       end
                     (* no type is declared, we infer based on the value *)
                     | _ =>
                       (case getTy(trexp init)
                         of T.NIL =>
                            (ErrorMsg.error pos "unqualified use of nil";
                             E.setVar(name, E.VarEntry{ty=getTy(trexp init)}, env))
                          | _ =>
                            E.setVar(name,
                                     E.VarEntry{ty=getTy(trexp init)}, env)))
                | A.TypeDec(decs) => (writeTyDecs(decs));
              writeDecs(restdecs))
          end
        | writeDecs([]) = ()
  in trexp(exp)
  end

fun transProg(exp : A.exp) =
    let val env = Env.base_env()
    in (transExp(exp, env);
        ())
    end

end (* structure Semant *)
