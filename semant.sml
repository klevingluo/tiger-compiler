signature SEMANT =
sig
  type env
  type expty

  val transProg : Absyn.exp -> Translate.exp
end

structure Semant : SEMANT =
struct

structure S = Symbol
structure T = Types
structure R = Translate
structure E = Env
structure A = Absyn
structure M = ErrorMsg

type env = Env.env
type expty = {exp: Translate.exp, ty: Types.ty}

fun getTy({exp, ty} : expty) = ty

fun isSubType(T.NIL, T.RECORD(fields, unique)) = true
  | isSubType(T.BOTTOM, _) = true
  | isSubType(x,y) = x = y

fun actual_ty(ty : T.ty, pos : int) =
    case ty
     of T.NAME(sym, tyref) => (* reference to an optional type *)
        (case (!tyref)
          of SOME(ty) => actual_ty(ty, pos)
           | _ => (M.error pos ("undefined type " ^ S.name sym);
                   T.BOTTOM))
      | _ => ty

(* throws an error if an unexpected type is found*)
fun assertType({exp : R.exp, ty : T.ty}, pos, expect) =
    if isSubType(actual_ty(ty, pos), actual_ty(expect, pos))
    then ()
    else M.error pos ("expected type: " ^ T.type2string(expect) ^
    " got type: " ^ T.type2string(ty))

(* throws an error if an unexpected type is found*)
fun assertSubType(ty, pos, expect) =
    if not isSubType(actual_ty(ty, pos), actual_ty(expect, pos))
    then M.error pos ("expected type: " ^ T.type2string(expect) ^
    " got type: " ^ T.type2string(ty))
    else ()

(* typechecks the values for a function call*)
fun checkArgs(param::params : T.ty list, {exp, ty}::args : expty list, pos : int) =
    (assertType({exp=exp, ty=ty}, pos, param);
     checkArgs(params, args, pos))
  | checkArgs([], arg::args, pos) = M.error pos "too many arguments"
  | checkArgs(param::params, [], pos) = M.error pos "not enough arguments"
  | checkArgs([], [], pos) = ()

(* typechecks a list of arguments for constructing a record field *)
(* params are the types desired, and args are the types that we have *)
(* returns a list of the args in order of declaration *)
(* TODO:  this is gonna be mad buggy, will need to fix *)
fun checkFields(param::params, arg::args, pos) =
    let val sortedArgs = ref []
        (* finds the arg corresponding to a single field, adds it to the sorted
         * args, returns the remaining args*)
        fun checkField((sym, ty), (argSym, {exp=argExp, ty=argTy}, argPos)::args) =
            if Symbol.name sym = Symbol.name argSym
            then (assertSubType(argTy, argPos, ty); 
                  sortedArgs := argExp::!sortedArgs;
                  args)
            else (argSym, {exp=argExp, ty=argTy}, argPos)::
                 checkField((sym, ty), args)
          | checkField((sym, ty), []) = 
            (M.error pos ("missing record field: " ^ S.name sym); [])
        fun checkFields(param::params, arg::args, pos) =
            checkFields(params, checkField(param), pos)
          | checkFields((sym, ty)::params, [], pos) =
              M.error pos ("missing argument(s) " ^ S.name sym)
          | checkFields([], (_, _, _)::args, pos) =
              M.error pos ("extra argument(s) " ^ S.name argSym)
          | checkFields([], [], pos) = ()
    in
      (checkFields(params, checkField(param), pos);
       rev !sortedArgs)
    end

fun transExp(exp : A.exp, env, lev: R.level) =
  let 
    (* gets the type from an expty *)
    fun findTy(sym, pos) = E.lookupTy(sym, env, pos)
    (* returns and expty and whether the var is writable or not *)
    (* TODO:  clean this up a bit*)
    fun transVar(A.SimpleVar(id, pos)) : (expty * bool) =
        let 
          val write = ref true
          fun transVarHelp(A.SimpleVar(id, pos)) : (expty * bool) =
            (case E.lookupVar(id, env, pos)
               of E.VarEntry{ty, access, writable} => 
                    (if not writable then write := false else ();
                     {exp = (R.simpleVar(access, level)), ty= actual_ty(ty, pos)})
                | _ => (M.error pos ("undefined variable " ^ S.name id);
                        {exp=(), ty= T.BOTTOM}))
            | transVarHelp(A.FieldVar(var, id, pos)) =
                  let val {exp, ty} = transVarHelp(var)
                      fun findFieldType((sym, ty)::fields, id, acc, pos) =
                          if sym = id
                          then (acc, actual_ty(ty, pos))
                          else findFieldType(fields, id, acc + 1, pos)
                        | findFieldType([], id, pos) =
                          (M.error pos ("undefined field " ^ S.name id);
                           (0, T.BOTTOM))
                  in case actual_ty(ty, pos)
                     of T.RECORD(fields, unique) => 
                          case findFieldType(fields, id, 0, pos) of
                               (ind, ty) => {exp=R.fieldVar(exp, ind), ty=ty}
                      | _ => (M.error pos ("no record type " ^ T.type2string(ty));
                          {exp= (), ty= T.BOTTOM})
                  end
            | transVarHelp(A.SubscriptVar(var, exp, pos)) =
                   let val {exp, ty} = transVarHelp(var)
                       val {exp=indexp, ty=indty} = trexp exp
                   in case actual_ty(ty, pos)
                        of T.ARRAY(ty, unique) => 
                           {exp= R.subscriptVar(exp, indexp), ty= ty}
                         | _ => (M.error pos ("no array type for " ^ T.type2string(ty));
                           {exp= (), ty= T.BOTTOM})
                   end
          and expt = transVarHelp(var)
        in
          (expt, !write)
        end
      (* detects loops in type definitions *)
      and detect_loop(ty, pos, acc) =
          case ty
           of T.NAME(sym, tyref) =>
              (case !tyref
                of SOME(ty2) =>
                   if isSome(List.find(fn ref2 => (tyref = ref2))(acc))
                   then M.error pos ("Unresolved type definition")
                   else detect_loop(ty2, pos, tyref::acc)
                 | NONE => M.error pos ("undefined type" ^ S.name sym))
            | _ => ()
      and trexp(A.OpExp{left, oper= oper, right, pos}) : expty =
        let
          val {exp=rexp, ty=rty} = trexp right
          val {exp=lexp, ty=lty} = trexp left
        in
          (case oper of
                A.EqOp     =>  assertSubType(rty, pos, lty)
              | A.NeqOp    =>  assertSubType(rty, pos, lty)
              | A.LtOp     => (assertSubType(rty, pos, T.INT); 
                               assertSubType(lty, pos, T.INT))
              | A.LeOp     => (assertSubType(rty, pos, T.INT); 
                               assertSubType(lty, pos, T.INT))
              | A.GtOp     => (assertSubType(rty, pos, T.INT); 
                               assertSubType(lty, pos, T.INT))
              | A.GeOp     => (assertSubType(rty, pos, T.INT); 
                               assertSubType(lty, pos, T.INT))
              | A.PlusOp   => (assertSubType(rty, pos, T.INT); 
                               assertSubType(lty, pos, T.INT))
              | A.MinusOp  => (assertSubType(rty, pos, T.INT); 
                               assertSubType(lty, pos, T.INT))
              | A.TimesOp  => (assertSubType(try, pos, T.INT); 
                               assertSubType(lty, pos, T.INT))
              | A.DivideOp => (assertSubType(rty, pos, T.INT); 
                               assertSubType(lty, pos, T.INT));
           R.opExp(rexp, oper, lexp))
        end
        | trexp (A.VarExp(var))         = (#1 transVar(var))
        | trexp (A.NilExp)              = {exp=R.nilExp(), ty= T.NIL}
        | trexp (A.IntExp(i))           = {exp=R.intExp(i), ty= T.INT}
        | trexp (A.StringExp(str, pos)) = {exp=R.stringExp(str), ty=T.STRING}
        (* TODO: is this right? *)
        | trexp (A.CallExp{func, args, pos}) =
          (case E.lookupVar(func, env, pos)
           of E.FunEntry{level, label, formals, result} =>
                let
                  val argexptys = map(trexp)(args)
                  val argexps = map(fn {exp, ty} => exp)(argexptys)
                in
                  (checkArgs(formals, argexptys, pos);
                   {exp=(R.callExp(label, argexps)), ty= result})
                end
            | _ => (M.error pos ("undefined function " ^ S.name func);
              {exp= (), ty= T.BOTTOM}))
        | trexp (A.RecordExp{fields = args, typ = typ, pos = pos}) =
          let val recdec = actual_ty(E.lookupTy(typ, env, pos), pos)
              fun trfield(sym, exp, pos) = (sym, trexp(exp), pos)
              val fields=map(trfield)(args)
              val fieldtys= map(fn (sym, {exp, ty}, pos) => (sym, ty, pos))(args)
              val fieldexps= map(fn (sym, {exp, ty}, pos) => (sym, exp))(args)
          in (case recdec
               of T.RECORD(params, unique) =>
                  (checkFields(params, fieldtys, pos);
                   {exp=(R.record(checkFields(params, fieldtys, pos))), 
                    ty=recdec})
                | _ => (M.error pos ("undefined record " ^ S.name typ);
                        {exp= (), ty= T.BOTTOM}))
          end
        | trexp (A.SeqExp(exps)) =
          let val exps = map(trexp)(exps)
          in case List.last(exps)
              of {exp=lastexp, ty=ty} =>
                 {exp=R.sequence(exps), ty=ty}
          end
        | trexp (A.AssignExp{var, exp, pos}) =
          let val (writable, {exp=varexp, ty=varty}) = transVar(var)
              val {exp=valexp, ty=valty} = trexp exp
          in
            (if not writable
             then M.error pos ("writing to read only variable: " ^ S.name var)
             else
             (assertType(valexp, pos, varty);
             {exp= (R.assign(varexp, valexp)), ty= T.UNIT}))
          end
        | trexp (A.IfExp{test, then', else', pos}) =
          (assertType(trexp test, pos, T.INT);
           let val {exp=testexp, ty=testy} = trexp test
               val {exp=thenexp, ty=thenty} = trexp then'
           in 
             (case else' of
                   SOME(exp) => 
                     let val {exp=elseexp, ty=elsety} = trexp exp
                     in
                       (assertSubType(elsety, pos, thenty);
                        {exp=R.IfExp(testexp, thenexp, SOME(elseexp))
                         ty=elsety})
                     end
                 | NONE => 
                     (assertSubType(thenty, pos, T.UNIT);
                      {exp=R.IfExp(testexp, thenexp, NONE)
                       ty=T.UNIT}))
           end)
          | trexp (A.WhileExp{test, body, pos}) =
              let val {exp:testexp, ty:testty} = trexp test
                  val {exp:bodyexp, ty:bodyty} = trexp test
              in
                (assertSubType(testty, pos, T.INT);
                 E.openLoop();
                 assertSubType(bodyty, pos, T.UNIT);
                 E.closeLoop();
                 {exp= (R.whileExp(testexp, bodyexp)), 
                  ty= T.UNIT})
              end
          | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
            let
              val whileAbsyn = A.LetExp({
                decs= [A.VarDec({name= Symbol.symbol var,
                                 escape= escape,
                                 typ=SOME(Symbol.symbol "int" * pos),
                                 init=lo,
                                 pos=pos}), 
                       A.VarDec({name=Symbol.symbol "_limit",
                                 escape=false,
                                 typ=SOME(Symbol.symbol "int" * pos),
                                 init=hi,
                                 pos=pos})], 
                body= A.WhileExp{test= A.IntExp(1)
                                 body= A.SeqExp(
                                   (body, pos)::
                                   A.IfExp(
                                     {test= A.OpExp(
                                              A.GeOp,
                                              A.VarExp(A.SimpleVar(var)),
                                              A.VarExp(A.SimpleVar(Symbol.symbol "_limit"))), 
                                      then'= A.BreakExp(pos), 
                                      pos= pos})::
                                   A.AssignExp({var= A.simpleVar(var), 
                                                exp= A.OpExp(A.PlusOp, 
                                                             A.VarExp(A.simpleVar(var))u, 
                                                             A.IntExp(1))
                                                pos= pos})::
                                   [])
                                 pos= pos},
                pos= pos})
            in
              trexp A.IfExp({test=A.OpExp(A.LeOp, lo, hi)
                             then'=whileAbsyn
                             else'=NONE
                             pos=pos})
            end
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
             then M.error pos "invalid break expression outside of loop"
             else ();
            {exp= (), ty= T.BOTTOM})
          | trexp (A.ArrayExp{typ, size, init, pos}) =
            (assertType(trexp size, pos, T.INT);
             (case actual_ty(E.lookupTy(typ, env, pos), pos)
               of T.ARRAY(ty, unique) =>
                  (assertType(trexp init, pos, actual_ty(ty,pos));
                   {exp= (), ty= T.ARRAY(ty, unique)})
                | ty => 
                    (M.error pos ("undefined array type " ^ S.name typ);
                     {exp= (), ty= T.BOTTOM})))
          | trexp (A.LetExp{decs, body, pos}) =
            (E.beginScope(env);
             transDec(decs);
             trexp body;
             E.endScope(env);
             {exp= (), ty= T.BOTTOM})
    and transDec(dec::restdecs, lev : R.level) : Tree.exp list=
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
                        of SOME(nm) => M.error pos "duplicate type declaration"
                         | NONE => findDups(decs, name::names))
                      | findDups(_, _) = ()
                   in 
                     findDups(fundecs, [])
                   end;
                   ())
            fun checkFunDecs({name, params, result, body, pos}::fundecs) =
              (E.beginScope(env);
               (* add the variables to the scope *)
               map(fn {name, escape, typ, pos} => 
                       E.setVar(name, 
                       E.VarEntry{ty=findTy(typ, pos), 
                                  access = (),
                                  writable=true}, 
                                  env))(params);
               let  
                 val resultTy =
                   case result
                     of SOME((sym, pos)) => findTy(sym, pos)
                      | _ => T.UNIT
                 val transBody = 
                   transExp(body, 
                            env, 
                            R.newLevel({parent= level,
                                        name= Temp.newlabel(),
                                        (* TODO:  map to escapes *)
                                        formals= params}))
               in 
                 (assertType(transBody, resultTy);
                  (* saves the fragment containing the translated body and frame
                   * information *)
                  R.procEntryExit(transBody, translate.newFrame({})))
               end;
               E.endScope(env))
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
                        of SOME(nm) => M.error pos "duplicate type declaration"
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
                   checkTyDecs(tydecs);
                   ())
          in case dec
               of A.FunctionDec(decs) => (writeFunDecs(decs);[])
                | A.VarDec{name, escape, typ, init, pos} =>
                  let
                    val ty = case typ
                               (* the type is declared, so we assign it and check *)
                               of SOME((sym, pos)) => E.lookupTy(sym, env, pos)
                               (* no type is declared, we infer based on the value *)
                                | NONE => case getTy(trexp init)
                                            of T.NIL =>
                                                 (M.error pos "unqualified use of nil";
                                                  T.BOTTOM)
                                             | ty => ty
                    and access = R.allocLocal(level)(escape)
                    and entry = E.VarEntry{ty=ty, 
                                           access=access,
                                           writable=true}
                    and tran = trexp init
                  in
                    (assertType(tran, pos, ty);
                     E.setVar(name, entry env);
                     R.initialize(R.simpleVar(access, level),
                                          tran)
                                          cccccccddccc
                  transDec(restdecs, lev : R.level))
                   end
        end
        | transDec([]) = ()
  in trexp(exp)
  end

fun transProg(exp : A.exp) =
    let val env = Env.base_env()
    in (transExp(exp, env);
        ())
    end

end (* structure Semant *)
