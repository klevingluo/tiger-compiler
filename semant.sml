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
   case ty of
       T.NAME(sym, tyref) => (* reference to an optional type *)
       (case (!tyref) of
             SOME(ty) => actual_ty(ty, pos)
           | _ => (M.error pos ("undefined type " ^ S.name sym); T.BOTTOM))
     | _ => ty

(* throws an error if an unexpected type is found*)
fun assertType({exp : R.exp, ty : T.ty}, pos, expect) =
  if isSubType(actual_ty(ty, pos), actual_ty(expect, pos))
  then ()
  else M.error pos ("expected type: " ^ T.type2string(expect) ^ " got type: " ^ T.type2string(ty))

(* throws an error if an unexpected type is found*)
fun assertSubType(ty, pos, expect) =
    if not (isSubType(actual_ty(ty, pos), actual_ty(expect, pos)))
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
fun checkFields(param::params, args, pos) =
  let val sortedArgs = ref []
  (* finds the arg corresponding to a single field, adds it to the sorted
   * args, returns the remaining args*)
    fun checkField((sym, ty), (argSym, {exp=argExp, ty=argTy}, argPos)::args) =
      if Symbol.name sym = Symbol.name argSym
      then (assertSubType(argTy, argPos, ty); 
            sortedArgs := argExp:: !sortedArgs; 
            args)
      else (argSym, {exp=argExp, ty=argTy}, argPos) :: checkField((sym, ty), args)
          | checkField((sym, ty), []) = 
            (M.error pos ("missing record field: " ^ S.name sym); [])
    fun checkFieldsHelper(param::params, arg::args, pos) =
        checkFieldsHelper(params, checkField(param, arg::args), pos)
      | checkFieldsHelper((sym, ty)::params, [], pos) =
              M.error pos ("missing argument(s) " ^ S.name sym)
      | checkFieldsHelper([], (argSym, _, _)::args, pos) =
              M.error pos ("extra argument(s) " ^ S.name argSym)
      | checkFieldsHelper([], [], pos) = ()
    in
      (checkFieldsHelper(params, checkField(param, args), pos);
       rev(!sortedArgs))
    end
 | checkFields([], args, pos) = []

fun transExp(exp : A.exp, env, level: R.level, break: Temp.label) =
  let 
    (* gets the type from an expty *)
    fun findTy(sym, pos) = E.lookupTy(sym, env, pos)
    (* returns and expty and whether the var is writable or not *)
    (* TODO:  clean this up a bit*)
    fun transVar(var) : (expty * bool) =
        let 
          val write = ref true
          fun transVarHelp(A.SimpleVar(id, pos)) : expty =
            (case E.lookupVar(id, env, pos)
               of E.VarEntry{ty, access, writable} => 
                    (if not writable then write := false else ();
                     {exp = (R.simpleVar(access, level)), ty= actual_ty(ty, pos)})
                | _ => (M.error pos ("undefined variable " ^ S.name id);
                        raise Fail "undefined var"))
            | transVarHelp(A.FieldVar(var, id, pos)) =
                  let val {exp, ty} = transVarHelp(var)
                      fun findFieldType((sym, ty)::fields, id, acc, pos) =
                          if sym = id
                          then (acc, actual_ty(ty, pos))
                          else findFieldType(fields, id, acc + 1, pos)
                        | findFieldType([], id, acc, pos) =
                          (M.error pos ("undefined field " ^ S.name id);
                           raise Fail "undefined field")
                  in case actual_ty(ty, pos)
                     of T.RECORD(fields, unique) => 
                          (case findFieldType(fields, id, 0, pos) of
                               (ind, ty) => {exp=R.fieldVar(exp, ind), ty=ty})
                      | _ => (M.error pos ("no record type " ^ T.type2string(ty));
                          raise Fail "not a record type")
                  end
            | transVarHelp(A.SubscriptVar(var, subexp, pos)) =
                   let val {exp, ty} = transVarHelp(var)
                       val {exp=indexp, ty=indty} = trexp subexp
                   in case actual_ty(ty, pos)
                        of T.ARRAY(ty, unique) => 
                           {exp= R.subscriptVar(exp, indexp), ty= ty}
                         | _ => 
                           (M.error pos ("no array type for " ^ T.type2string(ty));
                           raise Fail "not an array type")
                   end
          val expt = transVarHelp(var)
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
              | A.TimesOp  => (assertSubType(rty, pos, T.INT); 
                               assertSubType(lty, pos, T.INT))
              | A.DivideOp => (assertSubType(rty, pos, T.INT); 
                               assertSubType(lty, pos, T.INT));
              {exp=R.opExp(rexp, oper, lexp), ty=T.INT})
        end
        | trexp (A.VarExp(var))         = (#1(transVar(var)))
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
                    raise Fail "undefined function"))
        | trexp (A.RecordExp{fields = args, typ = typ, pos = pos}) =
          let val recdec = actual_ty(E.lookupTy(typ, env, pos), pos)
              fun trfield(sym, exp, pos) = (sym, trexp(exp), pos)
              val fields=map(trfield)(args)
              val fieldtys= map(fn (sym, {exp, ty}, pos) => (sym, ty, pos))(fields)
              val fieldexps= map(fn (sym, {exp, ty}, pos) => (sym, exp))(fields)
          in (case recdec
               of T.RECORD(params, unique) =>
                  (checkFields(params, fields, pos);
                   {exp=(R.recordExp(checkFields(params, fields, pos))), 
                    ty=recdec})
                | _ => (M.error pos ("undefined record " ^ S.name typ);
                        raise Fail "undefined record"))
          end
        | trexp (A.SeqExp(exps)) =
          if (List.null exps)
          then {exp=R.unitExp(), ty=T.UNIT}
          else
            let val transExps = map(fn (exp, pos) => trexp(exp))(exps)
                val bodies = map(fn ({exp= exp, ty= ty}) => exp)(transExps)
            in case List.last(transExps)
                 of {exp=_, ty=ty} => {exp=R.seqExp(bodies), ty=ty}
            end
        | trexp (A.AssignExp{var, exp, pos}) =
          let val ({exp=varexp, ty=varty}, writable) = transVar(var)
              val {exp=valexp, ty=valty} = trexp exp
          in
            (if (not writable)
             then (M.error pos ("writing to read only variable: "); raise Fail
             "read only var")
             else
             (assertSubType(valty, pos, varty);
             {exp= (R.assignExp(varexp, valexp)), ty= T.UNIT}))
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
                        {exp=R.ifExp(testexp, thenexp, SOME(elseexp)),
                         ty=elsety})
                     end
                 | NONE => 
                     (assertSubType(thenty, pos, T.UNIT);
                      {exp=R.ifExp(testexp, thenexp, NONE),
                       ty=T.UNIT}))
           end)
          | trexp (A.WhileExp{test, body, pos}) =
              let val {exp=testexp, ty=testty} = trexp test
                  val {exp=bodyexp, ty=bodyty} = trexp body
                  val donelab = Temp.newlabel()
                  val whileexp = R.whileExp(testexp, bodyexp, donelab)
              in
                (assertSubType(testty, pos, T.INT);
                 E.openLoop();
                 assertSubType(bodyty, pos, T.UNIT);
                 E.closeLoop();
                 {exp= whileexp, ty= T.UNIT})
              end
          | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
            let
              val whileAbsyn = A.LetExp({
                decs= [A.VarDec({name= var,
                                 escape= escape,
                                 typ=SOME(((Symbol.symbol "int"), pos)),
                                 init=lo,
                                 pos=pos}), 
                       A.VarDec({name=Symbol.symbol "_limit",
                                 escape=ref false,
                                 typ=SOME(Symbol.symbol "int", pos),
                                 init=hi,
                                 pos=pos})], 
                body= A.WhileExp{
                    test=A.IntExp(1),
                    body=A.SeqExp((body, pos)::
                                   (A.IfExp(
                                     {test= A.OpExp{
                                       left= A.VarExp(A.SimpleVar(var, pos)),
                                       oper= A.GeOp,
                                       right= A.VarExp(A.SimpleVar(Symbol.symbol
                                       "_limit", pos)),
                                       pos=pos}, 
                                      then'= A.BreakExp(pos), 
                                      else'=NONE,
                                      pos= pos}), pos)::
                                   (A.AssignExp(
                                       {var= A.SimpleVar(var,pos), 
                                        exp= A.OpExp({oper=A.PlusOp, 
                                                    right=A.VarExp(A.SimpleVar(var,pos)),
                                                    left=A.IntExp(1),
                                                    pos=pos}),
                                        pos= pos}), pos)::
                                   []),
                   pos= pos},
                pos= pos})
              val res = ref {exp= R.unitExp(), ty= T.UNIT}
            in
              (assertType(trexp hi, pos, T.INT);
               assertType(trexp lo, pos, T.INT);
               E.beginScope(env);
               E.setTy(var, T.INT, env);
               E.openLoop();
               res := trexp(A.IfExp({test=A.OpExp({
                   oper=A.LeOp, 
                   left=lo, 
                   right=hi,
                   pos=pos}),
                   then'=whileAbsyn,
                   else'=NONE,
                   pos=pos}));
               E.closeLoop();
               E.endScope(env);
               !res)
            end
          | trexp (A.BreakExp(pos)) =
            ((if not(E.inLoop())
             then M.error pos "invalid break expression outside of loop"
             else ());
             {exp= (R.breakExp(break)), ty= T.BOTTOM})
          | trexp (A.ArrayExp{typ, size, init, pos}) =
             (case actual_ty(E.lookupTy(typ, env, pos), pos) of
                  T.ARRAY(arrayty, unique) =>
                    let val {exp=sizeexp, ty=sizety} = trexp size
                        val {exp=initexp, ty=initty} = trexp init
                    in
                      (assertSubType(sizety, pos, T.INT);
                       assertSubType(initty, pos, actual_ty(arrayty,pos));
                       {exp=R.arrayExp(sizeexp, initexp), 
                        ty=T.ARRAY(arrayty, unique)})
                    end
                | ty => 
                    (M.error pos ("undefined array type " ^ S.name typ);
                     raise Fail "undefined array type"))
          | trexp (A.LetExp{decs, body, pos}) =
          let
            val res = ref {exp= R.nilExp(), ty= T.NIL}
            val inits = ref []
          in
            (E.beginScope(env);
             inits := transDec(decs);
             res := (case trexp(body) of 
                         {exp=exp, ty=ty} => {exp=R.letExp(!inits,exp), ty=ty});
             E.endScope(env);
             !res)
          end
    (* TODO: creates a new type and value environment, and returns a translate
     * exp.  This also reserves more space in the current frame for every
     * variable. and saves a function fragment for each function body.*)
    and transDec(dec::restdecs) : R.exp list =
        let 
            (* code for processing recursive type declarations *)
            fun addFunDecs({name, params, result, body, pos}::fundecs) =
                    let  
                      val resultTy =
                             case result of
                                  SOME((sym, pos)) => findTy(sym, pos)
                                | _ => T.UNIT
                      val paramTys = map(fn ({name, escape, typ, pos}) => 
                                                findTy(typ, pos))
                                         (params)
                    in 
                       (E.setVar(name, 
                                 E.FunEntry{formals=paramTys, 
                                            result=resultTy,
                                            level=level,
                                            label=Temp.newlabel()}, 
                                 env);
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
                                  (* we don't think this matters, since this is
                                   * only for typechecking *)
                                  access=R.allocLocal(level)(!escape),
                                  writable=true}, 
                                  env))(params);
               let  
                 val resultTy =
                   case result
                     of SOME((sym, pos)) => findTy(sym, pos)
                      | _ => T.UNIT
                 val {exp=bodyexp, ty=bodyty} = 
                   transExp(body, 
                            env, 
                            R.newLevel({parent=level,
                                        name=Temp.newlabel(),
                                        formals=
                                          map(fn({name, escape, typ, pos})=> !escape)
                                          (params)}),
                            break)
               in 
                 (assertSubType(bodyty, pos, resultTy);
                  (* saves the fragment containing the translated body and frame
                   * information *)
                  R.procEntryExit(level, bodyexp))
               end;
               E.endScope(env))
              | checkFunDecs([]) = ()
            fun writeFunDecs(decs: A.fundec list) =
                  (addFunDecs(decs: A.fundec list);
                   lookForFunDups(decs: A.fundec list);
                   checkFunDecs(decs: A.fundec list))
              (* code for processing recursive type declarations *)
            fun transTy(A.NameTy(sym, pos)) = E.lookupTy(sym, env, pos)
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
          in 
            List.revAppend(rev
            (case dec of
                  A.FunctionDec(decs: A.fundec list) => (writeFunDecs(decs);[])
                | A.TypeDec(decs) => (writeTyDecs(decs);[])
                | A.VarDec{name, escape, typ, init, pos} =>
                  let
                    val ty = (case typ
                               (* the type is declared, so we assign it and check *)
                               of SOME((sym, pos)) => E.lookupTy(sym, env, pos)
                               (* no type is declared, we infer based on the value *)
                                | NONE => case getTy(trexp init)
                                            of T.NIL =>
                                                 (M.error pos "unqualified use of nil";
                                                  T.BOTTOM)
                                             | ty => ty)
                    val access = R.allocLocal(level)(!escape)
                    val entry = E.VarEntry{ty=ty, 
                                           access=access,
                                           writable=true}
                    val {exp=initexp, ty=initty} = trexp init
                  in
                    (assertSubType(initty, pos, ty);
                     E.setVar(name, entry, env);
                     (* allocates space in the current frame and also creates
                      *)
                     [R.initialize(R.simpleVar(access, level), initexp)])
                  end),
                  transDec(restdecs))
          end
        | transDec([]) = []
  in trexp(exp)
  end

fun makeGraph(frag) =
  case frag of 
       MipsFrame.PROC{body, frame} => 
         (* MakeGraph.instrs2graph(MipsGen.codegen(frame, body)) *)
         map(fn x =>
           print(Assem.format(Temp.makestring)(x)))(MipsGen.codegen(frame, body))
     | MipsFrame.STRING(lab, str) => [()]

fun transProg(exp : A.exp) =
    let 
      val env = Env.base_env()
      val baselvl = R.outermost
      val _ = FindEscape.findEscape(exp)
      val {exp, ty} = transExp(exp, env, baselvl, Temp.newlabel())
    in 
      (map(makeGraph)(R.getResult());
       R.printtree(exp); 
       exp)
    end

end (* structure Semant *)
