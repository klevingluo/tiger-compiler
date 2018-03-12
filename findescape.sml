(* TODO : figure out if all of those d+1's are correct *)
structure FindEscape : 
sig 
  val findEscape: Absyn.exp -> unit
end =

struct
  structure A = Absyn

  type depth = int
  type escEnv = (depth * bool ref) Symbol.table

  (* looks through the variable references to the underlying var *)
  fun traverseVar(env:escEnv, d:depth, A.SimpleVar(id, pos)) =
      case env.look(var)
        of SOME((depth, escape)) =>
             if depth < d
             then escape := true
             else ()
         | NONE => ()
    | traverseVar(env:escEnv, d:depth, A.FieldVar(var, id, pos)) =
        traverseVar(var)
    | traverseVar(env:escEnv, d:depth, A.SubscriptVar(var, exp, pos)) =
        traverseVar(var)

  and traverseExp(env, d, A.OpExp{left, oper, right, pos}) =
    (traverseExp(env, d, left);
     traverseExp(env, d, right))
    | traverseExp(env, d, A.VarExp(var)) = 
      traverseVar(env, d, var)
    | traverseExp(env, d, A.NilExp) = ()
    | traverseExp(env, d, A.IntExp(int)) = ()
    | traverseExp(env, d, A.StringExp(str, pos)) = ()
    | traverseExp(env, d, A.CallExp{func, args, pos}) =
      map(fn x => traverseExp(env,d,x))(args)
    | traverseExp(env, d, A.RecordExp{fields = args, typ = typ, pos = pos}) =
      map(fn x => traverseExp(env,d,x))(args)
    | traverseExp(env, d, A.SeqExp(exps)) =
      map(fn x => traverseExp(env,d,x))(exps)
    | traverseExp(env, d, A.AssignExp{var, exp, pos}) =
      (traverseExp(env, d, exp);
       traverseVar(env, d, var))
    | traverseExp(env, d, A.IfExp{test, then', else', pos}) =
        (traverseExp(env,d,then');
         traverseExp(env,d,test);
        case else'
          of SOME(exp) => traverseExp(env,d,then')
           | NONE => ())
    | traverseExp(env, d, A.WhileExp{test, body, pos})= 
        (traverseExp(env,d,test);
         traverseExp(env,d,body))
    | traverseExp(env, d, A.ForExp{var, escape, lo, hi, body, pos}) =
        let
          loopEnv = Symbol.enter(env, var, (d+1, escape))
        in
          (traverseExp(env, d, lo);
           traverseExp(env, d, hi);
           traverseExp(loopEnv, d+1, body))
        end
    | traverseExp(env, d, A.BreakExp(pos)) = ()
    | traverseExp(env, d, A.LetExp{decs, body, pos})
        let
          bodyEnv = traverseDecs(env, d, decs)
        in
          traverseExp(bodyEnv, d+1, body)
        end
    | traverseExp(env, d, A.ArrayExp{typ, size, init, pos}) =
        (traverseExp(env, d, size):
         traverseExp(env, d, init))

  and traverseDecs(env, d, s:Absyn.dec list) : escEnv =
    let
      (* adds a field to the escEnv *)
      fun addField({name, escape, typ, pos} : A.field, env) = 
          Symbol.enter(env, name, (d + 1, escape))
      (* adds all fields, then checks the body of the function*)
      and traverseFun(fields, body) =
          let
            funEnv = foldr(addField)(env)(fields)
          in
            traverseExp(funEnv, d + 1, body)
          end
      (* checks all of the function declarations for escaped uses *)
      and traverseDec(env, d, A.FunctionDec(fundecs)) = 
          map( {name, params, result, body, pos} => 
               traverseFun(params, body))
               (fundecs)
        | traverseDec(env, d, A.VarDec{name, escape, typ, init, pos}) = 
          Symbol.enter(env, name, (d + 1, escape))
        | traverseDec(env, d, A.TypeDec(typedecs)) = env
    in
      map(fn x => traverseDec(env, d, x)(decs))
    end

  fun findEscape(prog: Absyn,exp) : unit = 
end
