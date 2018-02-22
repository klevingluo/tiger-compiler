signature ENV =
sig
  type ty
  datatype enventry = VarEntry of {ty: ty}
                    | FunEntry of {formals: ty list, result: ty}
  type env = (ty Symbol.table ref * enventry Symbol.table ref) list ref

  val base_env : env

  val openScope : env -> unit
  val closeScope : env -> unit
  val setVar: (Symbol.symbol * enventry * env) -> unit
  val setTy: (Symbol.symbol * ty * env) -> unit
  val lookupTy : Symbol.symbol * env -> ty option
  val lookupVar : Symbol.symbol * env -> enventry option
end

structure Env : ENV =
struct
  type ty=Types.ty

  datatype enventry = VarEntry of {ty: ty}
                    | FunEntry of {formals: ty list, result: ty}

  type scope = (ty Symbol.table ref * enventry Symbol.table ref)
  type env = scope list ref

  fun openScope(env) = env := (ref Symbol.empty, ref Symbol.empty):: !env

  fun closeScope(env) = 
    case !env 
      of [] => ErrorMsg.error 0 "Tried to close root scope"
       | scope::rest => env := rest

  fun set(sym, var, env, namespace) = let
    val table = (namespace (hd (! env)))
  in
    table := Symbol.enter(! table, sym, var)
  end

  fun lookup(sym, env, namespace) =
    case !env 
      of [] => NONE
       | scope::rest => 
           let 
             val table = (namespace scope)
             val maybe = Symbol.look(! table, sym)
           in
             case maybe 
             of SOME(result) => SOME(result)
              | NONE => lookup(sym, (ref (tl(!env))), namespace)
           end


  val tyNames = fn scope:scope => (#1 scope)
  fun setTy(sym, var, env) = set(sym, var, env, tyNames)
  fun lookupTy(sym, env) = lookup(sym, env, tyNames)

  val varNames = fn scope:scope => (#2 scope)
  fun setVar(sym, var, env) = set(sym, var, env, varNames)
  fun lookupVar(sym, env) = lookup(sym, env, varNames)

  val base_tenv =
      Symbol.enter(
          Symbol.enter(
              Symbol.empty,
              Symbol.symbol("int"),
              Types.INT),
          Symbol.symbol("string"),
          Types.STRING)

  val base_venv : enventry Symbol.table = Symbol.empty

  val base_env : env = ref [(ref base_tenv, ref base_venv)]
end

