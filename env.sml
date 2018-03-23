signature ENV =
sig
  type ty
  datatype enventry = VarEntry of {access: Translate.access, 
                                   ty: ty,
                                   writable: bool}
                    | FunEntry of {level: Translate.level,
                                   label: Temp.label,
                                   formals: ty list, 
                                   result: ty}

  type env = (ty Symbol.table ref * enventry Symbol.table ref) list ref

  val base_env : unit -> env

  val beginScope : env -> unit
  val endScope : env -> unit
  val openLoop : unit -> unit
  val closeLoop : unit -> unit
  val inLoop : unit -> bool
  val setVar: Symbol.symbol * enventry * env -> unit
  val setTy: Symbol.symbol * ty * env -> unit
  val lookupTy : Symbol.symbol * env * int -> ty
  val lookupVar : Symbol.symbol * env * int -> enventry
end

structure Env : ENV =
struct
  type ty=Types.ty

  datatype enventry = VarEntry of {access: Translate.access, 
                                   ty: ty,
                                   writable: bool}
                    | FunEntry of {level: Translate.level,
                                   label: Temp.label,
                                   formals: ty list, 
                                   result: ty}

  type scope = (ty Symbol.table ref * enventry Symbol.table ref)
  type env = scope list ref

  val breakenv : unit list ref = ref []
  fun beginScope(env) = env := (ref Symbol.empty, ref Symbol.empty):: !env

  fun endScope(env) = 
    case !env 
      of [] => ErrorMsg.error 0 "Tried to close root scope"
       | scope::rest => env := rest

  fun openLoop() =
      breakenv := () :: !breakenv

  fun closeLoop() =
      case !breakenv
       of (env::envs) => breakenv := envs
        | _ => ()

  fun inLoop() =
      case !breakenv
       of [] => false
        | _ => true

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
  fun lookupTy(sym, env, pos) = 
    case lookup(sym, env, tyNames)
      of SOME(ty) => ty
       | _ => (ErrorMsg.error pos ("undefined type " ^ Symbol.name sym); Types.BOTTOM)

  val varNames = fn scope:scope => (#2 scope)
  fun setVar(sym, var, env) = set(sym, var, env, varNames)

  fun lookupVar(sym, env, pos) = 
    case lookup(sym, env, varNames)
       of SOME(var) => var
        | _ => (ErrorMsg.error pos ("undefined variable " ^ Symbol.name sym);
             VarEntry{ty= Types.BOTTOM})

  val base_tenv =
      Symbol.enter(
          Symbol.enter(
              Symbol.empty,
              Symbol.symbol("int"),
              Types.INT),
          Symbol.symbol("string"),
          Types.STRING)

  val base_venv : enventry Symbol.table = Symbol.empty

  fun base_env() : env = ref [(ref base_tenv, ref base_venv)]
end
