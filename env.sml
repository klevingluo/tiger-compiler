signature ENV =
sig
    type ty
    datatype enventry = VarEntry of {ty: ty}
                      | FunEntry of {formals: ty list, result: ty}
    val base_tenv : ty IntMapTable.table
    val base_venv : enventry IntMapTable.table
end

structure Env : ENV =
struct
  type ty=Types.ty
  datatype enventry = VarEntry of {ty: ty}
                    | FunEntry of {formals: ty list, result: ty}

  val base_tenv =
      IntMapTable.enter(
          IntMapTable.enter(
              IntMapTable.empty,
              Symbol.symbol("int"),
              Types.INT),
          Symbol.symbol("string"),
          Types.STRING)

  val base_venv = IntMapTable.empty
end
