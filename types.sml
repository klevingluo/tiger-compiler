structure Types =
struct

  type unique = unit ref

  datatype ty =
  RECORD of (Symbol.symbol * ty) list * unique
              | NIL
              | INT
              | STRING
              | ARRAY of ty * unique
              | NAME of Symbol.symbol * ty option ref
              | UNIT
              | BOTTOM

  fun type2string(RECORD(fields, unique)) =
    let 
      fun transfields([]) = ""
        | transfields((sym, ty)::rest) = 
        (Symbol.name(sym) ^ " : " ^ 
        type2string(ty) ^ ", " ^ transfields(rest))
      val body = transfields(fields)
    in
      "{" ^ body ^ "}"
    end
        | type2string(NIL) = "nil"
        | type2string(INT) = "int"
        | type2string(STRING) = "string"
        | type2string(ARRAY(ty, unique)) = ("[" ^ type2string(ty) ^ "]")
        | type2string(UNIT) = "unit"
        | type2string(BOTTOM) = "bottom"
        | type2string(NAME(sym, maybe)) = 
        case !maybe
          of SOME(ty) => (Symbol.name(sym) ^ " AKA " ^ type2string(ty))
           | NONE => "unknown"

    end
