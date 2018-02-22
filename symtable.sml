(* a class for very efficient lookups of types*)

signature TYPE_ENV =
sig
  type binding
  type name
  type countour
  val lookup: string -> Types.ty
  val assign: string * Types.ty -> unit
  val scope: unit -> unit
  type typeEnv = {ht: (string, name) HashTable.hash_table}
end;


structure TypeEnv =
struct
  type name = Types.ty list ref
  type countour = name list ref
  type typeEnv = {ht: (string, name) HashTable.hash_table}

  val ht : (string, name) HashTable.hash_table = 
    HashTable.mkTable(HashString.hashString, op =)
    (42, Fail "not found")

  fun lookup (symbol) = hd(!(HashTable.lookup(ht)(symbol)))

  fun assign (symbol, value) =
    let
      val bindings = HashTable.lookup(ht)(symbol)
    in 
      bindings := value::(!bindings)
    end 
end;

