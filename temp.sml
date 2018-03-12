structure Temp :
sig
  eqtype temp
  val newtemp : unit -> temp
  structure Table : TABLE sharing type Table.key = temp
  val makestring : temp -> string

  type label = Symbol.symbol
  val newlabel : unit -> label
  val namedlabel : string -> label
end

struct
  val newtemp() = ref ();
end

