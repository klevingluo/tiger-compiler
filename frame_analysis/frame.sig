signature FRAME =
sig
  type register = string
  val FP : Temp.temp (* frame pointer *)
  val RV : Temp.temp (* return value, as seen by callee *)
  val registers : register list
  val tempMap : register Temp.Table.table
  (* translates the calling conventions of a C function to the tiger calling
   * conventions *)
  val externalCall: string * Tree.exp list -> Tree.exp

  type frame
  val newFrame : {name: Temp.label, formals: bool list} -> frame
  type access

  val name : frame -> Temp.label
  val formals : frame -> access list
  val allocLocal : frame -> bool -> access
  val string : Tree.label * string -> string

  val wordSize : int

  val argGetter : unit -> unit -> Temp.temp

  (* an access and a expression that evaluates to the frame that the variable
   * lives in, returns the mem address of the variable.*)
  val exp : access -> Tree.exp -> Tree.exp

  val procEntryExit1 : frame * Tree.stm -> Tree.stm
  val procEntryExit2 : frame * Assem.instr list -> Assem.instr list
  val procEntryExit3 : frame * Assem.instr list ->
                       {prolog: string, body: Assem.instr list, epilog: string}

  (* fragments, stored under the heap I believe *)
  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string
end
