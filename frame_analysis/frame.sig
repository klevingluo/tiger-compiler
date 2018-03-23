signature FRAME = 
sig 
  type frame
  type access
  val newFrame : {name: Temp.label, formals: bool list} -> frame
  val name : frame -> Temp.label
  val formals : frame -> access list
  val allocLocal : frame -> bool -> access

  (* this is the frame pointer *)
  val FP : Temp.temp
  (* the wordsize *)
  val wordSize : int

  (* an access and a expression that evaluates to the frame that the variable
   * lives in, returns the mem address of the variable.*)
  val exp : access -> Tree.exp -> Tree.exp

  (* fragments, stored under the heap I believe *)
  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

  (* translates the calling conventions of a C function to the tiger calling
   * conventions *)
  val externalCall: string * Tree.exp list -> Tree.exp

  val RV : Temp.temp (* as seen by callee *)

  val procEntryExit1 : frame * Tree.stm -> Tree.stm
end
