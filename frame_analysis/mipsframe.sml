structure MipsFrame : FRAME = 
struct 
  structure T = Tree
  val FP = Temp.newtemp()
  val RV = Temp.newtemp()
  val wordSize = 8

  (* InFrame indicates things that are in the frame at offset int from the stack
   * pointer.  InReg are register locations (which are copied onto the stack for
   * nonleaf operations *)
  datatype access = InFrame of int | InReg of Temp.temp

  type frame = {
    formals : access list,
    shift   : string list,
    numlocals : int ref,
    location : Temp.label
  }

  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string


  fun newFrame({name, formals}) =
    {
      (* will need to copy the stack pointer to the frame pointer, the move the
       * stack pointer to the end I'm pretty sure this will need to be in MIPS
       * instructions.
       *
       * I'm guessing alloclocal will get called here somewhere.  If the
       * argument is escaped.
       * *)
      formals=[],
      shift=[],
      numlocals=ref 0,
      location=Temp.newlabel()
      (* mips stuff in the shift bit *)
    }

  val name : frame -> Temp.label = fn df =>Temp.newlabel()
  (* this is wrong btw *)

  (* the list of where the formals for this call will be kept at run time *)
  val formals : frame -> access list = fn df => []

  fun allocLocal({formals, shift, numlocals, location}) =
    (numlocals := !numlocals + 1;
     fn esc =>
       if esc
       then InReg(Temp.newtemp())
       else InFrame(!numlocals(* new local variable*)))

  fun exp(acc)=
    fn fp =>
    case acc
      of (InFrame i) => T.MEM(T.BINOP(T.PLUS, fp, T.CONST i))
       | (InReg t) => T.TEMP t

  fun externalCall(s, args) =
    T.CALL(T.NAME(Temp.namedlabel s), args)

  (* just a stub for now *)
  fun procEntryExit1(frame, body) = body

end

