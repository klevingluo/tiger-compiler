structure MipsFrame : FRAME = 
struct 

  (* InFrame indicates things that are in the frame at offset int from the stack
   * pointer.  InReg are register locations (which are copied onto the stack for
   * nonleaf operations *)
  datatype access = InFrame of int | InReg of Temp.temp

  type frame = {
    formals : access list
    shift   : string list
    numlocals : int ref
    location : Temp.label
  }

  fun makeArg(escaped) =
    if escaped
    then Temp.newtemp()
    else Temp.newlabel()

  val newFrame : {name: Temp.label, formals: bool list} -> frame =
    {
      (* will need to copy the stack pointer to the frame pointer, the move the
       * stack pointer to the end I'm pretty sure this will need to be in MIPS
       * instructions.
       *
       * I'm guessing alloclocal will get called here somewhere.  If the
       * argument is escaped.
       * *)
      locals= map(makeArg)(formals)
      location= name
      numlocals = ref 0
      shift= ["mips stuff here, copy ret addr, alloc temps, save regs, move
      stack and frame pointers"]
    }
  val name : frame -> Temp.label

  (* the list of where the formals for this call will be kept at run time *)
  val formals : frame -> access list = ()

  val allocLocal(frame) =
    (* increase local allocation count*)
    fn esc =>
      if esc
      then InReg(Temp.newtemp())
      else InFrame((* new local variable*))
end

