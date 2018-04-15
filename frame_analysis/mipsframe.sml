structure MipsFrame : FRAME =
struct
  structure T = Tree
  val wordSize = 8

  type register = string

  val FP = Temp.newtemp()
  val RV = Temp.newtemp()

  (* 0 register *)
  val R0 = Temp.newtemp()
  (* return registers *)
  val R2 = Temp.newtemp()
  val R3 = Temp.newtemp()
  (* argument registers *)
  val R4 = Temp.newtemp()
  val R5 = Temp.newtemp()
  val R6 = Temp.newtemp()
  val R7 = Temp.newtemp()
  (* caller-save registers *)
  val R8 = Temp.newtemp()
  val R9 = Temp.newtemp()
  val R10 = Temp.newtemp()
  val R11 = Temp.newtemp()
  val R12 = Temp.newtemp()
  val R13 = Temp.newtemp()
  val R14 = Temp.newtemp()
  val R15 = Temp.newtemp()
  val R24 = Temp.newtemp()
  val R25 = Temp.newtemp()
  (* callee-save registers *)
  val R16 = Temp.newtemp()
  val R17 = Temp.newtemp()
  val R18 = Temp.newtemp()
  val R19 = Temp.newtemp()
  val R20 = Temp.newtemp()
  val R21 = Temp.newtemp()
  val R22 = Temp.newtemp()
  val R23 = Temp.newtemp()
  (* reserved kernel registers *)
  val R26 = Temp.newtemp()
  val R27 = Temp.newtemp()
  (* global area *)
  val R28 = Temp.newtemp()
  (* stack pointer *)
  val R29 = Temp.newtemp()
  (* frame pointer *)
  val R30 = Temp.newtemp()
  (* return program counter *)
  val R31 = Temp.newtemp()

  val specialregs = [R0, R2, R3, R26, R27, R28, R29, R30, R31]
  val argregs = [R4, R5, R6, R7]
  val callersaves = [R8, R9, R10, R11, R12, R13, R14, R15, R24, R25]
  val calleesaves = [R16, R17, R18, R19, R20, R21, R22, R23]

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

  fun argGetter() =
    let val num = ref ~1
    in
      fn () => (num := !num + 1; List.nth(argregs, !num))
    end

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
