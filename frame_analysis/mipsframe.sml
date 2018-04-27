structure MipsFrame : FRAME =
struct
  structure T = Tree
  val wordSize = 8

  type register = string

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

  val FP = R30
  val RV = R2

  val specialregs = [R0, R2, R3, R26, R27, R28, R29, R30, R31]
  val argregs =     [R4, R5, R6, R7]
  val callersaves = [R8, R9, R10, R11, R12, R13, R14, R15, R24, R25]
  val calleesaves = [R16, R17, R18, R19, R20, R21, R22, R23]

  (* InFrame indicates things that are in the frame at offset int from the stack
   * pointer.  InReg are register locations (which are copied onto the stack for
   * nonleaf operations *)
  datatype access = InFrame of int | InReg of Temp.temp

  type frame = {
    formals : access list,
    shift   : T.stm list,
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

  (* creates accesses for all the arguments. All escaped arguments are passed in
   * reverse order on the stack, and nonescaped arguments are passed in
   * registers.*)
  fun allocArgs(escs) =
    let
      val escArgs = ref 1
      fun allocArg(esc) =
        if esc
        then (escArgs := !escArgs - 1; InFrame(!escArgs))
        else InReg(Temp.newtemp())
    in
      map(allocArg)(escs)
    end

  fun newFrame({name, formals}) =
    let
      val stacksize = 8
    in
      {
        (* will need to copy the stack pointer to the frame pointer, the move the
         * stack pointer to the end I'm pretty sure this will need to be in MIPS
         * instructions.
         *
         * I'm guessing alloclocal will get called here somewhere.  If the
         * argument is escaped.
         * *)
        formals=allocArgs(formals),
        (* TODO: things in shift:
         * 1. the old stack pointer becomes the current frame pointer.
         * 2. the callee saves registers are copied to the stack frame*)
        shift=[
          (* we save the old frame pointer to a location just beyond the number
           * of local variables.*)
          T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP R29, T.CONST stacksize)),T.TEMP FP),
          (* we copy the old stack pointer to the frame pointer*)
          T.MOVE(T.TEMP FP, T.TEMP R29),
          (* we make a new stack pointer subtracting the frame size from the old
           * stack pointer*)
          T.MOVE(T.TEMP R29, T.BINOP(T.PLUS, T.CONST stacksize, T.TEMP R29)),

          (* saving all of the callee saves registers *)
          (* TODO: clean this up *)
          T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP R29, T.CONST(stacksize + 1))),T.TEMP 16),
          T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP R29, T.CONST(stacksize + 2))),T.TEMP 17),
          T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP R29, T.CONST(stacksize + 3))),T.TEMP 18),
          T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP R29, T.CONST(stacksize + 4))),T.TEMP 19),
          T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP R29, T.CONST(stacksize + 5))),T.TEMP 20),
          T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP R29, T.CONST(stacksize + 6))),T.TEMP 21),
          T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP R29, T.CONST(stacksize + 7))),T.TEMP 22),
          T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP R29, T.CONST(stacksize + 8))),T.TEMP 23)
        ],
        (* TODO: things after function exits:
         * 1. the old frame pointer is copied back from memory
         * 2. the callee saves registers are copied from the stack frame*)
         (*
        shiftBack=[]
          *)
        numlocals=ref 0,
        location=Temp.newlabel()
      }
    end

  fun name({formals, shift, numlocals, location}) = location

  (* the list of where the formals for this call will be kept at run time *)
  fun formals({formals, shift, numlocals, location}) = formals

  fun allocLocal({formals, shift, numlocals, location}) =
     fn esc =>
       if esc
       then (numlocals := !numlocals + 1; InFrame(!numlocals))
       else InReg(Temp.newtemp())

  fun exp(acc)=
    fn fp =>
    case acc
      of (InFrame i) => T.MEM(T.BINOP(T.PLUS, fp, T.CONST i))
       | (InReg t) => T.TEMP t

  fun externalCall(s, args) =
      T.CALL(T.NAME(Temp.namedlabel s), args)

  (* re-define this helper so we don't introduce a cyclic-dependency requiring translate *)
  fun seq(x::[]) = x
    | seq(x::rest) = T.SEQ(x, seq(rest))
    | seq([]) = T.EXP(T.CONST 0)

  (* 1. move all incoming arguements to the frame for escaping parameters, or a
        fresh temporary
     2. save all spilled vars.*)
  fun procEntryExit1(frame, body) =
      let
          val {formals, shift, numlocals, location} = frame
          val calleeSaveLocals = map (fn (cs) => allocLocal(frame)(false)) calleesaves
          fun moveCalleeSaves(temp::temps, loc::locals, genMove) =
              genMove(temp, loc)::moveCalleeSaves(temps, locals, genMove)
            | moveCalleeSaves([], [], _) = []
            (* we really shouldn't hit either of these conditions in practice *)
            | moveCalleeSaves([], _, _) = raise Fail "mismatched lists"
            | moveCalleeSaves(_, [], _) = raise Fail "mismatched lists"
          (* write calleesaves to local stack *)
          val localSaves = moveCalleeSaves(calleesaves, calleeSaveLocals,
                                           (fn(cs, csl) => T.MOVE(exp csl (T.TEMP FP), T.TEMP cs)))
          (* restore calleesaves from local stack *)
          val localRestores = moveCalleeSaves(calleesaves, calleeSaveLocals,
                                              fn(cs, csl) => T.MOVE(T.TEMP cs, exp csl (T.TEMP FP)))
      in
          (* 1. move incoming arguments 2. move calleesaves 3. body 4. restore caleesaves *)
          seq(shift @ localSaves @ [body] @ localRestores)
      end

  fun procEntryExit2(frame, instrs) =
      instrs @
      [Assem.OPER{assem="",
              src=specialregs @ calleesaves,
              dst=[], jump=SOME([])}]

  (* 1. Calculate the size of the outgoing parameter space in the frame
     2. Generate the prologue and epilogue for procedure entry, sp adjustment, and exit *)
  fun procEntryExit3({formals, shift, numlocals, location}, instrs) =
      let
          (* maximum legal value = our max #args + max #args of a child proc + #numlocals *)
          val outSpace = ((2 * List.length(argregs)) + !numlocals) * wordSize
          (* 0(sp) := fp, fp := sp, sp++  *)
          val prologue = String.concat([Symbol.name(location), ":\n",
                                        "sw $fp, 0($sp)\n",
                                        "move $fp, $sp\n",
                                        "addiu $sp, $sp, ", Int.toString(outSpace), "\n"])
          (* sp := fp, fp := 0(sp), return *)
          val epilogue = String.concat(["move $sp, $fp\n",
                                        "lw $fp, 0($sp)\n",
                                        "jr $ra\n"])
      in
          {prolog= prologue, body= instrs, epilog= epilogue}
      end

end
