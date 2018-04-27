structure MipsGen : CODEGEN =
struct

structure F = MipsFrame
structure T = Tree
structure A = Assem

(* codegen: M.frame * T.stm -> A.instr list *)
fun codegen(frame, stm) =
    let val ilist = ref (nil: A.instr list)
        fun emit(x) = ilist :=  x :: !ilist
        fun result(gen) = let val t = Temp.newtemp() in gen(t); t end

        (* one-liners for assembly string conversion *)
        fun int(i) = Int.toString(i) (* TODO: negatives? *)
        fun sym(s) = Symbol.name(s)

        (* munchStm: T.stm -> unit *)
        fun munchStm(T.SEQ(a, b)) = (munchStm(a); munchStm(b))
          | munchStm(T.EXP(e)) = (munchExp(e); ())
          | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST(i))), e2)) =
            emit(A.OPER{assem= "sw `s0, " ^ int(i) ^ "(`s1)\n",
                        src=[munchExp(e2), munchExp(e1)],
                        dst=[],
                        jump=NONE})
          | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST(i), e1)), e2)) =
            emit(A.OPER{assem= "sw `s0, " ^ int(i) ^ "(`s1)\n",
                        src=[munchExp(e2), munchExp(e1)],
                        dst=[],
                        jump=NONE})
          | munchStm(T.MOVE(T.MEM(T.BINOP(T.MINUS, e1, T.CONST(i))), e2)) =
            emit(A.OPER{assem= "sw `s0, " ^ int(~i) ^ "(`s1)\n",
                        src=[munchExp(e2), munchExp(e1)],
                        dst=[],
                        jump=NONE})
          | munchStm(T.MOVE(T.MEM(T.BINOP(T.MINUS, T.CONST(i), e1)), e2)) =
            emit(A.OPER{assem= "sw `s0, " ^ int(~i) ^ "(`s1)\n",
                        src=[munchExp(e2), munchExp(e1)],
                        dst=[],
                        jump=NONE})
          (* may be able to optimize this with an A.MOVE *)
          | munchStm(T.MOVE(T.MEM(e1), T.MEM(e2))) =
            emit(A.OPER{assem= "sw `s0, `s1\n",
                        src=[munchExp(e1), munchExp(e2)],
                        dst=[],
                        jump=NONE})
          | munchStm(T.MOVE(T.MEM(T.CONST(i)), e2)) =
            emit(A.OPER{assem= "sw `s0, " ^ int(i) ^ "(0)\n",
                        src=[munchExp(e2)],
                        dst=[],
                        jump=NONE})
          | munchStm(T.MOVE(T.MEM(e1), e2)) =
            emit(A.OPER{assem= "sw `s0, 0(`s1)\n",
                        src=[munchExp(e1), munchExp(e2)],
                        dst=[],
                        jump=NONE})
          | munchStm(T.MOVE(T.TEMP(e1), T.TEMP(e2))) =
            emit(A.MOVE{assem= "move `d0, `s0\n",
                        src=e2,
                        dst=e1})
          | munchStm(T.MOVE(T.TEMP(i), e2)) =
            emit(A.OPER{assem= "move `d0, `s0\n",
                        src=[munchExp(e2)],
                        dst=[i],
                        jump=NONE})
          | munchStm(T.LABEL(lab)) =
            emit(A.LABEL{assem= sym(lab) ^ ":\n",
                         lab= lab})
          (* such as the jump performed in a break *)
          (* TODO: could also be an unconditional branch? since the label is
             literal and not contained in a register, idk*)
          | munchStm(T.JUMP(T.NAME l1, _)) =
            emit(A.OPER{assem= "j `j0\n",
                        src=[],
                        dst=[],
                        jump=SOME([l1])})
          | munchStm(T.JUMP(e1, labels)) =
            emit(A.OPER{assem= "jr `s0\n",
                        src=[munchExp(e1)],
                        dst=[],
                        jump=SOME(labels)})
          (* conditionals: if <CONDITION> branch l1, else fall through and branch to l2 *)
          | munchStm(T.CJUMP(T.EQ, e1, e2, l1, l2)) =
            emit(A.OPER{assem= "beq `s0, `s1, `j0\nb `j1\n",
                        src=[munchExp(e1), munchExp(e2)],
                        dst=[],
                        jump=SOME([l1, l2])})
          | munchStm(T.CJUMP(T.NE, e1, e2, l1, l2)) =
            emit(A.OPER{assem= "bne `s0, `s1, `j0\nb `j1\n",
                        src=[munchExp(e1), munchExp(e2)],
                        dst=[],
                        jump=SOME([l1, l2])})
          | munchStm(T.CJUMP(T.LT, e1, e2, l1, l2)) =
            emit(A.OPER{assem= "blt `s0, `s1, `j0\nb `j1\n",
                        src=[munchExp(e1), munchExp(e2)],
                        dst=[],
                        jump=SOME([l1, l2])})
          | munchStm(T.CJUMP(T.GT, e1, e2, l1, l2)) =
            emit(A.OPER{assem= "bgt `s0, `s1, `j0\nb `j1\n",
                        src=[munchExp(e1), munchExp(e2)],
                        dst=[],
                        jump=SOME([l1, l2])})
          | munchStm(T.CJUMP(T.LE, e1, e2, l1, l2)) =
            emit(A.OPER{assem= "ble `s0, `s1, `j0\nb `j1\n",
                        src=[munchExp(e1), munchExp(e2)],
                        dst=[],
                        jump=SOME([l1, l2])})
          | munchStm(T.CJUMP(T.GE, e1, e2, l1, l2)) =
            emit(A.OPER{assem= "bge `s0, `s1, `j0\nb `j1\n",
                        src=[munchExp(e1), munchExp(e2)],
                        dst=[],
                        jump=SOME([l1, l2])})


        (* munchExp: T.exp -> Temp.temp *)
        and munchExp(T.ESEQ(s1, e1)) = (munchStm(s1); munchExp(e1))
         |  munchExp(T.MEM(T.BINOP(T.PLUS, e1, T.CONST(i)))) =
            result(fn(r) =>
                      emit(A.OPER{assem= "lw `d0, " ^ int(i) ^ "(`s0)\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp (T.MEM(T.BINOP(T.PLUS, T.CONST(i), e1))) =
            result(fn(r) =>
                      emit(A.OPER{assem= "lw `d0, " ^ int(i) ^ "(`s0)\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.MEM(T.BINOP(T.MINUS, e1, T.CONST(i)))) =
            result(fn(r) =>
                      emit(A.OPER{assem= "lw `d0, " ^ int(i) ^ "(`s0)\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp (T.MEM(T.BINOP(T.MINUS, T.CONST(i), e1))) =
            result(fn(r) =>
                      emit(A.OPER{assem= "lw `d0, " ^ int(i) ^ "(`s0)\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.MEM(T.CONST(i))) =
            result(fn(r) =>
                      emit(A.OPER{assem= "lw `d0, " ^ int(i) ^ "(0)\n",
                                  src=[],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.MEM(e1)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "lw `d0, 0(`s0)\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.PLUS, e1, T.CONST(i))) =
            result(fn(r) =>
                      emit(A.OPER{assem= "addiu `d0, `s0, " ^ int(i) ^ "\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.PLUS, T.CONST(i), e1)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "addiu `d0, `s0, " ^ int(i) ^ "\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.MINUS, e1, T.CONST(i))) =
            result(fn(r) =>
                      emit(A.OPER{assem= "addiu `d0, `s0, " ^ int(~i) ^ "\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.MINUS, T.CONST(i), e1)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "addiu `d0, `s0, " ^ int(~i) ^ "\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.CONST(i)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "addiu `d0, $0, " ^ int(i) ^ "\n",
                                  src=[],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.PLUS, e1, e2)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "addu `d0, `s0, `s1\n",
                                  src=[munchExp(e1), munchExp(e2)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.MINUS, e1, e2)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "subu `d0, `s0, `s1\n",
                                  src=[munchExp(e1), munchExp(e2)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.MUL, e1, e2)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "multu `d0, `s0, `s1\n",
                                  src=[munchExp(e1), munchExp(e2)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.DIV, e1, e2)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "divu `d0, `s0, `s1\n",
                                  src=[munchExp(e1), munchExp(e2)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.AND, e1, T.CONST(i))) =
            result(fn(r) =>
                      emit(A.OPER{assem= "andi `d0, `s0, " ^ int(i) ^ "\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.AND, T.CONST(i), e1)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "andi `d0, `s0, " ^ int(i) ^ "\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.AND, e1, e2)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "and `d0, `s0, `s1\n",
                                  src=[munchExp(e1), munchExp(e2)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.OR, e1, T.CONST(i))) =
            result(fn(r) =>
                      emit(A.OPER{assem= "ori `d0, `s0, " ^ int(i) ^ "\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.OR, T.CONST(i), e1)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "ori `d0, `s0, " ^ int(i) ^ "\n",
                                  src=[munchExp(e1)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.BINOP(T.OR, e1, e2)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "or `d0, `s0, `s1\n",
                                  src=[munchExp(e1), munchExp(e2)],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.TEMP(t)) = t
          | munchExp(T.NAME(l1)) =
            result(fn(r) =>
                      emit(A.OPER{assem= "la `d0, " ^ sym(l1) ^ "\n",
                                  src=[],
                                  dst=[r],
                                  jump=NONE}))
          | munchExp(T.CALL(T.NAME f, args)) =
            result(fn(r) =>
                      if (List.length(args) > 4)
                      then
                        raise Fail "too many function args"
                      else
                        let
                          val getter = F.argGetter()
                        in
                          (map(fn(arg) => 
                             munchStm(T.MOVE(T.TEMP(getter()),arg)))
                             (args);
                           emit(A.OPER{assem= "jal " ^ sym f ^ "\n",
                                       src=[],
                                       dst=[],
                                       jump=NONE}))
                        end)

    in munchStm(stm);
       rev(!ilist)
    end
end
