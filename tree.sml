signature TREE = 
sig 
  type label = Temp.label
  type size

datatype stm = SEQ of stm * stm
             | LABEL of label
             | JUMP of exp * label list
             | CJUMP of relop * exp * exp * label * label
             | MOVE of exp * exp
             | EXP of exp

     and exp = BINOP of binop * exp * exp
             | MEM of exp
             | TEMP of Temp.temp
             | ESEQ of stm * exp
             | NAME of label
             | CONST of int
             | CALL of exp * exp list

     and binop = PLUS | MINUS | MUL | DIV 
               | AND | OR | LSHIFT | RSHIFT | ARSHIFT | XOR

     and relop = EQ | NE | LT | GT | LE | GE 
               | ULT | ULE | UGT | UGE

  val notRel : relop -> relop
  val commute: relop -> relop
end

structure Tree : TREE = 
struct
  type label=Temp.label
  type size = int

datatype stm = SEQ of stm * stm
             | LABEL of label
             | JUMP of exp * label list
             | CJUMP of relop * exp * exp * label * label
             (* evaluate 1st and move the value of 2nd into it. *)
             | MOVE of exp * exp
             | EXP of exp

      and exp = BINOP of binop * exp * exp
              | MEM of exp
              | TEMP of Temp.temp
              | ESEQ of stm * exp
              | NAME of label
              | CONST of int
              | CALL of exp * exp list

      and binop = PLUS | MINUS | MUL | DIV 
                | AND | OR | LSHIFT | RSHIFT | ARSHIFT | XOR

      and relop = EQ | NE | LT | GT | LE | GE 
                | ULT | ULE | UGT | UGE

  (* TODO: fix these, this is wrong *)
  fun notRel(EQ) = NE
    | notRel(NE) = EQ
    | notRel(LT) = GE 
    | notRel(GE) = LT
    | notRel(LE) = GT
    | notRel(GT) = LE 
    | notRel(ULT) = UGE 
    | notRel(UGE) = ULT
    | notRel(ULE) = UGT
    | notRel(UGT) = ULE 
  fun commute(id) = id
end

