signature REG_ALLOC = 
sig
  type allocation = MipsFrame.register Temp.Table.table
  val alloc : Assem.instr list * MipsFrame.frame ->
                         Assem.instr list * allocation
end
