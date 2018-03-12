structure MipsFrame : FRAME = 
struct 

  datatype access = InFrame of int | InReg of Temp.temp

  type frame = {
    locals : Temp.temp list, 
    return : Temp.label, 
    temps  : Temp.temp list,
    args   : access list
  }

  val newFrame : {name: Temp.label, formals: bool list} -> frame =
    {
      locals= []
    }
  val name : frame -> Temp.label
  val formals : frame -> access list
  val allocLocal : frame -> bool -> access
end

