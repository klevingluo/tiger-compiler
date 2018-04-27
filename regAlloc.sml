signature REG_ALLOC = 
sig
  structure Frame : FRAME
  type allocation = Frame.register Temp.Table.table
  val alloc : Assem.instr list * Frame.frame ->
                         Assem.instr list * allocation
end

structure RegAlloc : REG_ALLOC =
struct
  structure Frame = MipsFrame
  structure T = Tree
  structure G = Graph
  structure S = RedBlackSetFn (struct
                      type ord_key = Temp.temp
                      fun compare(n1, n2) = 
                        String.compare(Temp.makestring(n1),Temp.makestring(n2))
                     end)

  type allocation = Frame.register Temp.Table.table

  fun alloc(program, frame) =
    let
      val program = ref program
      val allocation = Frame.tempMap
      fun rewriteProgram(spills): Assem.instr list = 
        let
          val newtemps = ref S.empty
          fun procSpill(tmp) =
            let
              val acc = Frame.allocLocal(frame)(true);
              val addr = case Frame.exp(acc)(T.TEMP(MipsFrame.FP)) of 
                              T.MEM(a) => a
                            | _ => raise Fail "spilled temp got assigned temp"
              fun contains(lis, tp) = 
                isSome(List.find(fn tmp2 => tmp = tmp2)(lis))
              fun subTemp(lis, a, b) : Assem.temp list =
                foldl(fn (tp, acc) => if tp = a then b::acc else tp::acc)([])(lis)
              fun foldfun(instr: Assem.instr, acc: Assem.instr list) = 
                let
                  val newtemp = Temp.newtemp()
                  fun sandwich(src, dst, instr) =
                    let 
                      val pre = if contains(src, tmp)
                                then (newtemps := S.add(!newtemps, newtemp);
                                      MipsGen.codegen(frame, T.MOVE(T.TEMP(newtemp), T.MEM(addr))))
                                else []
                      val post = if contains(dst, tmp)
                                then (newtemps := S.add(!newtemps, newtemp);
                                      MipsGen.codegen(frame, T.MOVE(T.MEM(addr),T.TEMP(newtemp))))
                                else []
                    in
                      (pre @ [instr] @ post)
                    end
                in
                  case instr of 
                       Assem.OPER{assem, dst, src , jump} =>
                         sandwich(src, 
                                  dst, 
                                  Assem.OPER{assem=assem, 
                                             src=(subTemp(src, tmp, newtemp)), 
                                             dst=(subTemp(dst, tmp, newtemp)),
                                             jump=jump})
                         @ acc
                     | Assem.MOVE{assem, dst, src} =>
                         if dst = tmp andalso src = tmp
                         then acc
                         else if dst = tmp
                         then instr ::
                            MipsGen.codegen(frame, T.MOVE(T.MEM(addr),T.TEMP(newtemp))) @
                            acc
                         else if src = tmp
                         then MipsGen.codegen(frame, T.MOVE(T.TEMP(newtemp), T.MEM(addr))) @
                            instr ::
                            acc
                         else instr :: acc
                     | _ => instr::acc
                end
            in
              program := foldl(foldfun)([])(!program)
            end
        in
          (app(procSpill)(spills);
           !program)
        end

      fun mainLoop() = 
        let
          val (igraph, liveFunc) = 
             Liveness.interferenceGraph((#1 (MakeGraph.instrs2graph(!program))))
          val (allocation, spills) = Color.color({
              interference = igraph,
              initial = allocation,
              spillCost = fn (node) => 1,
              node2live = liveFunc,
              registers = Frame.registers});
        in
           if not (List.null(spills))
           then (
             program := rewriteProgram(spills);
             Color.cleanSpills();
             mainLoop())
           else (!program, allocation)
        end
    in
      mainLoop()
    end

end
