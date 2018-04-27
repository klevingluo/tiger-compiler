CM.make("sources.cm");
let
  fun emitAssem(frag) =
    case frag of 
         MipsFrame.PROC{body, frame} => 
           (* MakeGraph.instrs2graph(MipsGen.codegen(frame, body)) *)
           app(fn x => print(Assem.format(Temp.makestring)(x)))
              (MipsGen.codegen(frame, body))
       | MipsFrame.STRING(lab, str) => (print("string frag"))

  fun test(frag) =
    case frag of 
         MipsFrame.PROC{body, frame} => 
           (* MakeGraph.instrs2graph(MipsGen.codegen(frame, body)) *)
           let 
             val (program, allocation) = 
               RegAlloc.alloc((MipsGen.codegen(frame, body)),frame);
             fun allocate(tmp) =
               case Temp.Table.look(allocation, tmp) of
                    SOME(x) => x
                  | NONE => raise Fail ("No allocation found for " ^ Temp.makestring(tmp))
           in
             (app(fn x => print(Assem.format(Temp.makestring)(x)))
              (program);
             app(fn x => print(Assem.format(allocate)(x)))
                (program))
           end
       | MipsFrame.STRING(lab, str) => (print("string frag"))

in
  let
    val absyn = Parse.parse("testcases/fib.tig")
    val frags = Semant.transProg(absyn)
  in
    (
     (*
      PrintAbsyn.print(TextIO.stdOut, absyn);
      *)
     map(emitAssem)(frags);
     map(test)(frags))
  end;
  OS.Process.exit(OS.Process.success)
end;

