CM.make("sources.cm");
let
  fun emitAssem(frag) =
    case frag of 
         MipsFrame.PROC{body, frame} => 
           (* MakeGraph.instrs2graph(MipsGen.codegen(frame, body)) *)
           app(fn x => print(Assem.format(Temp.makestring)(x)))
              (MipsGen.codegen(frame, body))
       | MipsFrame.STRING(lab, str) => (print("string frag"))
in
  let
    val absyn = Parse.parse("testcases/fib.tig")
    val frags = Semant.transProg(absyn)
  in
    (
     PrintAbsyn.print(TextIO.stdOut, absyn);
     map(emitAssem)(frags))
  end;
  OS.Process.exit(OS.Process.success)
end;

