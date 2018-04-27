CM.make("sources.cm");
let
  val outstream = TextIO.openOut "compiled.mips"

  fun emitAssem(frag) =
    case frag of 
         MipsFrame.PROC{body, frame} => 
           app(fn x => print(Assem.format(Temp.makestring)(x)))
              (MipsGen.codegen(frame, body))
       | MipsFrame.STRING(lab, str) => print(MipsFrame.string(lab, str))

  fun writeFrag(frag) =
    case frag of 
         MipsFrame.PROC{body, frame} => 
           let 
             val (program, allocation) = 
               RegAlloc.alloc((MipsGen.codegen(frame, body)),frame);
             fun allocate(tmp) =
               case Temp.Table.look(allocation, tmp) of
                    SOME(x) => x
                  | NONE => raise Fail ("No allocation found for " ^ Temp.makestring(tmp))
             fun notRegMove(instr) =
               case instr of 
                    Assem.MOVE{assem, dst, src} =>  not (allocate(dst) = allocate(src))
                  | _ => true
             (* remove register to same register moves *)
             val program = List.filter(notRegMove)(program)
             val {prolog, body, epilog} = MipsFrame.procEntryExit3(frame, program)
             val programString = prolog ^ 
                                 foldl(fn (instr, acc) =>
                                     Assem.format(allocate)(instr) ^ acc)("")(body) ^
                                 epilog
           in
             TextIO.output(outstream, (programString))
           end
       | MipsFrame.STRING(lab, str) => (print("string frag"))

  fun writeFile filename content =
    let 
      val fd = TextIO.openOut filename
      val _ = TextIO.output (fd, content) handle e => (TextIO.closeOut fd; raise e)
      val _ = TextIO.closeOut fd
    in ()
    end

in
  let
    val absyn = Parse.parse("testcases/fib.tig")
    val frags = Semant.transProg(absyn)
  in
    (
     (*
      PrintAbsyn.print(TextIO.stdOut, absyn);
      *)
     map(writeFrag)(frags))
  end;
  OS.Process.exit(OS.Process.success)
end;

