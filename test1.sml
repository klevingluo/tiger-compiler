CM.make("sources.cm");
let
  val absyn = Parse.parse("testcases/fib.tig")
in
  PrintAbsyn.print(TextIO.stdOut, absyn)
end;
OS.Process.exit(OS.Process.success);
