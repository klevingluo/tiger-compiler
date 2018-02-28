CM.make("sources.cm");

PrintAbsyn.print(TextIO.openOut "test_results/2.txt", 
 Parse.parse("testcases/queens.tig"));
handle Error => print("error")

OS.Process.exit(OS.Process.success);
