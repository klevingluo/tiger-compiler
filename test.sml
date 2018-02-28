CM.make("sources.cm");

fun runTestCase(tc) =
  let 
    val er = ref 0
  in
    ((Parse.parse("testcases/test" ^ Int.toString(tc) ^ ".tig"); ())
    handle Error => er := 1;
    !er)
  end;

fun test(tc, stream) =
 if runTestCase(tc) > 0 
 then ()
 else (TextIO.output (stream, (Int.toString(tc) ^ "ok\n"));());

(*PrintAbsyn.print(TextIO.stdOut, Parse.parse("testcases/test" ^
 * Int.toString(tc) ^ ".tig")) handle Error => print "error handled";*)
let 
  val counter = ref 1
  val outstream = TextIO.openAppend "testresults/tests"
in
  while !counter < 49 do (test( (!counter), outstream);counter := !counter + 1)
end;

OS.Process.exit(OS.Process.success);
