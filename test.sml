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
 then TextIO.output (stream, ("error" ^ Int.toString(tc) ^ "\n"))
 else (TextIO.output (stream, (Int.toString(tc) ^ "ok\n"));());

(*PrintAbsyn.print(TextIO.stdOut, Parse.parse("testcases/test" ^
 * Int.toString(tc) ^ ".tig")) handle Error => print "error handled";*)

let 
  val results = ref [0,0,0,0,0,0,0,0,1,1,
                     1,0,1,1,1,1,1,1,1,1,
                     1,1,1,1,1,1,0,1,1,0,
                     1,1,1,1,1,1,0,1,1,1,
                     0,0,1,0,1,0,0,0,1]
  val counter = ref 1
  val outstream = TextIO.openAppend "testresults/tests"
in
  while 
    !counter < 50 
  do 
  if (runTestCase(!counter) <> (hd(!results)))
  then
    (print("failed test: " ^ Int.toString(!counter) ^ "\n");
     counter := !counter + 1;
     results := tl(!results))
  else 
    (counter := !counter + 1;
     results := tl(!results))
end;

OS.Process.exit(OS.Process.success);
