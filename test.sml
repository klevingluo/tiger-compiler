CM.make("sources.cm");
use "tokens.sig";
use "tokens.sml";
use "errormsg.sml";
use "tiger.lex.sml";
use "driver.sml";
Parse.parse("test.tig");
OS.Process.exit(OS.Process.success);
