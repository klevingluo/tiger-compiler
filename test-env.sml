CM.make("sources-env.cm");
val en = Env.base_env;
val intsym = Symbol.symbol("int");
val arrsym = Symbol.symbol("arrty");
Env.lookupTy(intsym, en);
Env.setTy(arrsym,Types.ARRAY(Types.INT,ref ()),en);
Env.lookupTy(arrsym, en);
OS.Process.exit(OS.Process.success);
