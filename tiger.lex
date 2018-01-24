<<<<<<< HEAD
type pos = int
type lexresult = Tokens.token
val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
val commentDepth = 0
fun err(p1,p2) = ErrorMsg.error p1
val parsedString = ""

fun eof() = let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end

%% 
  digits=[0-9]+;
  letter=[a-zA-Z];
  character=[a-zA-Z0-9_];
  asciiNum=0[0-9][0-9]|10[0-9]|11[0-9]|12[0-7];
  escape=\\[n|t|\^[A-Za-z]|\"|\\|[\t\n ]*|{asciiNum}];
  string=\"([^\\\"]|escape)*\";
%%
<INITIAL>type => (Tokens.TYPE(yypos,yypos + 4));
<INITIAL>var => (Tokens.VAR(yypos,yypos + 3 ));
<INITIAL>function => (Tokens.FUNCTION(yypos,yypos + 8));
<INITIAL>break => (Tokens.BREAK(yypos,yypos + 5));
<INITIAL>of => (Tokens.OF(yypos,yypos + 2));
<INITIAL>end => (Tokens.END(yypos,yypos + 3));
<INITIAL>in => (Tokens.IN(yypos,yypos + 2 ));
<INITIAL>nil => (Tokens.NIL(yypos,yypos + 3 ));
<INITIAL>let => (Tokens.LET(yypos,yypos + 3 ));
<INITIAL>do => (Tokens.DO(yypos,yypos + 2 ));
<INITIAL>to => (Tokens.TO(yypos,yypos + 2 ));
<INITIAL>for => (Tokens.FOR(yypos,yypos + 3 ));
<INITIAL>while => (Tokens.WHILE(yypos,yypos + 5 ));
<INITIAL>else => (Tokens.ELSE(yypos,yypos + 4 ));
<INITIAL>then => (Tokens.THEN(yypos,yypos + 4 ));
<INITIAL>if => (Tokens.IF(yypos,yypos + 2 ));
<INITIAL>array => (Tokens.ARRAY(yypos,yypos + 5 ));
<INITIAL>{string} => (Tokens.STRING(yytext, yypos,yypos + size yytext));
<INITIAL>({letter}{character}*) => (Tokens.ID(yytext, yypos, yypos + size yytext));
<INITIAL>":=" => (Tokens.ASSIGN(yypos,yypos + 2 ));
<INITIAL>"|" => (Tokens.OR(yypos,yypos + 1 ));
<INITIAL>"&" => (Tokens.AND(yypos,yypos + 1 ));
<INITIAL>">=" => (Tokens.GE(yypos,yypos + 2 ));
<INITIAL>">" => (Tokens.GT(yypos,yypos + 1 ));
<INITIAL>"<=" => (Tokens.LE(yypos,yypos + 2 ));
<INITIAL>"<" => (Tokens.LT(yypos,yypos + 1 ));
<INITIAL>"<>" => (Tokens.NEQ(yypos,yypos + 2 ));
<INITIAL>"=" => (Tokens.EQ(yypos,yypos + 1 ));
<INITIAL>"/" => (Tokens.DIVIDE(yypos,yypos + 1 ));
<INITIAL>"*" => (Tokens.TIMES(yypos,yypos + 1 ));
<INITIAL>"-" => (Tokens.MINUS(yypos,yypos + 1 ));
<INITIAL>"+" => (Tokens.PLUS(yypos,yypos + 1 ));
<INITIAL>"." => (Tokens.DOT(yypos,yypos + 2 ));
<INITIAL>"}" => (Tokens.RBRACE(yypos,yypos + 1 ));
<INITIAL>"{" => (Tokens.LBRACE(yypos,yypos + 1 ));
<INITIAL>"]" => (Tokens.RBRACK(yypos,yypos + 1 ));
<INITIAL>"]" => (Tokens.LBRACK(yypos,yypos + 1 ));
<INITIAL>")" => (Tokens.RPAREN(yypos,yypos + 1 ));
<INITIAL>"(" => (Tokens.LPAREN(yypos,yypos + 1 ));
<INITIAL>";" => (Tokens.SEMICOLON(yypos,yypos + 1 ));
<INITIAL>":" => (Tokens.COLON(yypos,yypos + 1 ));
<INITIAL>"," => (Tokens.COMMA(yypos,yypos + 1 ));
<INITIAL>{digits} => (Tokens.INT(valOf(Int.fromString(yytext)), yypos,yypos + size yytext ));
<INITIAL>"$" => (Tokens.COMMA(yypos,yypos + 1 ));
<INITIAL>\n => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL>" " => (continue());
<INITIAL>\$  => (continue());
<INITIAL>\t  => (continue());
<INITIAL>\b  => (continue());
<INITIAL>. => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());
=======
type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
val commentDepth = ref 0

fun err(p1,p2) = ErrorMsg.error p1
fun eof() = let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end

%%
%s COMMENT;
digit=[0-9];
letter=[a-zA-Z];
character=[a-zA-Z0-9_];
asciiNum=0[0-9][0-9]|10[0-9]|11[0-9]|12[0-7];
escape=\\[n|t|\^[A-Za-z]|\"|\\|[\t\n ]*|{asciiNum}];
string=\"([^\\\"]|escape)*\";
%%

<INITIAL>"type"     => (Tokens.TYPE(yypos, yypos + 4));
<INITIAL>"var"      => (Tokens.VAR(yypos, yypos + 3 ));
<INITIAL>"function" => (Tokens.FUNCTION(yypos, yypos + 8));
<INITIAL>"break"    => (Tokens.BREAK(yypos, yypos + 5));
<INITIAL>"of"       => (Tokens.OF(yypos, yypos + 2));
<INITIAL>"end"      => (Tokens.END(yypos, yypos + 3));
<INITIAL>"in"       => (Tokens.IN(yypos, yypos + 2 ));
<INITIAL>"nil"      => (Tokens.NIL(yypos, yypos + 3 ));
<INITIAL>"let"      => (Tokens.LET(yypos, yypos + 3 ));
<INITIAL>"do"       => (Tokens.DO(yypos, yypos + 2 ));
<INITIAL>"to"       => (Tokens.TO(yypos, yypos + 2 ));
<INITIAL>"for"      => (Tokens.FOR(yypos, yypos + 3 ));
<INITIAL>"while"    => (Tokens.WHILE(yypos, yypos + 5 ));
<INITIAL>"else"     => (Tokens.ELSE(yypos, yypos + 4 ));
<INITIAL>"then"     => (Tokens.THEN(yypos, yypos + 4 ));
<INITIAL>"if"       => (Tokens.IF(yypos, yypos + 2 ));
<INITIAL>"array"    => (Tokens.ARRAY(yypos, yypos + 5 ));

<INITIAL>":=" => (Tokens.ASSIGN(yypos, yypos + 2));
<INITIAL>"|"  => (Tokens.OR(yypos, yypos + 1));
<INITIAL>"&"  => (Tokens.AND(yypos, yypos + 1));
<INITIAL>">=" => (Tokens.GE(yypos, yypos + 2));
<INITIAL>">"  => (Tokens.GT(yypos, yypos + 1));
<INITIAL>"<=" => (Tokens.LE(yypos, yypos + 2));
<INITIAL>"<"  => (Tokens.LT(yypos, yypos + 1));
<INITIAL>"<>" => (Tokens.NEQ(yypos, yypos + 2));
<INITIAL>"="  => (Tokens.EQ(yypos, yypos + 1));
<INITIAL>"/"  => (Tokens.DIVIDE(yypos, yypos + 1));
<INITIAL>"*"  => (Tokens.TIMES(yypos, yypos + 1));
<INITIAL>"-"  => (Tokens.MINUS(yypos, yypos + 1));
<INITIAL>"+"  => (Tokens.PLUS(yypos, yypos + 1));
<INITIAL>"."  => (Tokens.DOT(yypos, yypos + 2));
<INITIAL>"}"  => (Tokens.RBRACE(yypos, yypos + 1));
<INITIAL>"{"  => (Tokens.LBRACE(yypos, yypos + 1));
<INITIAL>"]"  => (Tokens.RBRACK(yypos, yypos + 1));
<INITIAL>"["  => (Tokens.LBRACK(yypos, yypos + 1));
<INITIAL>")"  => (Tokens.RPAREN(yypos, yypos + 1));
<INITIAL>"("  => (Tokens.LPAREN(yypos, yypos + 1));
<INITIAL>";"  => (Tokens.SEMICOLON(yypos,yypos + 1));
<INITIAL>":"  => (Tokens.COLON(yypos,yypos + 1));
<INITIAL>","  => (Tokens.COMMA(yypos,yypos + 1));

<INITIAL>{string}             => (Tokens.STRING(yytext, yypos, yypos + size(yytext)));
<INITIAL>{digit}+             => (Tokens.INT(valOf(Int.fromString(yytext)), yypos, yypos + size(yytext)));
<INITIAL>{letter}{character}* => (Tokens.ID(yytext, yypos, yypos + size(yytext)));

<INITIAL>" " => (continue());
<INITIAL>\$  => (continue());
<INITIAL>\t  => (continue());
<INITIAL>\b  => (continue());

<INITIAL> . => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());

<INITIAL>"/*" => (YYBEGIN COMMENT; commentDepth := !commentDepth + 1; continue());
<COMMENT>"/*" => (commentDepth := !commentDepth + 1; continue());
<COMMENT>"*/" => (commentDepth := !commentDepth - 1;
                  (if !commentDepth = 0
                   then YYBEGIN INITIAL
                   else ());
                  continue());
<COMMENT> .   => (continue());

\n   => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
>>>>>>> 534af20a82579636a040960239b4123230a4df25
