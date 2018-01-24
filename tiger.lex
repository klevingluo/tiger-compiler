type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
val commentDepth = ref 0
val string = ref [""]

fun err(p1,p2) = ErrorMsg.error p1
fun eof() = let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end

val controlChars = String.explode("ABCDEFGHIJKLMNOPQRSTUVWXYZ[/]^_")
fun indexOf(x1::xs, char) = if x1 = char then 0 else 1 + indexOf(xs, char)
fun controlChar(esc) = String.str(Char.chr(indexOf(controlChars, String.sub(esc, 2))))
fun asciiChar(esc) = String.str(Char.chr(valOf(Int.fromString(String.substring(esc,1,3)))));

%%
%s COMMENT;
%s STRING;
digit=[0-9];
letter=[a-zA-Z];
character=[a-zA-Z0-9_];
asciiNum=0[0-9][0-9]|10[0-9]|11[0-9]|12[0-7];
controlChar=[A-Z]|\[|\]|\^|\/|_;

escape=\\(n|t|\^[A-Za-z]|\"|\\|[\t\n ]+|{asciiNum});
string=\"([^\\\"]|{escape})*\";
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

<INITIAL>{digit}+             => (Tokens.INT(valOf(Int.fromString(yytext)), yypos, yypos + size(yytext)));
<INITIAL>{letter}{character}* => (Tokens.ID(yytext, yypos, yypos + size(yytext)));
<INITIAL>\"                   => (YYBEGIN STRING; string= ref[""]; continue());
<STRING>\\n                   => (string := "\n":: !string; continue());
<STRING>\\t                   => (string := "\t":: !string; continue());
<STRING>\\\^{controlChar}     => (string := controlChar(yytext):: !string; continue());
<STRING>\\{asciiNum}          => (string := asciiChar(yytext):: !string; continue());
<STRING>\\\\                  => (string := "\\":: !string; continue());
<STRING>\\[\t\n ]+            => (continue());
<STRING>\\.                   => (ErrorMsg.error yypos ("illegal escape character " ^ yytext); continue());
<STRING>[^\\\"]               => (string := yytext:: !string; continue());
<STRING>\"                    => (YYBEGIN INITIAL; Tokens.STRING(List.foldl((op ^))("")(!string), yypos, yypos + 2));

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
