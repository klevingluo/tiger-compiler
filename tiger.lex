type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos

val stringPos = ref (1, 1, 1)
val string = ref [""]

val commentPos = ref [(1, 1, 1)]

val state = ref "initial"

fun topLinePos() = let val (top :: _) = !linePos in top end
fun posTuple(pos) = let val (topLinePos :: _ ) = !linePos in (pos, !lineNum, topLinePos) end

fun err(p1,p2) = ErrorMsg.error p1
fun eof() =
    let
        val pos = hd(!linePos)
        val endState = !state
        val (strPos, strLineNum, strLinePos) = !stringPos
        val ((cmtPos, cmtLineNum, cmtLinePos) :: _) = !commentPos
    in
        (case endState of "string"  => ErrorMsg.error strPos ("unbalanced string " ^ Int.toString(strLineNum) ^ ":" ^ Int.toString(strPos - strLinePos))
                        | "comment" => ErrorMsg.error cmtPos ("unbalanced comment " ^ Int.toString(cmtLineNum) ^ ":" ^ Int.toString(cmtPos - cmtLinePos))
                        | _  => ());

        Tokens.EOF(pos, pos)
    end

datatype CharList = Nil | Cons of char * CharList;

val controlChars = String.explode("ABCDEFGHIJKLMNOPQRSTUVWXYZ[/]^_")

fun indexOf(chars, c) = let val (x::xs) = chars in if x = c then 0 else 1 + indexOf(xs, c) end
fun controlChar(esc) = String.str(Char.chr(indexOf(controlChars, String.sub(esc, 2))))
fun asciiChar(esc) = String.str(Char.chr(valOf(Int.fromString(String.substring(esc, 1, 3)))))

%%
%s STRING COMMENT;
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
<INITIAL>";"  => (Tokens.SEMICOLON(yypos, yypos + 1));
<INITIAL>":"  => (Tokens.COLON(yypos, yypos + 1));
<INITIAL>","  => (Tokens.COMMA(yypos, yypos + 1));

<INITIAL>{digit}+             => (Tokens.INT(valOf(Int.fromString(yytext)), yypos, yypos + size(yytext)));
<INITIAL>{letter}{character}* => (Tokens.ID(yytext, yypos, yypos + size(yytext)));
<INITIAL>\"                   => (YYBEGIN STRING; state := "string"; stringPos := posTuple(yypos); string := [""]; continue());
<STRING>\\n                   => (string := "\n" :: !string; continue());
<STRING>\\t                   => (string := "\t" :: !string; continue());
<STRING>\\\^{controlChar}     => (string := controlChar(yytext):: !string; continue());
<STRING>\\{asciiNum}          => (string := asciiChar(yytext):: !string; continue());
<STRING>\\\\                  => (string := "\\" :: !string; continue());
<STRING>\\[\t\n ]+            => (continue());
<STRING>\\.                   => (ErrorMsg.error yypos ("illegal escape character " ^ yytext); continue());
<STRING>[^\\\"]               => (string := yytext :: !string; continue());
<STRING>\"                    => (YYBEGIN INITIAL; state := "initial"; Tokens.STRING(List.foldl((op ^))("")(!string), (let val pos = !stringPos in #1(pos) end), yypos + 1));

<INITIAL>" "       => (continue());
<INITIAL>[\$\t\b]  => (continue());

<INITIAL> . => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());

<INITIAL>"/*" => (YYBEGIN COMMENT; state := "comment"; commentPos := posTuple(yypos) :: !commentPos ; continue());
<COMMENT>"/*" => (commentPos := posTuple(yypos) :: !commentPos; continue());
<COMMENT> .   => (continue());
<COMMENT>"*/" => (let
                     val (_ :: commentPos') = !commentPos
                  in
                     commentPos := commentPos';
                     if (length commentPos') = 1 then (YYBEGIN INITIAL; state := "initial") else ();
                     continue()
                  end);

\n   => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
