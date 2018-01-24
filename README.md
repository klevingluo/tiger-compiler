# tiger-compiler
CS 4410 project: Tiger MIPS compiler

### how to build (lexer)

You need to generate the sml lexer as specified in 'tiger.lex'. The resulting
file will be named 'tiger.lex.sml', and can be loaded into an interactive
session and then used to tokenize tiger code.

To build the entire program including the lexer, as specified in 'sources.cm':
`- CM.make "sources.cm";`

### how to run (lexer)
Once having built the program, in that same interactive session invoke:
`- Parse.parse("<RELATIVE_PATH_TO_TIGER_SOURCE_FILE>");`

You should see the parser print all tokens from the tiger source file, as well
as any errors encountered in the process.
