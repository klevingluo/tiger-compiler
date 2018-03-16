# this is a test mips program, I don't know what it will be but I will try to
# keep from being too ambitious
# spimsample.asm

         .data # nothing here
var1:    .word 23
var2:    .space 23

         .text # instrucions starting

main:     # indicates start of code (first instruction to execute)

li $t2, 1
li $v0, 1
move $a0, $t2
syscall

# End of program, leave a blank line afterwards for SPIM

