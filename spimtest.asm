# Author name: # Ben Bitdiddle
# Assignment number: Sample 0
# Date: 09-02-2003
# Program name: Largest of N numbers
# 
# SUMMARY 
#         This program finds the largest number in a given list of numbers.
# 
# INPUT 
#       The input to this program is a set of positive numbers entered by the
# user.
# 
# OUTPUT 
# The output is the largest number in the input set of numbers. 
# In the format 'the largest = (number)'
# 
# ASSUMPTIONS 
# The program assumes that only positive numbers are being entered.
# After entering each number the user must press <Enter>
#   To indicate that all the numbers have been entered the user should
# enter a number <= 0
# 

.data
prompt:
.asciiz "enter a number (0 to quit): "
display:
.asciiz "the largest = "
crlf:
.asciiz "\n"
.text
main:
li  $a1, 0    #reset the largest
loop:
li  $v0, 4    #syscall 4 to display string message
la  $a0, prompt #display the entry message
syscall

li  $v0, 5    #syscall 5 to read in a number
syscall

blez  $v0, break_loop #if number entered is 0 end
blt $v0, $a1, loop  #is no. entered greater than the largest we have
move  $a1, $v0  #if so replace largest

no_move:
j loop    #get more numbers

break_loop:
li  $v0, 4
la  $a0, display  #display message
syscall

li  $v0, 1    #syscall 1 for displaying numbers
move  $a0, $a1  #display largest number
syscall

li  $v0, 4
la  $a0, crlf #display \n some nice housekeeping
syscall
