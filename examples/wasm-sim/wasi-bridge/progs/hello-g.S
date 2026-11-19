# hello in the proved x86 G fragment (64-bit movs only) + syscall:
#   mov rax,1; mov rdi,1; movabs rsi,msg; mov rdx,14; syscall; mov rax,60; mov rdi,0; syscall
# The message is at the fixed address 0x402000 (linked with -Ttext=0x401000 -Tdata=0x402000).
        .globl _start
        .text
_start:
        movq    $1, %rax
        movq    $1, %rdi
        movabsq $msg, %rsi
        movq    $14, %rdx
        syscall
        movq    $60, %rax
        movq    $0, %rdi
        syscall
        .data
msg:    .ascii  "Hello, world!\n"
        .section .note.GNU-stack,"",@progbits
