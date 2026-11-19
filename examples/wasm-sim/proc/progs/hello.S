# Static x86-64 hello world: write(1, msg, len); exit(0).
        .globl _start
        .text
_start:
        mov     $1, %eax                # SYS_write
        mov     $1, %edi                # fd 1
        lea     msg(%rip), %rsi
        mov     $len, %edx
        syscall
        mov     $60, %eax               # SYS_exit
        xor     %edi, %edi
        syscall
        .section .rodata
msg:    .ascii  "Hello, world!\n"
        len = . - msg
        .section .note.GNU-stack,"",@progbits
