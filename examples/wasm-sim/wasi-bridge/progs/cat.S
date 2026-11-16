# cat: copy stdin to stdout in 64-byte chunks with read/write; exit_group(0) at end of input.
        .globl _start
        .text
_start:
1:      xor     %eax, %eax              # read(0, buf, 64)
        xor     %edi, %edi
        lea     buf(%rip), %rsi
        mov     $64, %edx
        syscall
        test    %rax, %rax
        jle     2f
        mov     %rax, %rdx              # write(1, buf, n)
        mov     $1, %eax
        mov     $1, %edi
        lea     buf(%rip), %rsi
        syscall
        jmp     1b
2:      mov     $231, %eax
        xor     %edi, %edi
        syscall
        .bss
buf:    .space  64
        .section .note.GNU-stack,"",@progbits
