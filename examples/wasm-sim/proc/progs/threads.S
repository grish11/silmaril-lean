# Two threads (raw clone, shared memory): the parent prints "ping" 3 times, waits for the
# child's flag, then exit_group(7); the child prints "pong" 3 times, sets the flag and spins.
        .globl _start
        .text
_start:
        mov     $56, %eax                       # clone
        mov     $0x50f00, %edi                  # VM|FS|FILES|SIGHAND|THREAD|SYSVSEM
        lea     stack_top(%rip), %rsi
        xor     %edx, %edx
        xor     %r10d, %r10d
        xor     %r8d, %r8d
        syscall
        test    %rax, %rax
        jz      child
        lea     ping(%rip), %rbx
        call    say3
1:      cmpl    $0, flag(%rip)
        je      1b
        mov     $231, %eax
        mov     $7, %edi
        syscall
child:  lea     pong(%rip), %rbx
        call    say3
        movl    $1, flag(%rip)
2:      jmp     2b
say3:   mov     $3, %r12d
3:      mov     $1, %eax
        mov     $1, %edi
        mov     %rbx, %rsi
        mov     $5, %edx
        syscall
        dec     %r12d
        jnz     3b
        ret
        .section .rodata
ping:   .ascii  "ping\n"
pong:   .ascii  "pong\n"
        .bss
        .align  16
flag:   .long   0
        .align  16
        .space  4096
stack_top:
        .section .note.GNU-stack,"",@progbits
