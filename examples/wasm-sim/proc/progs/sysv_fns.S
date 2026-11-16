# Hand-written System V test functions (good and deliberately bad).
        .text
        .globl add2, entry_rsp, bad_rbx, bad_rsp, bad_r12, sum8_asm
add2:   lea     (%rdi,%rsi), %rax       # a + b
        ret
entry_rsp:                              # rsp mod 16 at entry (AbiEntry: 8)
        mov     %rsp, %rax
        and     $15, %eax
        ret
sum8_asm:                               # a+..+f + two stack arguments
        lea     (%rdi,%rsi), %rax
        add     %rdx, %rax
        add     %rcx, %rax
        add     %r8, %rax
        add     %r9, %rax
        add     8(%rsp), %rax
        add     16(%rsp), %rax
        ret
bad_rbx:                                # clobbers callee-saved rbx
        mov     %rdi, %rbx
        mov     %rdi, %rax
        ret
bad_r12:                                # clobbers callee-saved r12
        lea     1(%r12), %r12
        ret
bad_rsp:                                # returns with rsp = entry rsp (not + 8)
        pop     %rcx
        push    %rcx
        push    %rcx
        ret
        .section .note.GNU-stack,"",@progbits
