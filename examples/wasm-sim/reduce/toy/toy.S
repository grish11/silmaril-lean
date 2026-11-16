# Toy for the reduction pipeline (docs/wasm-sim-reduction.md): a caller and two callees,
# one with a loop. System V AMD64.
#   sum_to(n)  = n + (n-1) + ... + 1   (mod 2^64; loop; as in the runtime simulator tests)
#   dbl(x)     = 2x                    (mod 2^64; straight line)
#   f(a, b)    = sum_to(a) + dbl(b)    (calls both; saves rbx, r12)
    .text
    .globl sum_to, dbl, f
    .type sum_to, @function
    .type dbl, @function
    .type f, @function
sum_to:
    xor %eax, %eax
    test %rdi, %rdi
    je 2f
1:
    add %rdi, %rax
    dec %rdi
    jne 1b
2:
    ret
    .size sum_to, . - sum_to
dbl:
    mov %rdi, %rax
    add %rax, %rax
    ret
    .size dbl, . - dbl
f:
    push %rbx
    push %r12
    sub $8, %rsp
    mov %rsi, %rbx
    call sum_to
    mov %rax, %r12
    mov %rbx, %rdi
    call dbl
    add %r12, %rax
    add $8, %rsp
    pop %r12
    pop %rbx
    ret
    .size f, . - f
    .section .note.GNU-stack,"",@progbits
