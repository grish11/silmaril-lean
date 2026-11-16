# Loops and calls: sum 1..n, fib, nested loop, and a hot loop used as a benchmark
# (iteration count in a0 on entry to `hot`, 6 instructions per iteration).
#include "rt.inc"
    .globl sum_to
sum_to:                 # 1 + ... + a0
    li t0, 0
1:  beqz a0, 2f
    add t0, t0, a0
    addi a0, a0, -1
    j 1b
2:  mv a0, t0
    ret

    .globl fib
fib:                    # iterative fib(a0)
    li t0, 0
    li t1, 1
1:  beqz a0, 2f
    add t2, t0, t1
    mv t0, t1
    mv t1, t2
    addi a0, a0, -1
    j 1b
2:  mv a0, t0
    ret

    .globl hot
hot:                    # xorshift-ish mixing loop, a0 iterations
    li t0, 0x9e3779b97f4a7c15
    li t1, 0
1:  xor t1, t1, t0
    slli t2, t1, 13
    add t1, t1, t2
    srli t2, t1, 7
    addi a0, a0, -1
    bnez a0, 1b
    mv a0, t1
    ret

test:
    addi sp, sp, -16
    sd ra, 8(sp)
    li a0, 1000
    call sum_to
    mv s0, a0
    li a0, 90
    call fib
    mv s1, a0
    li s2, 0
    li t3, 0
3:  li t4, 0
4:  add s2, s2, t4
    addi t4, t4, 1
    slti t5, t4, 30
    bnez t5, 4b
    addi t3, t3, 1
    sltiu t5, t3, 20
    bnez t5, 3b
    li a0, HOT_N
    call hot
    mv s3, a0
    ld ra, 8(sp)
    addi sp, sp, 16
    andi a0, s1, 0x7f
    ret
