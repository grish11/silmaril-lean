# Arithmetic functions (RV64IM): gcd, factorial, collatz, M-extension edge cases.
#include "rt.inc"
    .globl gcd
gcd:                    # gcd(a0, a1) by remainder
    beqz a1, 2f
1:  remu t0, a0, a1
    mv a0, a1
    mv a1, t0
    bnez a1, 1b
2:  ret

    .globl fact
fact:                   # a0! mod 2^64
    li t0, 1
1:  blez a0, 2f
    mul t0, t0, a0
    addi a0, a0, -1
    j 1b
2:  mv a0, t0
    ret

    .globl collatz
collatz:                # number of steps to reach 1
    li t0, 0
    li t1, 1
1:  beq a0, t1, 3f
    andi t2, a0, 1
    beqz t2, 2f
    slli t3, a0, 1
    add a0, a0, t3
    addi a0, a0, 1
    addi t0, t0, 1
    j 1b
2:  srli a0, a0, 1
    addi t0, t0, 1
    j 1b
3:  mv a0, t0
    ret

test:
    addi sp, sp, -16
    sd ra, 8(sp)
    li a0, 1071
    li a1, 462
    call gcd
    mv s0, a0                    # 21
    li a0, 20
    call fact
    mv s1, a0
    li a0, 27
    call collatz
    mv s2, a0                    # 111
    # M edge cases
    li t0, -1
    li t1, 0
    div s3, t0, t1               # -1
    divu s4, t0, t1              # all ones
    rem s5, t0, t1               # dividend
    li t2, 1
    slli t2, t2, 63              # INT64_MIN
    div s6, t2, t0               # overflow: INT64_MIN
    rem s7, t2, t0               # 0
    mulh s8, t2, t0
    mulhsu s9, t0, t2
    mulhu s10, t2, t0
    li t3, 0x80000000
    divw s11, t3, t0             # word overflow
    remuw t4, t0, t1
    mulw t5, t3, t3
    addiw a2, t3, -1
    sraiw a3, t3, 4
    srliw a4, t0, 4
    sllw a5, t0, t0
    subw a6, t1, t3
    sraw a7, t3, t0
    ld ra, 8(sp)
    addi sp, sp, 16
    add a0, s0, s2               # exit code 132
    ret
