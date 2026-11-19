# Memory operations: all load/store widths, sign/zero extension, a byte loop
# (string reverse) printed with write, memcpy by doublewords.
#include "rt.inc"
test:
    lla t0, buf
    li t1, 0x8899aabbccddeeff
    sd t1, 0(t0)
    sw t1, 8(t0)
    sh t1, 12(t0)
    sb t1, 14(t0)
    lb s0, 0(t0)
    lbu s1, 0(t0)
    lh s2, 2(t0)
    lhu s3, 2(t0)
    lw s4, 4(t0)
    lwu s5, 4(t0)
    ld s6, 8(t0)
    ld s7, 0(t0)
    # reverse "Hello, memory!\n" (without the newline) into out, then print
    lla a0, msg
    lla a1, out
    li a2, 14
    add t2, a0, a2
1:  addi t2, t2, -1
    lbu t3, 0(t2)
    sb t3, 0(a1)
    addi a1, a1, 1
    bne t2, a0, 1b
    li t3, 10
    sb t3, 0(a1)
    li a0, 1
    lla a1, out
    li a2, 15
    li a7, 64
    ecall
    # memcpy 64 bytes from buf to buf2 by doublewords
    lla a0, buf2
    lla a1, buf
    li a2, 8
2:  ld t4, 0(a1)
    sd t4, 0(a0)
    addi a0, a0, 8
    addi a1, a1, 8
    addi a2, a2, -1
    bnez a2, 2b
    lla t0, buf2
    ld s8, 8(t0)
    li a0, 7
    ret
    .data
msg: .ascii "Hello, memory!\n"
    .balign 8
buf: .space 64
buf2: .space 64
out: .space 16
