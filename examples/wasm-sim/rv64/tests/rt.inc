# Test runtime: _start sets a deterministic stack, calls `test`, then dumps
# x1..x30 (256-byte record: slot i = x_i, slots 0 and 31 zero) to stdout with
# write(1, ...) and exits with the low byte of a0. Deterministic under both
# qemu-riscv64 and the Wasm simulators (no dependence on the initial stack).
    .option nopic
    .text
    .globl _start
_start:
    lla sp, __stack_top
    call test
    .globl dump_exit
dump_exit:
    lla t6, regbuf
    .irp r, 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30
    sd x\r, (8*\r)(t6)
    .endr
    li a0, 1
    mv a1, t6
    li a2, 256
    li a7, 64
    ecall
    ld a0, 80(t6)
    li a7, 93
    ecall
    .bss
    .balign 16
regbuf: .space 256
    .space 65536
__stack_top:
    .text
