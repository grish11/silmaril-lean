	.file	"fft.c"
	.text
.Ltext0:
	.cfi_sections	.debug_frame
	.file 0 "." "fft.c"
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC7:
	.string	"%d: %+.3f %+.3fi\n"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB4:
	.file 1 "fft.c"
	.loc 1 40 1 view -0
	.cfi_startproc
	.loc 1 41 3 view .LVU1
	.loc 1 40 1 is_stmt 0 view .LVU2
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
.LBB23:
.LBB24:
	.loc 1 12 19 view .LVU3
	xorl	%edx, %edx
	.loc 1 12 12 view .LVU4
	movl	$1, %ecx
.LBE24:
.LBE23:
	.loc 1 40 1 view .LVU5
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$216, %rsp
	.cfi_def_cfa_offset 272
	.loc 1 41 18 view .LVU6
	movq	.LC4(%rip), %xmm0
	leaq	96(%rsp), %rsi
	movaps	%xmm0, 80(%rsp)
	movaps	%xmm0, 96(%rsp)
	movaps	%xmm0, 112(%rsp)
	movaps	%xmm0, 128(%rsp)
	pxor	%xmm0, %xmm0
	movaps	%xmm0, 144(%rsp)
	movaps	%xmm0, 160(%rsp)
	movaps	%xmm0, 176(%rsp)
	movaps	%xmm0, 192(%rsp)
	.loc 1 42 3 is_stmt 1 view .LVU7
.LVL0:
.LBB49:
.LBI23:
	.loc 1 9 13 view .LVU8
	.loc 1 12 3 view .LVU9
.LBB27:
	.loc 1 12 8 view .LVU10
	.loc 1 12 28 discriminator 1 view .LVU11
	.p2align 4,,10
	.p2align 3
.L2:
.LBB25:
	.loc 1 14 12 discriminator 1 view .LVU12
	.loc 1 13 9 is_stmt 0 view .LVU13
	movl	$4, %eax
	.loc 1 14 12 discriminator 1 view .LVU14
	testb	$4, %dl
	je	.L6
.LVL1:
	.p2align 4,,10
	.p2align 3
.L3:
	.loc 1 15 7 is_stmt 1 view .LVU15
	.loc 1 15 9 is_stmt 0 view .LVU16
	xorl	%eax, %edx
.LVL2:
	.loc 1 14 25 is_stmt 1 discriminator 2 view .LVU17
	sarl	%eax
.LVL3:
	.loc 1 14 12 discriminator 1 view .LVU18
	testl	%eax, %edx
	jne	.L3
.LVL4:
.L6:
	.loc 1 16 5 view .LVU19
	.loc 1 16 7 is_stmt 0 view .LVU20
	xorl	%eax, %edx
.LVL5:
	.loc 1 17 5 is_stmt 1 view .LVU21
	.loc 1 17 8 is_stmt 0 view .LVU22
	cmpl	%ecx, %edx
	jle	.L4
.LBB26:
	.loc 1 18 7 is_stmt 1 view .LVU23
	.loc 1 19 15 is_stmt 0 view .LVU24
	movslq	%edx, %rax
	leaq	80(%rsp), %rdi
.LVL6:
	.loc 1 19 15 view .LVU25
	movapd	(%rsi), %xmm0
.LVL7:
	.loc 1 19 7 is_stmt 1 view .LVU26
	.loc 1 19 15 is_stmt 0 view .LVU27
	salq	$4, %rax
	addq	%rdi, %rax
	.loc 1 19 12 view .LVU28
	movapd	(%rax), %xmm7
	movaps	%xmm7, (%rsi)
.LVL8:
	.loc 1 20 7 is_stmt 1 view .LVU29
	.loc 1 20 12 is_stmt 0 view .LVU30
	movaps	%xmm0, (%rax)
.LVL9:
.L4:
	.loc 1 20 12 view .LVU31
.LBE26:
.LBE25:
	.loc 1 12 34 is_stmt 1 discriminator 2 view .LVU32
	addl	$1, %ecx
.LVL10:
	.loc 1 12 28 discriminator 1 view .LVU33
	addq	$16, %rsi
	cmpl	$8, %ecx
	jne	.L2
	movl	$3, 12(%rsp)
	movsd	.LC0(%rip), %xmm6
.LBE27:
.LBB28:
	.loc 1 24 12 is_stmt 0 view .LVU34
	movl	$2, %ecx
.LVL11:
	.loc 1 24 12 view .LVU35
.LBE28:
.LBB46:
	movsd	.LC1(%rip), %xmm5
	movsd	.LC3(%rip), %xmm7
.LVL12:
	.p2align 4,,10
	.p2align 3
.L5:
	.loc 1 24 12 view .LVU36
.LBE46:
.LBB47:
.LBB29:
	.loc 1 25 5 is_stmt 1 view .LVU37
	.loc 1 26 5 view .LVU38
.LBB30:
	.loc 1 26 10 view .LVU39
	.loc 1 26 23 discriminator 1 view .LVU40
.LBB31:
.LBB32:
	.loc 1 28 31 is_stmt 0 discriminator 1 view .LVU41
	movl	%ecx, %r14d
	movslq	%ecx, %rsi
	leaq	80(%rsp), %rbp
.LVL13:
	.loc 1 28 31 discriminator 1 view .LVU42
.LBE32:
.LBE31:
	.loc 1 26 14 view .LVU43
	xorl	%eax, %eax
.LBB39:
.LBB35:
	.loc 1 28 31 discriminator 1 view .LVU44
	sarl	%r14d
	salq	$4, %rsi
	movq	%rbp, %r15
	movslq	%r14d, %rdi
	salq	$4, %rdi
.LVL14:
	.loc 1 28 25 is_stmt 1 discriminator 1 view .LVU45
	.p2align 4,,10
	.p2align 3
.L10:
	.loc 1 28 25 is_stmt 0 discriminator 1 view .LVU46
	leaq	(%rdi,%r15), %r12
.LBE35:
.LBE39:
	.loc 1 26 14 view .LVU47
	movq	%r15, %rbx
	pxor	%xmm3, %xmm3
.LBB40:
.LBB36:
	.loc 1 28 16 view .LVU48
	xorl	%r13d, %r13d
.LBE36:
.LBE40:
	.loc 1 26 14 view .LVU49
	movapd	%xmm7, %xmm2
	jmp	.L9
.LVL15:
	.p2align 4,,10
	.p2align 3
.L14:
.LBB41:
.LBB37:
	.loc 1 28 25 discriminator 1 view .LVU50
	movapd	%xmm4, %xmm3
	movapd	%xmm0, %xmm2
.LVL16:
.L9:
.LBB33:
	.loc 1 29 9 is_stmt 1 view .LVU51
	movapd	(%r12), %xmm1
	.loc 1 30 24 is_stmt 0 view .LVU52
	movapd	%xmm2, %xmm0
	movapd	%xmm3, %xmm8
	movapd	(%rbx), %xmm4
.LVL17:
	.loc 1 30 9 is_stmt 1 view .LVU53
	.loc 1 30 24 is_stmt 0 view .LVU54
	unpcklpd	%xmm0, %xmm0
	unpcklpd	%xmm8, %xmm8
	mulpd	%xmm1, %xmm0
	movapd	%xmm1, %xmm9
	shufpd	$1, %xmm1, %xmm9
	mulpd	%xmm8, %xmm9
	movapd	%xmm0, %xmm8
	addpd	%xmm9, %xmm8
	subpd	%xmm9, %xmm0
	movapd	%xmm8, %xmm9
	unpckhpd	%xmm8, %xmm8
	ucomisd	%xmm8, %xmm0
	movsd	%xmm0, %xmm9
	jp	.L22
.LVL18:
.L7:
	.loc 1 31 9 is_stmt 1 view .LVU55
	.loc 1 31 22 is_stmt 0 view .LVU56
	movapd	%xmm4, %xmm0
	.loc 1 33 12 view .LVU57
	movapd	%xmm5, %xmm1
	.loc 1 32 32 view .LVU58
	subpd	%xmm9, %xmm4
	.loc 1 31 22 view .LVU59
	addpd	%xmm9, %xmm0
	.loc 1 33 12 view .LVU60
	mulsd	%xmm3, %xmm1
	.loc 1 31 18 view .LVU61
	movaps	%xmm0, (%rbx)
	.loc 1 32 9 is_stmt 1 view .LVU62
	.loc 1 33 12 is_stmt 0 view .LVU63
	movapd	%xmm6, %xmm0
	mulsd	%xmm2, %xmm0
	.loc 1 32 28 view .LVU64
	movaps	%xmm4, (%r12)
	.loc 1 33 9 is_stmt 1 view .LVU65
	.loc 1 33 12 is_stmt 0 view .LVU66
	movapd	%xmm6, %xmm4
	mulsd	%xmm3, %xmm4
	subsd	%xmm1, %xmm0
	movapd	%xmm5, %xmm1
	mulsd	%xmm2, %xmm1
	addsd	%xmm1, %xmm4
	ucomisd	%xmm4, %xmm0
	jp	.L23
.L8:
.LVL19:
	.loc 1 33 12 view .LVU67
.LBE33:
	.loc 1 28 37 is_stmt 1 discriminator 3 view .LVU68
	addl	$1, %r13d
.LVL20:
	.loc 1 28 25 discriminator 1 view .LVU69
	addq	$16, %rbx
	addq	$16, %r12
	cmpl	%r13d, %r14d
	jg	.L14
.LBE37:
.LBE41:
	.loc 1 26 30 discriminator 2 view .LVU70
	addl	%ecx, %eax
.LVL21:
	.loc 1 26 23 discriminator 1 view .LVU71
	addq	%rsi, %r15
	cmpl	$7, %eax
	jle	.L10
.LBE30:
.LBE29:
	.loc 1 24 35 discriminator 2 view .LVU72
	addl	%ecx, %ecx
.LVL22:
	.loc 1 24 25 discriminator 1 view .LVU73
	subl	$1, 12(%rsp)
	je	.L15
.LBB44:
	.loc 1 25 24 is_stmt 0 view .LVU74
	pxor	%xmm1, %xmm1
	movsd	.LC6(%rip), %xmm7
	movsd	.LC5(%rip), %xmm0
.LVL23:
	.loc 1 25 24 view .LVU75
	movl	%ecx, (%rsp)
	cvtsi2sdl	%ecx, %xmm1
	divsd	%xmm1, %xmm7
	divsd	%xmm1, %xmm0
	movapd	%xmm7, %xmm1
	call	cexp
.LVL24:
	.loc 1 25 24 view .LVU76
	movl	(%rsp), %ecx
	movsd	.LC3(%rip), %xmm7
	movapd	%xmm0, %xmm6
	movapd	%xmm1, %xmm5
	jmp	.L5
.LVL25:
.L15:
	.loc 1 25 24 view .LVU77
.LBE44:
.LBE47:
.LBE49:
.LBB50:
	.loc 1 43 12 view .LVU78
	xorl	%ebx, %ebx
	.loc 1 44 5 view .LVU79
	pxor	%xmm2, %xmm2
.LVL26:
	.p2align 4,,10
	.p2align 3
.L11:
	.loc 1 44 5 is_stmt 1 view .LVU80
	movsd	0(%rbp), %xmm0
	movsd	8(%rbp), %xmm1
	movl	%ebx, %esi
	.loc 1 43 27 is_stmt 0 discriminator 3 view .LVU81
	addl	$1, %ebx
.LVL27:
	.loc 1 44 5 view .LVU82
	movl	$.LC7, %edi
	movl	$2, %eax
	.loc 1 43 21 discriminator 1 view .LVU83
	addq	$16, %rbp
	.loc 1 44 5 view .LVU84
	addsd	%xmm2, %xmm0
	addsd	%xmm2, %xmm1
	call	printf
.LVL28:
	.loc 1 43 27 is_stmt 1 discriminator 3 view .LVU85
	.loc 1 43 21 discriminator 1 view .LVU86
	cmpl	$8, %ebx
	pxor	%xmm2, %xmm2
	jne	.L11
.LBE50:
	.loc 1 45 3 view .LVU87
	.loc 1 46 1 is_stmt 0 view .LVU88
	addq	$216, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 48
.LVL29:
	.loc 1 46 1 view .LVU89
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
.LVL30:
.L22:
	.cfi_restore_state
	.loc 1 46 1 view .LVU90
	movapd	%xmm1, %xmm0
	unpckhpd	%xmm1, %xmm1
	movq	%rdi, 56(%rsp)
	movl	%ecx, 52(%rsp)
	movl	%eax, 48(%rsp)
	movq	%rsi, 24(%rsp)
	movsd	%xmm5, 72(%rsp)
	movsd	%xmm6, 64(%rsp)
	movaps	%xmm4, 32(%rsp)
	movsd	%xmm3, 16(%rsp)
	movsd	%xmm2, (%rsp)
	call	__muldc3
.LVL31:
	.loc 1 46 1 view .LVU91
	movsd	72(%rsp), %xmm5
	movsd	64(%rsp), %xmm6
	movapd	%xmm0, %xmm9
	movq	56(%rsp), %rdi
	movapd	32(%rsp), %xmm4
	movl	52(%rsp), %ecx
	movl	48(%rsp), %eax
	unpcklpd	%xmm1, %xmm9
	movsd	.LC3(%rip), %xmm7
	movq	24(%rsp), %rsi
	movsd	16(%rsp), %xmm3
	movsd	(%rsp), %xmm2
	jmp	.L7
.LVL32:
.L23:
	.loc 1 46 1 view .LVU92
	movapd	%xmm5, %xmm1
	movapd	%xmm6, %xmm0
	movq	%rdi, 32(%rsp)
	movl	%ecx, 52(%rsp)
	movl	%eax, 48(%rsp)
	movq	%rsi, 24(%rsp)
	movsd	%xmm5, 16(%rsp)
	movsd	%xmm6, (%rsp)
	call	__muldc3
.LVL33:
.LBB51:
.LBB48:
.LBB45:
.LBB43:
.LBB42:
.LBB38:
.LBB34:
	.loc 1 33 12 view .LVU93
	movq	32(%rsp), %rdi
	movl	52(%rsp), %ecx
	movsd	.LC3(%rip), %xmm7
	movl	48(%rsp), %eax
	movapd	%xmm1, %xmm4
	movq	24(%rsp), %rsi
	movsd	16(%rsp), %xmm5
	movsd	(%rsp), %xmm6
	jmp	.L8
.LBE34:
.LBE38:
.LBE42:
.LBE43:
.LBE45:
.LBE48:
.LBE51:
	.cfi_endproc
.LFE4:
	.size	main, .-main
	.section	.rodata.cst8,"aM",@progbits,8
	.align 8
.LC0:
	.long	0
	.long	-1074790400
	.align 8
.LC1:
	.long	856972295
	.long	-1130256858
	.set	.LC3,.LC4
	.section	.rodata.cst16,"aM",@progbits,16
	.align 16
.LC4:
	.long	0
	.long	1072693248
	.long	0
	.long	0
	.section	.rodata.cst8
	.align 8
.LC5:
	.long	0
	.long	-2147483648
	.align 8
.LC6:
	.long	1413754136
	.long	-1072094725
	.text
.Letext0:
	.file 2 "/usr/include/x86_64-linux-gnu/bits/cmathcalls.h"
	.file 3 "/usr/include/stdio.h"
	.file 4 "<built-in>"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0x36b
	.value	0x5
	.byte	0x1
	.byte	0x8
	.long	.Ldebug_abbrev0
	.uleb128 0xf
	.long	.LASF15
	.byte	0x1d
	.long	.LASF0
	.long	.LASF1
	.long	.LLRL19
	.quad	0
	.long	.Ldebug_line0
	.uleb128 0x1
	.byte	0x8
	.byte	0x4
	.long	.LASF2
	.uleb128 0x1
	.byte	0x1
	.byte	0x8
	.long	.LASF3
	.uleb128 0x1
	.byte	0x2
	.byte	0x7
	.long	.LASF4
	.uleb128 0x1
	.byte	0x4
	.byte	0x7
	.long	.LASF5
	.uleb128 0x1
	.byte	0x8
	.byte	0x7
	.long	.LASF6
	.uleb128 0x1
	.byte	0x1
	.byte	0x6
	.long	.LASF7
	.uleb128 0x1
	.byte	0x2
	.byte	0x5
	.long	.LASF8
	.uleb128 0x10
	.byte	0x4
	.byte	0x5
	.string	"int"
	.uleb128 0x1
	.byte	0x8
	.byte	0x5
	.long	.LASF9
	.uleb128 0x1
	.byte	0x1
	.byte	0x6
	.long	.LASF10
	.uleb128 0x11
	.long	0x69
	.uleb128 0x1
	.byte	0x4
	.byte	0x4
	.long	.LASF11
	.uleb128 0x12
	.long	.LASF13
	.byte	0x2
	.byte	0x59
	.byte	0x1
	.long	0x92
	.long	0x92
	.uleb128 0x7
	.long	0x92
	.byte	0
	.uleb128 0x1
	.byte	0x10
	.byte	0x3
	.long	.LASF12
	.uleb128 0x13
	.long	.LASF14
	.byte	0x3
	.value	0x164
	.byte	0xc
	.long	0x5b
	.long	0xb1
	.uleb128 0x7
	.long	0xb1
	.uleb128 0x14
	.byte	0
	.uleb128 0x8
	.long	0x70
	.uleb128 0x15
	.long	.LASF16
	.byte	0x1
	.byte	0x27
	.byte	0x5
	.long	0x5b
	.quad	.LFB4
	.quad	.LFE4-.LFB4
	.uleb128 0x1
	.byte	0x9c
	.long	0x2b2
	.uleb128 0x16
	.string	"x"
	.byte	0x1
	.byte	0x29
	.byte	0x12
	.long	0x2b2
	.uleb128 0x3
	.byte	0x91
	.sleb128 -192
	.uleb128 0x17
	.quad	.LBB50
	.quad	.LBE50-.LBB50
	.long	0x12f
	.uleb128 0x18
	.string	"i"
	.byte	0x1
	.byte	0x2b
	.byte	0xc
	.long	0x5b
	.long	.LLST18
	.long	.LVUS18
	.uleb128 0x9
	.quad	.LVL28
	.long	0x99
	.uleb128 0x5
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x9
	.byte	0x3
	.quad	.LC7
	.uleb128 0x5
	.uleb128 0x1
	.byte	0x54
	.uleb128 0x2
	.byte	0x73
	.sleb128 -1
	.byte	0
	.byte	0
	.uleb128 0x19
	.long	0x2c2
	.quad	.LBI23
	.byte	.LVU8
	.long	.LLRL0
	.byte	0x1
	.byte	0x2a
	.byte	0x3
	.long	0x269
	.uleb128 0xa
	.long	0x2d7
	.long	.LLST1
	.long	.LVUS1
	.uleb128 0xa
	.long	0x2cf
	.long	.LLST2
	.long	.LVUS2
	.uleb128 0xb
	.long	0x2df
	.long	.LLRL3
	.long	0x1d0
	.uleb128 0x3
	.long	0x2e4
	.long	.LLST4
	.long	.LVUS4
	.uleb128 0x3
	.long	0x2ed
	.long	.LLST5
	.long	.LVUS5
	.uleb128 0xc
	.long	0x2f6
	.quad	.LBB25
	.quad	.LBE25-.LBB25
	.uleb128 0x3
	.long	0x2f7
	.long	.LLST6
	.long	.LVUS6
	.uleb128 0xc
	.long	0x302
	.quad	.LBB26
	.quad	.LBE26-.LBB26
	.uleb128 0x3
	.long	0x303
	.long	.LLST7
	.long	.LVUS7
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x6
	.long	0x30f
	.long	.LLRL8
	.uleb128 0x3
	.long	0x310
	.long	.LLST9
	.long	.LVUS9
	.uleb128 0x6
	.long	0x31b
	.long	.LLRL10
	.uleb128 0xd
	.long	0x31c
	.uleb128 0xb
	.long	0x325
	.long	.LLRL11
	.long	0x259
	.uleb128 0x3
	.long	0x326
	.long	.LLST12
	.long	.LVUS12
	.uleb128 0x6
	.long	0x32f
	.long	.LLRL13
	.uleb128 0x3
	.long	0x330
	.long	.LLST14
	.long	.LVUS14
	.uleb128 0x6
	.long	0x33a
	.long	.LLRL13
	.uleb128 0x3
	.long	0x33b
	.long	.LLST15
	.long	.LVUS15
	.uleb128 0x6
	.long	0x344
	.long	.LLRL16
	.uleb128 0x3
	.long	0x345
	.long	.LLST17
	.long	.LVUS17
	.uleb128 0xd
	.long	0x34e
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x1a
	.quad	.LVL24
	.long	0x7c
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x1b
	.quad	.LVL31
	.long	0x363
	.long	0x28f
	.uleb128 0x5
	.uleb128 0x1
	.byte	0x63
	.uleb128 0x6
	.byte	0x91
	.sleb128 -272
	.byte	0xa6
	.byte	0x8
	.uleb128 0x2a
	.uleb128 0x5
	.uleb128 0x1
	.byte	0x64
	.uleb128 0x6
	.byte	0x91
	.sleb128 -256
	.byte	0xa6
	.byte	0x8
	.uleb128 0x2a
	.byte	0
	.uleb128 0x9
	.quad	.LVL33
	.long	0x363
	.uleb128 0x5
	.uleb128 0x1
	.byte	0x61
	.uleb128 0x6
	.byte	0x91
	.sleb128 -272
	.byte	0xa6
	.byte	0x8
	.uleb128 0x2a
	.uleb128 0x5
	.uleb128 0x1
	.byte	0x62
	.uleb128 0x6
	.byte	0x91
	.sleb128 -256
	.byte	0xa6
	.byte	0x8
	.uleb128 0x2a
	.byte	0
	.byte	0
	.uleb128 0x1c
	.long	0x92
	.long	0x2c2
	.uleb128 0x1d
	.long	0x46
	.byte	0x7
	.byte	0
	.uleb128 0x1e
	.string	"fft"
	.byte	0x1
	.byte	0x9
	.byte	0xd
	.byte	0x1
	.long	0x35e
	.uleb128 0xe
	.string	"x"
	.byte	0x21
	.long	0x35e
	.uleb128 0xe
	.string	"n"
	.byte	0x28
	.long	0x5b
	.uleb128 0x1f
	.long	0x30f
	.uleb128 0x2
	.string	"i"
	.byte	0xc
	.byte	0xc
	.long	0x5b
	.uleb128 0x2
	.string	"j"
	.byte	0xc
	.byte	0x13
	.long	0x5b
	.uleb128 0x4
	.uleb128 0x2
	.string	"bit"
	.byte	0xd
	.byte	0x9
	.long	0x5b
	.uleb128 0x4
	.uleb128 0x2
	.string	"t"
	.byte	0x12
	.byte	0x16
	.long	0x92
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x4
	.uleb128 0x2
	.string	"len"
	.byte	0x18
	.byte	0xc
	.long	0x5b
	.uleb128 0x4
	.uleb128 0x2
	.string	"w"
	.byte	0x19
	.byte	0x14
	.long	0x92
	.uleb128 0x4
	.uleb128 0x2
	.string	"i"
	.byte	0x1a
	.byte	0xe
	.long	0x5b
	.uleb128 0x4
	.uleb128 0x2
	.string	"wk"
	.byte	0x1b
	.byte	0x16
	.long	0x92
	.uleb128 0x4
	.uleb128 0x2
	.string	"k"
	.byte	0x1c
	.byte	0x10
	.long	0x5b
	.uleb128 0x4
	.uleb128 0x2
	.string	"u"
	.byte	0x1d
	.byte	0x18
	.long	0x92
	.uleb128 0x2
	.string	"v"
	.byte	0x1e
	.byte	0x18
	.long	0x92
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x8
	.long	0x92
	.uleb128 0x20
	.long	.LASF17
	.long	.LASF17
	.byte	0x4
	.byte	0
	.byte	0
	.section	.debug_abbrev,"",@progbits
.Ldebug_abbrev0:
	.uleb128 0x1
	.uleb128 0x24
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0xe
	.byte	0
	.byte	0
	.uleb128 0x2
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x3
	.uleb128 0x34
	.byte	0
	.uleb128 0x31
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x17
	.uleb128 0x2137
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x4
	.uleb128 0xb
	.byte	0x1
	.byte	0
	.byte	0
	.uleb128 0x5
	.uleb128 0x49
	.byte	0
	.uleb128 0x2
	.uleb128 0x18
	.uleb128 0x7e
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x6
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x31
	.uleb128 0x13
	.uleb128 0x55
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x7
	.uleb128 0x5
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x8
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x9
	.uleb128 0x48
	.byte	0x1
	.uleb128 0x7d
	.uleb128 0x1
	.uleb128 0x7f
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xa
	.uleb128 0x5
	.byte	0
	.uleb128 0x31
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x17
	.uleb128 0x2137
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x31
	.uleb128 0x13
	.uleb128 0x55
	.uleb128 0x17
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xc
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x31
	.uleb128 0x13
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.byte	0
	.byte	0
	.uleb128 0xd
	.uleb128 0x34
	.byte	0
	.uleb128 0x31
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xe
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x21
	.sleb128 9
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xf
	.uleb128 0x11
	.byte	0x1
	.uleb128 0x25
	.uleb128 0xe
	.uleb128 0x13
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0x1f
	.uleb128 0x1b
	.uleb128 0x1f
	.uleb128 0x55
	.uleb128 0x17
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x10
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x10
	.uleb128 0x24
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0x8
	.byte	0
	.byte	0
	.uleb128 0x11
	.uleb128 0x26
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x12
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x13
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x14
	.uleb128 0x18
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x15
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7a
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x16
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x17
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x18
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x17
	.uleb128 0x2137
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x19
	.uleb128 0x1d
	.byte	0x1
	.uleb128 0x31
	.uleb128 0x13
	.uleb128 0x52
	.uleb128 0x1
	.uleb128 0x2138
	.uleb128 0xb
	.uleb128 0x55
	.uleb128 0x17
	.uleb128 0x58
	.uleb128 0xb
	.uleb128 0x59
	.uleb128 0xb
	.uleb128 0x57
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1a
	.uleb128 0x48
	.byte	0
	.uleb128 0x7d
	.uleb128 0x1
	.uleb128 0x7f
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1b
	.uleb128 0x48
	.byte	0x1
	.uleb128 0x7d
	.uleb128 0x1
	.uleb128 0x7f
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1c
	.uleb128 0x1
	.byte	0x1
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1d
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x1e
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x20
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1f
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x20
	.uleb128 0x2e
	.byte	0
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3c
	.uleb128 0x19
	.uleb128 0x6e
	.uleb128 0xe
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.byte	0
	.byte	0
	.byte	0
	.section	.debug_loclists,"",@progbits
	.long	.Ldebug_loc3-.Ldebug_loc2
.Ldebug_loc2:
	.value	0x5
	.byte	0x8
	.byte	0
	.long	0
.Ldebug_loc0:
.LVUS18:
	.uleb128 .LVU80
	.uleb128 .LVU82
	.uleb128 .LVU82
	.uleb128 .LVU85
	.uleb128 .LVU85
	.uleb128 .LVU86
	.uleb128 .LVU86
	.uleb128 .LVU89
.LLST18:
	.byte	0x6
	.quad	.LVL26
	.byte	0x4
	.uleb128 .LVL26-.LVL26
	.uleb128 .LVL27-.LVL26
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL27-.LVL26
	.uleb128 .LVL28-1-.LVL26
	.uleb128 0x1
	.byte	0x54
	.byte	0x4
	.uleb128 .LVL28-1-.LVL26
	.uleb128 .LVL28-.LVL26
	.uleb128 0x3
	.byte	0x73
	.sleb128 -1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL28-.LVL26
	.uleb128 .LVL29-.LVL26
	.uleb128 0x1
	.byte	0x53
	.byte	0
.LVUS1:
	.uleb128 .LVU9
	.uleb128 .LVU80
	.uleb128 .LVU90
	.uleb128 0
.LLST1:
	.byte	0x6
	.quad	.LVL0
	.byte	0x4
	.uleb128 .LVL0-.LVL0
	.uleb128 .LVL26-.LVL0
	.uleb128 0x2
	.byte	0x38
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL30-.LVL0
	.uleb128 .LFE4-.LVL0
	.uleb128 0x2
	.byte	0x38
	.byte	0x9f
	.byte	0
.LVUS2:
	.uleb128 .LVU8
	.uleb128 .LVU25
	.uleb128 .LVU25
	.uleb128 .LVU31
	.uleb128 .LVU31
	.uleb128 .LVU42
	.uleb128 .LVU42
	.uleb128 .LVU80
	.uleb128 .LVU90
	.uleb128 0
.LLST2:
	.byte	0x6
	.quad	.LVL0
	.byte	0x4
	.uleb128 .LVL0-.LVL0
	.uleb128 .LVL6-.LVL0
	.uleb128 0x4
	.byte	0x91
	.sleb128 -192
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL6-.LVL0
	.uleb128 .LVL9-.LVL0
	.uleb128 0x1
	.byte	0x55
	.byte	0x4
	.uleb128 .LVL9-.LVL0
	.uleb128 .LVL13-.LVL0
	.uleb128 0x4
	.byte	0x91
	.sleb128 -192
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL13-.LVL0
	.uleb128 .LVL26-.LVL0
	.uleb128 0x1
	.byte	0x56
	.byte	0x4
	.uleb128 .LVL30-.LVL0
	.uleb128 .LFE4-.LVL0
	.uleb128 0x1
	.byte	0x56
	.byte	0
.LVUS4:
	.uleb128 .LVU11
	.uleb128 .LVU12
	.uleb128 .LVU12
	.uleb128 .LVU35
.LLST4:
	.byte	0x6
	.quad	.LVL0
	.byte	0x4
	.uleb128 .LVL0-.LVL0
	.uleb128 .LVL0-.LVL0
	.uleb128 0x2
	.byte	0x31
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL0-.LVL0
	.uleb128 .LVL11-.LVL0
	.uleb128 0x1
	.byte	0x52
	.byte	0
.LVUS5:
	.uleb128 .LVU11
	.uleb128 .LVU12
	.uleb128 .LVU12
	.uleb128 .LVU36
.LLST5:
	.byte	0x6
	.quad	.LVL0
	.byte	0x4
	.uleb128 .LVL0-.LVL0
	.uleb128 .LVL0-.LVL0
	.uleb128 0x2
	.byte	0x30
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL0-.LVL0
	.uleb128 .LVL12-.LVL0
	.uleb128 0x1
	.byte	0x51
	.byte	0
.LVUS6:
	.uleb128 .LVU12
	.uleb128 .LVU15
	.uleb128 .LVU15
	.uleb128 .LVU19
.LLST6:
	.byte	0x6
	.quad	.LVL0
	.byte	0x4
	.uleb128 .LVL0-.LVL0
	.uleb128 .LVL1-.LVL0
	.uleb128 0x2
	.byte	0x34
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL1-.LVL0
	.uleb128 .LVL4-.LVL0
	.uleb128 0x1
	.byte	0x50
	.byte	0
.LVUS7:
	.uleb128 .LVU26
	.uleb128 .LVU29
.LLST7:
	.byte	0x8
	.quad	.LVL7
	.uleb128 .LVL8-.LVL7
	.uleb128 0x8
	.byte	0x74
	.sleb128 0
	.byte	0x93
	.uleb128 0x8
	.byte	0x74
	.sleb128 8
	.byte	0x93
	.uleb128 0x8
	.byte	0
.LVUS9:
	.uleb128 .LVU36
	.uleb128 .LVU76
	.uleb128 .LVU76
	.uleb128 .LVU77
	.uleb128 .LVU77
	.uleb128 .LVU80
	.uleb128 .LVU90
	.uleb128 .LVU91
	.uleb128 .LVU91
	.uleb128 .LVU92
	.uleb128 .LVU92
	.uleb128 .LVU93
	.uleb128 .LVU93
	.uleb128 0
.LLST9:
	.byte	0x6
	.quad	.LVL12
	.byte	0x4
	.uleb128 .LVL12-.LVL12
	.uleb128 .LVL24-1-.LVL12
	.uleb128 0x1
	.byte	0x52
	.byte	0x4
	.uleb128 .LVL24-1-.LVL12
	.uleb128 .LVL25-.LVL12
	.uleb128 0x3
	.byte	0x91
	.sleb128 -272
	.byte	0x4
	.uleb128 .LVL25-.LVL12
	.uleb128 .LVL26-.LVL12
	.uleb128 0x1
	.byte	0x52
	.byte	0x4
	.uleb128 .LVL30-.LVL12
	.uleb128 .LVL31-1-.LVL12
	.uleb128 0x1
	.byte	0x52
	.byte	0x4
	.uleb128 .LVL31-1-.LVL12
	.uleb128 .LVL32-.LVL12
	.uleb128 0x3
	.byte	0x91
	.sleb128 -220
	.byte	0x4
	.uleb128 .LVL32-.LVL12
	.uleb128 .LVL33-1-.LVL12
	.uleb128 0x1
	.byte	0x52
	.byte	0x4
	.uleb128 .LVL33-1-.LVL12
	.uleb128 .LFE4-.LVL12
	.uleb128 0x3
	.byte	0x91
	.sleb128 -220
	.byte	0
.LVUS12:
	.uleb128 .LVU40
	.uleb128 .LVU46
	.uleb128 .LVU46
	.uleb128 .LVU76
	.uleb128 .LVU77
	.uleb128 .LVU80
	.uleb128 .LVU90
	.uleb128 .LVU91
	.uleb128 .LVU91
	.uleb128 .LVU92
	.uleb128 .LVU92
	.uleb128 .LVU93
	.uleb128 .LVU93
	.uleb128 0
.LLST12:
	.byte	0x6
	.quad	.LVL12
	.byte	0x4
	.uleb128 .LVL12-.LVL12
	.uleb128 .LVL14-.LVL12
	.uleb128 0x2
	.byte	0x30
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL14-.LVL12
	.uleb128 .LVL24-1-.LVL12
	.uleb128 0x1
	.byte	0x50
	.byte	0x4
	.uleb128 .LVL25-.LVL12
	.uleb128 .LVL26-.LVL12
	.uleb128 0x1
	.byte	0x50
	.byte	0x4
	.uleb128 .LVL30-.LVL12
	.uleb128 .LVL31-1-.LVL12
	.uleb128 0x1
	.byte	0x50
	.byte	0x4
	.uleb128 .LVL31-1-.LVL12
	.uleb128 .LVL32-.LVL12
	.uleb128 0x3
	.byte	0x91
	.sleb128 -224
	.byte	0x4
	.uleb128 .LVL32-.LVL12
	.uleb128 .LVL33-1-.LVL12
	.uleb128 0x1
	.byte	0x50
	.byte	0x4
	.uleb128 .LVL33-1-.LVL12
	.uleb128 .LFE4-.LVL12
	.uleb128 0x3
	.byte	0x91
	.sleb128 -224
	.byte	0
.LVUS14:
	.uleb128 .LVU45
	.uleb128 .LVU50
	.uleb128 .LVU50
	.uleb128 .LVU51
	.uleb128 .LVU67
	.uleb128 .LVU75
	.uleb128 .LVU77
	.uleb128 .LVU80
.LLST14:
	.byte	0x6
	.quad	.LVL14
	.byte	0x4
	.uleb128 .LVL14-.LVL14
	.uleb128 .LVL15-.LVL14
	.uleb128 0x18
	.byte	0x9e
	.uleb128 0x8
	.long	0
	.long	0x3ff00000
	.byte	0x93
	.uleb128 0x8
	.byte	0x9e
	.uleb128 0x8
	.long	0
	.long	0
	.byte	0x93
	.uleb128 0x8
	.byte	0x4
	.uleb128 .LVL15-.LVL14
	.uleb128 .LVL16-.LVL14
	.uleb128 0x6
	.byte	0x61
	.byte	0x93
	.uleb128 0x8
	.byte	0x65
	.byte	0x93
	.uleb128 0x8
	.byte	0x4
	.uleb128 .LVL19-.LVL14
	.uleb128 .LVL23-.LVL14
	.uleb128 0x6
	.byte	0x61
	.byte	0x93
	.uleb128 0x8
	.byte	0x65
	.byte	0x93
	.uleb128 0x8
	.byte	0x4
	.uleb128 .LVL25-.LVL14
	.uleb128 .LVL26-.LVL14
	.uleb128 0x6
	.byte	0x61
	.byte	0x93
	.uleb128 0x8
	.byte	0x65
	.byte	0x93
	.uleb128 0x8
	.byte	0
.LVUS15:
	.uleb128 .LVU45
	.uleb128 .LVU50
	.uleb128 .LVU50
	.uleb128 .LVU80
	.uleb128 .LVU90
	.uleb128 0
.LLST15:
	.byte	0x6
	.quad	.LVL14
	.byte	0x4
	.uleb128 .LVL14-.LVL14
	.uleb128 .LVL15-.LVL14
	.uleb128 0x2
	.byte	0x30
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL15-.LVL14
	.uleb128 .LVL26-.LVL14
	.uleb128 0x1
	.byte	0x5d
	.byte	0x4
	.uleb128 .LVL30-.LVL14
	.uleb128 .LFE4-.LVL14
	.uleb128 0x1
	.byte	0x5d
	.byte	0
.LVUS17:
	.uleb128 .LVU53
	.uleb128 .LVU55
	.uleb128 .LVU90
	.uleb128 .LVU91
.LLST17:
	.byte	0x6
	.quad	.LVL17
	.byte	0x4
	.uleb128 .LVL17-.LVL17
	.uleb128 .LVL18-.LVL17
	.uleb128 0x8
	.byte	0x73
	.sleb128 0
	.byte	0x93
	.uleb128 0x8
	.byte	0x73
	.sleb128 8
	.byte	0x93
	.uleb128 0x8
	.byte	0x4
	.uleb128 .LVL30-.LVL17
	.uleb128 .LVL31-1-.LVL17
	.uleb128 0x8
	.byte	0x73
	.sleb128 0
	.byte	0x93
	.uleb128 0x8
	.byte	0x73
	.sleb128 8
	.byte	0x93
	.uleb128 0x8
	.byte	0
.Ldebug_loc3:
	.section	.debug_aranges,"",@progbits
	.long	0x2c
	.value	0x2
	.long	.Ldebug_info0
	.byte	0x8
	.byte	0
	.value	0
	.value	0
	.quad	.LFB4
	.quad	.LFE4-.LFB4
	.quad	0
	.quad	0
	.section	.debug_rnglists,"",@progbits
.Ldebug_ranges0:
	.long	.Ldebug_ranges3-.Ldebug_ranges2
.Ldebug_ranges2:
	.value	0x5
	.byte	0x8
	.byte	0
	.long	0
.LLRL0:
	.byte	0x5
	.quad	.LBB23
	.byte	0x4
	.uleb128 .LBB23-.LBB23
	.uleb128 .LBE23-.LBB23
	.byte	0x4
	.uleb128 .LBB49-.LBB23
	.uleb128 .LBE49-.LBB23
	.byte	0x4
	.uleb128 .LBB51-.LBB23
	.uleb128 .LBE51-.LBB23
	.byte	0
.LLRL3:
	.byte	0x5
	.quad	.LBB24
	.byte	0x4
	.uleb128 .LBB24-.LBB24
	.uleb128 .LBE24-.LBB24
	.byte	0x4
	.uleb128 .LBB27-.LBB24
	.uleb128 .LBE27-.LBB24
	.byte	0x4
	.uleb128 .LBB46-.LBB24
	.uleb128 .LBE46-.LBB24
	.byte	0
.LLRL8:
	.byte	0x5
	.quad	.LBB28
	.byte	0x4
	.uleb128 .LBB28-.LBB28
	.uleb128 .LBE28-.LBB28
	.byte	0x4
	.uleb128 .LBB47-.LBB28
	.uleb128 .LBE47-.LBB28
	.byte	0x4
	.uleb128 .LBB48-.LBB28
	.uleb128 .LBE48-.LBB28
	.byte	0
.LLRL10:
	.byte	0x5
	.quad	.LBB29
	.byte	0x4
	.uleb128 .LBB29-.LBB29
	.uleb128 .LBE29-.LBB29
	.byte	0x4
	.uleb128 .LBB44-.LBB29
	.uleb128 .LBE44-.LBB29
	.byte	0x4
	.uleb128 .LBB45-.LBB29
	.uleb128 .LBE45-.LBB29
	.byte	0
.LLRL11:
	.byte	0x5
	.quad	.LBB30
	.byte	0x4
	.uleb128 .LBB30-.LBB30
	.uleb128 .LBE30-.LBB30
	.byte	0x4
	.uleb128 .LBB43-.LBB30
	.uleb128 .LBE43-.LBB30
	.byte	0
.LLRL13:
	.byte	0x5
	.quad	.LBB31
	.byte	0x4
	.uleb128 .LBB31-.LBB31
	.uleb128 .LBE31-.LBB31
	.byte	0x4
	.uleb128 .LBB39-.LBB31
	.uleb128 .LBE39-.LBB31
	.byte	0x4
	.uleb128 .LBB40-.LBB31
	.uleb128 .LBE40-.LBB31
	.byte	0x4
	.uleb128 .LBB41-.LBB31
	.uleb128 .LBE41-.LBB31
	.byte	0x4
	.uleb128 .LBB42-.LBB31
	.uleb128 .LBE42-.LBB31
	.byte	0
.LLRL16:
	.byte	0x5
	.quad	.LBB33
	.byte	0x4
	.uleb128 .LBB33-.LBB33
	.uleb128 .LBE33-.LBB33
	.byte	0x4
	.uleb128 .LBB34-.LBB33
	.uleb128 .LBE34-.LBB33
	.byte	0
.LLRL19:
	.byte	0x7
	.quad	.LFB4
	.uleb128 .LFE4-.LFB4
	.byte	0
.Ldebug_ranges3:
	.section	.debug_line,"",@progbits
.Ldebug_line0:
	.section	.debug_str,"MS",@progbits,1
.LASF7:
	.string	"signed char"
.LASF12:
	.string	"complex double"
.LASF6:
	.string	"long unsigned int"
.LASF17:
	.string	"__muldc3"
.LASF10:
	.string	"char"
.LASF3:
	.string	"unsigned char"
.LASF16:
	.string	"main"
.LASF15:
	.string	"GNU C11 13.3.0 -mtune=generic -march=x86-64 -g -O2 -std=c11 -fno-asynchronous-unwind-tables"
.LASF2:
	.string	"double"
.LASF9:
	.string	"long int"
.LASF4:
	.string	"short unsigned int"
.LASF14:
	.string	"printf"
.LASF5:
	.string	"unsigned int"
.LASF11:
	.string	"float"
.LASF8:
	.string	"short int"
.LASF13:
	.string	"cexp"
	.section	.debug_line_str,"MS",@progbits,1
.LASF1:
	.string	"."
.LASF0:
	.string	"fft.c"
	.ident	"GCC: (GNU) 13.3.0"
	.section	.note.GNU-stack,"",@progbits
