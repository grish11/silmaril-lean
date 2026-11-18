	.file	"fft.c"
	.text
.Ltext0:
	.cfi_sections	.debug_frame
	.file 0 "." "fft.c"
	.type	fft, @function
fft:
.LFB0:
	.file 1 "fft.c"
	.loc 1 10 1
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$208, %rsp
	movq	%rdi, -200(%rbp)
	movl	%esi, -204(%rbp)
.LBB2:
	.loc 1 12 12
	movl	$1, -4(%rbp)
	.loc 1 12 19
	movl	$0, -8(%rbp)
	.loc 1 12 3
	jmp	.L2
.L6:
.LBB3:
	.loc 1 13 9
	movl	-204(%rbp), %eax
	sarl	%eax
	movl	%eax, -12(%rbp)
	.loc 1 14 5
	jmp	.L3
.L4:
	.loc 1 15 9
	movl	-12(%rbp), %eax
	xorl	%eax, -8(%rbp)
	.loc 1 14 25 discriminator 2
	sarl	-12(%rbp)
.L3:
	.loc 1 14 14 discriminator 1
	movl	-8(%rbp), %eax
	andl	-12(%rbp), %eax
	.loc 1 14 12 discriminator 1
	testl	%eax, %eax
	jne	.L4
	.loc 1 16 7
	movl	-12(%rbp), %eax
	xorl	%eax, -8(%rbp)
	.loc 1 17 8
	movl	-4(%rbp), %eax
	cmpl	-8(%rbp), %eax
	jge	.L5
.LBB4:
	.loc 1 18 27
	movl	-4(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	movq	-200(%rbp), %rax
	addq	%rdx, %rax
	movsd	(%rax), %xmm0
	movsd	%xmm0, -176(%rbp)
	movsd	8(%rax), %xmm0
	movsd	%xmm0, -184(%rbp)
	.loc 1 18 22
	movsd	-184(%rbp), %xmm0
	movsd	-176(%rbp), %xmm1
	movsd	%xmm1, -104(%rbp)
	movsd	%xmm0, -96(%rbp)
	.loc 1 19 15
	movl	-8(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	movq	-200(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 19 8
	movl	-4(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rcx
	movq	-200(%rbp), %rax
	addq	%rcx, %rax
	movsd	(%rdx), %xmm1
	movsd	8(%rdx), %xmm0
	.loc 1 19 12
	movsd	%xmm1, (%rax)
	movsd	%xmm0, 8(%rax)
	.loc 1 20 8
	movl	-8(%rbp), %eax
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	movq	-200(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 20 12
	movsd	-176(%rbp), %xmm0
	movsd	%xmm0, (%rax)
	movsd	-184(%rbp), %xmm0
	movsd	%xmm0, 8(%rax)
.L5:
.LBE4:
.LBE3:
	.loc 1 12 34 discriminator 2
	addl	$1, -4(%rbp)
.L2:
	.loc 1 12 28 discriminator 1
	movl	-4(%rbp), %eax
	cmpl	-204(%rbp), %eax
	jl	.L6
.LBE2:
.LBB5:
	.loc 1 24 12
	movl	$2, -16(%rbp)
	.loc 1 24 3
	jmp	.L7
.L12:
.LBB6:
	.loc 1 25 24
	pxor	%xmm0, %xmm0
	cvtsi2sdl	-16(%rbp), %xmm0
	movsd	.LC2(%rip), %xmm1
	movapd	%xmm1, %xmm2
	divsd	%xmm0, %xmm2
	movsd	.LC3(%rip), %xmm1
	divsd	%xmm0, %xmm1
	movapd	%xmm2, %xmm0
	call	cexp
	movq	%xmm0, %rax
	movapd	%xmm1, %xmm0
	movq	%rax, -40(%rbp)
	movsd	%xmm0, -32(%rbp)
	movsd	-40(%rbp), %xmm0
	movsd	%xmm0, -112(%rbp)
	movsd	-32(%rbp), %xmm0
	movsd	%xmm0, -120(%rbp)
.LBB7:
	.loc 1 26 14
	movl	$0, -20(%rbp)
	.loc 1 26 5
	jmp	.L8
.L11:
.LBB8:
	.loc 1 27 22
	movsd	.LC1(%rip), %xmm0
	movsd	%xmm0, -56(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -48(%rbp)
.LBB9:
	.loc 1 28 16
	movl	$0, -24(%rbp)
	.loc 1 28 7
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -136(%rbp)
	movsd	.LC1(%rip), %xmm0
	movsd	%xmm0, -128(%rbp)
	jmp	.L9
.L10:
.LBB10:
	.loc 1 29 32
	movl	-20(%rbp), %edx
	movl	-24(%rbp), %eax
	addl	%edx, %eax
	cltq
	.loc 1 29 29
	salq	$4, %rax
	movq	%rax, %rdx
	movq	-200(%rbp), %rax
	addq	%rdx, %rax
	movsd	(%rax), %xmm0
	movsd	%xmm0, -144(%rbp)
	movsd	8(%rax), %xmm0
	movsd	%xmm0, -152(%rbp)
	.loc 1 29 24
	movsd	-152(%rbp), %xmm0
	movsd	-144(%rbp), %xmm1
	movsd	%xmm1, -72(%rbp)
	movsd	%xmm0, -64(%rbp)
	.loc 1 30 32
	movl	-20(%rbp), %edx
	movl	-24(%rbp), %eax
	addl	%eax, %edx
	.loc 1 30 42
	movl	-16(%rbp), %eax
	movl	%eax, %ecx
	shrl	$31, %ecx
	addl	%ecx, %eax
	sarl	%eax
	.loc 1 30 36
	addl	%edx, %eax
	cltq
	.loc 1 30 29
	salq	$4, %rax
	movq	%rax, %rdx
	movq	-200(%rbp), %rax
	addq	%rdx, %rax
	movsd	(%rax), %xmm1
	movsd	8(%rax), %xmm2
	.loc 1 30 24
	movsd	-136(%rbp), %xmm0
	movq	-128(%rbp), %rax
	movapd	%xmm2, %xmm3
	movapd	%xmm1, %xmm2
	movapd	%xmm0, %xmm1
	movq	%rax, %xmm0
	call	__muldc3
	movq	%xmm0, %rax
	movapd	%xmm1, %xmm0
	movq	%rax, -88(%rbp)
	movsd	%xmm0, -80(%rbp)
	movsd	-88(%rbp), %xmm0
	movsd	%xmm0, -160(%rbp)
	movsd	-80(%rbp), %xmm0
	movsd	%xmm0, -168(%rbp)
	.loc 1 31 13
	movl	-20(%rbp), %edx
	movl	-24(%rbp), %eax
	addl	%edx, %eax
	cltq
	.loc 1 31 10
	salq	$4, %rax
	movq	%rax, %rdx
	movq	-200(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 31 22
	movsd	-144(%rbp), %xmm0
	movapd	%xmm0, %xmm1
	addsd	-160(%rbp), %xmm1
	movsd	-152(%rbp), %xmm0
	addsd	-168(%rbp), %xmm0
	.loc 1 31 18
	movsd	%xmm1, (%rax)
	movsd	%xmm0, 8(%rax)
	.loc 1 32 13
	movl	-20(%rbp), %edx
	movl	-24(%rbp), %eax
	addl	%eax, %edx
	.loc 1 32 23
	movl	-16(%rbp), %eax
	movl	%eax, %ecx
	shrl	$31, %ecx
	addl	%ecx, %eax
	sarl	%eax
	.loc 1 32 17
	addl	%edx, %eax
	cltq
	.loc 1 32 10
	salq	$4, %rax
	movq	%rax, %rdx
	movq	-200(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 32 32
	movsd	-144(%rbp), %xmm0
	movapd	%xmm0, %xmm1
	subsd	-160(%rbp), %xmm1
	movsd	-152(%rbp), %xmm0
	subsd	-168(%rbp), %xmm0
	.loc 1 32 28
	movsd	%xmm1, (%rax)
	movsd	%xmm0, 8(%rax)
	.loc 1 33 12
	movsd	-120(%rbp), %xmm2
	movsd	-112(%rbp), %xmm1
	movsd	-136(%rbp), %xmm0
	movq	-128(%rbp), %rax
	movapd	%xmm2, %xmm3
	movapd	%xmm1, %xmm2
	movapd	%xmm0, %xmm1
	movq	%rax, %xmm0
	call	__muldc3
	movq	%xmm0, %rax
	movapd	%xmm1, %xmm0
	movq	%rax, -56(%rbp)
	movsd	%xmm0, -48(%rbp)
	movsd	-56(%rbp), %xmm0
	movsd	%xmm0, -128(%rbp)
	movsd	-48(%rbp), %xmm0
	movsd	%xmm0, -136(%rbp)
.LBE10:
	.loc 1 28 37 discriminator 3
	addl	$1, -24(%rbp)
.L9:
	.loc 1 28 31 discriminator 1
	movl	-16(%rbp), %eax
	movl	%eax, %edx
	shrl	$31, %edx
	addl	%edx, %eax
	sarl	%eax
	.loc 1 28 25 discriminator 1
	cmpl	%eax, -24(%rbp)
	jl	.L10
.LBE9:
.LBE8:
	.loc 1 26 30 discriminator 2
	movl	-16(%rbp), %eax
	addl	%eax, -20(%rbp)
.L8:
	.loc 1 26 23 discriminator 1
	movl	-20(%rbp), %eax
	cmpl	-204(%rbp), %eax
	jl	.L11
.LBE7:
.LBE6:
	.loc 1 24 35 discriminator 2
	sall	-16(%rbp)
.L7:
	.loc 1 24 25 discriminator 1
	movl	-16(%rbp), %eax
	cmpl	-204(%rbp), %eax
	jle	.L12
.LBE5:
	.loc 1 37 1
	nop
	nop
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	fft, .-fft
	.section	.rodata
.LC4:
	.string	"%d: %+.3f %+.3fi\n"
	.text
	.globl	main
	.type	main, @function
main:
.LFB1:
	.loc 1 40 1
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$144, %rsp
	.loc 1 41 18
	movsd	.LC1(%rip), %xmm0
	movsd	%xmm0, -144(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -136(%rbp)
	movsd	.LC1(%rip), %xmm0
	movsd	%xmm0, -128(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -120(%rbp)
	movsd	.LC1(%rip), %xmm0
	movsd	%xmm0, -112(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -104(%rbp)
	movsd	.LC1(%rip), %xmm0
	movsd	%xmm0, -96(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -88(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -80(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -72(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -64(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -56(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -48(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -40(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -32(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -24(%rbp)
	.loc 1 42 3
	leaq	-144(%rbp), %rax
	movl	$8, %esi
	movq	%rax, %rdi
	call	fft
.LBB11:
	.loc 1 43 12
	movl	$0, -4(%rbp)
	.loc 1 43 3
	jmp	.L14
.L15:
	.loc 1 44 56
	movl	-4(%rbp), %eax
	cltq
	salq	$4, %rax
	addq	%rbp, %rax
	subq	$144, %rax
	movsd	8(%rax), %xmm1
	.loc 1 44 5
	pxor	%xmm0, %xmm0
	movapd	%xmm1, %xmm2
	addsd	%xmm0, %xmm2
	.loc 1 44 37
	movl	-4(%rbp), %eax
	cltq
	salq	$4, %rax
	addq	%rbp, %rax
	subq	$144, %rax
	movsd	(%rax), %xmm1
	.loc 1 44 5
	pxor	%xmm0, %xmm0
	addsd	%xmm0, %xmm1
	movq	%xmm1, %rdx
	movl	-4(%rbp), %eax
	movapd	%xmm2, %xmm1
	movq	%rdx, %xmm0
	movl	%eax, %esi
	movl	$.LC4, %edi
	movl	$2, %eax
	call	printf
	.loc 1 43 27 discriminator 3
	addl	$1, -4(%rbp)
.L14:
	.loc 1 43 21 discriminator 1
	cmpl	$7, -4(%rbp)
	jle	.L15
.LBE11:
	.loc 1 45 10
	movl	$0, %eax
	.loc 1 46 1
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1:
	.size	main, .-main
	.section	.rodata
	.align 8
.LC1:
	.long	0
	.long	1072693248
	.align 8
.LC2:
	.long	0
	.long	-2147483648
	.align 8
.LC3:
	.long	1413754136
	.long	-1072094725
	.text
.Letext0:
	.file 2 "/usr/include/stdio.h"
	.file 3 "/usr/include/x86_64-linux-gnu/bits/cmathcalls.h"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0x284
	.value	0x5
	.byte	0x1
	.byte	0x8
	.long	.Ldebug_abbrev0
	.uleb128 0x7
	.long	.LASF15
	.byte	0x1d
	.long	.LASF0
	.long	.LASF1
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.long	.Ldebug_line0
	.uleb128 0x2
	.byte	0x1
	.byte	0x8
	.long	.LASF2
	.uleb128 0x2
	.byte	0x2
	.byte	0x7
	.long	.LASF3
	.uleb128 0x2
	.byte	0x4
	.byte	0x7
	.long	.LASF4
	.uleb128 0x2
	.byte	0x8
	.byte	0x7
	.long	.LASF5
	.uleb128 0x2
	.byte	0x1
	.byte	0x6
	.long	.LASF6
	.uleb128 0x2
	.byte	0x2
	.byte	0x5
	.long	.LASF7
	.uleb128 0x8
	.byte	0x4
	.byte	0x5
	.string	"int"
	.uleb128 0x2
	.byte	0x8
	.byte	0x5
	.long	.LASF8
	.uleb128 0x2
	.byte	0x1
	.byte	0x6
	.long	.LASF9
	.uleb128 0x9
	.long	0x66
	.uleb128 0x2
	.byte	0x4
	.byte	0x4
	.long	.LASF10
	.uleb128 0x2
	.byte	0x8
	.byte	0x4
	.long	.LASF11
	.uleb128 0xa
	.long	.LASF12
	.byte	0x2
	.value	0x164
	.byte	0xc
	.long	0x58
	.long	0x98
	.uleb128 0x4
	.long	0x98
	.uleb128 0xb
	.byte	0
	.uleb128 0x5
	.long	0x6d
	.uleb128 0xc
	.long	.LASF13
	.byte	0x3
	.byte	0x59
	.byte	0x1
	.long	0xb3
	.long	0xb3
	.uleb128 0x4
	.long	0xb3
	.byte	0
	.uleb128 0x2
	.byte	0x10
	.byte	0x3
	.long	.LASF14
	.uleb128 0xd
	.long	.LASF16
	.byte	0x1
	.byte	0x27
	.byte	0x5
	.long	0x58
	.quad	.LFB1
	.quad	.LFE1-.LFB1
	.uleb128 0x1
	.byte	0x9c
	.long	0x108
	.uleb128 0x1
	.string	"x"
	.byte	0x29
	.byte	0x12
	.long	0x108
	.uleb128 0x3
	.byte	0x91
	.sleb128 -160
	.uleb128 0x3
	.quad	.LBB11
	.quad	.LBE11-.LBB11
	.uleb128 0x1
	.string	"i"
	.byte	0x2b
	.byte	0xc
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -20
	.byte	0
	.byte	0
	.uleb128 0xe
	.long	0xb3
	.long	0x118
	.uleb128 0xf
	.long	0x43
	.byte	0x7
	.byte	0
	.uleb128 0x10
	.string	"fft"
	.byte	0x1
	.byte	0x9
	.byte	0xd
	.quad	.LFB0
	.quad	.LFE0-.LFB0
	.uleb128 0x1
	.byte	0x9c
	.long	0x282
	.uleb128 0x6
	.string	"x"
	.byte	0x21
	.long	0x282
	.uleb128 0x3
	.byte	0x91
	.sleb128 -216
	.uleb128 0x6
	.string	"n"
	.byte	0x28
	.long	0x58
	.uleb128 0x3
	.byte	0x91
	.sleb128 -220
	.uleb128 0x11
	.quad	.LBB2
	.quad	.LBE2-.LBB2
	.long	0x1bb
	.uleb128 0x1
	.string	"i"
	.byte	0xc
	.byte	0xc
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -20
	.uleb128 0x1
	.string	"j"
	.byte	0xc
	.byte	0x13
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x3
	.quad	.LBB3
	.quad	.LBE3-.LBB3
	.uleb128 0x1
	.string	"bit"
	.byte	0xd
	.byte	0x9
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -28
	.uleb128 0x3
	.quad	.LBB4
	.quad	.LBE4-.LBB4
	.uleb128 0x1
	.string	"t"
	.byte	0x12
	.byte	0x16
	.long	0xb3
	.uleb128 0x3
	.byte	0x91
	.sleb128 -120
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x3
	.quad	.LBB5
	.quad	.LBE5-.LBB5
	.uleb128 0x1
	.string	"len"
	.byte	0x18
	.byte	0xc
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.uleb128 0x3
	.quad	.LBB6
	.quad	.LBE6-.LBB6
	.uleb128 0x1
	.string	"w"
	.byte	0x19
	.byte	0x14
	.long	0xb3
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0x3
	.quad	.LBB7
	.quad	.LBE7-.LBB7
	.uleb128 0x1
	.string	"i"
	.byte	0x1a
	.byte	0xe
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -36
	.uleb128 0x3
	.quad	.LBB8
	.quad	.LBE8-.LBB8
	.uleb128 0x1
	.string	"wk"
	.byte	0x1b
	.byte	0x16
	.long	0xb3
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.uleb128 0x3
	.quad	.LBB9
	.quad	.LBE9-.LBB9
	.uleb128 0x1
	.string	"k"
	.byte	0x1c
	.byte	0x10
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x3
	.quad	.LBB10
	.quad	.LBE10-.LBB10
	.uleb128 0x1
	.string	"u"
	.byte	0x1d
	.byte	0x18
	.long	0xb3
	.uleb128 0x3
	.byte	0x91
	.sleb128 -88
	.uleb128 0x1
	.string	"v"
	.byte	0x1e
	.byte	0x18
	.long	0xb3
	.uleb128 0x3
	.byte	0x91
	.sleb128 -104
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x5
	.long	0xb3
	.byte	0
	.section	.debug_abbrev,"",@progbits
.Ldebug_abbrev0:
	.uleb128 0x1
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
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x2
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
	.uleb128 0x3
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.byte	0
	.byte	0
	.uleb128 0x4
	.uleb128 0x5
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x5
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x6
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
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x7
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
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x10
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x8
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
	.uleb128 0x9
	.uleb128 0x26
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xa
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
	.uleb128 0xb
	.uleb128 0x18
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0xc
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
	.uleb128 0xd
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
	.uleb128 0x7c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xe
	.uleb128 0x1
	.byte	0x1
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xf
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x10
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
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x11
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
	.byte	0
	.section	.debug_aranges,"",@progbits
	.long	0x2c
	.value	0x2
	.long	.Ldebug_info0
	.byte	0x8
	.byte	0
	.value	0
	.value	0
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.quad	0
	.quad	0
	.section	.debug_line,"",@progbits
.Ldebug_line0:
	.section	.debug_str,"MS",@progbits,1
.LASF6:
	.string	"signed char"
.LASF14:
	.string	"complex double"
.LASF5:
	.string	"long unsigned int"
.LASF9:
	.string	"char"
.LASF2:
	.string	"unsigned char"
.LASF16:
	.string	"main"
.LASF8:
	.string	"long int"
.LASF15:
	.string	"GNU C11 13.3.0 -mtune=generic -march=x86-64 -g -O0 -std=c11 -fno-asynchronous-unwind-tables"
.LASF11:
	.string	"double"
.LASF3:
	.string	"short unsigned int"
.LASF12:
	.string	"printf"
.LASF10:
	.string	"float"
.LASF7:
	.string	"short int"
.LASF4:
	.string	"unsigned int"
.LASF13:
	.string	"cexp"
	.section	.debug_line_str,"MS",@progbits,1
.LASF1:
	.string	"."
.LASF0:
	.string	"fft.c"
	.ident	"GCC: (GNU) 13.3.0"
	.section	.note.GNU-stack,"",@progbits
