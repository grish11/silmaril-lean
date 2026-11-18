	.file	"msort.c"
	.text
.Ltext0:
	.cfi_sections	.debug_frame
	.file 0 "." "msort.c"
	.type	merge, @function
merge:
.LFB0:
	.file 1 "msort.c"
	.loc 1 5 1
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
	movl	%edx, -36(%rbp)
	movl	%ecx, -40(%rbp)
	movl	%r8d, -44(%rbp)
	.loc 1 6 7
	movl	-36(%rbp), %eax
	movl	%eax, -4(%rbp)
	.loc 1 6 15
	movl	-40(%rbp), %eax
	movl	%eax, -8(%rbp)
	.loc 1 6 24
	movl	-36(%rbp), %eax
	movl	%eax, -12(%rbp)
	.loc 1 7 9
	jmp	.L2
.L6:
	.loc 1 8 18
	movl	-4(%rbp), %eax
	cltq
	leaq	0(,%rax,4), %rdx
	movq	-24(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %edx
	.loc 1 8 26
	movl	-8(%rbp), %eax
	cltq
	leaq	0(,%rax,4), %rcx
	movq	-24(%rbp), %rax
	addq	%rcx, %rax
	movl	(%rax), %eax
	.loc 1 8 40
	cmpl	%eax, %edx
	jg	.L3
	.loc 1 8 36 discriminator 1
	movl	-4(%rbp), %eax
	leal	1(%rax), %edx
	movl	%edx, -4(%rbp)
	cltq
	.loc 1 8 34 discriminator 1
	leaq	0(,%rax,4), %rdx
	movq	-24(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 8 40 discriminator 1
	movl	(%rax), %eax
	jmp	.L4
.L3:
	.loc 1 8 45 discriminator 2
	movl	-8(%rbp), %eax
	leal	1(%rax), %edx
	movl	%edx, -8(%rbp)
	cltq
	.loc 1 8 43 discriminator 2
	leaq	0(,%rax,4), %rdx
	movq	-24(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 8 40 discriminator 2
	movl	(%rax), %eax
.L4:
	.loc 1 8 10 discriminator 4
	movl	-12(%rbp), %edx
	leal	1(%rdx), %ecx
	movl	%ecx, -12(%rbp)
	movslq	%edx, %rdx
	.loc 1 8 8 discriminator 4
	leaq	0(,%rdx,4), %rcx
	movq	-32(%rbp), %rdx
	addq	%rcx, %rdx
	.loc 1 8 14 discriminator 4
	movl	%eax, (%rdx)
.L2:
	.loc 1 7 18
	movl	-4(%rbp), %eax
	cmpl	-40(%rbp), %eax
	jge	.L7
	.loc 1 7 18 is_stmt 0 discriminator 1
	movl	-8(%rbp), %eax
	cmpl	-44(%rbp), %eax
	jl	.L6
	.loc 1 9 9 is_stmt 1
	jmp	.L7
.L8:
	.loc 1 10 19
	movl	-4(%rbp), %eax
	leal	1(%rax), %edx
	movl	%edx, -4(%rbp)
	cltq
	.loc 1 10 17
	leaq	0(,%rax,4), %rdx
	movq	-24(%rbp), %rax
	leaq	(%rdx,%rax), %rcx
	.loc 1 10 10
	movl	-12(%rbp), %eax
	leal	1(%rax), %edx
	movl	%edx, -12(%rbp)
	cltq
	.loc 1 10 8
	leaq	0(,%rax,4), %rdx
	movq	-32(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 10 17
	movl	(%rcx), %eax
	.loc 1 10 14
	movl	%eax, (%rdx)
.L7:
	.loc 1 9 12
	movl	-4(%rbp), %eax
	cmpl	-40(%rbp), %eax
	jl	.L8
	.loc 1 11 9
	jmp	.L9
.L10:
	.loc 1 12 19
	movl	-8(%rbp), %eax
	leal	1(%rax), %edx
	movl	%edx, -8(%rbp)
	cltq
	.loc 1 12 17
	leaq	0(,%rax,4), %rdx
	movq	-24(%rbp), %rax
	leaq	(%rdx,%rax), %rcx
	.loc 1 12 10
	movl	-12(%rbp), %eax
	leal	1(%rax), %edx
	movl	%edx, -12(%rbp)
	cltq
	.loc 1 12 8
	leaq	0(,%rax,4), %rdx
	movq	-32(%rbp), %rax
	addq	%rax, %rdx
	.loc 1 12 17
	movl	(%rcx), %eax
	.loc 1 12 14
	movl	%eax, (%rdx)
.L9:
	.loc 1 11 12
	movl	-8(%rbp), %eax
	cmpl	-44(%rbp), %eax
	jl	.L10
	.loc 1 13 10
	movl	-36(%rbp), %eax
	movl	%eax, -12(%rbp)
	.loc 1 13 3
	jmp	.L11
.L12:
	.loc 1 14 15
	movl	-12(%rbp), %eax
	cltq
	leaq	0(,%rax,4), %rdx
	movq	-32(%rbp), %rax
	addq	%rdx, %rax
	.loc 1 14 6
	movl	-12(%rbp), %edx
	movslq	%edx, %rdx
	leaq	0(,%rdx,4), %rcx
	movq	-24(%rbp), %rdx
	addq	%rcx, %rdx
	.loc 1 14 15
	movl	(%rax), %eax
	.loc 1 14 10
	movl	%eax, (%rdx)
	.loc 1 13 25 discriminator 3
	addl	$1, -12(%rbp)
.L11:
	.loc 1 13 18 discriminator 1
	movl	-12(%rbp), %eax
	cmpl	-44(%rbp), %eax
	jl	.L12
	.loc 1 15 1
	nop
	nop
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	merge, .-merge
	.globl	msort
	.type	msort, @function
msort:
.LFB1:
	.loc 1 18 1
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$48, %rsp
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
	movl	%edx, -36(%rbp)
	movl	%ecx, -40(%rbp)
	.loc 1 19 10
	movl	-40(%rbp), %eax
	subl	-36(%rbp), %eax
	.loc 1 19 6
	cmpl	$1, %eax
	jle	.L16
	.loc 1 21 22
	movl	-40(%rbp), %eax
	subl	-36(%rbp), %eax
	.loc 1 21 28
	movl	%eax, %edx
	shrl	$31, %edx
	addl	%edx, %eax
	sarl	%eax
	movl	%eax, %edx
	.loc 1 21 7
	movl	-36(%rbp), %eax
	addl	%edx, %eax
	movl	%eax, -4(%rbp)
	.loc 1 22 3
	movl	-4(%rbp), %ecx
	movl	-36(%rbp), %edx
	movq	-32(%rbp), %rsi
	movq	-24(%rbp), %rax
	movq	%rax, %rdi
	call	msort
	.loc 1 23 3
	movl	-40(%rbp), %ecx
	movl	-4(%rbp), %edx
	movq	-32(%rbp), %rsi
	movq	-24(%rbp), %rax
	movq	%rax, %rdi
	call	msort
	.loc 1 24 3
	movl	-40(%rbp), %edi
	movl	-4(%rbp), %ecx
	movl	-36(%rbp), %edx
	movq	-32(%rbp), %rsi
	movq	-24(%rbp), %rax
	movl	%edi, %r8d
	movq	%rax, %rdi
	call	merge
	jmp	.L13
.L16:
	.loc 1 20 5
	nop
.L13:
	.loc 1 25 1
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1:
	.size	msort, .-msort
	.section	.rodata
.LC0:
	.string	"%d%c"
	.text
	.globl	main
	.type	main, @function
main:
.LFB2:
	.loc 1 28 1
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$80, %rsp
	.loc 1 29 7
	movl	$5, -48(%rbp)
	movl	$2, -44(%rbp)
	movl	$7, -40(%rbp)
	movl	$1, -36(%rbp)
	movl	$8, -32(%rbp)
	movl	$3, -28(%rbp)
	movl	$6, -24(%rbp)
	movl	$4, -20(%rbp)
	.loc 1 31 3
	leaq	-80(%rbp), %rsi
	leaq	-48(%rbp), %rax
	movl	$8, %ecx
	movl	$0, %edx
	movq	%rax, %rdi
	call	msort
.LBB2:
	.loc 1 32 12
	movl	$0, -4(%rbp)
	.loc 1 32 3
	jmp	.L18
.L21:
	.loc 1 33 5
	cmpl	$7, -4(%rbp)
	jne	.L19
	.loc 1 33 5 is_stmt 0 discriminator 1
	movl	$10, %edx
	jmp	.L20
.L19:
	.loc 1 33 5 discriminator 2
	movl	$32, %edx
.L20:
	.loc 1 33 5 discriminator 4
	movl	-4(%rbp), %eax
	cltq
	movl	-48(%rbp,%rax,4), %eax
	movl	%eax, %esi
	movl	$.LC0, %edi
	movl	$0, %eax
	call	printf
	.loc 1 32 27 is_stmt 1 discriminator 2
	addl	$1, -4(%rbp)
.L18:
	.loc 1 32 21 discriminator 1
	cmpl	$7, -4(%rbp)
	jle	.L21
.LBE2:
	.loc 1 34 10
	movl	$0, %eax
	.loc 1 35 1
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE2:
	.size	main, .-main
.Letext0:
	.file 2 "/usr/include/stdio.h"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0x1df
	.value	0x5
	.byte	0x1
	.byte	0x8
	.long	.Ldebug_abbrev0
	.uleb128 0x5
	.long	.LASF10
	.byte	0x1d
	.long	.LASF0
	.long	.LASF1
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.long	.Ldebug_line0
	.uleb128 0x2
	.byte	0x8
	.byte	0x7
	.long	.LASF2
	.uleb128 0x2
	.byte	0x4
	.byte	0x7
	.long	.LASF3
	.uleb128 0x2
	.byte	0x1
	.byte	0x8
	.long	.LASF4
	.uleb128 0x2
	.byte	0x2
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
	.uleb128 0x6
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
	.uleb128 0x7
	.long	0x66
	.uleb128 0x8
	.long	.LASF11
	.byte	0x2
	.value	0x164
	.byte	0xc
	.long	0x58
	.long	0x8a
	.uleb128 0x9
	.long	0x8a
	.uleb128 0xa
	.byte	0
	.uleb128 0x4
	.long	0x6d
	.uleb128 0xb
	.long	.LASF12
	.byte	0x1
	.byte	0x1b
	.byte	0x5
	.long	0x58
	.quad	.LFB2
	.quad	.LFE2-.LFB2
	.uleb128 0x1
	.byte	0x9c
	.long	0xeb
	.uleb128 0x3
	.string	"a"
	.byte	0x1d
	.byte	0x7
	.long	0xeb
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0x3
	.string	"tmp"
	.byte	0x1e
	.byte	0x7
	.long	0xeb
	.uleb128 0x3
	.byte	0x91
	.sleb128 -96
	.uleb128 0xc
	.quad	.LBB2
	.quad	.LBE2-.LBB2
	.uleb128 0x3
	.string	"i"
	.byte	0x20
	.byte	0xc
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -20
	.byte	0
	.byte	0
	.uleb128 0xd
	.long	0x58
	.long	0xfb
	.uleb128 0xe
	.long	0x2e
	.byte	0x7
	.byte	0
	.uleb128 0xf
	.long	.LASF13
	.byte	0x1
	.byte	0x11
	.byte	0x6
	.quad	.LFB1
	.quad	.LFE1-.LFB1
	.uleb128 0x1
	.byte	0x9c
	.long	0x15c
	.uleb128 0x1
	.string	"a"
	.byte	0x11
	.byte	0x11
	.long	0x15c
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x1
	.string	"tmp"
	.byte	0x11
	.byte	0x19
	.long	0x15c
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x1
	.string	"lo"
	.byte	0x11
	.byte	0x22
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -52
	.uleb128 0x1
	.string	"hi"
	.byte	0x11
	.byte	0x2a
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0x3
	.string	"mid"
	.byte	0x15
	.byte	0x7
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -20
	.byte	0
	.uleb128 0x4
	.long	0x58
	.uleb128 0x10
	.long	.LASF14
	.byte	0x1
	.byte	0x4
	.byte	0xd
	.quad	.LFB0
	.quad	.LFE0-.LFB0
	.uleb128 0x1
	.byte	0x9c
	.uleb128 0x1
	.string	"a"
	.byte	0x4
	.byte	0x18
	.long	0x15c
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x1
	.string	"tmp"
	.byte	0x4
	.byte	0x20
	.long	0x15c
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x1
	.string	"lo"
	.byte	0x4
	.byte	0x29
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -52
	.uleb128 0x1
	.string	"mid"
	.byte	0x4
	.byte	0x31
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0x1
	.string	"hi"
	.byte	0x4
	.byte	0x3a
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -60
	.uleb128 0x3
	.string	"i"
	.byte	0x6
	.byte	0x7
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -20
	.uleb128 0x3
	.string	"j"
	.byte	0x6
	.byte	0xf
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.uleb128 0x3
	.string	"k"
	.byte	0x6
	.byte	0x18
	.long	0x58
	.uleb128 0x2
	.byte	0x91
	.sleb128 -28
	.byte	0
	.byte	0
	.section	.debug_abbrev,"",@progbits
.Ldebug_abbrev0:
	.uleb128 0x1
	.uleb128 0x5
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
	.uleb128 0x4
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x5
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
	.uleb128 0x6
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
	.uleb128 0x7
	.uleb128 0x26
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x8
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
	.uleb128 0x9
	.uleb128 0x5
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xa
	.uleb128 0x18
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0xb
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
	.uleb128 0xc
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.byte	0
	.byte	0
	.uleb128 0xd
	.uleb128 0x1
	.byte	0x1
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xe
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0xf
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
	.uleb128 0x10
	.uleb128 0x2e
	.byte	0x1
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
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7a
	.uleb128 0x19
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
.LASF13:
	.string	"msort"
.LASF3:
	.string	"unsigned int"
.LASF2:
	.string	"long unsigned int"
.LASF9:
	.string	"char"
.LASF14:
	.string	"merge"
.LASF4:
	.string	"unsigned char"
.LASF12:
	.string	"main"
.LASF8:
	.string	"long int"
.LASF10:
	.string	"GNU C11 13.3.0 -mtune=generic -march=x86-64 -g -O0 -std=c11 -fno-asynchronous-unwind-tables"
.LASF5:
	.string	"short unsigned int"
.LASF11:
	.string	"printf"
.LASF7:
	.string	"short int"
.LASF6:
	.string	"signed char"
	.section	.debug_line_str,"MS",@progbits,1
.LASF0:
	.string	"msort.c"
.LASF1:
	.string	"."
	.ident	"GCC: (GNU) 13.3.0"
	.section	.note.GNU-stack,"",@progbits
