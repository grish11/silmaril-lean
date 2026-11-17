	.file	"msort.c"
	.text
.Ltext0:
	.cfi_sections	.debug_frame
	.file 0 "." "msort.c"
	.p2align 4
	.globl	msort
	.type	msort, @function
msort:
.LVL0:
.LFB4:
	.file 1 "msort.c"
	.loc 1 18 1 view -0
	.cfi_startproc
	.loc 1 19 3 view .LVU1
	.loc 1 18 1 is_stmt 0 view .LVU2
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	.loc 1 19 10 view .LVU3
	movl	%ecx, %r14d
	subl	%edx, %r14d
	.loc 1 18 1 view .LVU4
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset 3, -48
	.loc 1 19 6 view .LVU5
	cmpl	$1, %r14d
	jle	.L1
	.loc 1 21 28 view .LVU6
	sarl	%r14d
	movl	%ecx, %r12d
	.loc 1 21 3 is_stmt 1 view .LVU7
	movq	%rdi, %rbp
	movq	%rsi, %r13
	.loc 1 21 7 is_stmt 0 view .LVU8
	addl	%edx, %r14d
.LVL1:
	.loc 1 22 3 is_stmt 1 view .LVU9
	movl	%edx, %ebx
	movl	%r14d, %ecx
.LVL2:
	.loc 1 22 3 is_stmt 0 view .LVU10
	call	msort
.LVL3:
	.loc 1 23 3 is_stmt 1 view .LVU11
	movl	%r12d, %ecx
	movl	%r14d, %edx
	movq	%r13, %rsi
	movq	%rbp, %rdi
	call	msort
.LVL4:
	.loc 1 24 3 view .LVU12
.LBB4:
.LBI4:
	.loc 1 4 13 view .LVU13
.LBB5:
	.loc 1 6 3 view .LVU14
	.loc 1 7 3 view .LVU15
	.loc 1 7 18 view .LVU16
	cmpl	%r14d, %r12d
	jle	.L13
	leal	1(%rbx), %ecx
	.loc 1 6 15 is_stmt 0 view .LVU17
	movl	%r14d, %esi
	.loc 1 6 7 view .LVU18
	movl	%ebx, %edi
	movslq	%ecx, %rcx
	jmp	.L6
.LVL5:
	.p2align 4,,10
	.p2align 3
.L24:
	.loc 1 8 40 discriminator 1 view .LVU19
	movl	%eax, %edx
	.loc 1 8 36 discriminator 1 view .LVU20
	addl	$1, %edi
.LVL6:
	.loc 1 7 18 view .LVU21
	leaq	1(%rcx), %rax
	.loc 1 8 14 discriminator 4 view .LVU22
	movl	%edx, -4(%r13,%rcx,4)
	.loc 1 7 18 is_stmt 1 view .LVU23
	cmpl	%esi, %r12d
	jle	.L15
.L25:
	.loc 1 7 18 is_stmt 0 view .LVU24
	cmpl	%edi, %r14d
	jle	.L15
	.loc 1 7 18 view .LVU25
	movq	%rax, %rcx
.LVL7:
.L6:
	.loc 1 8 5 is_stmt 1 view .LVU26
	.loc 1 8 18 is_stmt 0 view .LVU27
	movslq	%edi, %rax
	.loc 1 8 26 view .LVU28
	movslq	%esi, %rdx
	.loc 1 8 18 view .LVU29
	movl	0(%rbp,%rax,4), %eax
	.loc 1 8 26 view .LVU30
	movl	0(%rbp,%rdx,4), %edx
	.loc 1 8 40 view .LVU31
	cmpl	%eax, %edx
	jge	.L24
.LVL8:
	.loc 1 8 45 discriminator 2 view .LVU32
	addl	$1, %esi
.LVL9:
	.loc 1 8 14 discriminator 4 view .LVU33
	movl	%edx, -4(%r13,%rcx,4)
	.loc 1 7 18 is_stmt 1 view .LVU34
	leaq	1(%rcx), %rax
	cmpl	%esi, %r12d
	jg	.L25
.L15:
	.loc 1 9 12 view .LVU35
	cmpl	%edi, %r14d
	jle	.L8
.LVL10:
.L3:
	.loc 1 9 12 is_stmt 0 view .LVU36
	movslq	%edi, %rax
	movl	%r14d, %r8d
	subl	%edi, %r8d
	leaq	0(%rbp,%rax,4), %r10
	movslq	%ecx, %rax
	leaq	0(%r13,%rax,4), %r9
	salq	$2, %r8
	.loc 1 6 7 view .LVU37
	xorl	%eax, %eax
.LVL11:
	.p2align 4,,10
	.p2align 3
.L9:
	.loc 1 10 5 is_stmt 1 view .LVU38
	.loc 1 10 17 is_stmt 0 view .LVU39
	movl	(%r10,%rax), %edx
	.loc 1 10 14 view .LVU40
	movl	%edx, (%r9,%rax)
	.loc 1 9 12 is_stmt 1 view .LVU41
	addq	$4, %rax
.LVL12:
	.loc 1 9 12 is_stmt 0 view .LVU42
	cmpq	%r8, %rax
	jne	.L9
	addl	%ecx, %r14d
.LVL13:
	.loc 1 9 12 view .LVU43
	movl	%r14d, %ecx
	subl	%edi, %ecx
.LVL14:
.L8:
	.loc 1 11 12 is_stmt 1 view .LVU44
	cmpl	%esi, %r12d
	jle	.L10
	.loc 1 11 12 is_stmt 0 view .LVU45
	movl	%r12d, %edi
	movslq	%esi, %rax
	movslq	%ecx, %rcx
	subl	%esi, %edi
	leaq	0(%r13,%rcx,4), %rcx
	leaq	0(%rbp,%rax,4), %rsi
.LVL15:
	.loc 1 11 12 view .LVU46
	xorl	%eax, %eax
.LVL16:
	.loc 1 11 12 view .LVU47
	salq	$2, %rdi
.LVL17:
	.p2align 4,,10
	.p2align 3
.L11:
	.loc 1 12 5 is_stmt 1 view .LVU48
	.loc 1 12 17 is_stmt 0 view .LVU49
	movl	(%rsi,%rax), %edx
	.loc 1 12 14 view .LVU50
	movl	%edx, (%rcx,%rax)
	.loc 1 11 12 is_stmt 1 view .LVU51
	addq	$4, %rax
	.loc 1 11 12 is_stmt 0 view .LVU52
	cmpq	%rdi, %rax
	jne	.L11
.LVL18:
.L10:
	.loc 1 13 18 is_stmt 1 discriminator 1 view .LVU53
	cmpl	%ebx, %r12d
	jle	.L1
	movslq	%ebx, %rax
.LVL19:
	.p2align 4,,10
	.p2align 3
.L12:
	.loc 1 14 5 view .LVU54
	.loc 1 14 15 is_stmt 0 view .LVU55
	movl	0(%r13,%rax,4), %edx
	.loc 1 14 10 view .LVU56
	movl	%edx, 0(%rbp,%rax,4)
	.loc 1 13 25 is_stmt 1 discriminator 3 view .LVU57
.LVL20:
	.loc 1 13 18 discriminator 1 view .LVU58
	addq	$1, %rax
.LVL21:
	.loc 1 13 18 is_stmt 0 discriminator 1 view .LVU59
	cmpl	%eax, %r12d
	jg	.L12
.LVL22:
.L1:
	.loc 1 13 18 discriminator 1 view .LVU60
.LBE5:
.LBE4:
	.loc 1 25 1 view .LVU61
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbp
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
.LVL23:
	.p2align 4,,10
	.p2align 3
.L13:
	.cfi_restore_state
.LBB7:
.LBB6:
	.loc 1 6 24 view .LVU62
	movl	%ebx, %ecx
	.loc 1 6 15 view .LVU63
	movl	%r14d, %esi
	.loc 1 6 7 view .LVU64
	movl	%ebx, %edi
	jmp	.L3
.LBE6:
.LBE7:
	.cfi_endproc
.LFE4:
	.size	msort, .-msort
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC2:
	.string	"%d%c"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB5:
	.loc 1 28 1 is_stmt 1 view -0
	.cfi_startproc
	.loc 1 29 3 view .LVU66
	.loc 1 28 1 is_stmt 0 view .LVU67
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	.loc 1 31 3 view .LVU68
	movl	$8, %ecx
	xorl	%edx, %edx
	.loc 1 28 1 view .LVU69
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	subq	$72, %rsp
	.cfi_def_cfa_offset 96
	.loc 1 29 7 view .LVU70
	movdqa	.LC0(%rip), %xmm0
	.loc 1 31 3 view .LVU71
	leaq	32(%rsp), %rsi
	movq	%rsp, %rdi
	leaq	28(%rsp), %rbp
	movq	%rsp, %rbx
	.loc 1 29 7 view .LVU72
	movaps	%xmm0, (%rsp)
	movdqa	.LC1(%rip), %xmm0
	movaps	%xmm0, 16(%rsp)
	.loc 1 30 3 is_stmt 1 view .LVU73
	.loc 1 31 3 view .LVU74
	call	msort
.LVL24:
	.loc 1 32 3 view .LVU75
.LBB8:
	.loc 1 32 8 view .LVU76
	.loc 1 32 21 discriminator 1 view .LVU77
	.loc 1 33 5 view .LVU78
	.p2align 4,,10
	.p2align 3
.L27:
	.loc 1 33 5 is_stmt 0 discriminator 4 view .LVU79
	movl	(%rbx), %esi
	movl	$32, %edx
	movl	$.LC2, %edi
	xorl	%eax, %eax
	.loc 1 33 5 view .LVU80
	addq	$4, %rbx
.LVL25:
	.loc 1 33 5 discriminator 4 view .LVU81
	call	printf
.LVL26:
	.loc 1 32 27 is_stmt 1 discriminator 2 view .LVU82
	.loc 1 32 21 discriminator 1 view .LVU83
	.loc 1 33 5 view .LVU84
	cmpq	%rbx, %rbp
	jne	.L27
	.loc 1 33 5 is_stmt 0 discriminator 4 view .LVU85
	movl	28(%rsp), %esi
	movl	$10, %edx
	movl	$.LC2, %edi
	xorl	%eax, %eax
	call	printf
.LVL27:
	.loc 1 32 27 is_stmt 1 discriminator 2 view .LVU86
	.loc 1 32 21 discriminator 1 view .LVU87
.LBE8:
	.loc 1 34 3 view .LVU88
	.loc 1 35 1 is_stmt 0 view .LVU89
	addq	$72, %rsp
	.cfi_def_cfa_offset 24
	xorl	%eax, %eax
	popq	%rbx
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE5:
	.size	main, .-main
	.section	.rodata.cst16,"aM",@progbits,16
	.align 16
.LC0:
	.long	5
	.long	2
	.long	7
	.long	1
	.align 16
.LC1:
	.long	8
	.long	3
	.long	6
	.long	4
	.text
.Letext0:
	.file 2 "/usr/include/stdio.h"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0x307
	.value	0x5
	.byte	0x1
	.byte	0x8
	.long	.Ldebug_abbrev0
	.uleb128 0xd
	.long	.LASF10
	.byte	0x1d
	.long	.LASF0
	.long	.LASF1
	.long	.LLRL15
	.quad	0
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
	.uleb128 0xe
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
	.uleb128 0xf
	.long	0x62
	.uleb128 0x10
	.long	.LASF11
	.byte	0x2
	.value	0x164
	.byte	0xc
	.long	0x54
	.long	0x86
	.uleb128 0x11
	.long	0x86
	.uleb128 0x12
	.byte	0
	.uleb128 0x9
	.long	0x69
	.uleb128 0x13
	.long	.LASF12
	.byte	0x1
	.byte	0x1b
	.byte	0x5
	.long	0x54
	.quad	.LFB5
	.quad	.LFE5-.LFB5
	.uleb128 0x1
	.byte	0x9c
	.long	0x157
	.uleb128 0xa
	.string	"a"
	.byte	0x1d
	.long	0x157
	.uleb128 0x3
	.byte	0x91
	.sleb128 -96
	.uleb128 0xa
	.string	"tmp"
	.byte	0x1e
	.long	0x157
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0x14
	.quad	.LBB8
	.quad	.LBE8-.LBB8
	.long	0x132
	.uleb128 0xb
	.string	"i"
	.byte	0x20
	.byte	0xc
	.long	0x54
	.long	.LLST14
	.long	.LVUS14
	.uleb128 0xc
	.quad	.LVL26
	.long	0x6e
	.long	0x111
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x9
	.byte	0x3
	.quad	.LC2
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x51
	.uleb128 0x2
	.byte	0x8
	.byte	0x20
	.byte	0
	.uleb128 0x6
	.quad	.LVL27
	.long	0x6e
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x9
	.byte	0x3
	.quad	.LC2
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x51
	.uleb128 0x1
	.byte	0x3a
	.byte	0
	.byte	0
	.uleb128 0x6
	.quad	.LVL24
	.long	0x167
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x73
	.sleb128 0
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x54
	.uleb128 0x2
	.byte	0x91
	.sleb128 -64
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x51
	.uleb128 0x1
	.byte	0x30
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x52
	.uleb128 0x1
	.byte	0x38
	.byte	0
	.byte	0
	.uleb128 0x15
	.long	0x54
	.long	0x167
	.uleb128 0x16
	.long	0x2a
	.byte	0x7
	.byte	0
	.uleb128 0x17
	.long	.LASF13
	.byte	0x1
	.byte	0x11
	.byte	0x6
	.quad	.LFB4
	.quad	.LFE4-.LFB4
	.uleb128 0x1
	.byte	0x9c
	.long	0x2b5
	.uleb128 0x5
	.string	"a"
	.byte	0x11
	.long	0x2b5
	.long	.LLST0
	.long	.LVUS0
	.uleb128 0x5
	.string	"tmp"
	.byte	0x19
	.long	0x2b5
	.long	.LLST1
	.long	.LVUS1
	.uleb128 0x5
	.string	"lo"
	.byte	0x22
	.long	0x54
	.long	.LLST2
	.long	.LVUS2
	.uleb128 0x5
	.string	"hi"
	.byte	0x2a
	.long	0x54
	.long	.LLST3
	.long	.LVUS3
	.uleb128 0xb
	.string	"mid"
	.byte	0x15
	.byte	0x7
	.long	0x54
	.long	.LLST4
	.long	.LVUS4
	.uleb128 0x18
	.long	0x2ba
	.quad	.LBI4
	.byte	.LVU13
	.long	.LLRL5
	.byte	0x1
	.byte	0x18
	.byte	0x3
	.long	0x264
	.uleb128 0x3
	.long	0x2e8
	.long	.LLST6
	.long	.LVUS6
	.uleb128 0x3
	.long	0x2de
	.long	.LLST7
	.long	.LVUS7
	.uleb128 0x3
	.long	0x2d5
	.long	.LLST8
	.long	.LVUS8
	.uleb128 0x3
	.long	0x2cb
	.long	.LLST9
	.long	.LVUS9
	.uleb128 0x3
	.long	0x2c3
	.long	.LLST10
	.long	.LVUS10
	.uleb128 0x19
	.long	.LLRL5
	.uleb128 0x7
	.long	0x2f1
	.long	.LLST11
	.long	.LVUS11
	.uleb128 0x7
	.long	0x2f9
	.long	.LLST12
	.long	.LVUS12
	.uleb128 0x7
	.long	0x301
	.long	.LLST13
	.long	.LVUS13
	.byte	0
	.byte	0
	.uleb128 0xc
	.quad	.LVL3
	.long	0x167
	.long	0x28e
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x76
	.sleb128 0
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x54
	.uleb128 0x2
	.byte	0x7d
	.sleb128 0
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x51
	.uleb128 0x2
	.byte	0x73
	.sleb128 0
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x52
	.uleb128 0x2
	.byte	0x7e
	.sleb128 0
	.byte	0
	.uleb128 0x6
	.quad	.LVL4
	.long	0x167
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x76
	.sleb128 0
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x54
	.uleb128 0x2
	.byte	0x7d
	.sleb128 0
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x51
	.uleb128 0x2
	.byte	0x7e
	.sleb128 0
	.uleb128 0x1
	.uleb128 0x1
	.byte	0x52
	.uleb128 0x2
	.byte	0x7c
	.sleb128 0
	.byte	0
	.byte	0
	.uleb128 0x9
	.long	0x54
	.uleb128 0x1a
	.long	.LASF14
	.byte	0x1
	.byte	0x4
	.byte	0xd
	.byte	0x1
	.uleb128 0x4
	.string	"a"
	.byte	0x18
	.long	0x2b5
	.uleb128 0x4
	.string	"tmp"
	.byte	0x20
	.long	0x2b5
	.uleb128 0x4
	.string	"lo"
	.byte	0x29
	.long	0x54
	.uleb128 0x4
	.string	"mid"
	.byte	0x31
	.long	0x54
	.uleb128 0x4
	.string	"hi"
	.byte	0x3a
	.long	0x54
	.uleb128 0x8
	.string	"i"
	.byte	0x7
	.long	0x54
	.uleb128 0x8
	.string	"j"
	.byte	0xf
	.long	0x54
	.uleb128 0x8
	.string	"k"
	.byte	0x18
	.long	0x54
	.byte	0
	.byte	0
	.section	.debug_abbrev,"",@progbits
.Ldebug_abbrev0:
	.uleb128 0x1
	.uleb128 0x49
	.byte	0
	.uleb128 0x2
	.uleb128 0x18
	.uleb128 0x7e
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
	.uleb128 0x4
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x21
	.sleb128 4
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x5
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x21
	.sleb128 17
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
	.uleb128 0x6
	.uleb128 0x48
	.byte	0x1
	.uleb128 0x7d
	.uleb128 0x1
	.uleb128 0x7f
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x7
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
	.uleb128 0x8
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x21
	.sleb128 6
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x9
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xa
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
	.uleb128 0x21
	.sleb128 7
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0xb
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
	.uleb128 0x17
	.uleb128 0x2137
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0xc
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
	.uleb128 0xd
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
	.uleb128 0xe
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
	.uleb128 0xf
	.uleb128 0x26
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x10
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
	.uleb128 0x11
	.uleb128 0x5
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x12
	.uleb128 0x18
	.byte	0
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
	.uleb128 0x14
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
	.uleb128 0x15
	.uleb128 0x1
	.byte	0x1
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x16
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x17
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
	.uleb128 0x7a
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x18
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
	.uleb128 0x19
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x55
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x1a
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
	.uleb128 0x20
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
.LVUS14:
	.uleb128 .LVU77
	.uleb128 .LVU79
	.uleb128 .LVU79
	.uleb128 .LVU81
	.uleb128 .LVU81
	.uleb128 .LVU83
	.uleb128 .LVU87
	.uleb128 0
.LLST14:
	.byte	0x6
	.quad	.LVL24
	.byte	0x4
	.uleb128 .LVL24-.LVL24
	.uleb128 .LVL24-.LVL24
	.uleb128 0x2
	.byte	0x30
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL24-.LVL24
	.uleb128 .LVL25-.LVL24
	.uleb128 0xa
	.byte	0x73
	.sleb128 0
	.byte	0x91
	.sleb128 0
	.byte	0x1c
	.byte	0x23
	.uleb128 0x60
	.byte	0x32
	.byte	0x25
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL25-.LVL24
	.uleb128 .LVL26-.LVL24
	.uleb128 0xa
	.byte	0x73
	.sleb128 0
	.byte	0x91
	.sleb128 0
	.byte	0x1c
	.byte	0x23
	.uleb128 0x5c
	.byte	0x32
	.byte	0x25
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL27-.LVL24
	.uleb128 .LFE5-.LVL24
	.uleb128 0x2
	.byte	0x38
	.byte	0x9f
	.byte	0
.LVUS0:
	.uleb128 0
	.uleb128 .LVU11
	.uleb128 .LVU11
	.uleb128 .LVU60
	.uleb128 .LVU60
	.uleb128 .LVU62
	.uleb128 .LVU62
	.uleb128 0
.LLST0:
	.byte	0x6
	.quad	.LVL0
	.byte	0x4
	.uleb128 .LVL0-.LVL0
	.uleb128 .LVL3-1-.LVL0
	.uleb128 0x1
	.byte	0x55
	.byte	0x4
	.uleb128 .LVL3-1-.LVL0
	.uleb128 .LVL22-.LVL0
	.uleb128 0x1
	.byte	0x56
	.byte	0x4
	.uleb128 .LVL22-.LVL0
	.uleb128 .LVL23-.LVL0
	.uleb128 0x4
	.byte	0xa3
	.uleb128 0x1
	.byte	0x55
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL23-.LVL0
	.uleb128 .LFE4-.LVL0
	.uleb128 0x1
	.byte	0x56
	.byte	0
.LVUS1:
	.uleb128 0
	.uleb128 .LVU11
	.uleb128 .LVU11
	.uleb128 .LVU60
	.uleb128 .LVU60
	.uleb128 .LVU62
	.uleb128 .LVU62
	.uleb128 0
.LLST1:
	.byte	0x6
	.quad	.LVL0
	.byte	0x4
	.uleb128 .LVL0-.LVL0
	.uleb128 .LVL3-1-.LVL0
	.uleb128 0x1
	.byte	0x54
	.byte	0x4
	.uleb128 .LVL3-1-.LVL0
	.uleb128 .LVL22-.LVL0
	.uleb128 0x1
	.byte	0x5d
	.byte	0x4
	.uleb128 .LVL22-.LVL0
	.uleb128 .LVL23-.LVL0
	.uleb128 0x4
	.byte	0xa3
	.uleb128 0x1
	.byte	0x54
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL23-.LVL0
	.uleb128 .LFE4-.LVL0
	.uleb128 0x1
	.byte	0x5d
	.byte	0
.LVUS2:
	.uleb128 0
	.uleb128 .LVU11
	.uleb128 .LVU11
	.uleb128 .LVU60
	.uleb128 .LVU60
	.uleb128 .LVU62
	.uleb128 .LVU62
	.uleb128 0
.LLST2:
	.byte	0x6
	.quad	.LVL0
	.byte	0x4
	.uleb128 .LVL0-.LVL0
	.uleb128 .LVL3-1-.LVL0
	.uleb128 0x1
	.byte	0x51
	.byte	0x4
	.uleb128 .LVL3-1-.LVL0
	.uleb128 .LVL22-.LVL0
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL22-.LVL0
	.uleb128 .LVL23-.LVL0
	.uleb128 0x4
	.byte	0xa3
	.uleb128 0x1
	.byte	0x51
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL23-.LVL0
	.uleb128 .LFE4-.LVL0
	.uleb128 0x1
	.byte	0x53
	.byte	0
.LVUS3:
	.uleb128 0
	.uleb128 .LVU10
	.uleb128 .LVU10
	.uleb128 .LVU60
	.uleb128 .LVU60
	.uleb128 .LVU62
	.uleb128 .LVU62
	.uleb128 0
.LLST3:
	.byte	0x6
	.quad	.LVL0
	.byte	0x4
	.uleb128 .LVL0-.LVL0
	.uleb128 .LVL2-.LVL0
	.uleb128 0x1
	.byte	0x52
	.byte	0x4
	.uleb128 .LVL2-.LVL0
	.uleb128 .LVL22-.LVL0
	.uleb128 0x1
	.byte	0x5c
	.byte	0x4
	.uleb128 .LVL22-.LVL0
	.uleb128 .LVL23-.LVL0
	.uleb128 0x4
	.byte	0xa3
	.uleb128 0x1
	.byte	0x52
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL23-.LVL0
	.uleb128 .LFE4-.LVL0
	.uleb128 0x1
	.byte	0x5c
	.byte	0
.LVUS4:
	.uleb128 .LVU9
	.uleb128 .LVU43
	.uleb128 .LVU43
	.uleb128 .LVU60
	.uleb128 .LVU62
	.uleb128 0
.LLST4:
	.byte	0x6
	.quad	.LVL1
	.byte	0x4
	.uleb128 .LVL1-.LVL1
	.uleb128 .LVL13-.LVL1
	.uleb128 0x1
	.byte	0x5e
	.byte	0x4
	.uleb128 .LVL13-.LVL1
	.uleb128 .LVL22-.LVL1
	.uleb128 0xb
	.byte	0x7c
	.sleb128 0
	.byte	0x73
	.sleb128 0
	.byte	0x1c
	.byte	0x31
	.byte	0x26
	.byte	0x73
	.sleb128 0
	.byte	0x22
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL23-.LVL1
	.uleb128 .LFE4-.LVL1
	.uleb128 0x1
	.byte	0x5e
	.byte	0
.LVUS6:
	.uleb128 .LVU13
	.uleb128 .LVU60
	.uleb128 .LVU62
	.uleb128 0
.LLST6:
	.byte	0x6
	.quad	.LVL4
	.byte	0x4
	.uleb128 .LVL4-.LVL4
	.uleb128 .LVL22-.LVL4
	.uleb128 0x1
	.byte	0x5c
	.byte	0x4
	.uleb128 .LVL23-.LVL4
	.uleb128 .LFE4-.LVL4
	.uleb128 0x1
	.byte	0x5c
	.byte	0
.LVUS7:
	.uleb128 .LVU13
	.uleb128 .LVU43
	.uleb128 .LVU43
	.uleb128 .LVU60
	.uleb128 .LVU62
	.uleb128 0
.LLST7:
	.byte	0x6
	.quad	.LVL4
	.byte	0x4
	.uleb128 .LVL4-.LVL4
	.uleb128 .LVL13-.LVL4
	.uleb128 0x1
	.byte	0x5e
	.byte	0x4
	.uleb128 .LVL13-.LVL4
	.uleb128 .LVL22-.LVL4
	.uleb128 0xb
	.byte	0x7c
	.sleb128 0
	.byte	0x73
	.sleb128 0
	.byte	0x1c
	.byte	0x31
	.byte	0x26
	.byte	0x73
	.sleb128 0
	.byte	0x22
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL23-.LVL4
	.uleb128 .LFE4-.LVL4
	.uleb128 0x1
	.byte	0x5e
	.byte	0
.LVUS8:
	.uleb128 .LVU13
	.uleb128 .LVU60
	.uleb128 .LVU62
	.uleb128 0
.LLST8:
	.byte	0x6
	.quad	.LVL4
	.byte	0x4
	.uleb128 .LVL4-.LVL4
	.uleb128 .LVL22-.LVL4
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL23-.LVL4
	.uleb128 .LFE4-.LVL4
	.uleb128 0x1
	.byte	0x53
	.byte	0
.LVUS9:
	.uleb128 .LVU13
	.uleb128 .LVU60
	.uleb128 .LVU62
	.uleb128 0
.LLST9:
	.byte	0x6
	.quad	.LVL4
	.byte	0x4
	.uleb128 .LVL4-.LVL4
	.uleb128 .LVL22-.LVL4
	.uleb128 0x1
	.byte	0x5d
	.byte	0x4
	.uleb128 .LVL23-.LVL4
	.uleb128 .LFE4-.LVL4
	.uleb128 0x1
	.byte	0x5d
	.byte	0
.LVUS10:
	.uleb128 .LVU13
	.uleb128 .LVU60
	.uleb128 .LVU62
	.uleb128 0
.LLST10:
	.byte	0x6
	.quad	.LVL4
	.byte	0x4
	.uleb128 .LVL4-.LVL4
	.uleb128 .LVL22-.LVL4
	.uleb128 0x1
	.byte	0x56
	.byte	0x4
	.uleb128 .LVL23-.LVL4
	.uleb128 .LFE4-.LVL4
	.uleb128 0x1
	.byte	0x56
	.byte	0
.LVUS11:
	.uleb128 .LVU15
	.uleb128 .LVU19
	.uleb128 .LVU19
	.uleb128 .LVU21
	.uleb128 .LVU21
	.uleb128 .LVU38
	.uleb128 .LVU38
	.uleb128 .LVU39
	.uleb128 .LVU39
	.uleb128 .LVU42
	.uleb128 .LVU42
	.uleb128 .LVU44
	.uleb128 .LVU62
	.uleb128 0
.LLST11:
	.byte	0x6
	.quad	.LVL4
	.byte	0x4
	.uleb128 .LVL4-.LVL4
	.uleb128 .LVL5-.LVL4
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL5-.LVL4
	.uleb128 .LVL6-.LVL4
	.uleb128 0x3
	.byte	0x75
	.sleb128 1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL6-.LVL4
	.uleb128 .LVL11-.LVL4
	.uleb128 0x1
	.byte	0x55
	.byte	0x4
	.uleb128 .LVL11-.LVL4
	.uleb128 .LVL11-.LVL4
	.uleb128 0x8
	.byte	0x70
	.sleb128 0
	.byte	0x32
	.byte	0x25
	.byte	0x75
	.sleb128 0
	.byte	0x22
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL11-.LVL4
	.uleb128 .LVL12-.LVL4
	.uleb128 0xa
	.byte	0x70
	.sleb128 0
	.byte	0x32
	.byte	0x25
	.byte	0x75
	.sleb128 0
	.byte	0x22
	.byte	0x23
	.uleb128 0x1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL12-.LVL4
	.uleb128 .LVL14-.LVL4
	.uleb128 0xa
	.byte	0x70
	.sleb128 -4
	.byte	0x32
	.byte	0x25
	.byte	0x75
	.sleb128 0
	.byte	0x22
	.byte	0x23
	.uleb128 0x1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL23-.LVL4
	.uleb128 .LFE4-.LVL4
	.uleb128 0x1
	.byte	0x53
	.byte	0
.LVUS12:
	.uleb128 .LVU15
	.uleb128 .LVU19
	.uleb128 .LVU19
	.uleb128 .LVU32
	.uleb128 .LVU32
	.uleb128 .LVU33
	.uleb128 .LVU33
	.uleb128 .LVU36
	.uleb128 .LVU44
	.uleb128 .LVU46
	.uleb128 .LVU46
	.uleb128 .LVU47
	.uleb128 .LVU62
	.uleb128 0
.LLST12:
	.byte	0x6
	.quad	.LVL4
	.byte	0x4
	.uleb128 .LVL4-.LVL4
	.uleb128 .LVL5-.LVL4
	.uleb128 0x1
	.byte	0x5e
	.byte	0x4
	.uleb128 .LVL5-.LVL4
	.uleb128 .LVL8-.LVL4
	.uleb128 0x1
	.byte	0x54
	.byte	0x4
	.uleb128 .LVL8-.LVL4
	.uleb128 .LVL9-.LVL4
	.uleb128 0x3
	.byte	0x74
	.sleb128 1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL9-.LVL4
	.uleb128 .LVL10-.LVL4
	.uleb128 0x1
	.byte	0x54
	.byte	0x4
	.uleb128 .LVL14-.LVL4
	.uleb128 .LVL15-.LVL4
	.uleb128 0x1
	.byte	0x54
	.byte	0x4
	.uleb128 .LVL15-.LVL4
	.uleb128 .LVL16-.LVL4
	.uleb128 0x1
	.byte	0x50
	.byte	0x4
	.uleb128 .LVL23-.LVL4
	.uleb128 .LFE4-.LVL4
	.uleb128 0x1
	.byte	0x5e
	.byte	0
.LVUS13:
	.uleb128 .LVU15
	.uleb128 .LVU19
	.uleb128 .LVU19
	.uleb128 .LVU21
	.uleb128 .LVU21
	.uleb128 .LVU26
	.uleb128 .LVU26
	.uleb128 .LVU33
	.uleb128 .LVU33
	.uleb128 .LVU38
	.uleb128 .LVU38
	.uleb128 .LVU39
	.uleb128 .LVU39
	.uleb128 .LVU42
	.uleb128 .LVU42
	.uleb128 .LVU43
	.uleb128 .LVU43
	.uleb128 .LVU44
	.uleb128 .LVU53
	.uleb128 .LVU54
	.uleb128 .LVU54
	.uleb128 .LVU58
	.uleb128 .LVU58
	.uleb128 .LVU59
	.uleb128 .LVU59
	.uleb128 .LVU60
	.uleb128 .LVU62
	.uleb128 0
.LLST13:
	.byte	0x6
	.quad	.LVL4
	.byte	0x4
	.uleb128 .LVL4-.LVL4
	.uleb128 .LVL5-.LVL4
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL5-.LVL4
	.uleb128 .LVL6-.LVL4
	.uleb128 0x3
	.byte	0x72
	.sleb128 -1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL6-.LVL4
	.uleb128 .LVL7-.LVL4
	.uleb128 0x1
	.byte	0x52
	.byte	0x4
	.uleb128 .LVL7-.LVL4
	.uleb128 .LVL9-.LVL4
	.uleb128 0x3
	.byte	0x72
	.sleb128 -1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL9-.LVL4
	.uleb128 .LVL11-.LVL4
	.uleb128 0x1
	.byte	0x52
	.byte	0x4
	.uleb128 .LVL11-.LVL4
	.uleb128 .LVL11-.LVL4
	.uleb128 0x8
	.byte	0x70
	.sleb128 0
	.byte	0x32
	.byte	0x25
	.byte	0x72
	.sleb128 0
	.byte	0x22
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL11-.LVL4
	.uleb128 .LVL12-.LVL4
	.uleb128 0xa
	.byte	0x70
	.sleb128 0
	.byte	0x32
	.byte	0x25
	.byte	0x72
	.sleb128 0
	.byte	0x22
	.byte	0x23
	.uleb128 0x1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL12-.LVL4
	.uleb128 .LVL13-.LVL4
	.uleb128 0xa
	.byte	0x70
	.sleb128 -4
	.byte	0x32
	.byte	0x25
	.byte	0x72
	.sleb128 0
	.byte	0x22
	.byte	0x23
	.uleb128 0x1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL13-.LVL4
	.uleb128 .LVL14-.LVL4
	.uleb128 0xd
	.byte	0x70
	.sleb128 -4
	.byte	0x32
	.byte	0x25
	.byte	0x75
	.sleb128 0
	.byte	0x1c
	.byte	0x7e
	.sleb128 0
	.byte	0x22
	.byte	0x23
	.uleb128 0x1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL18-.LVL4
	.uleb128 .LVL19-.LVL4
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL19-.LVL4
	.uleb128 .LVL20-.LVL4
	.uleb128 0x1
	.byte	0x50
	.byte	0x4
	.uleb128 .LVL20-.LVL4
	.uleb128 .LVL21-.LVL4
	.uleb128 0x3
	.byte	0x70
	.sleb128 1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL21-.LVL4
	.uleb128 .LVL22-.LVL4
	.uleb128 0x1
	.byte	0x50
	.byte	0x4
	.uleb128 .LVL23-.LVL4
	.uleb128 .LFE4-.LVL4
	.uleb128 0x1
	.byte	0x53
	.byte	0
.Ldebug_loc3:
	.section	.debug_aranges,"",@progbits
	.long	0x3c
	.value	0x2
	.long	.Ldebug_info0
	.byte	0x8
	.byte	0
	.value	0
	.value	0
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.quad	.LFB5
	.quad	.LFE5-.LFB5
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
.LLRL5:
	.byte	0x5
	.quad	.LBB4
	.byte	0x4
	.uleb128 .LBB4-.LBB4
	.uleb128 .LBE4-.LBB4
	.byte	0x4
	.uleb128 .LBB7-.LBB4
	.uleb128 .LBE7-.LBB4
	.byte	0
.LLRL15:
	.byte	0x7
	.quad	.Ltext0
	.uleb128 .Letext0-.Ltext0
	.byte	0x7
	.quad	.LFB5
	.uleb128 .LFE5-.LFB5
	.byte	0
.Ldebug_ranges3:
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
.LASF10:
	.string	"GNU C11 13.3.0 -mtune=generic -march=x86-64 -g -O2 -std=c11 -fno-asynchronous-unwind-tables"
.LASF8:
	.string	"long int"
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
