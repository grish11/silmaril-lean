	.file	"lisp.c"
	.text
.Ltext0:
	.cfi_sections	.debug_frame
	.file 0 "." "lisp.c"
	.p2align 4
	.type	read, @function
read:
.LFB9:
	.file 1 "lisp.c"
	.loc 1 33 1 view -0
	.cfi_startproc
	.loc 1 34 3 view .LVU1
	.loc 1 33 1 is_stmt 0 view .LVU2
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
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
	subq	$56, %rsp
	.cfi_def_cfa_offset 112
	.loc 1 34 10 discriminator 1 view .LVU3
	call	__ctype_b_loc
.LVL0:
	movq	p(%rip), %r14
	.loc 1 34 10 is_stmt 1 discriminator 1 view .LVU4
	movq	(%rax), %rdi
	movq	%rax, %rbx
	movzbl	(%r14), %edx
	movq	%rdx, %rax
	movzwl	(%rdi,%rdx,2), %edx
	testb	$32, %dh
	je	.L2
	leaq	1(%r14), %rcx
	.p2align 4,,10
	.p2align 3
.L3:
	.loc 1 34 38 discriminator 2 view .LVU5
	.loc 1 34 10 is_stmt 0 discriminator 1 view .LVU6
	movzbl	(%rcx), %edx
	.loc 1 34 39 discriminator 2 view .LVU7
	movq	%rcx, %r14
	.loc 1 34 10 is_stmt 1 discriminator 1 view .LVU8
	leaq	1(%rcx), %rcx
	movq	%rdx, %rax
	movzwl	(%rdi,%rdx,2), %edx
	testb	$32, %dh
	jne	.L3
	movq	%r14, p(%rip)
.L2:
	.loc 1 35 3 view .LVU9
	.loc 1 35 6 is_stmt 0 view .LVU10
	cmpb	$40, %al
	je	.L39
	.loc 1 45 3 is_stmt 1 view .LVU11
	.loc 1 45 6 is_stmt 0 discriminator 1 view .LVU12
	testb	$8, %dh
	jne	.L10
	.loc 1 51 57 is_stmt 1 discriminator 1 view .LVU13
	.loc 1 51 10 is_stmt 0 discriminator 1 view .LVU14
	movq	%r14, %rbx
	.loc 1 51 57 discriminator 1 view .LVU15
	xorl	%r8d, %r8d
	testb	%al, %al
	jne	.L11
	jmp	.L40
	.p2align 4,,10
	.p2align 3
.L15:
	.loc 1 51 71 is_stmt 1 discriminator 5 view .LVU16
	.loc 1 51 10 is_stmt 0 discriminator 1 view .LVU17
	movzbl	1(%rbx), %eax
	.loc 1 51 72 discriminator 5 view .LVU18
	addq	$1, %rbx
	.loc 1 51 57 is_stmt 1 discriminator 1 view .LVU19
	testb	%al, %al
	je	.L41
	.loc 1 51 17 is_stmt 0 discriminator 1 view .LVU20
	movzbl	%al, %edx
	movl	%ecx, %r8d
	.loc 1 51 72 discriminator 5 view .LVU21
	movq	%rbx, %rbp
	.loc 1 51 17 discriminator 1 view .LVU22
	movzwl	(%rdi,%rdx,2), %edx
.L11:
	.loc 1 51 44 discriminator 3 view .LVU23
	subl	$40, %eax
	cmpb	$1, %al
	seta	%al
	.loc 1 51 13 discriminator 1 view .LVU24
	shrw	$13, %dx
	xorl	$1, %edx
	.loc 1 51 57 discriminator 4 view .LVU25
	andb	%dl, %al
	movl	%eax, %ecx
	jne	.L15
	testb	%r8b, %r8b
	je	.L16
	movq	%rbp, p(%rip)
.L16:
	.loc 1 53 33 view .LVU26
	subq	%r14, %rbx
.L12:
	.loc 1 52 3 is_stmt 1 view .LVU27
.LVL1:
.LBB57:
.LBI57:
	.loc 1 14 14 view .LVU28
.LBB58:
	.loc 1 14 31 view .LVU29
	.loc 1 14 52 is_stmt 0 view .LVU30
	movslq	used(%rip), %r13
	leal	1(%r13), %eax
	movl	%eax, used(%rip)
	.loc 1 14 37 view .LVU31
	leaq	0(%r13,%r13,4), %rax
	salq	$3, %rax
	leaq	arena(%rax), %rsi
	.loc 1 14 64 view .LVU32
	movl	$1, arena(%rax)
.LBE58:
.LBE57:
.LBB60:
.LBB61:
.LBB62:
	.loc 1 24 21 discriminator 1 view .LVU33
	movslq	nnames(%rip), %rax
.LBE62:
.LBE61:
.LBE60:
.LBB66:
.LBB59:
	.loc 1 14 37 view .LVU34
	movq	%rsi, 8(%rsp)
.LVL2:
	.loc 1 14 57 is_stmt 1 view .LVU35
	.loc 1 14 69 view .LVU36
	.loc 1 14 69 is_stmt 0 view .LVU37
.LBE59:
.LBE66:
	.loc 1 53 3 is_stmt 1 view .LVU38
.LBB67:
.LBI60:
	.loc 1 22 20 view .LVU39
.LBB64:
	.loc 1 24 3 view .LVU40
.LBB63:
	.loc 1 24 8 view .LVU41
	.loc 1 24 21 discriminator 1 view .LVU42
	movl	%eax, 20(%rsp)
	testl	%eax, %eax
	jle	.L42
	movslq	20(%rsp), %rax
	movl	$names, %r15d
	movq	%rax, %r12
	movq	%rax, 24(%rsp)
	salq	$4, %r12
	addq	%r15, %r12
	jmp	.L20
.LVL3:
	.p2align 4,,10
	.p2align 3
.L18:
	.loc 1 24 32 discriminator 2 view .LVU43
	.loc 1 24 21 discriminator 1 view .LVU44
	addq	$16, %r15
	cmpq	%r12, %r15
	je	.L17
.LVL4:
.L20:
	.loc 1 25 5 view .LVU45
	.loc 1 25 9 is_stmt 0 view .LVU46
	movq	%r15, %rdi
	.loc 1 25 21 view .LVU47
	movq	%r15, %rbp
	.loc 1 25 9 view .LVU48
	call	strlen
.LVL5:
	.loc 1 25 8 discriminator 1 view .LVU49
	cmpq	%rbx, %rax
	jne	.L18
	.loc 1 25 35 discriminator 1 view .LVU50
	movq	%rbx, %rdx
	movq	%r14, %rsi
	movq	%r15, %rdi
	call	strncmp
.LVL6:
	.loc 1 25 31 discriminator 1 view .LVU51
	testl	%eax, %eax
	jne	.L18
.LVL7:
.L19:
	.loc 1 25 31 discriminator 1 view .LVU52
.LBE63:
.LBE64:
.LBE67:
	.loc 1 53 10 discriminator 1 view .LVU53
	leaq	0(%r13,%r13,4), %rax
	movq	%rbp, arena+16(,%rax,8)
	.loc 1 54 3 is_stmt 1 view .LVU54
.LVL8:
.L1:
	.loc 1 55 1 is_stmt 0 view .LVU55
	movq	8(%rsp), %rax
	addq	$56, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
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
.LVL9:
.L42:
	.cfi_restore_state
	.loc 1 55 1 view .LVU56
	movq	%rax, 24(%rsp)
.LVL10:
	.p2align 4,,10
	.p2align 3
.L17:
.LBB68:
.LBB65:
	.loc 1 27 3 is_stmt 1 view .LVU57
	.loc 1 27 15 is_stmt 0 view .LVU58
	movq	24(%rsp), %rax
	.loc 1 27 3 view .LVU59
	movq	%r14, %rsi
	movq	%rbx, %rdx
	.loc 1 27 15 view .LVU60
	salq	$4, %rax
	leaq	names(%rax), %rbp
	.loc 1 27 3 view .LVU61
	movq	%rbp, %rdi
	call	memcpy
.LVL11:
	.loc 1 28 3 is_stmt 1 view .LVU62
	.loc 1 29 22 is_stmt 0 view .LVU63
	movl	20(%rsp), %r14d
.LVL12:
	.loc 1 28 20 view .LVU64
	movb	$0, 0(%rbp,%rbx)
	.loc 1 29 3 is_stmt 1 view .LVU65
	.loc 1 29 22 is_stmt 0 view .LVU66
	addl	$1, %r14d
	movl	%r14d, nnames(%rip)
	.loc 1 29 10 view .LVU67
	jmp	.L19
.LVL13:
	.p2align 4,,10
	.p2align 3
.L10:
	.loc 1 29 10 view .LVU68
	leaq	1(%r14), %rsi
.LBE65:
.LBE68:
.LBB69:
	.loc 1 46 10 view .LVU69
	xorl	%edx, %edx
	.p2align 4,,10
	.p2align 3
.L13:
.LVL14:
	.loc 1 47 40 is_stmt 1 discriminator 2 view .LVU70
	.loc 1 47 54 is_stmt 0 discriminator 2 view .LVU71
	movsbl	%al, %eax
	.loc 1 47 12 discriminator 1 view .LVU72
	movzbl	(%rsi), %ecx
	.loc 1 47 47 discriminator 2 view .LVU73
	leaq	(%rdx,%rdx,4), %rdx
.LVL15:
	.loc 1 47 56 discriminator 2 view .LVU74
	movq	%rsi, %r8
	.loc 1 47 59 discriminator 2 view .LVU75
	subl	$48, %eax
	.loc 1 47 12 discriminator 1 view .LVU76
	addq	$1, %rsi
	.loc 1 47 59 discriminator 2 view .LVU77
	cltq
	.loc 1 47 42 discriminator 2 view .LVU78
	leaq	(%rax,%rdx,2), %rdx
.LVL16:
	.loc 1 47 12 is_stmt 1 discriminator 1 view .LVU79
	movq	%rcx, %rax
	testb	$8, 1(%rdi,%rcx,2)
	jne	.L13
.LBB70:
.LBB71:
.LBB72:
.LBB73:
	.loc 1 14 52 is_stmt 0 view .LVU80
	movslq	used(%rip), %rax
	movq	%r8, p(%rip)
.LBE73:
.LBE72:
.LBE71:
.LBE70:
	.loc 1 48 5 is_stmt 1 view .LVU81
.LVL17:
.LBB79:
.LBI70:
	.loc 1 15 14 view .LVU82
.LBB78:
	.loc 1 15 28 view .LVU83
.LBB76:
.LBI72:
	.loc 1 14 14 view .LVU84
.LBB74:
	.loc 1 14 31 view .LVU85
	.loc 1 14 52 is_stmt 0 view .LVU86
	leal	1(%rax), %ecx
	.loc 1 14 37 view .LVU87
	leaq	(%rax,%rax,4), %rax
	salq	$3, %rax
	.loc 1 14 52 view .LVU88
	movl	%ecx, used(%rip)
	.loc 1 14 37 view .LVU89
	leaq	arena(%rax), %rsi
.LBE74:
.LBE76:
	.loc 1 15 54 discriminator 1 view .LVU90
	movq	%rdx, arena+8(%rax)
.LBB77:
.LBB75:
	.loc 1 14 37 view .LVU91
	movq	%rsi, 8(%rsp)
.LVL18:
	.loc 1 14 57 is_stmt 1 view .LVU92
	.loc 1 14 64 is_stmt 0 view .LVU93
	movl	$0, arena(%rax)
	.loc 1 14 69 is_stmt 1 view .LVU94
.LVL19:
	.loc 1 14 69 is_stmt 0 view .LVU95
.LBE75:
.LBE77:
	.loc 1 15 47 is_stmt 1 discriminator 1 view .LVU96
	.loc 1 15 59 discriminator 1 view .LVU97
	.loc 1 15 59 is_stmt 0 discriminator 1 view .LVU98
.LBE78:
.LBE79:
	.loc 1 48 12 view .LVU99
	jmp	.L1
.LVL20:
	.p2align 4,,10
	.p2align 3
.L39:
	.loc 1 48 12 view .LVU100
.LBE69:
.LBB80:
	.loc 1 36 5 is_stmt 1 view .LVU101
	.loc 1 36 6 is_stmt 0 view .LVU102
	leaq	1(%r14), %rsi
	.loc 1 37 26 view .LVU103
	leaq	40(%rsp), %rbp
	.loc 1 37 11 view .LVU104
	movq	$nil, 40(%rsp)
	.loc 1 36 6 view .LVU105
	movq	%rsi, p(%rip)
	.loc 1 37 5 is_stmt 1 view .LVU106
.LVL21:
	.p2align 4,,10
	.p2align 3
.L5:
	.loc 1 39 14 discriminator 1 view .LVU107
	movzbl	(%rsi), %edx
	testb	$32, 1(%rdi,%rdx,2)
	jne	.L6
.L44:
	.loc 1 40 7 view .LVU108
	.loc 1 40 10 is_stmt 0 view .LVU109
	cmpb	$41, %dl
	je	.L43
	.loc 1 41 7 is_stmt 1 view .LVU110
	.loc 1 41 15 is_stmt 0 view .LVU111
	call	read
.LVL22:
	.loc 1 39 14 discriminator 1 view .LVU112
	movq	(%rbx), %rdi
	.loc 1 41 15 view .LVU113
	movq	%rax, %rsi
.LVL23:
.LBB81:
.LBI81:
	.loc 1 16 14 is_stmt 1 view .LVU114
.LBB82:
	.loc 1 16 39 view .LVU115
.LBB83:
.LBI83:
	.loc 1 14 14 view .LVU116
.LBB84:
	.loc 1 14 31 view .LVU117
	.loc 1 14 52 is_stmt 0 view .LVU118
	movslq	used(%rip), %rax
.LVL24:
	.loc 1 14 52 view .LVU119
	leal	1(%rax), %edx
	leaq	(%rax,%rax,4), %rcx
	movl	%edx, used(%rip)
	leaq	0(,%rcx,8), %rdx
.LVL25:
	.loc 1 14 57 is_stmt 1 view .LVU120
.LBE84:
.LBE83:
	.loc 1 16 66 is_stmt 0 discriminator 1 view .LVU121
	movq	%rsi, arena+24(%rdx)
.LBE82:
.LBE81:
	.loc 1 39 14 discriminator 1 view .LVU122
	movq	p(%rip), %rsi
.LVL26:
.LBB90:
.LBB89:
.LBB87:
.LBB85:
	.loc 1 14 64 view .LVU123
	leaq	arena(%rdx), %rax
.LVL27:
	.loc 1 14 64 view .LVU124
	movl	$2, arena(,%rcx,8)
	.loc 1 14 69 is_stmt 1 view .LVU125
.LVL28:
	.loc 1 14 69 is_stmt 0 view .LVU126
.LBE85:
.LBE87:
	.loc 1 16 59 is_stmt 1 discriminator 1 view .LVU127
	.loc 1 16 71 discriminator 1 view .LVU128
	.loc 1 16 78 is_stmt 0 discriminator 1 view .LVU129
	movq	$nil, arena+32(%rdx)
	.loc 1 16 83 is_stmt 1 discriminator 1 view .LVU130
.LVL29:
.LBB88:
.LBB86:
	.loc 1 14 37 is_stmt 0 view .LVU131
	movq	%rax, 0(%rbp)
.LBE86:
.LBE88:
.LBE89:
.LBE90:
	.loc 1 42 7 is_stmt 1 view .LVU132
	.loc 1 42 12 is_stmt 0 view .LVU133
	leaq	arena+32(%rdx), %rbp
.LVL30:
	.loc 1 38 5 is_stmt 1 view .LVU134
	.loc 1 39 14 discriminator 1 view .LVU135
	movzbl	(%rsi), %edx
	testb	$32, 1(%rdi,%rdx,2)
	je	.L44
.LVL31:
.L6:
	.loc 1 39 42 discriminator 2 view .LVU136
	.loc 1 39 43 is_stmt 0 discriminator 2 view .LVU137
	addq	$1, %rsi
	movq	%rsi, p(%rip)
	jmp	.L5
	.p2align 4,,10
	.p2align 3
.L43:
	.loc 1 40 24 is_stmt 1 discriminator 1 view .LVU138
	.loc 1 40 36 is_stmt 0 discriminator 1 view .LVU139
	movq	40(%rsp), %rax
	.loc 1 40 25 discriminator 1 view .LVU140
	addq	$1, %rsi
	movq	%rsi, p(%rip)
	.loc 1 40 29 is_stmt 1 discriminator 1 view .LVU141
	.loc 1 40 36 is_stmt 0 discriminator 1 view .LVU142
	movq	%rax, 8(%rsp)
	jmp	.L1
.LVL32:
	.p2align 4,,10
	.p2align 3
.L41:
	.loc 1 40 36 discriminator 1 view .LVU143
	movq	%rbx, p(%rip)
.LBE80:
	.loc 1 53 33 view .LVU144
	subq	%r14, %rbx
	jmp	.L12
.L40:
	.loc 1 51 57 discriminator 1 view .LVU145
	xorl	%ebx, %ebx
	jmp	.L12
	.cfi_endproc
.LFE9:
	.size	read, .-read
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC0:
	.string	"quote"
.LC1:
	.string	"car"
.LC2:
	.string	"cdr"
.LC3:
	.string	"cons"
	.text
	.p2align 4
	.type	eval, @function
eval:
.LVL33:
.LFB10:
	.loc 1 58 1 is_stmt 1 view -0
	.cfi_startproc
	.loc 1 59 3 view .LVU147
	.loc 1 59 6 is_stmt 0 view .LVU148
	cmpl	$2, (%rdi)
	jne	.L68
	.loc 1 58 1 view .LVU149
	pushq	%r12
	.cfi_def_cfa_offset 16
	.cfi_offset 12, -16
	pushq	%rbp
	.cfi_def_cfa_offset 24
	.cfi_offset 6, -24
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
.LVL34:
.L47:
	.loc 1 60 3 is_stmt 1 view .LVU150
	.loc 1 60 15 is_stmt 0 view .LVU151
	movq	24(%rdi), %rax
	.loc 1 61 9 view .LVU152
	movq	32(%rdi), %rbp
	.loc 1 62 8 view .LVU153
	movl	$.LC0, %esi
	.loc 1 60 15 view .LVU154
	movq	16(%rax), %rbx
.LVL35:
	.loc 1 61 3 is_stmt 1 view .LVU155
	.loc 1 62 3 view .LVU156
	.loc 1 62 8 is_stmt 0 view .LVU157
	movq	%rbx, %rdi
	call	strcmp
.LVL36:
	.loc 1 62 6 discriminator 1 view .LVU158
	testl	%eax, %eax
	je	.L69
	.loc 1 63 3 is_stmt 1 view .LVU159
	.loc 1 63 8 is_stmt 0 view .LVU160
	cmpb	$105, (%rbx)
	je	.L70
.L50:
	.loc 1 65 3 is_stmt 1 view .LVU161
	.loc 1 65 8 is_stmt 0 view .LVU162
	movl	$.LC1, %esi
	movq	%rbx, %rdi
	call	strcmp
.LVL37:
	.loc 1 65 6 discriminator 1 view .LVU163
	testl	%eax, %eax
	je	.L71
	.loc 1 66 3 is_stmt 1 view .LVU164
	.loc 1 66 8 is_stmt 0 view .LVU165
	movl	$.LC2, %esi
	movq	%rbx, %rdi
	call	strcmp
.LVL38:
	.loc 1 66 6 discriminator 1 view .LVU166
	testl	%eax, %eax
	je	.L72
	.loc 1 67 3 is_stmt 1 view .LVU167
	.loc 1 67 8 is_stmt 0 view .LVU168
	movl	$.LC3, %esi
	movq	%rbx, %rdi
	call	strcmp
.LVL39:
	.loc 1 67 6 discriminator 1 view .LVU169
	testl	%eax, %eax
	je	.L73
	.loc 1 68 3 is_stmt 1 view .LVU170
	.loc 1 68 15 is_stmt 0 view .LVU171
	movzbl	(%rbx), %eax
	subl	$42, %eax
	jne	.L56
	movzbl	1(%rbx), %eax
.L56:
	.loc 1 68 14 discriminator 1 view .LVU172
	xorl	%r12d, %r12d
	testl	%eax, %eax
	sete	%r12b
.LVL40:
	.loc 1 69 3 is_stmt 1 view .LVU173
	.loc 1 69 20 discriminator 1 view .LVU174
	cmpl	$2, 0(%rbp)
	jne	.L57
.LVL41:
.L60:
	.loc 1 70 5 view .LVU175
	.loc 1 70 53 is_stmt 0 view .LVU176
	cmpb	$42, (%rbx)
	.loc 1 70 41 discriminator 1 view .LVU177
	movq	24(%rbp), %rdi
	.loc 1 70 53 view .LVU178
	je	.L74
	.loc 1 70 61 discriminator 2 view .LVU179
	call	eval
.LVL42:
	.loc 1 70 53 discriminator 1 view .LVU180
	addq	8(%rax), %r12
.LVL43:
.L59:
	.loc 1 69 34 is_stmt 1 view .LVU181
	movq	32(%rbp), %rbp
.LVL44:
	.loc 1 69 20 discriminator 1 view .LVU182
	cmpl	$2, 0(%rbp)
	je	.L60
.LVL45:
.L57:
	.loc 1 71 3 view .LVU183
.LBB91:
.LBI91:
	.loc 1 15 14 view .LVU184
.LBB92:
	.loc 1 15 28 view .LVU185
.LBB93:
.LBI93:
	.loc 1 14 14 view .LVU186
.LBB94:
	.loc 1 14 31 view .LVU187
	.loc 1 14 52 is_stmt 0 view .LVU188
	movslq	used(%rip), %rax
	leal	1(%rax), %edx
	movl	%edx, used(%rip)
	.loc 1 14 37 view .LVU189
	leaq	(%rax,%rax,4), %rdx
	salq	$3, %rdx
	leaq	arena(%rdx), %rax
.LVL46:
	.loc 1 14 57 is_stmt 1 view .LVU190
	.loc 1 14 64 is_stmt 0 view .LVU191
	movl	$0, arena(%rdx)
	.loc 1 14 69 is_stmt 1 view .LVU192
.LVL47:
	.loc 1 14 69 is_stmt 0 view .LVU193
.LBE94:
.LBE93:
	.loc 1 15 47 is_stmt 1 discriminator 1 view .LVU194
	.loc 1 15 54 is_stmt 0 discriminator 1 view .LVU195
	movq	%r12, 8(%rax)
	.loc 1 15 59 is_stmt 1 discriminator 1 view .LVU196
.LVL48:
	.loc 1 15 59 is_stmt 0 discriminator 1 view .LVU197
.LBE92:
.LBE91:
	.loc 1 72 1 view .LVU198
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 24
.LVL49:
	.loc 1 72 1 view .LVU199
	popq	%rbp
	.cfi_def_cfa_offset 16
.LVL50:
	.loc 1 72 1 view .LVU200
	popq	%r12
	.cfi_def_cfa_offset 8
	ret
.LVL51:
	.p2align 4,,10
	.p2align 3
.L70:
	.cfi_restore_state
	.loc 1 63 8 view .LVU201
	cmpb	$102, 1(%rbx)
	jne	.L50
	.loc 1 63 6 discriminator 1 view .LVU202
	cmpb	$0, 2(%rbx)
	jne	.L50
	.loc 1 64 5 is_stmt 1 view .LVU203
	.loc 1 64 17 is_stmt 0 view .LVU204
	movq	24(%rbp), %rdi
	call	eval
.LVL52:
	.loc 1 64 12 discriminator 1 view .LVU205
	cmpq	$0, 8(%rax)
	movq	32(%rbp), %rax
	je	.L51
	.loc 1 64 12 discriminator 2 view .LVU206
	movq	24(%rax), %rdi
	.loc 1 59 3 is_stmt 1 view .LVU207
	.loc 1 59 6 is_stmt 0 view .LVU208
	cmpl	$2, (%rdi)
	je	.L47
.L62:
	.loc 1 59 30 discriminator 1 view .LVU209
	movq	%rdi, %rax
.LVL53:
.L45:
	.loc 1 72 1 view .LVU210
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
.LVL54:
	.loc 1 72 1 view .LVU211
	popq	%r12
	.cfi_def_cfa_offset 8
	ret
.LVL55:
	.p2align 4,,10
	.p2align 3
.L51:
	.cfi_restore_state
	.loc 1 64 12 discriminator 2 view .LVU212
	movq	32(%rax), %rax
	movq	24(%rax), %rdi
	.loc 1 59 3 is_stmt 1 view .LVU213
	.loc 1 59 6 is_stmt 0 view .LVU214
	cmpl	$2, (%rdi)
	je	.L47
	jmp	.L62
	.p2align 4,,10
	.p2align 3
.L69:
	.loc 1 62 29 is_stmt 1 discriminator 1 view .LVU215
	.loc 1 62 40 is_stmt 0 discriminator 1 view .LVU216
	movq	24(%rbp), %rax
	.loc 1 72 1 view .LVU217
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 24
.LVL56:
	.loc 1 72 1 view .LVU218
	popq	%rbp
	.cfi_def_cfa_offset 16
.LVL57:
	.loc 1 72 1 view .LVU219
	popq	%r12
	.cfi_def_cfa_offset 8
	ret
.LVL58:
	.p2align 4,,10
	.p2align 3
.L71:
	.cfi_restore_state
	.loc 1 65 27 is_stmt 1 discriminator 1 view .LVU220
	.loc 1 65 34 is_stmt 0 discriminator 1 view .LVU221
	movq	24(%rbp), %rdi
	call	eval
.LVL59:
	.loc 1 65 49 discriminator 1 view .LVU222
	movq	24(%rax), %rax
	.loc 1 65 49 view .LVU223
	jmp	.L45
.LVL60:
	.p2align 4,,10
	.p2align 3
.L74:
	.loc 1 70 32 discriminator 1 view .LVU224
	call	eval
.LVL61:
	.loc 1 70 53 discriminator 1 view .LVU225
	imulq	8(%rax), %r12
.LVL62:
	.loc 1 70 53 discriminator 1 view .LVU226
	jmp	.L59
.LVL63:
	.p2align 4,,10
	.p2align 3
.L68:
	.cfi_def_cfa_offset 8
	.cfi_restore 3
	.cfi_restore 6
	.cfi_restore 12
	.loc 1 59 30 discriminator 1 view .LVU227
	movq	%rdi, %rax
	.loc 1 72 1 view .LVU228
	ret
.LVL64:
	.p2align 4,,10
	.p2align 3
.L72:
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	.cfi_offset 6, -24
	.cfi_offset 12, -16
	.loc 1 66 27 is_stmt 1 discriminator 1 view .LVU229
	.loc 1 66 34 is_stmt 0 discriminator 1 view .LVU230
	movq	24(%rbp), %rdi
	call	eval
.LVL65:
	.loc 1 66 49 discriminator 1 view .LVU231
	movq	32(%rax), %rax
	.loc 1 66 49 view .LVU232
	jmp	.L45
.L73:
	.loc 1 67 28 is_stmt 1 discriminator 1 view .LVU233
	.loc 1 67 71 is_stmt 0 discriminator 1 view .LVU234
	movq	32(%rbp), %rax
	.loc 1 67 35 discriminator 1 view .LVU235
	movq	24(%rax), %rdi
	call	eval
.LVL66:
	movq	24(%rbp), %rdi
	movq	%rax, %rbx
.LVL67:
	.loc 1 67 35 discriminator 1 view .LVU236
	call	eval
.LVL68:
	movq	%rax, %rcx
.LVL69:
.LBB95:
.LBI95:
	.loc 1 16 14 is_stmt 1 view .LVU237
.LBB96:
	.loc 1 16 39 view .LVU238
.LBB97:
.LBI97:
	.loc 1 14 14 view .LVU239
.LBB98:
	.loc 1 14 31 view .LVU240
	.loc 1 14 52 is_stmt 0 view .LVU241
	movslq	used(%rip), %rax
.LVL70:
	.loc 1 14 52 view .LVU242
	leal	1(%rax), %edx
	movl	%edx, used(%rip)
	.loc 1 14 37 view .LVU243
	leaq	(%rax,%rax,4), %rdx
	salq	$3, %rdx
	leaq	arena(%rdx), %rax
.LVL71:
	.loc 1 14 57 is_stmt 1 view .LVU244
	.loc 1 14 64 is_stmt 0 view .LVU245
	movl	$2, arena(%rdx)
	.loc 1 14 69 is_stmt 1 view .LVU246
.LVL72:
	.loc 1 14 69 is_stmt 0 view .LVU247
.LBE98:
.LBE97:
	.loc 1 16 59 is_stmt 1 discriminator 1 view .LVU248
	.loc 1 16 66 is_stmt 0 discriminator 1 view .LVU249
	movq	%rcx, 24(%rax)
	.loc 1 16 71 is_stmt 1 discriminator 1 view .LVU250
	.loc 1 16 78 is_stmt 0 discriminator 1 view .LVU251
	movq	%rbx, 32(%rax)
	.loc 1 16 83 is_stmt 1 discriminator 1 view .LVU252
.LVL73:
	.loc 1 16 83 is_stmt 0 discriminator 1 view .LVU253
.LBE96:
.LBE95:
	.loc 1 67 35 view .LVU254
	jmp	.L45
	.cfi_endproc
.LFE10:
	.size	eval, .-eval
	.section	.rodata.str1.1
.LC4:
	.string	"%ld"
.LC5:
	.string	"%s"
.LC6:
	.string	"()"
.LC7:
	.string	" . "
	.text
	.p2align 4
	.type	print, @function
print:
.LVL74:
.LFB11:
	.loc 1 75 1 is_stmt 1 view -0
	.cfi_startproc
	.loc 1 76 3 view .LVU256
	.loc 1 75 1 is_stmt 0 view .LVU257
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset 3, -16
	.loc 1 76 8 view .LVU258
	movl	(%rdi), %eax
	.loc 1 75 1 view .LVU259
	movq	%rdi, %rbx
	.loc 1 76 6 view .LVU260
	testl	%eax, %eax
	je	.L86
	.loc 1 77 8 is_stmt 1 view .LVU261
	.loc 1 77 11 is_stmt 0 view .LVU262
	cmpl	$1, %eax
	je	.L87
	.loc 1 78 8 is_stmt 1 view .LVU263
	.loc 1 78 11 is_stmt 0 view .LVU264
	cmpl	$3, %eax
	je	.L88
.LVL75:
.LBB107:
.LBI107:
	.loc 1 74 13 is_stmt 1 view .LVU265
.LBB108:
	.loc 1 80 5 view .LVU266
.LBB109:
.LBI109:
	.file 2 "/usr/include/x86_64-linux-gnu/bits/stdio.h"
	.loc 2 82 1 view .LVU267
.LBB110:
	.loc 2 84 3 view .LVU268
	.loc 2 84 10 is_stmt 0 view .LVU269
	movq	stdout(%rip), %rsi
	movl	$40, %edi
.LVL76:
	.loc 2 84 10 view .LVU270
	call	putc
.LVL77:
	.loc 2 84 10 view .LVU271
	jmp	.L80
.LVL78:
	.p2align 4,,10
	.p2align 3
.L89:
	.loc 2 84 10 view .LVU272
.LBE110:
.LBE109:
	.loc 1 85 7 is_stmt 1 view .LVU273
.LBB111:
.LBI111:
	.loc 2 82 1 view .LVU274
.LBB112:
	.loc 2 84 3 view .LVU275
	.loc 2 84 10 is_stmt 0 view .LVU276
	movq	stdout(%rip), %rsi
	movl	$32, %edi
	call	putc
.LVL79:
	.loc 2 84 10 view .LVU277
.LBE112:
.LBE111:
	.loc 1 81 5 is_stmt 1 view .LVU278
.L80:
	.loc 1 81 5 view .LVU279
	.loc 1 82 7 view .LVU280
	movq	24(%rbx), %rdi
	call	print
.LVL80:
	.loc 1 83 7 view .LVU281
	.loc 1 83 9 is_stmt 0 view .LVU282
	movq	32(%rbx), %rbx
.LVL81:
	.loc 1 84 7 is_stmt 1 view .LVU283
	.loc 1 84 12 is_stmt 0 view .LVU284
	movl	(%rbx), %eax
	.loc 1 84 10 view .LVU285
	cmpl	$2, %eax
	je	.L89
	.loc 1 87 5 is_stmt 1 view .LVU286
	.loc 1 87 8 is_stmt 0 view .LVU287
	cmpl	$3, %eax
	jne	.L90
.L81:
	.loc 1 88 5 is_stmt 1 view .LVU288
.LVL82:
.LBB113:
.LBI113:
	.loc 2 82 1 view .LVU289
.LBB114:
	.loc 2 84 3 view .LVU290
	.loc 2 84 10 is_stmt 0 view .LVU291
	movq	stdout(%rip), %rsi
	movl	$41, %edi
.LBE114:
.LBE113:
.LBE108:
.LBE107:
	.loc 1 90 1 view .LVU292
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 8
.LVL83:
.LBB119:
.LBB117:
.LBB116:
.LBB115:
	.loc 2 84 10 view .LVU293
	jmp	putc
.LVL84:
	.p2align 4,,10
	.p2align 3
.L86:
	.cfi_restore_state
	.loc 2 84 10 view .LVU294
.LBE115:
.LBE116:
.LBE117:
.LBE119:
	.loc 1 76 22 is_stmt 1 discriminator 1 view .LVU295
	movq	8(%rdi), %rsi
	.loc 1 90 1 is_stmt 0 view .LVU296
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 8
.LVL85:
	.loc 1 76 22 discriminator 1 view .LVU297
	movl	$.LC4, %edi
.LVL86:
	.loc 1 76 22 discriminator 1 view .LVU298
	jmp	printf
.LVL87:
	.p2align 4,,10
	.p2align 3
.L88:
	.cfi_restore_state
	.loc 1 78 27 is_stmt 1 discriminator 1 view .LVU299
	movl	$.LC6, %edi
	xorl	%eax, %eax
	.loc 1 90 1 is_stmt 0 view .LVU300
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 8
.LVL88:
	.loc 1 78 27 discriminator 1 view .LVU301
	jmp	printf
.LVL89:
	.p2align 4,,10
	.p2align 3
.L90:
	.cfi_restore_state
.LBB120:
.LBB118:
	.loc 1 87 26 is_stmt 1 discriminator 1 view .LVU302
	movl	$.LC7, %edi
	xorl	%eax, %eax
	call	printf
.LVL90:
	.loc 1 87 41 discriminator 1 view .LVU303
	movq	%rbx, %rdi
	call	print
.LVL91:
	jmp	.L81
.LVL92:
	.p2align 4,,10
	.p2align 3
.L87:
	.loc 1 87 41 is_stmt 0 discriminator 1 view .LVU304
.LBE118:
.LBE120:
	.loc 1 77 27 is_stmt 1 discriminator 1 view .LVU305
	movq	16(%rdi), %rsi
	xorl	%eax, %eax
	movl	$.LC5, %edi
	.loc 1 90 1 is_stmt 0 view .LVU306
	popq	%rbx
	.cfi_def_cfa_offset 8
.LVL93:
	.loc 1 77 27 discriminator 1 view .LVU307
	jmp	printf
.LVL94:
	.cfi_endproc
.LFE11:
	.size	print, .-print
	.section	.rodata.str1.8,"aMS",@progbits,1
	.align 8
.LC8:
	.string	"(+ 1 (* 2 3) (if 0 100 (car (quote (4 5)))))"
	.section	.rodata.str1.1
.LC9:
	.string	"(cons 1 (quote (2 3)))"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB12:
	.loc 1 93 1 is_stmt 1 view -0
	.cfi_startproc
	.loc 1 94 3 view .LVU309
	.loc 1 93 1 is_stmt 0 view .LVU310
	subq	$8, %rsp
	.cfi_def_cfa_offset 16
	.loc 1 94 5 view .LVU311
	movq	$.LC8, p(%rip)
	.loc 1 95 3 is_stmt 1 view .LVU312
	call	read
.LVL95:
	movq	%rax, %rdi
	.loc 1 95 3 is_stmt 0 discriminator 1 view .LVU313
	call	eval
.LVL96:
	movq	%rax, %rdi
	.loc 1 95 3 discriminator 2 view .LVU314
	call	print
.LVL97:
	.loc 1 96 3 is_stmt 1 view .LVU315
.LBB121:
.LBI121:
	.loc 2 82 1 view .LVU316
.LBB122:
	.loc 2 84 3 view .LVU317
	.loc 2 84 10 is_stmt 0 view .LVU318
	movq	stdout(%rip), %rsi
	movl	$10, %edi
	call	putc
.LVL98:
	.loc 2 84 10 view .LVU319
.LBE122:
.LBE121:
	.loc 1 97 3 is_stmt 1 view .LVU320
	.loc 1 97 5 is_stmt 0 view .LVU321
	movq	$.LC9, p(%rip)
	.loc 1 98 3 is_stmt 1 view .LVU322
	call	read
.LVL99:
	movq	%rax, %rdi
	.loc 1 98 3 is_stmt 0 discriminator 1 view .LVU323
	call	eval
.LVL100:
	movq	%rax, %rdi
	.loc 1 98 3 discriminator 2 view .LVU324
	call	print
.LVL101:
	.loc 1 99 3 is_stmt 1 view .LVU325
.LBB123:
.LBI123:
	.loc 2 82 1 view .LVU326
.LBB124:
	.loc 2 84 3 view .LVU327
	.loc 2 84 10 is_stmt 0 view .LVU328
	movq	stdout(%rip), %rsi
	movl	$10, %edi
	call	putc
.LVL102:
	.loc 2 84 10 view .LVU329
.LBE124:
.LBE123:
	.loc 1 100 3 is_stmt 1 view .LVU330
	.loc 1 101 1 is_stmt 0 view .LVU331
	xorl	%eax, %eax
	addq	$8, %rsp
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE12:
	.size	main, .-main
	.local	nnames
	.comm	nnames,4,4
	.local	names
	.comm	names,1024,32
	.local	p
	.comm	p,8,8
	.data
	.align 32
	.type	nil, @object
	.size	nil, 40
nil:
	.long	3
	.zero	4
	.quad	0
	.quad	0
	.quad	0
	.quad	0
	.local	used
	.comm	used,4,4
	.local	arena
	.comm	arena,40960,32
	.text
.Letext0:
	.file 3 "/usr/include/x86_64-linux-gnu/bits/types.h"
	.file 4 "/usr/local/lib/gcc/x86_64-linux-gnu/13.3.0/include/stddef.h"
	.file 5 "/usr/include/x86_64-linux-gnu/bits/types/struct_FILE.h"
	.file 6 "/usr/include/x86_64-linux-gnu/bits/types/FILE.h"
	.file 7 "/usr/include/stdio.h"
	.file 8 "/usr/include/string.h"
	.file 9 "/usr/include/ctype.h"
	.file 10 "<built-in>"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0xd17
	.value	0x5
	.byte	0x1
	.byte	0x8
	.long	.Ldebug_abbrev0
	.uleb128 0x28
	.long	.LASF80
	.byte	0x1d
	.long	.LASF0
	.long	.LASF1
	.long	.LLRL45
	.quad	0
	.long	.Ldebug_line0
	.uleb128 0x8
	.byte	0x1
	.byte	0x8
	.long	.LASF2
	.uleb128 0x8
	.byte	0x2
	.byte	0x7
	.long	.LASF3
	.uleb128 0x1d
	.long	0x31
	.uleb128 0x8
	.byte	0x4
	.byte	0x7
	.long	.LASF4
	.uleb128 0x8
	.byte	0x8
	.byte	0x7
	.long	.LASF5
	.uleb128 0x8
	.byte	0x1
	.byte	0x6
	.long	.LASF6
	.uleb128 0x8
	.byte	0x2
	.byte	0x5
	.long	.LASF7
	.uleb128 0x29
	.byte	0x4
	.byte	0x5
	.string	"int"
	.uleb128 0x8
	.byte	0x8
	.byte	0x5
	.long	.LASF8
	.uleb128 0xe
	.long	.LASF9
	.byte	0x3
	.byte	0x98
	.byte	0x19
	.long	0x60
	.uleb128 0xe
	.long	.LASF10
	.byte	0x3
	.byte	0x99
	.byte	0x1b
	.long	0x60
	.uleb128 0x2a
	.byte	0x8
	.uleb128 0x5
	.long	0x86
	.uleb128 0x8
	.byte	0x1
	.byte	0x6
	.long	.LASF11
	.uleb128 0x1d
	.long	0x86
	.uleb128 0x2b
	.byte	0x7
	.byte	0x4
	.long	0x3d
	.byte	0x9
	.byte	0x2f
	.byte	0x1
	.long	0xf1
	.uleb128 0x9
	.long	.LASF12
	.value	0x100
	.uleb128 0x9
	.long	.LASF13
	.value	0x200
	.uleb128 0x9
	.long	.LASF14
	.value	0x400
	.uleb128 0x9
	.long	.LASF15
	.value	0x800
	.uleb128 0x9
	.long	.LASF16
	.value	0x1000
	.uleb128 0x9
	.long	.LASF17
	.value	0x2000
	.uleb128 0x9
	.long	.LASF18
	.value	0x4000
	.uleb128 0x9
	.long	.LASF19
	.value	0x8000
	.uleb128 0xf
	.long	.LASF20
	.byte	0x1
	.uleb128 0xf
	.long	.LASF21
	.byte	0x2
	.uleb128 0xf
	.long	.LASF22
	.byte	0x4
	.uleb128 0xf
	.long	.LASF23
	.byte	0x8
	.byte	0
	.uleb128 0xe
	.long	.LASF24
	.byte	0x4
	.byte	0xd6
	.byte	0x17
	.long	0x44
	.uleb128 0x1e
	.long	.LASF59
	.byte	0xd8
	.byte	0x5
	.byte	0x31
	.byte	0x8
	.long	0x267
	.uleb128 0x1
	.long	.LASF25
	.byte	0x33
	.byte	0x7
	.long	0x59
	.byte	0
	.uleb128 0x1
	.long	.LASF26
	.byte	0x36
	.byte	0x9
	.long	0x81
	.byte	0x8
	.uleb128 0x1
	.long	.LASF27
	.byte	0x37
	.byte	0x9
	.long	0x81
	.byte	0x10
	.uleb128 0x1
	.long	.LASF28
	.byte	0x38
	.byte	0x9
	.long	0x81
	.byte	0x18
	.uleb128 0x1
	.long	.LASF29
	.byte	0x39
	.byte	0x9
	.long	0x81
	.byte	0x20
	.uleb128 0x1
	.long	.LASF30
	.byte	0x3a
	.byte	0x9
	.long	0x81
	.byte	0x28
	.uleb128 0x1
	.long	.LASF31
	.byte	0x3b
	.byte	0x9
	.long	0x81
	.byte	0x30
	.uleb128 0x1
	.long	.LASF32
	.byte	0x3c
	.byte	0x9
	.long	0x81
	.byte	0x38
	.uleb128 0x1
	.long	.LASF33
	.byte	0x3d
	.byte	0x9
	.long	0x81
	.byte	0x40
	.uleb128 0x1
	.long	.LASF34
	.byte	0x40
	.byte	0x9
	.long	0x81
	.byte	0x48
	.uleb128 0x1
	.long	.LASF35
	.byte	0x41
	.byte	0x9
	.long	0x81
	.byte	0x50
	.uleb128 0x1
	.long	.LASF36
	.byte	0x42
	.byte	0x9
	.long	0x81
	.byte	0x58
	.uleb128 0x1
	.long	.LASF37
	.byte	0x44
	.byte	0x16
	.long	0x280
	.byte	0x60
	.uleb128 0x1
	.long	.LASF38
	.byte	0x46
	.byte	0x14
	.long	0x285
	.byte	0x68
	.uleb128 0x1
	.long	.LASF39
	.byte	0x48
	.byte	0x7
	.long	0x59
	.byte	0x70
	.uleb128 0x1
	.long	.LASF40
	.byte	0x49
	.byte	0x7
	.long	0x59
	.byte	0x74
	.uleb128 0x1
	.long	.LASF41
	.byte	0x4a
	.byte	0xb
	.long	0x67
	.byte	0x78
	.uleb128 0x1
	.long	.LASF42
	.byte	0x4d
	.byte	0x12
	.long	0x31
	.byte	0x80
	.uleb128 0x1
	.long	.LASF43
	.byte	0x4e
	.byte	0xf
	.long	0x4b
	.byte	0x82
	.uleb128 0x1
	.long	.LASF44
	.byte	0x4f
	.byte	0x8
	.long	0x28a
	.byte	0x83
	.uleb128 0x1
	.long	.LASF45
	.byte	0x51
	.byte	0xf
	.long	0x29a
	.byte	0x88
	.uleb128 0x1
	.long	.LASF46
	.byte	0x59
	.byte	0xd
	.long	0x73
	.byte	0x90
	.uleb128 0x1
	.long	.LASF47
	.byte	0x5b
	.byte	0x17
	.long	0x2a4
	.byte	0x98
	.uleb128 0x1
	.long	.LASF48
	.byte	0x5c
	.byte	0x19
	.long	0x2ae
	.byte	0xa0
	.uleb128 0x1
	.long	.LASF49
	.byte	0x5d
	.byte	0x14
	.long	0x285
	.byte	0xa8
	.uleb128 0x1
	.long	.LASF50
	.byte	0x5e
	.byte	0x9
	.long	0x7f
	.byte	0xb0
	.uleb128 0x1
	.long	.LASF51
	.byte	0x5f
	.byte	0xa
	.long	0xf1
	.byte	0xb8
	.uleb128 0x1
	.long	.LASF52
	.byte	0x60
	.byte	0x7
	.long	0x59
	.byte	0xc0
	.uleb128 0x1
	.long	.LASF53
	.byte	0x62
	.byte	0x8
	.long	0x2b3
	.byte	0xc4
	.byte	0
	.uleb128 0xe
	.long	.LASF54
	.byte	0x6
	.byte	0x7
	.byte	0x19
	.long	0xfd
	.uleb128 0x2c
	.long	.LASF81
	.byte	0x5
	.byte	0x2b
	.byte	0xe
	.uleb128 0x18
	.long	.LASF55
	.uleb128 0x5
	.long	0x27b
	.uleb128 0x5
	.long	0xfd
	.uleb128 0x15
	.long	0x86
	.long	0x29a
	.uleb128 0x16
	.long	0x44
	.byte	0
	.byte	0
	.uleb128 0x5
	.long	0x273
	.uleb128 0x18
	.long	.LASF56
	.uleb128 0x5
	.long	0x29f
	.uleb128 0x18
	.long	.LASF57
	.uleb128 0x5
	.long	0x2a9
	.uleb128 0x15
	.long	0x86
	.long	0x2c3
	.uleb128 0x16
	.long	0x44
	.byte	0x13
	.byte	0
	.uleb128 0x5
	.long	0x267
	.uleb128 0x2d
	.long	.LASF71
	.byte	0x7
	.byte	0x90
	.byte	0xe
	.long	0x2c3
	.uleb128 0x2e
	.string	"tag"
	.byte	0x7
	.byte	0x4
	.long	0x3d
	.byte	0x1
	.byte	0x7
	.byte	0x6
	.long	0x2ff
	.uleb128 0x19
	.string	"NUM"
	.byte	0
	.uleb128 0x19
	.string	"SYM"
	.byte	0x1
	.uleb128 0xf
	.long	.LASF58
	.byte	0x2
	.uleb128 0x19
	.string	"NIL"
	.byte	0x3
	.byte	0
	.uleb128 0x1e
	.long	.LASF60
	.byte	0x28
	.byte	0x1
	.byte	0x8
	.byte	0x10
	.long	0x344
	.uleb128 0x10
	.string	"tag"
	.byte	0x20
	.long	0x2d4
	.byte	0
	.uleb128 0x10
	.string	"num"
	.byte	0x2a
	.long	0x60
	.byte	0x8
	.uleb128 0x10
	.string	"sym"
	.byte	0x3b
	.long	0x344
	.byte	0x10
	.uleb128 0x10
	.string	"car"
	.byte	0x4d
	.long	0x349
	.byte	0x18
	.uleb128 0x10
	.string	"cdr"
	.byte	0x53
	.long	0x349
	.byte	0x20
	.byte	0
	.uleb128 0x5
	.long	0x8d
	.uleb128 0x5
	.long	0x2ff
	.uleb128 0xe
	.long	.LASF60
	.byte	0x1
	.byte	0x8
	.byte	0x5a
	.long	0x2ff
	.uleb128 0x15
	.long	0x34e
	.long	0x36b
	.uleb128 0x2f
	.long	0x44
	.value	0x3ff
	.byte	0
	.uleb128 0x11
	.long	.LASF61
	.byte	0xa
	.byte	0xd
	.long	0x35a
	.uleb128 0x9
	.byte	0x3
	.quad	arena
	.uleb128 0x11
	.long	.LASF62
	.byte	0xb
	.byte	0xc
	.long	0x59
	.uleb128 0x9
	.byte	0x3
	.quad	used
	.uleb128 0x1f
	.string	"nil"
	.byte	0xc
	.byte	0xd
	.long	0x34e
	.uleb128 0x9
	.byte	0x3
	.quad	nil
	.uleb128 0x1f
	.string	"p"
	.byte	0x12
	.byte	0x14
	.long	0x344
	.uleb128 0x9
	.byte	0x3
	.quad	p
	.uleb128 0x15
	.long	0x86
	.long	0x3d3
	.uleb128 0x16
	.long	0x44
	.byte	0x3f
	.uleb128 0x16
	.long	0x44
	.byte	0xf
	.byte	0
	.uleb128 0x11
	.long	.LASF63
	.byte	0x13
	.byte	0xd
	.long	0x3bd
	.uleb128 0x9
	.byte	0x3
	.quad	names
	.uleb128 0x11
	.long	.LASF64
	.byte	0x14
	.byte	0xc
	.long	0x59
	.uleb128 0x9
	.byte	0x3
	.quad	nnames
	.uleb128 0x1a
	.long	.LASF65
	.byte	0x7
	.value	0x226
	.byte	0xc
	.long	0x59
	.long	0x419
	.uleb128 0x6
	.long	0x59
	.uleb128 0x6
	.long	0x2c3
	.byte	0
	.uleb128 0x1a
	.long	.LASF66
	.byte	0x7
	.value	0x164
	.byte	0xc
	.long	0x59
	.long	0x431
	.uleb128 0x6
	.long	0x344
	.uleb128 0x30
	.byte	0
	.uleb128 0x1b
	.long	.LASF67
	.byte	0x9c
	.byte	0xc
	.long	0x59
	.long	0x44b
	.uleb128 0x6
	.long	0x344
	.uleb128 0x6
	.long	0x344
	.byte	0
	.uleb128 0x1b
	.long	.LASF68
	.byte	0x2b
	.byte	0xe
	.long	0x7f
	.long	0x46a
	.uleb128 0x6
	.long	0x7f
	.uleb128 0x6
	.long	0x46a
	.uleb128 0x6
	.long	0xf1
	.byte	0
	.uleb128 0x5
	.long	0x46f
	.uleb128 0x31
	.uleb128 0x1b
	.long	.LASF69
	.byte	0x9f
	.byte	0xc
	.long	0x59
	.long	0x48f
	.uleb128 0x6
	.long	0x344
	.uleb128 0x6
	.long	0x344
	.uleb128 0x6
	.long	0xf1
	.byte	0
	.uleb128 0x1a
	.long	.LASF70
	.byte	0x8
	.value	0x197
	.byte	0xf
	.long	0xf1
	.long	0x4a6
	.uleb128 0x6
	.long	0x344
	.byte	0
	.uleb128 0x32
	.long	.LASF82
	.byte	0x9
	.byte	0x4f
	.byte	0x23
	.long	0x4b2
	.uleb128 0x5
	.long	0x4b7
	.uleb128 0x5
	.long	0x38
	.uleb128 0x33
	.long	.LASF83
	.byte	0x1
	.byte	0x5c
	.byte	0x5
	.long	0x59
	.quad	.LFB12
	.quad	.LFE12-.LFB12
	.uleb128 0x1
	.byte	0x9c
	.long	0x5b7
	.uleb128 0xc
	.long	0xb43
	.quad	.LBI121
	.byte	.LVU316
	.quad	.LBB121
	.quad	.LBE121-.LBB121
	.byte	0x60
	.byte	0x3
	.long	0x523
	.uleb128 0x3
	.long	0xb54
	.long	.LLST43
	.long	.LVUS43
	.uleb128 0xb
	.quad	.LVL98
	.long	0x3fd
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x1
	.byte	0x3a
	.byte	0
	.byte	0
	.uleb128 0xc
	.long	0xb43
	.quad	.LBI123
	.byte	.LVU326
	.quad	.LBB123
	.quad	.LBE123-.LBB123
	.byte	0x63
	.byte	0x3
	.long	0x568
	.uleb128 0x3
	.long	0xb54
	.long	.LLST44
	.long	.LVUS44
	.uleb128 0xb
	.quad	.LVL102
	.long	0x3fd
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x1
	.byte	0x3a
	.byte	0
	.byte	0
	.uleb128 0x4
	.quad	.LVL95
	.long	0x82f
	.uleb128 0x4
	.quad	.LVL96
	.long	0x5d4
	.uleb128 0x4
	.quad	.LVL97
	.long	0x5b7
	.uleb128 0x4
	.quad	.LVL99
	.long	0x82f
	.uleb128 0x4
	.quad	.LVL100
	.long	0x5d4
	.uleb128 0x4
	.quad	.LVL101
	.long	0x5b7
	.byte	0
	.uleb128 0x34
	.long	.LASF84
	.byte	0x1
	.byte	0x4a
	.byte	0xd
	.byte	0x1
	.long	0x5cf
	.uleb128 0xa
	.string	"c"
	.byte	0x1
	.byte	0x4a
	.byte	0x19
	.long	0x5cf
	.byte	0
	.uleb128 0x5
	.long	0x34e
	.uleb128 0x20
	.long	.LASF73
	.byte	0x39
	.long	0x5cf
	.quad	.LFB10
	.quad	.LFE10-.LFB10
	.uleb128 0x1
	.byte	0x9c
	.long	0x82f
	.uleb128 0x35
	.string	"e"
	.byte	0x1
	.byte	0x39
	.byte	0x19
	.long	0x5cf
	.long	.LLST23
	.long	.LVUS23
	.uleb128 0x17
	.string	"op"
	.byte	0x3c
	.byte	0xf
	.long	0x344
	.long	.LLST24
	.long	.LVUS24
	.uleb128 0x21
	.long	.LASF72
	.byte	0x3d
	.byte	0x9
	.long	0x5cf
	.long	.LLST25
	.long	.LVUS25
	.uleb128 0x17
	.string	"acc"
	.byte	0x44
	.byte	0x8
	.long	0x60
	.long	.LLST26
	.long	.LVUS26
	.uleb128 0xc
	.long	0xb00
	.quad	.LBI91
	.byte	.LVU184
	.quad	.LBB91
	.quad	.LBE91-.LBB91
	.byte	0x47
	.byte	0xa
	.long	0x6b8
	.uleb128 0x3
	.long	0xb0e
	.long	.LLST27
	.long	.LVUS27
	.uleb128 0x7
	.long	0xb18
	.long	.LLST28
	.long	.LVUS28
	.uleb128 0x22
	.long	0xb22
	.quad	.LBI93
	.byte	.LVU186
	.quad	.LBB93
	.quad	.LBE93-.LBB93
	.byte	0xf
	.byte	0x26
	.uleb128 0x3
	.long	0xb2f
	.long	.LLST29
	.long	.LVUS29
	.uleb128 0x7
	.long	0xb39
	.long	.LLST30
	.long	.LVUS30
	.byte	0
	.byte	0
	.uleb128 0xc
	.long	0xad3
	.quad	.LBI95
	.byte	.LVU237
	.quad	.LBB95
	.quad	.LBE95-.LBB95
	.byte	0x43
	.byte	0x23
	.long	0x73f
	.uleb128 0x3
	.long	0xaec
	.long	.LLST31
	.long	.LVUS31
	.uleb128 0x3
	.long	0xae2
	.long	.LLST32
	.long	.LVUS32
	.uleb128 0x7
	.long	0xaf6
	.long	.LLST33
	.long	.LVUS33
	.uleb128 0x22
	.long	0xb22
	.quad	.LBI97
	.byte	.LVU239
	.quad	.LBB97
	.quad	.LBE97-.LBB97
	.byte	0x10
	.byte	0x31
	.uleb128 0x3
	.long	0xb2f
	.long	.LLST34
	.long	.LVUS34
	.uleb128 0x7
	.long	0xb39
	.long	.LLST35
	.long	.LVUS35
	.byte	0
	.byte	0
	.uleb128 0xd
	.quad	.LVL36
	.long	0x431
	.long	0x764
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x73
	.sleb128 0
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x54
	.uleb128 0x9
	.byte	0x3
	.quad	.LC0
	.byte	0
	.uleb128 0xd
	.quad	.LVL37
	.long	0x431
	.long	0x789
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x73
	.sleb128 0
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x54
	.uleb128 0x9
	.byte	0x3
	.quad	.LC1
	.byte	0
	.uleb128 0xd
	.quad	.LVL38
	.long	0x431
	.long	0x7ae
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x73
	.sleb128 0
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x54
	.uleb128 0x9
	.byte	0x3
	.quad	.LC2
	.byte	0
	.uleb128 0xd
	.quad	.LVL39
	.long	0x431
	.long	0x7d3
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x73
	.sleb128 0
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x54
	.uleb128 0x9
	.byte	0x3
	.quad	.LC3
	.byte	0
	.uleb128 0x4
	.quad	.LVL42
	.long	0x5d4
	.uleb128 0x4
	.quad	.LVL52
	.long	0x5d4
	.uleb128 0x4
	.quad	.LVL59
	.long	0x5d4
	.uleb128 0x4
	.quad	.LVL61
	.long	0x5d4
	.uleb128 0x4
	.quad	.LVL65
	.long	0x5d4
	.uleb128 0x4
	.quad	.LVL66
	.long	0x5d4
	.uleb128 0x4
	.quad	.LVL68
	.long	0x5d4
	.byte	0
	.uleb128 0x20
	.long	.LASF74
	.byte	0x20
	.long	0x5cf
	.quad	.LFB9
	.quad	.LFE9-.LFB9
	.uleb128 0x1
	.byte	0x9c
	.long	0xa9f
	.uleb128 0x12
	.string	"s"
	.byte	0x32
	.byte	0xf
	.long	0x344
	.uleb128 0x17
	.string	"c"
	.byte	0x34
	.byte	0x9
	.long	0x5cf
	.long	.LLST0
	.long	.LVUS0
	.uleb128 0x23
	.quad	.LBB80
	.quad	.LBE80-.LBB80
	.long	0x929
	.uleb128 0x11
	.long	.LASF75
	.byte	0x25
	.byte	0xb
	.long	0x5cf
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.uleb128 0x21
	.long	.LASF76
	.byte	0x25
	.byte	0x1a
	.long	0xa9f
	.long	.LLST15
	.long	.LVUS15
	.uleb128 0x13
	.long	0xad3
	.quad	.LBI81
	.byte	.LVU114
	.long	.LLRL16
	.byte	0x29
	.byte	0xf
	.long	0x91b
	.uleb128 0x3
	.long	0xaec
	.long	.LLST17
	.long	.LVUS17
	.uleb128 0x3
	.long	0xae2
	.long	.LLST18
	.long	.LVUS18
	.uleb128 0x14
	.long	.LLRL16
	.uleb128 0x7
	.long	0xaf6
	.long	.LLST19
	.long	.LVUS19
	.uleb128 0x1c
	.long	0xb22
	.quad	.LBI83
	.byte	.LVU116
	.long	.LLRL20
	.byte	0x10
	.byte	0x31
	.uleb128 0x3
	.long	0xb2f
	.long	.LLST21
	.long	.LVUS21
	.uleb128 0x14
	.long	.LLRL20
	.uleb128 0x7
	.long	0xb39
	.long	.LLST22
	.long	.LVUS22
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x4
	.quad	.LVL22
	.long	0x82f
	.byte	0
	.uleb128 0x23
	.quad	.LBB69
	.quad	.LBE69-.LBB69
	.long	0x9ba
	.uleb128 0x17
	.string	"n"
	.byte	0x2e
	.byte	0xa
	.long	0x60
	.long	.LLST8
	.long	.LVUS8
	.uleb128 0x1c
	.long	0xb00
	.quad	.LBI70
	.byte	.LVU82
	.long	.LLRL9
	.byte	0x30
	.byte	0xc
	.uleb128 0x3
	.long	0xb0e
	.long	.LLST10
	.long	.LVUS10
	.uleb128 0x14
	.long	.LLRL9
	.uleb128 0x7
	.long	0xb18
	.long	.LLST11
	.long	.LVUS11
	.uleb128 0x1c
	.long	0xb22
	.quad	.LBI72
	.byte	.LVU84
	.long	.LLRL12
	.byte	0xf
	.byte	0x26
	.uleb128 0x3
	.long	0xb2f
	.long	.LLST13
	.long	.LVUS13
	.uleb128 0x14
	.long	.LLRL12
	.uleb128 0x7
	.long	0xb39
	.long	.LLST14
	.long	.LVUS14
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x13
	.long	0xb22
	.quad	.LBI57
	.byte	.LVU28
	.long	.LLRL1
	.byte	0x34
	.byte	0xd
	.long	0x9f3
	.uleb128 0x3
	.long	0xb2f
	.long	.LLST2
	.long	.LVUS2
	.uleb128 0x14
	.long	.LLRL1
	.uleb128 0x7
	.long	0xb39
	.long	.LLST3
	.long	.LVUS3
	.byte	0
	.byte	0
	.uleb128 0x13
	.long	0xaa4
	.quad	.LBI60
	.byte	.LVU39
	.long	.LLRL4
	.byte	0x35
	.byte	0xc
	.long	0xa91
	.uleb128 0x36
	.long	0xabd
	.uleb128 0x3
	.long	0xab3
	.long	.LLST5
	.long	.LVUS5
	.uleb128 0x37
	.long	0xac7
	.long	.LLRL6
	.long	0xa70
	.uleb128 0x7
	.long	0xac8
	.long	.LLST7
	.long	.LVUS7
	.uleb128 0xd
	.quad	.LVL5
	.long	0x48f
	.long	0xa4f
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x7f
	.sleb128 0
	.byte	0
	.uleb128 0xb
	.quad	.LVL6
	.long	0x470
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x7f
	.sleb128 0
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x54
	.uleb128 0x2
	.byte	0x7e
	.sleb128 0
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x51
	.uleb128 0x2
	.byte	0x73
	.sleb128 0
	.byte	0
	.byte	0
	.uleb128 0xb
	.quad	.LVL11
	.long	0xd0f
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x76
	.sleb128 0
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x54
	.uleb128 0x2
	.byte	0x7e
	.sleb128 0
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x51
	.uleb128 0x2
	.byte	0x73
	.sleb128 0
	.byte	0
	.byte	0
	.uleb128 0x4
	.quad	.LVL0
	.long	0x4a6
	.byte	0
	.uleb128 0x5
	.long	0x5cf
	.uleb128 0x24
	.long	.LASF77
	.byte	0x16
	.byte	0x14
	.long	0x344
	.long	0xad3
	.uleb128 0xa
	.string	"s"
	.byte	0x1
	.byte	0x16
	.byte	0x27
	.long	0x344
	.uleb128 0xa
	.string	"n"
	.byte	0x1
	.byte	0x16
	.byte	0x31
	.long	0xf1
	.uleb128 0x38
	.uleb128 0x12
	.string	"i"
	.byte	0x18
	.byte	0xc
	.long	0x59
	.byte	0
	.byte	0
	.uleb128 0x24
	.long	.LASF78
	.byte	0x10
	.byte	0xe
	.long	0x5cf
	.long	0xb00
	.uleb128 0xa
	.string	"a"
	.byte	0x1
	.byte	0x10
	.byte	0x19
	.long	0x5cf
	.uleb128 0xa
	.string	"d"
	.byte	0x1
	.byte	0x10
	.byte	0x22
	.long	0x5cf
	.uleb128 0x12
	.string	"c"
	.byte	0x10
	.byte	0x2d
	.long	0x5cf
	.byte	0
	.uleb128 0x25
	.string	"num"
	.byte	0xf
	.long	0x5cf
	.long	0xb22
	.uleb128 0xa
	.string	"n"
	.byte	0x1
	.byte	0xf
	.byte	0x17
	.long	0x60
	.uleb128 0x12
	.string	"c"
	.byte	0xf
	.byte	0x22
	.long	0x5cf
	.byte	0
	.uleb128 0x25
	.string	"mk"
	.byte	0xe
	.long	0x5cf
	.long	0xb43
	.uleb128 0xa
	.string	"t"
	.byte	0x1
	.byte	0xe
	.byte	0x1a
	.long	0x2d4
	.uleb128 0x12
	.string	"c"
	.byte	0xe
	.byte	0x25
	.long	0x5cf
	.byte	0
	.uleb128 0x39
	.long	.LASF79
	.byte	0x2
	.byte	0x52
	.byte	0x1
	.long	0x59
	.byte	0x3
	.long	0xb61
	.uleb128 0xa
	.string	"__c"
	.byte	0x2
	.byte	0x52
	.byte	0xe
	.long	0x59
	.byte	0
	.uleb128 0x3a
	.long	0x5b7
	.quad	.LFB11
	.quad	.LFE11-.LFB11
	.uleb128 0x1
	.byte	0x9c
	.long	0xd0f
	.uleb128 0x3
	.long	0x5c4
	.long	.LLST36
	.long	.LVUS36
	.uleb128 0x13
	.long	0x5b7
	.quad	.LBI107
	.byte	.LVU265
	.long	.LLRL37
	.byte	0x4a
	.byte	0xd
	.long	0xcb5
	.uleb128 0x3
	.long	0x5c4
	.long	.LLST38
	.long	.LVUS38
	.uleb128 0xc
	.long	0xb43
	.quad	.LBI109
	.byte	.LVU267
	.quad	.LBB109
	.quad	.LBE109-.LBB109
	.byte	0x50
	.byte	0x5
	.long	0xbf4
	.uleb128 0x3
	.long	0xb54
	.long	.LLST39
	.long	.LVUS39
	.uleb128 0xb
	.quad	.LVL77
	.long	0x3fd
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x8
	.byte	0x28
	.byte	0
	.byte	0
	.uleb128 0xc
	.long	0xb43
	.quad	.LBI111
	.byte	.LVU274
	.quad	.LBB111
	.quad	.LBE111-.LBB111
	.byte	0x55
	.byte	0x7
	.long	0xc3a
	.uleb128 0x3
	.long	0xb54
	.long	.LLST40
	.long	.LVUS40
	.uleb128 0xb
	.quad	.LVL79
	.long	0x3fd
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x8
	.byte	0x20
	.byte	0
	.byte	0
	.uleb128 0x13
	.long	0xb43
	.quad	.LBI113
	.byte	.LVU289
	.long	.LLRL41
	.byte	0x58
	.byte	0x5
	.long	0xc74
	.uleb128 0x3
	.long	0xb54
	.long	.LLST42
	.long	.LVUS42
	.uleb128 0x26
	.quad	.LVL84
	.long	0x3fd
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x8
	.byte	0x29
	.byte	0
	.byte	0
	.uleb128 0x4
	.quad	.LVL80
	.long	0x5b7
	.uleb128 0xd
	.quad	.LVL90
	.long	0x419
	.long	0xca0
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x9
	.byte	0x3
	.quad	.LC7
	.byte	0
	.uleb128 0xb
	.quad	.LVL91
	.long	0x5b7
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x73
	.sleb128 0
	.byte	0
	.byte	0
	.uleb128 0x27
	.quad	.LVL87
	.long	0x419
	.long	0xcd4
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x9
	.byte	0x3
	.quad	.LC4
	.byte	0
	.uleb128 0x27
	.quad	.LVL89
	.long	0x419
	.long	0xcf3
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x9
	.byte	0x3
	.quad	.LC6
	.byte	0
	.uleb128 0x26
	.quad	.LVL94
	.long	0x419
	.uleb128 0x2
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x9
	.byte	0x3
	.quad	.LC5
	.byte	0
	.byte	0
	.uleb128 0x3b
	.long	.LASF68
	.long	.LASF85
	.byte	0xa
	.byte	0
	.byte	0
	.section	.debug_abbrev,"",@progbits
.Ldebug_abbrev0:
	.uleb128 0x1
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 5
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x38
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x2
	.uleb128 0x49
	.byte	0
	.uleb128 0x2
	.uleb128 0x18
	.uleb128 0x7e
	.uleb128 0x18
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
	.uleb128 0x48
	.byte	0
	.uleb128 0x7d
	.uleb128 0x1
	.uleb128 0x7f
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
	.uleb128 0x49
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
	.uleb128 0x9
	.uleb128 0x28
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x1c
	.uleb128 0x5
	.byte	0
	.byte	0
	.uleb128 0xa
	.uleb128 0x5
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
	.byte	0
	.byte	0
	.uleb128 0xb
	.uleb128 0x48
	.byte	0x1
	.uleb128 0x7d
	.uleb128 0x1
	.uleb128 0x7f
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xc
	.uleb128 0x1d
	.byte	0x1
	.uleb128 0x31
	.uleb128 0x13
	.uleb128 0x52
	.uleb128 0x1
	.uleb128 0x2138
	.uleb128 0xb
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x58
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x59
	.uleb128 0xb
	.uleb128 0x57
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xd
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
	.uleb128 0xe
	.uleb128 0x16
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xf
	.uleb128 0x28
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x1c
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x10
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x38
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x11
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
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
	.uleb128 0x12
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
	.uleb128 0x13
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
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x59
	.uleb128 0xb
	.uleb128 0x57
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x14
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x55
	.uleb128 0x17
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
	.uleb128 0x18
	.uleb128 0x13
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3c
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0x19
	.uleb128 0x28
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x1c
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x1a
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
	.uleb128 0x1b
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 8
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
	.uleb128 0x1c
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
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x59
	.uleb128 0xb
	.uleb128 0x57
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x1d
	.uleb128 0x26
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1e
	.uleb128 0x13
	.byte	0x1
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1f
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
	.uleb128 0x20
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 14
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
	.uleb128 0x21
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
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
	.uleb128 0x22
	.uleb128 0x1d
	.byte	0x1
	.uleb128 0x31
	.uleb128 0x13
	.uleb128 0x52
	.uleb128 0x1
	.uleb128 0x2138
	.uleb128 0xb
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x58
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x59
	.uleb128 0xb
	.uleb128 0x57
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x23
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
	.uleb128 0x24
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x20
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x25
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0x21
	.sleb128 14
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x20
	.uleb128 0x21
	.sleb128 1
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x26
	.uleb128 0x48
	.byte	0x1
	.uleb128 0x7d
	.uleb128 0x1
	.uleb128 0x82
	.uleb128 0x19
	.uleb128 0x7f
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x27
	.uleb128 0x48
	.byte	0x1
	.uleb128 0x7d
	.uleb128 0x1
	.uleb128 0x82
	.uleb128 0x19
	.uleb128 0x7f
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x28
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
	.uleb128 0x29
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
	.uleb128 0x2a
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x2b
	.uleb128 0x4
	.byte	0x1
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x2c
	.uleb128 0x16
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x2d
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3c
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0x2e
	.uleb128 0x4
	.byte	0x1
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x2f
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0x5
	.byte	0
	.byte	0
	.uleb128 0x30
	.uleb128 0x18
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x31
	.uleb128 0x26
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x32
	.uleb128 0x2e
	.byte	0
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
	.byte	0
	.byte	0
	.uleb128 0x33
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
	.uleb128 0x34
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
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x35
	.uleb128 0x5
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
	.uleb128 0x36
	.uleb128 0x5
	.byte	0
	.uleb128 0x31
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x37
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
	.uleb128 0x38
	.uleb128 0xb
	.byte	0x1
	.byte	0
	.byte	0
	.uleb128 0x39
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
	.uleb128 0x20
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x3a
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x31
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
	.uleb128 0x3b
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
.LVUS43:
	.uleb128 .LVU316
	.uleb128 .LVU319
.LLST43:
	.byte	0x8
	.quad	.LVL97
	.uleb128 .LVL98-.LVL97
	.uleb128 0x2
	.byte	0x3a
	.byte	0x9f
	.byte	0
.LVUS44:
	.uleb128 .LVU326
	.uleb128 .LVU329
.LLST44:
	.byte	0x8
	.quad	.LVL101
	.uleb128 .LVL102-.LVL101
	.uleb128 0x2
	.byte	0x3a
	.byte	0x9f
	.byte	0
.LVUS23:
	.uleb128 0
	.uleb128 .LVU150
	.uleb128 .LVU150
	.uleb128 .LVU227
	.uleb128 .LVU227
	.uleb128 .LVU229
	.uleb128 .LVU229
	.uleb128 0
.LLST23:
	.byte	0x6
	.quad	.LVL33
	.byte	0x4
	.uleb128 .LVL33-.LVL33
	.uleb128 .LVL34-.LVL33
	.uleb128 0x1
	.byte	0x55
	.byte	0x4
	.uleb128 .LVL34-.LVL33
	.uleb128 .LVL63-.LVL33
	.uleb128 0x4
	.byte	0xa3
	.uleb128 0x1
	.byte	0x55
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL63-.LVL33
	.uleb128 .LVL64-.LVL33
	.uleb128 0x1
	.byte	0x55
	.byte	0x4
	.uleb128 .LVL64-.LVL33
	.uleb128 .LFE10-.LVL33
	.uleb128 0x4
	.byte	0xa3
	.uleb128 0x1
	.byte	0x55
	.byte	0x9f
	.byte	0
.LVUS24:
	.uleb128 .LVU155
	.uleb128 .LVU199
	.uleb128 .LVU201
	.uleb128 .LVU210
	.uleb128 .LVU212
	.uleb128 .LVU218
	.uleb128 .LVU220
	.uleb128 .LVU227
	.uleb128 .LVU229
	.uleb128 .LVU236
.LLST24:
	.byte	0x6
	.quad	.LVL35
	.byte	0x4
	.uleb128 .LVL35-.LVL35
	.uleb128 .LVL49-.LVL35
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL51-.LVL35
	.uleb128 .LVL53-.LVL35
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL55-.LVL35
	.uleb128 .LVL56-.LVL35
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL58-.LVL35
	.uleb128 .LVL63-.LVL35
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL64-.LVL35
	.uleb128 .LVL67-.LVL35
	.uleb128 0x1
	.byte	0x53
	.byte	0
.LVUS25:
	.uleb128 .LVU156
	.uleb128 .LVU200
	.uleb128 .LVU201
	.uleb128 .LVU211
	.uleb128 .LVU212
	.uleb128 .LVU219
	.uleb128 .LVU220
	.uleb128 .LVU227
	.uleb128 .LVU229
	.uleb128 0
.LLST25:
	.byte	0x6
	.quad	.LVL35
	.byte	0x4
	.uleb128 .LVL35-.LVL35
	.uleb128 .LVL50-.LVL35
	.uleb128 0x1
	.byte	0x56
	.byte	0x4
	.uleb128 .LVL51-.LVL35
	.uleb128 .LVL54-.LVL35
	.uleb128 0x1
	.byte	0x56
	.byte	0x4
	.uleb128 .LVL55-.LVL35
	.uleb128 .LVL57-.LVL35
	.uleb128 0x1
	.byte	0x56
	.byte	0x4
	.uleb128 .LVL58-.LVL35
	.uleb128 .LVL63-.LVL35
	.uleb128 0x1
	.byte	0x56
	.byte	0x4
	.uleb128 .LVL64-.LVL35
	.uleb128 .LFE10-.LVL35
	.uleb128 0x1
	.byte	0x56
	.byte	0
.LVUS26:
	.uleb128 .LVU173
	.uleb128 .LVU175
	.uleb128 .LVU175
	.uleb128 .LVU183
	.uleb128 .LVU224
	.uleb128 .LVU226
.LLST26:
	.byte	0x6
	.quad	.LVL40
	.byte	0x4
	.uleb128 .LVL40-.LVL40
	.uleb128 .LVL41-.LVL40
	.uleb128 0x6
	.byte	0x7c
	.sleb128 0
	.byte	0x8
	.byte	0xff
	.byte	0x1a
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL41-.LVL40
	.uleb128 .LVL45-.LVL40
	.uleb128 0x1
	.byte	0x5c
	.byte	0x4
	.uleb128 .LVL60-.LVL40
	.uleb128 .LVL62-.LVL40
	.uleb128 0x1
	.byte	0x5c
	.byte	0
.LVUS27:
	.uleb128 .LVU184
	.uleb128 .LVU197
.LLST27:
	.byte	0x8
	.quad	.LVL45
	.uleb128 .LVL48-.LVL45
	.uleb128 0x1
	.byte	0x5c
	.byte	0
.LVUS28:
	.uleb128 .LVU193
	.uleb128 .LVU201
.LLST28:
	.byte	0x8
	.quad	.LVL47
	.uleb128 .LVL51-.LVL47
	.uleb128 0x1
	.byte	0x50
	.byte	0
.LVUS29:
	.uleb128 .LVU186
	.uleb128 .LVU193
.LLST29:
	.byte	0x8
	.quad	.LVL45
	.uleb128 .LVL47-.LVL45
	.uleb128 0x2
	.byte	0x30
	.byte	0x9f
	.byte	0
.LVUS30:
	.uleb128 .LVU190
	.uleb128 .LVU193
.LLST30:
	.byte	0x8
	.quad	.LVL46
	.uleb128 .LVL47-.LVL46
	.uleb128 0x1
	.byte	0x50
	.byte	0
.LVUS31:
	.uleb128 .LVU237
	.uleb128 .LVU253
.LLST31:
	.byte	0x8
	.quad	.LVL69
	.uleb128 .LVL73-.LVL69
	.uleb128 0x1
	.byte	0x53
	.byte	0
.LVUS32:
	.uleb128 .LVU237
	.uleb128 .LVU242
	.uleb128 .LVU242
	.uleb128 .LVU253
.LLST32:
	.byte	0x6
	.quad	.LVL69
	.byte	0x4
	.uleb128 .LVL69-.LVL69
	.uleb128 .LVL70-.LVL69
	.uleb128 0x1
	.byte	0x50
	.byte	0x4
	.uleb128 .LVL70-.LVL69
	.uleb128 .LVL73-.LVL69
	.uleb128 0x1
	.byte	0x52
	.byte	0
.LVUS33:
	.uleb128 .LVU247
	.uleb128 0
.LLST33:
	.byte	0x8
	.quad	.LVL72
	.uleb128 .LFE10-.LVL72
	.uleb128 0x1
	.byte	0x50
	.byte	0
.LVUS34:
	.uleb128 .LVU239
	.uleb128 .LVU247
.LLST34:
	.byte	0x8
	.quad	.LVL69
	.uleb128 .LVL72-.LVL69
	.uleb128 0x2
	.byte	0x32
	.byte	0x9f
	.byte	0
.LVUS35:
	.uleb128 .LVU244
	.uleb128 .LVU247
.LLST35:
	.byte	0x8
	.quad	.LVL71
	.uleb128 .LVL72-.LVL71
	.uleb128 0x1
	.byte	0x50
	.byte	0
.LVUS0:
	.uleb128 .LVU37
	.uleb128 .LVU43
	.uleb128 .LVU43
	.uleb128 .LVU55
	.uleb128 .LVU56
	.uleb128 .LVU57
	.uleb128 .LVU57
	.uleb128 .LVU68
.LLST0:
	.byte	0x6
	.quad	.LVL2
	.byte	0x4
	.uleb128 .LVL2-.LVL2
	.uleb128 .LVL3-.LVL2
	.uleb128 0x1
	.byte	0x54
	.byte	0x4
	.uleb128 .LVL3-.LVL2
	.uleb128 .LVL8-.LVL2
	.uleb128 0x3
	.byte	0x91
	.sleb128 -104
	.byte	0x4
	.uleb128 .LVL9-.LVL2
	.uleb128 .LVL10-.LVL2
	.uleb128 0x1
	.byte	0x54
	.byte	0x4
	.uleb128 .LVL10-.LVL2
	.uleb128 .LVL13-.LVL2
	.uleb128 0x3
	.byte	0x91
	.sleb128 -104
	.byte	0
.LVUS15:
	.uleb128 .LVU107
	.uleb128 .LVU143
.LLST15:
	.byte	0x8
	.quad	.LVL21
	.uleb128 .LVL32-.LVL21
	.uleb128 0x1
	.byte	0x56
	.byte	0
.LVUS17:
	.uleb128 .LVU114
	.uleb128 .LVU131
.LLST17:
	.byte	0x8
	.quad	.LVL23
	.uleb128 .LVL29-.LVL23
	.uleb128 0xa
	.byte	0x3
	.quad	nil
	.byte	0x9f
	.byte	0
.LVUS18:
	.uleb128 .LVU114
	.uleb128 .LVU119
	.uleb128 .LVU119
	.uleb128 .LVU123
	.uleb128 .LVU123
	.uleb128 .LVU131
.LLST18:
	.byte	0x6
	.quad	.LVL23
	.byte	0x4
	.uleb128 .LVL23-.LVL23
	.uleb128 .LVL24-.LVL23
	.uleb128 0x1
	.byte	0x50
	.byte	0x4
	.uleb128 .LVL24-.LVL23
	.uleb128 .LVL26-.LVL23
	.uleb128 0x1
	.byte	0x54
	.byte	0x4
	.uleb128 .LVL26-.LVL23
	.uleb128 .LVL29-.LVL23
	.uleb128 0xc
	.byte	0x71
	.sleb128 0
	.byte	0x3
	.quad	arena+24
	.byte	0x22
	.byte	0
.LVUS19:
	.uleb128 .LVU126
	.uleb128 .LVU136
.LLST19:
	.byte	0x8
	.quad	.LVL28
	.uleb128 .LVL31-.LVL28
	.uleb128 0x1
	.byte	0x50
	.byte	0
.LVUS21:
	.uleb128 .LVU116
	.uleb128 .LVU126
.LLST21:
	.byte	0x8
	.quad	.LVL23
	.uleb128 .LVL28-.LVL23
	.uleb128 0x2
	.byte	0x32
	.byte	0x9f
	.byte	0
.LVUS22:
	.uleb128 .LVU120
	.uleb128 .LVU124
	.uleb128 .LVU124
	.uleb128 .LVU126
.LLST22:
	.byte	0x6
	.quad	.LVL25
	.byte	0x4
	.uleb128 .LVL25-.LVL25
	.uleb128 .LVL27-.LVL25
	.uleb128 0xd
	.byte	0x71
	.sleb128 0
	.byte	0x3
	.quad	arena
	.byte	0x22
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL27-.LVL25
	.uleb128 .LVL28-.LVL25
	.uleb128 0x1
	.byte	0x50
	.byte	0
.LVUS8:
	.uleb128 .LVU70
	.uleb128 .LVU74
	.uleb128 .LVU79
	.uleb128 .LVU100
.LLST8:
	.byte	0x6
	.quad	.LVL14
	.byte	0x4
	.uleb128 .LVL14-.LVL14
	.uleb128 .LVL15-.LVL14
	.uleb128 0x1
	.byte	0x51
	.byte	0x4
	.uleb128 .LVL16-.LVL14
	.uleb128 .LVL20-.LVL14
	.uleb128 0x1
	.byte	0x51
	.byte	0
.LVUS10:
	.uleb128 .LVU82
	.uleb128 .LVU98
.LLST10:
	.byte	0x8
	.quad	.LVL17
	.uleb128 .LVL19-.LVL17
	.uleb128 0x1
	.byte	0x51
	.byte	0
.LVUS11:
	.uleb128 .LVU95
	.uleb128 .LVU100
.LLST11:
	.byte	0x8
	.quad	.LVL19
	.uleb128 .LVL20-.LVL19
	.uleb128 0x1
	.byte	0x54
	.byte	0
.LVUS13:
	.uleb128 .LVU84
	.uleb128 .LVU95
.LLST13:
	.byte	0x8
	.quad	.LVL17
	.uleb128 .LVL19-.LVL17
	.uleb128 0x2
	.byte	0x30
	.byte	0x9f
	.byte	0
.LVUS14:
	.uleb128 .LVU92
	.uleb128 .LVU95
.LLST14:
	.byte	0x8
	.quad	.LVL18
	.uleb128 .LVL19-.LVL18
	.uleb128 0x1
	.byte	0x54
	.byte	0
.LVUS2:
	.uleb128 .LVU28
	.uleb128 .LVU37
.LLST2:
	.byte	0x8
	.quad	.LVL1
	.uleb128 .LVL2-.LVL1
	.uleb128 0x2
	.byte	0x31
	.byte	0x9f
	.byte	0
.LVUS3:
	.uleb128 .LVU35
	.uleb128 .LVU37
.LLST3:
	.byte	0x8
	.quad	.LVL2
	.uleb128 .LVL2-.LVL2
	.uleb128 0x1
	.byte	0x54
	.byte	0
.LVUS5:
	.uleb128 .LVU39
	.uleb128 .LVU52
	.uleb128 .LVU56
	.uleb128 .LVU64
.LLST5:
	.byte	0x6
	.quad	.LVL2
	.byte	0x4
	.uleb128 .LVL2-.LVL2
	.uleb128 .LVL7-.LVL2
	.uleb128 0x1
	.byte	0x5e
	.byte	0x4
	.uleb128 .LVL9-.LVL2
	.uleb128 .LVL12-.LVL2
	.uleb128 0x1
	.byte	0x5e
	.byte	0
.LVUS7:
	.uleb128 .LVU42
	.uleb128 .LVU43
	.uleb128 .LVU43
	.uleb128 .LVU44
	.uleb128 .LVU44
	.uleb128 .LVU45
	.uleb128 .LVU45
	.uleb128 .LVU52
	.uleb128 .LVU56
	.uleb128 .LVU57
.LLST7:
	.byte	0x6
	.quad	.LVL2
	.byte	0x4
	.uleb128 .LVL2-.LVL2
	.uleb128 .LVL3-.LVL2
	.uleb128 0x2
	.byte	0x30
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL3-.LVL2
	.uleb128 .LVL3-.LVL2
	.uleb128 0xf
	.byte	0x76
	.sleb128 0
	.byte	0x3
	.quad	names
	.byte	0x1c
	.byte	0x34
	.byte	0x25
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL3-.LVL2
	.uleb128 .LVL4-.LVL2
	.uleb128 0x11
	.byte	0x76
	.sleb128 0
	.byte	0x3
	.quad	names
	.byte	0x1c
	.byte	0x34
	.byte	0x25
	.byte	0x23
	.uleb128 0x1
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL4-.LVL2
	.uleb128 .LVL7-.LVL2
	.uleb128 0xf
	.byte	0x7f
	.sleb128 0
	.byte	0x3
	.quad	names
	.byte	0x1c
	.byte	0x34
	.byte	0x25
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL9-.LVL2
	.uleb128 .LVL10-.LVL2
	.uleb128 0x2
	.byte	0x30
	.byte	0x9f
	.byte	0
.LVUS36:
	.uleb128 0
	.uleb128 .LVU270
	.uleb128 .LVU270
	.uleb128 .LVU272
	.uleb128 .LVU272
	.uleb128 .LVU294
	.uleb128 .LVU294
	.uleb128 .LVU297
	.uleb128 .LVU297
	.uleb128 .LVU298
	.uleb128 .LVU298
	.uleb128 .LVU299
	.uleb128 .LVU299
	.uleb128 .LVU301
	.uleb128 .LVU301
	.uleb128 .LVU304
	.uleb128 .LVU304
	.uleb128 .LVU307
	.uleb128 .LVU307
	.uleb128 0
.LLST36:
	.byte	0x6
	.quad	.LVL74
	.byte	0x4
	.uleb128 .LVL74-.LVL74
	.uleb128 .LVL76-.LVL74
	.uleb128 0x1
	.byte	0x55
	.byte	0x4
	.uleb128 .LVL76-.LVL74
	.uleb128 .LVL78-.LVL74
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL78-.LVL74
	.uleb128 .LVL84-.LVL74
	.uleb128 0x4
	.byte	0xa3
	.uleb128 0x1
	.byte	0x55
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL84-.LVL74
	.uleb128 .LVL85-.LVL74
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL85-.LVL74
	.uleb128 .LVL86-.LVL74
	.uleb128 0x1
	.byte	0x55
	.byte	0x4
	.uleb128 .LVL86-.LVL74
	.uleb128 .LVL87-.LVL74
	.uleb128 0x4
	.byte	0xa3
	.uleb128 0x1
	.byte	0x55
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL87-.LVL74
	.uleb128 .LVL88-.LVL74
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL88-.LVL74
	.uleb128 .LVL92-.LVL74
	.uleb128 0x4
	.byte	0xa3
	.uleb128 0x1
	.byte	0x55
	.byte	0x9f
	.byte	0x4
	.uleb128 .LVL92-.LVL74
	.uleb128 .LVL93-.LVL74
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL93-.LVL74
	.uleb128 .LFE11-.LVL74
	.uleb128 0x4
	.byte	0xa3
	.uleb128 0x1
	.byte	0x55
	.byte	0x9f
	.byte	0
.LVUS38:
	.uleb128 .LVU265
	.uleb128 .LVU270
	.uleb128 .LVU270
	.uleb128 .LVU293
	.uleb128 .LVU302
	.uleb128 .LVU304
.LLST38:
	.byte	0x6
	.quad	.LVL75
	.byte	0x4
	.uleb128 .LVL75-.LVL75
	.uleb128 .LVL76-.LVL75
	.uleb128 0x1
	.byte	0x55
	.byte	0x4
	.uleb128 .LVL76-.LVL75
	.uleb128 .LVL83-.LVL75
	.uleb128 0x1
	.byte	0x53
	.byte	0x4
	.uleb128 .LVL89-.LVL75
	.uleb128 .LVL92-.LVL75
	.uleb128 0x1
	.byte	0x53
	.byte	0
.LVUS39:
	.uleb128 .LVU267
	.uleb128 .LVU271
.LLST39:
	.byte	0x8
	.quad	.LVL75
	.uleb128 .LVL77-.LVL75
	.uleb128 0x3
	.byte	0x8
	.byte	0x28
	.byte	0x9f
	.byte	0
.LVUS40:
	.uleb128 .LVU274
	.uleb128 .LVU277
.LLST40:
	.byte	0x8
	.quad	.LVL78
	.uleb128 .LVL79-.LVL78
	.uleb128 0x3
	.byte	0x8
	.byte	0x20
	.byte	0x9f
	.byte	0
.LVUS42:
	.uleb128 .LVU289
	.uleb128 .LVU294
.LLST42:
	.byte	0x8
	.quad	.LVL82
	.uleb128 .LVL84-.LVL82
	.uleb128 0x3
	.byte	0x8
	.byte	0x29
	.byte	0x9f
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
	.quad	.LFB12
	.quad	.LFE12-.LFB12
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
.LLRL1:
	.byte	0x5
	.quad	.LBB57
	.byte	0x4
	.uleb128 .LBB57-.LBB57
	.uleb128 .LBE57-.LBB57
	.byte	0x4
	.uleb128 .LBB66-.LBB57
	.uleb128 .LBE66-.LBB57
	.byte	0
.LLRL4:
	.byte	0x5
	.quad	.LBB60
	.byte	0x4
	.uleb128 .LBB60-.LBB60
	.uleb128 .LBE60-.LBB60
	.byte	0x4
	.uleb128 .LBB67-.LBB60
	.uleb128 .LBE67-.LBB60
	.byte	0x4
	.uleb128 .LBB68-.LBB60
	.uleb128 .LBE68-.LBB60
	.byte	0
.LLRL6:
	.byte	0x5
	.quad	.LBB62
	.byte	0x4
	.uleb128 .LBB62-.LBB62
	.uleb128 .LBE62-.LBB62
	.byte	0x4
	.uleb128 .LBB63-.LBB62
	.uleb128 .LBE63-.LBB62
	.byte	0
.LLRL9:
	.byte	0x5
	.quad	.LBB70
	.byte	0x4
	.uleb128 .LBB70-.LBB70
	.uleb128 .LBE70-.LBB70
	.byte	0x4
	.uleb128 .LBB79-.LBB70
	.uleb128 .LBE79-.LBB70
	.byte	0
.LLRL12:
	.byte	0x5
	.quad	.LBB72
	.byte	0x4
	.uleb128 .LBB72-.LBB72
	.uleb128 .LBE72-.LBB72
	.byte	0x4
	.uleb128 .LBB76-.LBB72
	.uleb128 .LBE76-.LBB72
	.byte	0x4
	.uleb128 .LBB77-.LBB72
	.uleb128 .LBE77-.LBB72
	.byte	0
.LLRL16:
	.byte	0x5
	.quad	.LBB81
	.byte	0x4
	.uleb128 .LBB81-.LBB81
	.uleb128 .LBE81-.LBB81
	.byte	0x4
	.uleb128 .LBB90-.LBB81
	.uleb128 .LBE90-.LBB81
	.byte	0
.LLRL20:
	.byte	0x5
	.quad	.LBB83
	.byte	0x4
	.uleb128 .LBB83-.LBB83
	.uleb128 .LBE83-.LBB83
	.byte	0x4
	.uleb128 .LBB87-.LBB83
	.uleb128 .LBE87-.LBB83
	.byte	0x4
	.uleb128 .LBB88-.LBB83
	.uleb128 .LBE88-.LBB83
	.byte	0
.LLRL37:
	.byte	0x5
	.quad	.LBB107
	.byte	0x4
	.uleb128 .LBB107-.LBB107
	.uleb128 .LBE107-.LBB107
	.byte	0x4
	.uleb128 .LBB119-.LBB107
	.uleb128 .LBE119-.LBB107
	.byte	0x4
	.uleb128 .LBB120-.LBB107
	.uleb128 .LBE120-.LBB107
	.byte	0
.LLRL41:
	.byte	0x5
	.quad	.LBB113
	.byte	0x4
	.uleb128 .LBB113-.LBB113
	.uleb128 .LBE113-.LBB113
	.byte	0x4
	.uleb128 .LBB116-.LBB113
	.uleb128 .LBE116-.LBB113
	.byte	0
.LLRL45:
	.byte	0x7
	.quad	.Ltext0
	.uleb128 .Letext0-.Ltext0
	.byte	0x7
	.quad	.LFB12
	.uleb128 .LFE12-.LFB12
	.byte	0
.Ldebug_ranges3:
	.section	.debug_line,"",@progbits
.Ldebug_line0:
	.section	.debug_str,"MS",@progbits,1
.LASF66:
	.string	"printf"
.LASF9:
	.string	"__off_t"
.LASF19:
	.string	"_ISgraph"
.LASF38:
	.string	"_chain"
.LASF84:
	.string	"print"
.LASF67:
	.string	"strcmp"
.LASF24:
	.string	"size_t"
.LASF44:
	.string	"_shortbuf"
.LASF80:
	.string	"GNU C11 13.3.0 -mtune=generic -march=x86-64 -g -O2 -std=c11 -fno-asynchronous-unwind-tables"
.LASF17:
	.string	"_ISspace"
.LASF13:
	.string	"_ISlower"
.LASF14:
	.string	"_ISalpha"
.LASF47:
	.string	"_codecvt"
.LASF15:
	.string	"_ISdigit"
.LASF6:
	.string	"signed char"
.LASF39:
	.string	"_fileno"
.LASF27:
	.string	"_IO_read_end"
.LASF8:
	.string	"long int"
.LASF77:
	.string	"intern"
.LASF25:
	.string	"_flags"
.LASF78:
	.string	"cons"
.LASF23:
	.string	"_ISalnum"
.LASF42:
	.string	"_cur_column"
.LASF79:
	.string	"putchar"
.LASF56:
	.string	"_IO_codecvt"
.LASF58:
	.string	"CONS"
.LASF41:
	.string	"_old_offset"
.LASF46:
	.string	"_offset"
.LASF20:
	.string	"_ISblank"
.LASF61:
	.string	"arena"
.LASF22:
	.string	"_ISpunct"
.LASF55:
	.string	"_IO_marker"
.LASF4:
	.string	"unsigned int"
.LASF50:
	.string	"_freeres_buf"
.LASF70:
	.string	"strlen"
.LASF5:
	.string	"long unsigned int"
.LASF64:
	.string	"nnames"
.LASF30:
	.string	"_IO_write_ptr"
.LASF3:
	.string	"short unsigned int"
.LASF34:
	.string	"_IO_save_base"
.LASF85:
	.string	"__builtin_memcpy"
.LASF45:
	.string	"_lock"
.LASF40:
	.string	"_flags2"
.LASF52:
	.string	"_mode"
.LASF65:
	.string	"putc"
.LASF71:
	.string	"stdout"
.LASF76:
	.string	"tail"
.LASF26:
	.string	"_IO_read_ptr"
.LASF81:
	.string	"_IO_lock_t"
.LASF59:
	.string	"_IO_FILE"
.LASF62:
	.string	"used"
.LASF37:
	.string	"_markers"
.LASF2:
	.string	"unsigned char"
.LASF33:
	.string	"_IO_buf_end"
.LASF69:
	.string	"strncmp"
.LASF7:
	.string	"short int"
.LASF57:
	.string	"_IO_wide_data"
.LASF43:
	.string	"_vtable_offset"
.LASF54:
	.string	"FILE"
.LASF63:
	.string	"names"
.LASF75:
	.string	"head"
.LASF60:
	.string	"cell"
.LASF11:
	.string	"char"
.LASF82:
	.string	"__ctype_b_loc"
.LASF21:
	.string	"_IScntrl"
.LASF16:
	.string	"_ISxdigit"
.LASF10:
	.string	"__off64_t"
.LASF28:
	.string	"_IO_read_base"
.LASF68:
	.string	"memcpy"
.LASF36:
	.string	"_IO_save_end"
.LASF51:
	.string	"__pad5"
.LASF31:
	.string	"_IO_write_end"
.LASF53:
	.string	"_unused2"
.LASF12:
	.string	"_ISupper"
.LASF35:
	.string	"_IO_backup_base"
.LASF74:
	.string	"read"
.LASF49:
	.string	"_freeres_list"
.LASF48:
	.string	"_wide_data"
.LASF72:
	.string	"args"
.LASF83:
	.string	"main"
.LASF29:
	.string	"_IO_write_base"
.LASF32:
	.string	"_IO_buf_base"
.LASF18:
	.string	"_ISprint"
.LASF73:
	.string	"eval"
	.section	.debug_line_str,"MS",@progbits,1
.LASF1:
	.string	"."
.LASF0:
	.string	"lisp.c"
	.ident	"GCC: (GNU) 13.3.0"
	.section	.note.GNU-stack,"",@progbits
