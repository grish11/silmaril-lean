	.file	"lisp.c"
	.text
.Ltext0:
	.cfi_sections	.debug_frame
	.file 0 "." "lisp.c"
	.local	arena
	.comm	arena,40960,32
	.local	used
	.comm	used,4,4
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
	.text
	.type	mk, @function
mk:
.LFB0:
	.file 1 "lisp.c"
	.loc 1 14 29
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movl	%edi, -20(%rbp)
	.loc 1 14 52
	movl	used(%rip), %eax
	leal	1(%rax), %edx
	movl	%edx, used(%rip)
	.loc 1 14 37
	movslq	%eax, %rdx
	movq	%rdx, %rax
	salq	$2, %rax
	addq	%rdx, %rax
	salq	$3, %rax
	addq	$arena, %rax
	movq	%rax, -8(%rbp)
	.loc 1 14 64
	movq	-8(%rbp), %rax
	movl	-20(%rbp), %edx
	movl	%edx, (%rax)
	.loc 1 14 76
	movq	-8(%rbp), %rax
	.loc 1 14 79
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	mk, .-mk
	.type	num, @function
num:
.LFB1:
	.loc 1 15 26
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$24, %rsp
	movq	%rdi, -24(%rbp)
	.loc 1 15 38
	movl	$0, %edi
	call	mk
	movq	%rax, -8(%rbp)
	.loc 1 15 54 discriminator 1
	movq	-8(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 8(%rax)
	.loc 1 15 66 discriminator 1
	movq	-8(%rbp), %rax
	.loc 1 15 69
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1:
	.size	num, .-num
	.type	cons, @function
cons:
.LFB2:
	.loc 1 16 37
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
	.loc 1 16 49
	movl	$2, %edi
	call	mk
	movq	%rax, -8(%rbp)
	.loc 1 16 66 discriminator 1
	movq	-8(%rbp), %rax
	movq	-24(%rbp), %rdx
	movq	%rdx, 24(%rax)
	.loc 1 16 78 discriminator 1
	movq	-8(%rbp), %rax
	movq	-32(%rbp), %rdx
	movq	%rdx, 32(%rax)
	.loc 1 16 90 discriminator 1
	movq	-8(%rbp), %rax
	.loc 1 16 93
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE2:
	.size	cons, .-cons
	.local	p
	.comm	p,8,8
	.local	names
	.comm	names,1024,32
	.local	nnames
	.comm	nnames,4,4
	.type	intern, @function
intern:
.LFB3:
	.loc 1 23 1
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$32, %rsp
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
.LBB2:
	.loc 1 24 12
	movl	$0, -4(%rbp)
	.loc 1 24 3
	jmp	.L8
.L11:
	.loc 1 25 21
	movl	-4(%rbp), %eax
	cltq
	salq	$4, %rax
	addq	$names, %rax
	.loc 1 25 9
	movq	%rax, %rdi
	call	strlen
	.loc 1 25 8 discriminator 1
	cmpq	%rax, -32(%rbp)
	jne	.L9
	.loc 1 25 48 discriminator 1
	movl	-4(%rbp), %eax
	cltq
	salq	$4, %rax
	leaq	names(%rax), %rcx
	.loc 1 25 35 discriminator 1
	movq	-32(%rbp), %rdx
	movq	-24(%rbp), %rax
	movq	%rax, %rsi
	movq	%rcx, %rdi
	call	strncmp
	.loc 1 25 31 discriminator 1
	testl	%eax, %eax
	jne	.L9
	.loc 1 26 14
	movl	-4(%rbp), %eax
	cltq
	salq	$4, %rax
	addq	$names, %rax
	jmp	.L10
.L9:
	.loc 1 24 32 discriminator 2
	addl	$1, -4(%rbp)
.L8:
	.loc 1 24 21 discriminator 1
	movl	nnames(%rip), %eax
	cmpl	%eax, -4(%rbp)
	jl	.L11
.LBE2:
	.loc 1 27 15
	movl	nnames(%rip), %eax
	cltq
	salq	$4, %rax
	leaq	names(%rax), %rcx
	.loc 1 27 3
	movq	-32(%rbp), %rdx
	movq	-24(%rbp), %rax
	movq	%rax, %rsi
	movq	%rcx, %rdi
	call	memcpy
	.loc 1 28 16
	movl	nnames(%rip), %eax
	.loc 1 28 20
	cltq
	salq	$4, %rax
	movq	%rax, %rdx
	movq	-32(%rbp), %rax
	addq	%rdx, %rax
	addq	$names, %rax
	movb	$0, (%rax)
	.loc 1 29 22
	movl	nnames(%rip), %eax
	leal	1(%rax), %edx
	movl	%edx, nnames(%rip)
	.loc 1 29 10
	cltq
	salq	$4, %rax
	addq	$names, %rax
.L10:
	.loc 1 30 1
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE3:
	.size	intern, .-intern
	.type	read, @function
read:
.LFB4:
	.loc 1 33 1
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$48, %rsp
	.loc 1 34 9
	jmp	.L13
.L14:
	.loc 1 34 39 discriminator 2
	movq	p(%rip), %rax
	addq	$1, %rax
	movq	%rax, p(%rip)
.L13:
	.loc 1 34 10 discriminator 1
	call	__ctype_b_loc
	movq	(%rax), %rdx
	movq	p(%rip), %rax
	movzbl	(%rax), %eax
	movzbl	%al, %eax
	addq	%rax, %rax
	addq	%rdx, %rax
	movzwl	(%rax), %eax
	movzwl	%ax, %eax
	andl	$8192, %eax
	testl	%eax, %eax
	jne	.L14
	.loc 1 35 7
	movq	p(%rip), %rax
	movzbl	(%rax), %eax
	.loc 1 35 6
	cmpb	$40, %al
	jne	.L15
.LBB3:
	.loc 1 36 6
	movq	p(%rip), %rax
	addq	$1, %rax
	movq	%rax, p(%rip)
	.loc 1 37 11
	movq	$nil, -40(%rbp)
	.loc 1 37 26
	leaq	-40(%rbp), %rax
	movq	%rax, -8(%rbp)
	.loc 1 39 13
	jmp	.L16
.L17:
	.loc 1 39 43 discriminator 2
	movq	p(%rip), %rax
	addq	$1, %rax
	movq	%rax, p(%rip)
.L16:
	.loc 1 39 14 discriminator 1
	call	__ctype_b_loc
	movq	(%rax), %rdx
	movq	p(%rip), %rax
	movzbl	(%rax), %eax
	movzbl	%al, %eax
	addq	%rax, %rax
	addq	%rdx, %rax
	movzwl	(%rax), %eax
	movzwl	%ax, %eax
	andl	$8192, %eax
	testl	%eax, %eax
	jne	.L17
	.loc 1 40 11
	movq	p(%rip), %rax
	movzbl	(%rax), %eax
	.loc 1 40 10
	cmpb	$41, %al
	jne	.L18
	.loc 1 40 25 discriminator 1
	movq	p(%rip), %rax
	addq	$1, %rax
	movq	%rax, p(%rip)
	.loc 1 40 36 discriminator 1
	movq	-40(%rbp), %rax
	.loc 1 40 36 is_stmt 0
	jmp	.L21
.L18:
	.loc 1 41 15 is_stmt 1
	call	read
	.loc 1 41 15 is_stmt 0 discriminator 1
	movl	$nil, %esi
	movq	%rax, %rdi
	call	cons
	.loc 1 41 13 is_stmt 1 discriminator 2
	movq	-8(%rbp), %rdx
	movq	%rax, (%rdx)
	.loc 1 42 16
	movq	-8(%rbp), %rax
	movq	(%rax), %rax
	.loc 1 42 12
	addq	$32, %rax
	movq	%rax, -8(%rbp)
	.loc 1 39 13
	jmp	.L16
.L15:
.LBE3:
	.loc 1 45 7
	call	__ctype_b_loc
	.loc 1 45 7 is_stmt 0 discriminator 1
	movq	(%rax), %rdx
	movq	p(%rip), %rax
	movzbl	(%rax), %eax
	movzbl	%al, %eax
	addq	%rax, %rax
	addq	%rdx, %rax
	movzwl	(%rax), %eax
	movzwl	%ax, %eax
	andl	$2048, %eax
	.loc 1 45 6 is_stmt 1 discriminator 1
	testl	%eax, %eax
	je	.L22
.LBB4:
	.loc 1 46 10
	movq	$0, -16(%rbp)
	.loc 1 47 11
	jmp	.L23
.L24:
	.loc 1 47 47 discriminator 2
	movq	-16(%rbp), %rdx
	movq	%rdx, %rax
	salq	$2, %rax
	addq	%rdx, %rax
	addq	%rax, %rax
	movq	%rax, %rcx
	.loc 1 47 56 discriminator 2
	movq	p(%rip), %rax
	leaq	1(%rax), %rdx
	movq	%rdx, p(%rip)
	.loc 1 47 54 discriminator 2
	movzbl	(%rax), %eax
	movsbl	%al, %eax
	.loc 1 47 59 discriminator 2
	subl	$48, %eax
	cltq
	.loc 1 47 42 discriminator 2
	addq	%rcx, %rax
	movq	%rax, -16(%rbp)
.L23:
	.loc 1 47 12 discriminator 1
	call	__ctype_b_loc
	movq	(%rax), %rdx
	movq	p(%rip), %rax
	movzbl	(%rax), %eax
	movzbl	%al, %eax
	addq	%rax, %rax
	addq	%rdx, %rax
	movzwl	(%rax), %eax
	movzwl	%ax, %eax
	andl	$2048, %eax
	testl	%eax, %eax
	jne	.L24
	.loc 1 48 12
	movq	-16(%rbp), %rax
	movq	%rax, %rdi
	call	num
	jmp	.L21
.L22:
.LBE4:
	.loc 1 50 15
	movq	p(%rip), %rax
	movq	%rax, -24(%rbp)
	.loc 1 51 9
	jmp	.L25
.L27:
	.loc 1 51 72 discriminator 5
	movq	p(%rip), %rax
	addq	$1, %rax
	movq	%rax, p(%rip)
.L25:
	.loc 1 51 10 discriminator 1
	movq	p(%rip), %rax
	movzbl	(%rax), %eax
	.loc 1 51 57 discriminator 1
	testb	%al, %al
	je	.L26
	.loc 1 51 17 discriminator 2
	call	__ctype_b_loc
	.loc 1 51 17 is_stmt 0 discriminator 1
	movq	(%rax), %rdx
	movq	p(%rip), %rax
	movzbl	(%rax), %eax
	movzbl	%al, %eax
	addq	%rax, %rax
	addq	%rdx, %rax
	movzwl	(%rax), %eax
	movzwl	%ax, %eax
	andl	$8192, %eax
	.loc 1 51 13 is_stmt 1 discriminator 1
	testl	%eax, %eax
	jne	.L26
	.loc 1 51 47 discriminator 3
	movq	p(%rip), %rax
	movzbl	(%rax), %eax
	.loc 1 51 44 discriminator 3
	cmpb	$40, %al
	je	.L26
	.loc 1 51 60 discriminator 4
	movq	p(%rip), %rax
	movzbl	(%rax), %eax
	.loc 1 51 57 discriminator 4
	cmpb	$41, %al
	jne	.L27
.L26:
	.loc 1 52 13
	movl	$1, %edi
	call	mk
	movq	%rax, -32(%rbp)
	.loc 1 53 33
	movq	p(%rip), %rax
	subq	-24(%rbp), %rax
	.loc 1 53 12
	movq	%rax, %rdx
	movq	-24(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	intern
	.loc 1 53 10 discriminator 1
	movq	-32(%rbp), %rdx
	movq	%rax, 16(%rdx)
	.loc 1 54 10
	movq	-32(%rbp), %rax
.L21:
	.loc 1 55 1
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE4:
	.size	read, .-read
	.section	.rodata
.LC0:
	.string	"quote"
.LC1:
	.string	"if"
.LC2:
	.string	"car"
.LC3:
	.string	"cdr"
.LC4:
	.string	"cons"
.LC5:
	.string	"*"
	.text
	.type	eval, @function
eval:
.LFB5:
	.loc 1 58 1
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%rbx
	subq	$56, %rsp
	.cfi_offset 3, -24
	movq	%rdi, -56(%rbp)
	.loc 1 59 8
	movq	-56(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 59 6
	cmpl	$2, %eax
	je	.L29
	.loc 1 59 30 discriminator 1
	movq	-56(%rbp), %rax
	.loc 1 59 30 is_stmt 0
	jmp	.L30
.L29:
	.loc 1 60 21 is_stmt 1
	movq	-56(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 60 15
	movq	16(%rax), %rax
	movq	%rax, -40(%rbp)
	.loc 1 61 9
	movq	-56(%rbp), %rax
	movq	32(%rax), %rax
	movq	%rax, -24(%rbp)
	.loc 1 62 8
	movq	-40(%rbp), %rax
	movl	$.LC0, %esi
	movq	%rax, %rdi
	call	strcmp
	.loc 1 62 6 discriminator 1
	testl	%eax, %eax
	jne	.L31
	.loc 1 62 40 discriminator 1
	movq	-24(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 62 40 is_stmt 0
	jmp	.L30
.L31:
	.loc 1 63 8 is_stmt 1
	movq	-40(%rbp), %rax
	movl	$.LC1, %esi
	movq	%rax, %rdi
	call	strcmp
	.loc 1 63 6 discriminator 1
	testl	%eax, %eax
	jne	.L32
	.loc 1 64 26
	movq	-24(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 64 17
	movq	%rax, %rdi
	call	eval
	.loc 1 64 32 discriminator 1
	movq	8(%rax), %rax
	.loc 1 64 12 discriminator 1
	testq	%rax, %rax
	je	.L33
	.loc 1 64 44 discriminator 1
	movq	-24(%rbp), %rax
	movq	32(%rax), %rax
	.loc 1 64 12 discriminator 1
	movq	24(%rax), %rax
	jmp	.L34
.L33:
	.loc 1 64 61 discriminator 2
	movq	-24(%rbp), %rax
	movq	32(%rax), %rax
	.loc 1 64 66 discriminator 2
	movq	32(%rax), %rax
	.loc 1 64 12 discriminator 2
	movq	24(%rax), %rax
.L34:
	.loc 1 64 12 is_stmt 0 discriminator 4
	movq	%rax, %rdi
	call	eval
	.loc 1 64 12
	jmp	.L30
.L32:
	.loc 1 65 8 is_stmt 1
	movq	-40(%rbp), %rax
	movl	$.LC2, %esi
	movq	%rax, %rdi
	call	strcmp
	.loc 1 65 6 discriminator 1
	testl	%eax, %eax
	jne	.L35
	.loc 1 65 43 discriminator 1
	movq	-24(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 65 34 discriminator 1
	movq	%rax, %rdi
	call	eval
	.loc 1 65 49 discriminator 1
	movq	24(%rax), %rax
	.loc 1 65 49 is_stmt 0
	jmp	.L30
.L35:
	.loc 1 66 8 is_stmt 1
	movq	-40(%rbp), %rax
	movl	$.LC3, %esi
	movq	%rax, %rdi
	call	strcmp
	.loc 1 66 6 discriminator 1
	testl	%eax, %eax
	jne	.L36
	.loc 1 66 43 discriminator 1
	movq	-24(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 66 34 discriminator 1
	movq	%rax, %rdi
	call	eval
	.loc 1 66 49 discriminator 1
	movq	32(%rax), %rax
	.loc 1 66 49 is_stmt 0
	jmp	.L30
.L36:
	.loc 1 67 8 is_stmt 1
	movq	-40(%rbp), %rax
	movl	$.LC4, %esi
	movq	%rax, %rdi
	call	strcmp
	.loc 1 67 6 discriminator 1
	testl	%eax, %eax
	jne	.L37
	.loc 1 67 66 discriminator 1
	movq	-24(%rbp), %rax
	movq	32(%rax), %rax
	.loc 1 67 71 discriminator 1
	movq	24(%rax), %rax
	.loc 1 67 35 discriminator 1
	movq	%rax, %rdi
	call	eval
	movq	%rax, %rbx
	.loc 1 67 49 discriminator 1
	movq	-24(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 67 35 discriminator 1
	movq	%rax, %rdi
	call	eval
	.loc 1 67 35 is_stmt 0 discriminator 2
	movq	%rbx, %rsi
	movq	%rax, %rdi
	call	cons
	.loc 1 67 35
	jmp	.L30
.L37:
	.loc 1 68 15 is_stmt 1
	movq	-40(%rbp), %rax
	movl	$.LC5, %esi
	movq	%rax, %rdi
	call	strcmp
	.loc 1 68 14 discriminator 1
	testl	%eax, %eax
	sete	%al
	.loc 1 68 8 discriminator 1
	movzbl	%al, %eax
	movq	%rax, -32(%rbp)
	.loc 1 69 3
	jmp	.L38
.L41:
	.loc 1 70 12
	movq	-40(%rbp), %rax
	movzbl	(%rax), %eax
	.loc 1 70 53
	cmpb	$42, %al
	jne	.L39
	.loc 1 70 41 discriminator 1
	movq	-24(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 70 32 discriminator 1
	movq	%rax, %rdi
	call	eval
	.loc 1 70 47 discriminator 1
	movq	8(%rax), %rax
	.loc 1 70 53 discriminator 1
	imulq	-32(%rbp), %rax
	jmp	.L40
.L39:
	.loc 1 70 70 discriminator 2
	movq	-24(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 70 61 discriminator 2
	movq	%rax, %rdi
	call	eval
	.loc 1 70 76 discriminator 1
	movq	8(%rax), %rdx
	.loc 1 70 53 discriminator 1
	movq	-32(%rbp), %rax
	addq	%rdx, %rax
.L40:
	.loc 1 70 9 discriminator 4
	movq	%rax, -32(%rbp)
	.loc 1 69 34
	movq	-24(%rbp), %rax
	movq	32(%rax), %rax
	movq	%rax, -24(%rbp)
.L38:
	.loc 1 69 14 discriminator 1
	movq	-24(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 69 20 discriminator 1
	cmpl	$2, %eax
	je	.L41
	.loc 1 71 10
	movq	-32(%rbp), %rax
	movq	%rax, %rdi
	call	num
.L30:
	.loc 1 72 1
	movq	-8(%rbp), %rbx
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE5:
	.size	eval, .-eval
	.section	.rodata
.LC6:
	.string	"%ld"
.LC7:
	.string	"%s"
.LC8:
	.string	"()"
.LC9:
	.string	" . "
	.text
	.type	print, @function
print:
.LFB6:
	.loc 1 75 1
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	.loc 1 76 8
	movq	-8(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 76 6
	testl	%eax, %eax
	jne	.L43
	.loc 1 76 22 discriminator 1
	movq	-8(%rbp), %rax
	movq	8(%rax), %rax
	movq	%rax, %rsi
	movl	$.LC6, %edi
	movl	$0, %eax
	call	printf
	.loc 1 90 1
	jmp	.L53
.L43:
	.loc 1 77 13
	movq	-8(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 77 11
	cmpl	$1, %eax
	jne	.L45
	.loc 1 77 27 discriminator 1
	movq	-8(%rbp), %rax
	movq	16(%rax), %rax
	movq	%rax, %rsi
	movl	$.LC7, %edi
	movl	$0, %eax
	call	printf
	.loc 1 90 1
	jmp	.L53
.L45:
	.loc 1 78 13
	movq	-8(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 78 11
	cmpl	$3, %eax
	jne	.L46
	.loc 1 78 27 discriminator 1
	movl	$.LC8, %edi
	movl	$0, %eax
	call	printf
	.loc 1 90 1
	jmp	.L53
.L46:
	.loc 1 80 5
	movl	$40, %edi
	call	putchar
.L49:
	.loc 1 82 14
	movq	-8(%rbp), %rax
	movq	24(%rax), %rax
	.loc 1 82 7
	movq	%rax, %rdi
	call	print
	.loc 1 83 9
	movq	-8(%rbp), %rax
	movq	32(%rax), %rax
	movq	%rax, -8(%rbp)
	.loc 1 84 12
	movq	-8(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 84 10
	cmpl	$2, %eax
	jne	.L52
	.loc 1 85 7
	movl	$32, %edi
	call	putchar
	.loc 1 82 7
	jmp	.L49
.L52:
	.loc 1 84 27
	nop
	.loc 1 87 10
	movq	-8(%rbp), %rax
	movl	(%rax), %eax
	.loc 1 87 8
	cmpl	$3, %eax
	je	.L50
	.loc 1 87 26 discriminator 1
	movl	$.LC9, %edi
	movl	$0, %eax
	call	printf
	.loc 1 87 41 discriminator 1
	movq	-8(%rbp), %rax
	movq	%rax, %rdi
	call	print
.L50:
	.loc 1 88 5
	movl	$41, %edi
	call	putchar
.L53:
	.loc 1 90 1
	nop
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE6:
	.size	print, .-print
	.section	.rodata
	.align 8
.LC10:
	.string	"(+ 1 (* 2 3) (if 0 100 (car (quote (4 5)))))"
.LC11:
	.string	"(cons 1 (quote (2 3)))"
	.text
	.globl	main
	.type	main, @function
main:
.LFB7:
	.loc 1 93 1
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	.loc 1 94 5
	movq	$.LC10, p(%rip)
	.loc 1 95 3
	call	read
	.loc 1 95 3 is_stmt 0 discriminator 1
	movq	%rax, %rdi
	call	eval
	.loc 1 95 3 discriminator 2
	movq	%rax, %rdi
	call	print
	.loc 1 96 3 is_stmt 1
	movl	$10, %edi
	call	putchar
	.loc 1 97 5
	movq	$.LC11, p(%rip)
	.loc 1 98 3
	call	read
	.loc 1 98 3 is_stmt 0 discriminator 1
	movq	%rax, %rdi
	call	eval
	.loc 1 98 3 discriminator 2
	movq	%rax, %rdi
	call	print
	.loc 1 99 3 is_stmt 1
	movl	$10, %edi
	call	putchar
	.loc 1 100 10
	movl	$0, %eax
	.loc 1 101 1
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE7:
	.size	main, .-main
.Letext0:
	.file 2 "/usr/local/lib/gcc/x86_64-linux-gnu/13.3.0/include/stddef.h"
	.file 3 "/usr/include/stdio.h"
	.file 4 "/usr/include/string.h"
	.file 5 "/usr/include/ctype.h"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0x508
	.value	0x5
	.byte	0x1
	.byte	0x8
	.long	.Ldebug_abbrev0
	.uleb128 0x13
	.long	.LASF43
	.byte	0x1d
	.long	.LASF0
	.long	.LASF1
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.long	.Ldebug_line0
	.uleb128 0x3
	.byte	0x1
	.byte	0x8
	.long	.LASF2
	.uleb128 0x3
	.byte	0x2
	.byte	0x7
	.long	.LASF3
	.uleb128 0xe
	.long	0x35
	.uleb128 0x3
	.byte	0x4
	.byte	0x7
	.long	.LASF4
	.uleb128 0x3
	.byte	0x8
	.byte	0x7
	.long	.LASF5
	.uleb128 0x3
	.byte	0x1
	.byte	0x6
	.long	.LASF6
	.uleb128 0x3
	.byte	0x2
	.byte	0x5
	.long	.LASF7
	.uleb128 0x14
	.byte	0x4
	.byte	0x5
	.string	"int"
	.uleb128 0x3
	.byte	0x8
	.byte	0x5
	.long	.LASF8
	.uleb128 0x15
	.byte	0x8
	.uleb128 0x3
	.byte	0x1
	.byte	0x6
	.long	.LASF9
	.uleb128 0xe
	.long	0x6d
	.uleb128 0x16
	.byte	0x7
	.byte	0x4
	.long	0x41
	.byte	0x5
	.byte	0x2f
	.byte	0x1
	.long	0xd8
	.uleb128 0x4
	.long	.LASF10
	.value	0x100
	.uleb128 0x4
	.long	.LASF11
	.value	0x200
	.uleb128 0x4
	.long	.LASF12
	.value	0x400
	.uleb128 0x4
	.long	.LASF13
	.value	0x800
	.uleb128 0x4
	.long	.LASF14
	.value	0x1000
	.uleb128 0x4
	.long	.LASF15
	.value	0x2000
	.uleb128 0x4
	.long	.LASF16
	.value	0x4000
	.uleb128 0x4
	.long	.LASF17
	.value	0x8000
	.uleb128 0x8
	.long	.LASF18
	.byte	0x1
	.uleb128 0x8
	.long	.LASF19
	.byte	0x2
	.uleb128 0x8
	.long	.LASF20
	.byte	0x4
	.uleb128 0x8
	.long	.LASF21
	.byte	0x8
	.byte	0
	.uleb128 0xf
	.long	.LASF23
	.byte	0x2
	.byte	0xd6
	.byte	0x17
	.long	0x48
	.uleb128 0x17
	.string	"tag"
	.byte	0x7
	.byte	0x4
	.long	0x41
	.byte	0x1
	.byte	0x7
	.byte	0x6
	.long	0x10f
	.uleb128 0xb
	.string	"NUM"
	.byte	0
	.uleb128 0xb
	.string	"SYM"
	.byte	0x1
	.uleb128 0x8
	.long	.LASF22
	.byte	0x2
	.uleb128 0xb
	.string	"NIL"
	.byte	0x3
	.byte	0
	.uleb128 0x18
	.long	.LASF24
	.byte	0x28
	.byte	0x1
	.byte	0x8
	.byte	0x10
	.long	0x154
	.uleb128 0x9
	.string	"tag"
	.byte	0x20
	.long	0xe4
	.byte	0
	.uleb128 0x9
	.string	"num"
	.byte	0x2a
	.long	0x64
	.byte	0x8
	.uleb128 0x9
	.string	"sym"
	.byte	0x3b
	.long	0x154
	.byte	0x10
	.uleb128 0x9
	.string	"car"
	.byte	0x4d
	.long	0x159
	.byte	0x18
	.uleb128 0x9
	.string	"cdr"
	.byte	0x53
	.long	0x159
	.byte	0x20
	.byte	0
	.uleb128 0x6
	.long	0x74
	.uleb128 0x6
	.long	0x10f
	.uleb128 0xf
	.long	.LASF24
	.byte	0x1
	.byte	0x8
	.byte	0x5a
	.long	0x10f
	.uleb128 0x10
	.long	0x15e
	.long	0x17b
	.uleb128 0x19
	.long	0x48
	.value	0x3ff
	.byte	0
	.uleb128 0x7
	.long	.LASF25
	.byte	0xa
	.byte	0xd
	.long	0x16a
	.uleb128 0x9
	.byte	0x3
	.quad	arena
	.uleb128 0x7
	.long	.LASF26
	.byte	0xb
	.byte	0xc
	.long	0x5d
	.uleb128 0x9
	.byte	0x3
	.quad	used
	.uleb128 0x1
	.string	"nil"
	.byte	0xc
	.byte	0xd
	.long	0x15e
	.uleb128 0x9
	.byte	0x3
	.quad	nil
	.uleb128 0x1
	.string	"p"
	.byte	0x12
	.byte	0x14
	.long	0x154
	.uleb128 0x9
	.byte	0x3
	.quad	p
	.uleb128 0x10
	.long	0x6d
	.long	0x1e3
	.uleb128 0x11
	.long	0x48
	.byte	0x3f
	.uleb128 0x11
	.long	0x48
	.byte	0xf
	.byte	0
	.uleb128 0x7
	.long	.LASF27
	.byte	0x13
	.byte	0xd
	.long	0x1cd
	.uleb128 0x9
	.byte	0x3
	.quad	names
	.uleb128 0x7
	.long	.LASF28
	.byte	0x14
	.byte	0xc
	.long	0x5d
	.uleb128 0x9
	.byte	0x3
	.quad	nnames
	.uleb128 0xc
	.long	.LASF29
	.byte	0x3
	.value	0x22c
	.byte	0xc
	.long	0x5d
	.long	0x224
	.uleb128 0x2
	.long	0x5d
	.byte	0
	.uleb128 0xc
	.long	.LASF30
	.byte	0x3
	.value	0x164
	.byte	0xc
	.long	0x5d
	.long	0x23c
	.uleb128 0x2
	.long	0x154
	.uleb128 0x1a
	.byte	0
	.uleb128 0xd
	.long	.LASF31
	.byte	0x9c
	.byte	0xc
	.long	0x5d
	.long	0x256
	.uleb128 0x2
	.long	0x154
	.uleb128 0x2
	.long	0x154
	.byte	0
	.uleb128 0x1b
	.long	.LASF44
	.byte	0x5
	.byte	0x4f
	.byte	0x23
	.long	0x262
	.uleb128 0x6
	.long	0x267
	.uleb128 0x6
	.long	0x3c
	.uleb128 0xd
	.long	.LASF32
	.byte	0x2b
	.byte	0xe
	.long	0x6b
	.long	0x28b
	.uleb128 0x2
	.long	0x6b
	.uleb128 0x2
	.long	0x28b
	.uleb128 0x2
	.long	0xd8
	.byte	0
	.uleb128 0x6
	.long	0x290
	.uleb128 0x1c
	.uleb128 0xd
	.long	.LASF33
	.byte	0x9f
	.byte	0xc
	.long	0x5d
	.long	0x2b0
	.uleb128 0x2
	.long	0x154
	.uleb128 0x2
	.long	0x154
	.uleb128 0x2
	.long	0xd8
	.byte	0
	.uleb128 0xc
	.long	.LASF34
	.byte	0x4
	.value	0x197
	.byte	0xf
	.long	0xd8
	.long	0x2c7
	.uleb128 0x2
	.long	0x154
	.byte	0
	.uleb128 0x1d
	.long	.LASF45
	.byte	0x1
	.byte	0x5c
	.byte	0x5
	.long	0x5d
	.quad	.LFB7
	.quad	.LFE7-.LFB7
	.uleb128 0x1
	.byte	0x9c
	.uleb128 0x1e
	.long	.LASF42
	.byte	0x1
	.byte	0x4a
	.byte	0xd
	.quad	.LFB6
	.quad	.LFE6-.LFB6
	.uleb128 0x1
	.byte	0x9c
	.long	0x310
	.uleb128 0x5
	.string	"c"
	.byte	0x4a
	.byte	0x19
	.long	0x310
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x6
	.long	0x15e
	.uleb128 0xa
	.long	.LASF36
	.byte	0x39
	.byte	0xe
	.long	0x310
	.quad	.LFB5
	.quad	.LFE5-.LFB5
	.uleb128 0x1
	.byte	0x9c
	.long	0x36d
	.uleb128 0x5
	.string	"e"
	.byte	0x39
	.byte	0x19
	.long	0x310
	.uleb128 0x3
	.byte	0x91
	.sleb128 -72
	.uleb128 0x1
	.string	"op"
	.byte	0x3c
	.byte	0xf
	.long	0x154
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0x7
	.long	.LASF35
	.byte	0x3d
	.byte	0x9
	.long	0x310
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x1
	.string	"acc"
	.byte	0x44
	.byte	0x8
	.long	0x64
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.byte	0
	.uleb128 0xa
	.long	.LASF37
	.byte	0x20
	.byte	0xe
	.long	0x310
	.quad	.LFB4
	.quad	.LFE4-.LFB4
	.uleb128 0x1
	.byte	0x9c
	.long	0x3f7
	.uleb128 0x1
	.string	"s"
	.byte	0x32
	.byte	0xf
	.long	0x154
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x1
	.string	"c"
	.byte	0x34
	.byte	0x9
	.long	0x310
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x1f
	.quad	.LBB3
	.quad	.LBE3-.LBB3
	.long	0x3d8
	.uleb128 0x7
	.long	.LASF38
	.byte	0x25
	.byte	0xb
	.long	0x310
	.uleb128 0x2
	.byte	0x91
	.sleb128 -56
	.uleb128 0x7
	.long	.LASF39
	.byte	0x25
	.byte	0x1a
	.long	0x3f7
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x12
	.quad	.LBB4
	.quad	.LBE4-.LBB4
	.uleb128 0x1
	.string	"n"
	.byte	0x2e
	.byte	0xa
	.long	0x64
	.uleb128 0x2
	.byte	0x91
	.sleb128 -32
	.byte	0
	.byte	0
	.uleb128 0x6
	.long	0x310
	.uleb128 0xa
	.long	.LASF40
	.byte	0x16
	.byte	0x14
	.long	0x154
	.quad	.LFB3
	.quad	.LFE3-.LFB3
	.uleb128 0x1
	.byte	0x9c
	.long	0x454
	.uleb128 0x5
	.string	"s"
	.byte	0x16
	.byte	0x27
	.long	0x154
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x5
	.string	"n"
	.byte	0x16
	.byte	0x31
	.long	0xd8
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x12
	.quad	.LBB2
	.quad	.LBE2-.LBB2
	.uleb128 0x1
	.string	"i"
	.byte	0x18
	.byte	0xc
	.long	0x5d
	.uleb128 0x2
	.byte	0x91
	.sleb128 -20
	.byte	0
	.byte	0
	.uleb128 0xa
	.long	.LASF41
	.byte	0x10
	.byte	0xe
	.long	0x310
	.quad	.LFB2
	.quad	.LFE2-.LFB2
	.uleb128 0x1
	.byte	0x9c
	.long	0x49a
	.uleb128 0x5
	.string	"a"
	.byte	0x10
	.byte	0x19
	.long	0x310
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x5
	.string	"d"
	.byte	0x10
	.byte	0x22
	.long	0x310
	.uleb128 0x2
	.byte	0x91
	.sleb128 -48
	.uleb128 0x1
	.string	"c"
	.byte	0x10
	.byte	0x2d
	.long	0x310
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x20
	.string	"num"
	.byte	0x1
	.byte	0xf
	.byte	0xe
	.long	0x310
	.quad	.LFB1
	.quad	.LFE1-.LFB1
	.uleb128 0x1
	.byte	0x9c
	.long	0x4d5
	.uleb128 0x5
	.string	"n"
	.byte	0xf
	.byte	0x17
	.long	0x64
	.uleb128 0x2
	.byte	0x91
	.sleb128 -40
	.uleb128 0x1
	.string	"c"
	.byte	0xf
	.byte	0x22
	.long	0x310
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
	.uleb128 0x21
	.string	"mk"
	.byte	0x1
	.byte	0xe
	.byte	0xe
	.long	0x310
	.quad	.LFB0
	.quad	.LFE0-.LFB0
	.uleb128 0x1
	.byte	0x9c
	.uleb128 0x5
	.string	"t"
	.byte	0xe
	.byte	0x1a
	.long	0xe4
	.uleb128 0x2
	.byte	0x91
	.sleb128 -36
	.uleb128 0x1
	.string	"c"
	.byte	0xe
	.byte	0x25
	.long	0x310
	.uleb128 0x2
	.byte	0x91
	.sleb128 -24
	.byte	0
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
	.uleb128 0x5
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x3
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
	.uleb128 0x4
	.uleb128 0x28
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x1c
	.uleb128 0x5
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
	.uleb128 0xb
	.uleb128 0x39
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x6
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0x21
	.sleb128 8
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x7
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
	.uleb128 0x8
	.uleb128 0x28
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x1c
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x9
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
	.uleb128 0xa
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
	.uleb128 0xb
	.uleb128 0x28
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x1c
	.uleb128 0xb
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
	.uleb128 0xd
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0x21
	.sleb128 4
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
	.uleb128 0xe
	.uleb128 0x26
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xf
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
	.uleb128 0x10
	.uleb128 0x1
	.byte	0x1
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x11
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x12
	.uleb128 0xb
	.byte	0x1
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.byte	0
	.byte	0
	.uleb128 0x13
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
	.uleb128 0x14
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
	.uleb128 0x15
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x16
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
	.uleb128 0x17
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
	.uleb128 0x18
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
	.uleb128 0x19
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0x5
	.byte	0
	.byte	0
	.uleb128 0x1a
	.uleb128 0x18
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x1b
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
	.uleb128 0x1c
	.uleb128 0x26
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x1d
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
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x7c
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0x1e
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
	.uleb128 0x7c
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x1f
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
	.uleb128 0x20
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
	.uleb128 0x21
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
.LASF19:
	.string	"_IScntrl"
.LASF22:
	.string	"CONS"
.LASF28:
	.string	"nnames"
.LASF7:
	.string	"short int"
.LASF23:
	.string	"size_t"
.LASF43:
	.string	"GNU C11 13.3.0 -mtune=generic -march=x86-64 -g -O0 -std=c11 -fno-asynchronous-unwind-tables"
.LASF17:
	.string	"_ISgraph"
.LASF20:
	.string	"_ISpunct"
.LASF29:
	.string	"putchar"
.LASF45:
	.string	"main"
.LASF32:
	.string	"memcpy"
.LASF33:
	.string	"strncmp"
.LASF13:
	.string	"_ISdigit"
.LASF38:
	.string	"head"
.LASF18:
	.string	"_ISblank"
.LASF21:
	.string	"_ISalnum"
.LASF15:
	.string	"_ISspace"
.LASF37:
	.string	"read"
.LASF40:
	.string	"intern"
.LASF8:
	.string	"long int"
.LASF30:
	.string	"printf"
.LASF39:
	.string	"tail"
.LASF2:
	.string	"unsigned char"
.LASF36:
	.string	"eval"
.LASF6:
	.string	"signed char"
.LASF42:
	.string	"print"
.LASF4:
	.string	"unsigned int"
.LASF12:
	.string	"_ISalpha"
.LASF27:
	.string	"names"
.LASF35:
	.string	"args"
.LASF3:
	.string	"short unsigned int"
.LASF9:
	.string	"char"
.LASF11:
	.string	"_ISlower"
.LASF34:
	.string	"strlen"
.LASF25:
	.string	"arena"
.LASF14:
	.string	"_ISxdigit"
.LASF41:
	.string	"cons"
.LASF5:
	.string	"long unsigned int"
.LASF44:
	.string	"__ctype_b_loc"
.LASF31:
	.string	"strcmp"
.LASF16:
	.string	"_ISprint"
.LASF26:
	.string	"used"
.LASF10:
	.string	"_ISupper"
.LASF24:
	.string	"cell"
	.section	.debug_line_str,"MS",@progbits,1
.LASF1:
	.string	"."
.LASF0:
	.string	"lisp.c"
	.ident	"GCC: (GNU) 13.3.0"
	.section	.note.GNU-stack,"",@progbits
