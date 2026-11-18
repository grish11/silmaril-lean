# Small SysV x86-64 functions for difftests / lockstep / P-calls (Intel syntax, GNU as).
# Only rel8/rel32 control flow (position independent). See tools/wasm-sim (difftest-fn).
        .intel_syntax noprefix
        .text

        .globl add2                      # long add2(long a, long b)
add2:
.Ladd2: lea rax, [rdi + rsi]
        ret

        .globl max2                      # long max2(long a, long b), signed
max2:   mov rax, rdi
        cmp rdi, rsi
        cmovl rax, rsi
        ret

        .globl abs1                      # long abs1(long a), wrapping
abs1:   mov rax, rdi
        neg rax
        cmovs rax, rdi
        ret

        .globl sum_to                    # unsigned long sum_to(unsigned long n) = n(n+1)/2 by a loop
sum_to:
.Lsum_to: xor eax, eax
        test rdi, rdi
        je 2f
1:      add rax, rdi
        dec rdi
        jne 1b
2:      ret

        .globl strlen1                   # size_t strlen1(const char *s)
strlen1: mov rax, rdi
1:      movzx ecx, byte ptr [rax]
        test ecx, ecx
        je 2f
        inc rax
        jmp 1b
2:      sub rax, rdi
        ret

        .globl memcpy1                   # void *memcpy1(void *d, const void *s, size_t n): 8 bytes, then bytes
memcpy1: mov rax, rdi
        xor ecx, ecx
1:      lea r8, [rcx + 8]
        cmp r8, rdx
        ja 2f
        mov r9, qword ptr [rsi + rcx]
        mov qword ptr [rdi + rcx], r9
        mov rcx, r8
        jmp 1b
2:      cmp rcx, rdx
        jae 3f
        movzx r9d, byte ptr [rsi + rcx]
        mov byte ptr [rdi + rcx], r9b
        inc rcx
        jmp 2b
3:      ret

        .globl gcd                       # unsigned long gcd(unsigned long a, unsigned long b)
gcd:    mov rax, rdi
        test rsi, rsi
        je 2f
1:      xor edx, edx
        div rsi
        mov rax, rsi
        mov rsi, rdx
        test rsi, rsi
        jne 1b
2:      ret

        .globl popcount1                 # int popcount1(unsigned long x): Kernighan loop
popcount1: xor eax, eax
        test rdi, rdi
        je 2f
1:      lea rcx, [rdi - 1]
        and rdi, rcx
        inc eax
        test rdi, rdi
        jne 1b
2:      ret

        .globl popcount2                 # int popcount2(unsigned long x): shift loop with setc
popcount2: xor eax, eax
        mov ecx, 64
1:      shr rdi, 1
        setc dl
        movzx edx, dl
        add eax, edx
        dec ecx
        jne 1b
        ret

        .globl fact                      # unsigned long fact(unsigned long n), recursive, wrapping
fact:
.Lfact: push rbx
        mov rbx, rdi
        mov eax, 1
        cmp rdi, 1
        jbe 1f
        lea rdi, [rdi - 1]
        call .Lfact
        imul rax, rbx
1:      pop rbx
        ret

        .globl sw                        # long sw(long k): tiny switch (compare chain + default)
sw:     cmp rdi, 3
        ja 9f
        je 3f
        cmp edi, 1
        je 1f
        jb 0f
        mov rax, 200                     # k = 2
        ret
0:      mov eax, 100
        ret
1:      mov rax, -1
        ret
3:      lea rax, [rdi*8 + 7]
        ret
9:      mov rax, rdi
        sar rax, 2
        sbb rax, 0
        ret

        .globl mix                       # long mix(long a, long b, long c): flags, shifts, imul, setcc
mix:    mov rax, rdi
        imul rax, rsi
        mov rcx, rdx
        shl rax, cl
        xor r8d, r8d
        cmp rdi, rsi
        setg r8b
        add rax, r8
        imul r9, rdx, 37
        sub rax, r9
        mov r10, rax
        shr r10, 7
        xor rax, r10
        adc rax, rdi
        ret

        .globl divs                      # long divs(long a, long b): signed div with remainder mixed in (b != 0)
divs:   mov rax, rdi
        cqo
        idiv rsi
        lea rax, [rax + rdx*2]
        ret

        .globl twice_sum                 # long twice_sum(long a, long b) = sum_to(a) + add2(b, b)
twice_sum: push rbx
        push r12
        sub rsp, 8
        mov rbx, rsi
        call .Lsum_to
        mov r12, rax
        mov rdi, rbx
        mov rsi, rbx
        call .Ladd2
        add rax, r12
        add rsp, 8
        pop r12
        pop rbx
        ret
