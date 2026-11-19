#!/usr/bin/env bash
# test.sh ARCH OBJDIR -- the built tcc (natively, or under qemu-user for aarch64) compiles C to an
# object file of its own architecture; the system gcc links it; the program runs.
. "$(dirname "$0")/../common.sh"
start_test tinycc "$1" "$2"
t=$(mktemp -d)
cat > "$t/hello.c" <<'C'
int printf(const char *, ...);
static int fib(int n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
int main(void) { printf("hello from tcc %d\n", fib(20)); return 0; }
C
check "${RUNS}tcc -v" "tcc version 0.9.27 ($( [ "$ARCH" = x86_64 ] && echo x86_64 || echo AArch64 ) Linux)" "$("${RUN[@]}" "$OBJ/tcc" -v 2>&1 | head -1)"
"${RUN[@]}" "$OBJ/tcc" -c "$t/hello.c" -o "$t/hello.o"
check "file hello.o (tcc -c output is an ELF relocatable for $ARCH)" 1 "$(file "$t/hello.o" | grep -c "relocatable, $( [ "$ARCH" = x86_64 ] && echo x86-64 || echo 'ARM aarch64')")"
# tcc 0.9.27 emits absolute (non-PIC) relocations on AArch64 (R_AARCH64_MOVW_UABS_*), so link -no-pie
$CC -no-pie "$t/hello.o" -o "$t/hello"
check "${RUNS}./hello (compiled by tcc, linked by $CC -no-pie)" "hello from tcc 6765" "$("${RUN[@]}" "$t/hello")"
rm -rf "$t"
exit $TEST_FAILED
