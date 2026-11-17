/* Benchmark workload (static, no libc): total Collatz steps for n in [1, N], N = 20000 by
   default or 1000 * strlen(argv[1]); prints the total in hex; exit code = total & 255.
   Uses only add/shift/and/cmp/branches (no mul/div), so every simulator runs it. */
static inline long sys3(long nr, long a, long b, long c) {
  long r;
  __asm__ volatile("syscall" : "=a"(r) : "a"(nr), "D"(a), "S"(b), "d"(c) : "rcx", "r11", "memory");
  return r;
}
void cmain(long *sp) {
  long argc = sp[0];
  char **argv = (char **)(sp + 1);
  unsigned long N = 20000;
  if (argc > 1) { N = 0; for (char *p = argv[1]; *p; p++) N += 1000; }
  unsigned long total = 0;
  for (unsigned long n = 1; n <= N; n++) {
    unsigned long x = n;
    while (x != 1) { x = (x & 1) ? x + (x << 1) + 1 : x >> 1; total++; }
  }
  char buf[20];
  int i = 19;
  buf[i] = '\n';
  do { buf[--i] = "0123456789abcdef"[total & 15]; total >>= 4; } while (total);
  sys3(1, 1, (long)(buf + i), 20 - i);
  sys3(231, (long)(total & 255), 0, 0);
  __builtin_unreachable();
}
__asm__(".globl _start\n_start:\n  mov %rsp, %rdi\n  and $-16, %rsp\n  call cmain\n  hlt\n");
