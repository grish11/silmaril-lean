/* Static C hello world without libc: inline syscalls only.
   Build: gcc -O2 -nostdlib -static -fno-pie -no-pie -fno-stack-protector \
          -fcf-protection=none -fno-asynchronous-unwind-tables */
typedef unsigned long u64;

static inline long sys3(long nr, long a, long b, long c) {
  long r;
  __asm__ volatile("syscall" : "=a"(r) : "a"(nr), "D"(a), "S"(b), "d"(c)
                   : "rcx", "r11", "memory");
  return r;
}

static u64 my_strlen(const char *s) {
  u64 n = 0;
  while (s[n]) n++;
  return n;
}

/* argc/argv are read from the initial stack the loader builds. */
void cmain(long *sp) {
  long argc = sp[0];
  char **argv = (char **)(sp + 1);
  static const char msg[] = "Hello from C!\n";
  sys3(1, 1, (long)msg, sizeof msg - 1);
  for (long i = 0; i < argc; i++) {
    sys3(1, 1, (long)argv[i], (long)my_strlen(argv[i]));
    sys3(1, 1, (long)"\n", 1);
  }
  /* brk(0) then grow by 4096 and touch it */
  long b0 = sys3(12, 0, 0, 0);
  long b1 = sys3(12, b0 + 4096, 0, 0);
  if (b1 == b0 + 4096) {
    char *p = (char *)b0;
    p[0] = 'b'; p[1] = 'r'; p[2] = 'k'; p[3] = '\n';
    sys3(1, 1, (long)p, 4);
  }
  sys3(231, (int)(argc + 41), 0, 0); /* exit_group(argc + 41) */
  __builtin_unreachable();
}

__asm__(".globl _start\n_start:\n  mov %rsp, %rdi\n  and $-16, %rsp\n  call cmain\n  hlt\n");
