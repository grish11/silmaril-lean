/* A dynamically linked program (no libc): puts/strlen/putchar come from a shared library.
   Natively that is libstub.so (stub.c, raw syscalls); on the simulator the loader binds them
   to foreign addresses and `ext.call` runs a Wasm (or host) implementation. */
int puts(const char *);
unsigned long strlen(const char *);
int putchar(int);

static inline long sys1(long nr, long a) {
  long r;
  __asm__ volatile("syscall" : "=a"(r) : "a"(nr), "D"(a) : "rcx", "r11", "memory");
  return r;
}

void cmain(long *sp) {
  long argc = sp[0];
  char **argv = (char **)(sp + 1);
  int r = puts("Hello through a foreign puts!");
  putchar('a' + (r & 15));
  putchar('\n');
  unsigned long total = 0;
  for (long i = 0; i < argc; i++) {
    unsigned long n = strlen(argv[i]);
    total += n;
    putchar('a' + (n & 15));
  }
  putchar('\n');
  sys1(231, (long)(total & 63));
  __builtin_unreachable();
}

__asm__(".globl _start\n_start:\n  mov %rsp, %rdi\n  and $-16, %rsp\n  call cmain\n  hlt\n");
