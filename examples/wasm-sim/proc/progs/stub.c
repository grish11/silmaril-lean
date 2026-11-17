/* libstub.so: the native foreign library for dyn (raw syscalls, no libc). */
static long sys3(long nr, long a, long b, long c) {
  long r;
  __asm__ volatile("syscall" : "=a"(r) : "a"(nr), "D"(a), "S"(b), "d"(c) : "rcx", "r11", "memory");
  return r;
}
unsigned long strlen(const char *s) { unsigned long n = 0; while (s[n]) n++; return n; }
int puts(const char *s) {
  unsigned long n = strlen(s);
  sys3(1, 1, (long)s, (long)n);
  sys3(1, 1, (long)"\n", 1);
  return (int)n + 1;
}
int putchar(int c) { char b = (char)c; sys3(1, 1, (long)&b, 1); return c & 255; }
