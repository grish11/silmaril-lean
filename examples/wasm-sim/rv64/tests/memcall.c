// Functions with memory accesses and calls, compiled with clang -O2 -fno-builtin
// (rv64im), as sources of decomposed RV64 problems (problems/memcall.toml).
typedef unsigned long u64;

__attribute__((noinline)) long sq(long x) { return x * x; }

__attribute__((noinline)) long tri(long n) {
  long s = 0;
  while (n > 0) s += n--;
  return s;
}

__attribute__((noinline)) long f(long a, long b) { return tri(a) + sq(b); }

__attribute__((noinline)) long sum_array(const long *a, long n) {
  long s = 0;
  for (long i = 0; i < n; i++) s += a[i];
  return s;
}

__attribute__((noinline)) long sum_sq(const long *a, long n) {
  long s = 0;
  for (long i = 0; i < n; i++) s += sq(a[i]);
  return s;
}

__attribute__((noinline)) void fill(long *a, long n, long v) {
  for (long i = 0; i < n; i++) a[i] = v;
}

__attribute__((noinline)) void scale(long *a, long n, long k) {
  for (long i = 0; i < n; i++) a[i] = a[i] * k;
}

long test(void) {
  static long buf[16];
  fill(buf, 16, 3);
  scale(buf, 8, 5);
  return f(10, 4) + sum_array(buf, 16) + sum_sq(buf, 4);
}
