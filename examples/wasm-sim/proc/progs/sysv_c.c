/* C System V test functions (gcc -O2). `pair` is returned in rax:rdx. */
typedef unsigned long u64;
typedef struct { u64 a, b; } pair;

long mix(long a, long b, long c, long d, long e, long f) {
  return ((a * 3 + (b << 5)) ^ (c - d)) + (e | f) - (a >> 3);
}
long sum8(long a, long b, long c, long d, long e, long f, long g, long h) {
  return a + b + c + d + e + f + g * 3 - h;
}
pair addsub(u64 a, u64 b) { return (pair){a + b, a - b}; }
u64 collatz(u64 n) {
  n = (n & 1023) | 1;
  u64 k = 0;
  while (n != 1) { n = (n & 1) ? 3 * n + 1 : n >> 1; k++; }
  return k;
}
u64 fib(u64 n) {
  u64 a = 0, b = 1;
  for (n &= 63; n; n--) { u64 t = a + b; a = b; b = t; }
  return a;
}
long clamp(long x, long lo, long hi) { return x < lo ? lo : x > hi ? hi : x; }
int popc(u64 x) { int k = 0; while (x) { x &= x - 1; k++; } return k; }
__attribute__((noinline)) long helper(long x) { return x * 7 + 1; }
long callsave(long a, long b) { long x = helper(a); long y = helper(b); return x * y + a; }
int cmp3(long a, long b) { return (a > b) - (a < b); }
unsigned char lowbyte(u64 a, u64 b) { return (unsigned char)(a + b); }
