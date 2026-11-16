/* Small C functions compiled with gcc -O2 for end-to-end difftests (wasm-sim difftest-fn --c).
   Built by tools/wasm-sim (x86/difftest.rs: build_c): gcc -O2 -c, ld -N -Ttext=0, objcopy -O binary. */
#include <stddef.h>
#include <stdint.h>

int popc(unsigned long x) { int n = 0; while (x) { x &= x - 1; n++; } return n; }
long sum_arr(const long *a, long n) { long s = 0; for (long i = 0; i < n; i++) s += a[i]; return s; }
int strcmp1(const char *a, const char *b) {
  while (*a && *a == *b) { a++; b++; }
  return (unsigned char)*a - (unsigned char)*b;
}
void reverse(char *s, long n) { for (long i = 0, j = n - 1; i < j; i++, j--) { char t = s[i]; s[i] = s[j]; s[j] = t; } }
long fib(long n) { long a = 0, b = 1; while (n-- > 0) { long t = a + b; a = b; b = t; } return a; }
unsigned long isqrt(unsigned long x) {
  unsigned long r = 0, bit = 1UL << 62;
  while (bit > x) bit >>= 2;
  while (bit) { if (x >= r + bit) { x -= r + bit; r = (r >> 1) + bit; } else r >>= 1; bit >>= 2; }
  return r;
}
int ctz_clz(unsigned long x) { return x ? __builtin_ctzl(x) * 100 + __builtin_clzl(x) : -1; }
unsigned long collatz(unsigned long n) { unsigned long k = 0; while (n > 1 && k < 1000) { n = (n & 1) ? 3 * n + 1 : n / 2; k++; } return k; }
int is_prime(unsigned n) { if (n < 2) return 0; for (unsigned d = 2; d * d <= n && d < 65536; d++) if (n % d == 0) return 0; return 1; }
int classify(int k) {
  switch (k) {
  case 0: return 11; case 1: return 22; case 2: return k * 7; case 3: return 45;
  case 4: return -3; case 5: return 99; case 6: return k << 4; case 7: return 1;
  default: return k > 100 ? 5 : -k;
  }
}
uint32_t crc32b(const uint8_t *p, size_t n) {
  uint32_t c = 0xffffffffu;
  for (size_t i = 0; i < n; i++) { c ^= p[i]; for (int k = 0; k < 8; k++) c = (c >> 1) ^ (0xedb88320u & -(c & 1)); }
  return ~c;
}
int sum_bytes(const signed char *p, long n) { int s = 0; for (long i = 0; i < n; i++) s += p[i]; return s; }
unsigned short bswap16(unsigned short x) { return (unsigned short)((x << 8) | (x >> 8)); }
uint64_t rotl64(uint64_t x, int k) { return (x << (k & 63)) | (x >> (-k & 63)); }
void isort(int *a, long n) {
  for (long i = 1; i < n; i++) { int v = a[i]; long j = i - 1; while (j >= 0 && a[j] > v) { a[j + 1] = a[j]; j--; } a[j + 1] = v; }
}
uint64_t mulhi(uint64_t a, uint64_t b) { return (uint64_t)(((unsigned __int128)a * b) >> 64); }
short sat_add16(short a, short b) { int s = a + b; return s > 32767 ? 32767 : s < -32768 ? -32768 : (short)s; }
