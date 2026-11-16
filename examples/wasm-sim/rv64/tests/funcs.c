// Leaf functions compiled with clang -O2 (rv64im) as sources of RV64 problems
// for `wasm-sim-rv reduce` (problems/*.spec). `test` is the program entry
// called by crt.S; its result is the exit code.
typedef unsigned long u64;

long max3(long a, long b, long c) {
  long m = a > b ? a : b;
  return m > c ? m : c;
}

long clamp(long x, long lo, long hi) { return x < lo ? lo : (x > hi ? hi : x); }

u64 absdiff(long a, long b) { return a > b ? (u64)a - (u64)b : (u64)b - (u64)a; }

u64 gcdu(u64 a, u64 b) {
  while (b != 0) {
    u64 t = a % b;
    a = b;
    b = t;
  }
  return a;
}

u64 isqrt(u64 n) {
  u64 r = 0, bit = 1UL << 62;
  while (bit > n) bit >>= 2;
  while (bit != 0) {
    if (n >= r + bit) {
      n -= r + bit;
      r = (r >> 1) + bit;
    } else {
      r >>= 1;
    }
    bit >>= 2;
  }
  return r;
}

u64 popcount(u64 x) {
  u64 c = 0;
  while (x) {
    x &= x - 1;
    c++;
  }
  return c;
}

long test(void) {
  volatile long v[4] = {3, -7, 12, 1000003};
  long acc = max3(v[0], v[1], v[2]) + clamp(v[3], v[1], v[2]) + (long)absdiff(v[1], v[2]);
  acc += (long)gcdu((u64)v[3] * 6, 36) + (long)isqrt((u64)v[3]) + (long)popcount((u64)v[1]);
  return acc;
}
