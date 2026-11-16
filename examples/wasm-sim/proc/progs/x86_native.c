/* Native driver for examples/wasm-sim/x86/tests/funcs.S: reads "name a1 .. a8" lines (hex), prints
   "rax rdx" in hex (same protocol as sysv_native.c). */
#include <stdio.h>
#include <string.h>
typedef unsigned long u64;
typedef struct { u64 a, b; } pair;
typedef pair (*fn8)(u64, u64, u64, u64, u64, u64, u64, u64);
#define F(n) extern char n[];
F(add2) F(max2) F(abs1) F(sum_to) F(gcd) F(popcount1) F(popcount2) F(fact) F(sw) F(mix) F(divs)
static struct { const char *name; void *f; } tab[] = {
#define E(n) {#n, (void *)n},
  E(add2) E(max2) E(abs1) E(sum_to) E(gcd) E(popcount1) E(popcount2) E(fact) E(sw) E(mix) E(divs)
};
int main(void) {
  char name[64]; u64 a[8];
  while (scanf("%63s %lx %lx %lx %lx %lx %lx %lx %lx", name, &a[0], &a[1], &a[2], &a[3], &a[4],
               &a[5], &a[6], &a[7]) == 9) {
    void *f = 0;
    for (unsigned i = 0; i < sizeof tab / sizeof *tab; i++)
      if (!strcmp(tab[i].name, name)) f = tab[i].f;
    if (!f) { printf("? ?\n"); continue; }
    pair r = ((fn8)f)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]);
    printf("%lx %lx\n", r.a, r.b);
  }
  return 0;
}
