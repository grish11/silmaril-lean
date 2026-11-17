/* Native driver: reads "name a1 .. a8" lines (hex), prints "rax rdx" in hex. */
#include <stdio.h>
#include <string.h>
typedef unsigned long u64;
typedef struct { u64 a, b; } pair;
typedef pair (*fn8)(u64, u64, u64, u64, u64, u64, u64, u64);
#define F(n) extern char n[];
F(add2) F(entry_rsp) F(sum8_asm) F(mix) F(sum8) F(addsub) F(collatz) F(fib) F(clamp) F(popc)
F(callsave) F(cmp3) F(lowbyte)
static struct { const char *name; void *f; } tab[] = {
#define E(n) {#n, (void *)n},
  E(add2) E(entry_rsp) E(sum8_asm) E(mix) E(sum8) E(addsub) E(collatz) E(fib) E(clamp) E(popc)
  E(callsave) E(cmp3) E(lowbyte)
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
