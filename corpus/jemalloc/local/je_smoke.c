/* local/je_smoke.c -- repository-authored test driver (not upstream). Why: test.sh links it against
 * the built libjemalloc.so.2 (natively / under qemu-user) to show the library works: it queries
 * mallctl("version"), allocates and frees a range of size classes, and checks usable sizes and
 * statistics. Not shipped as an artifact. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int mallctl(const char *name, void *oldp, size_t *oldlenp, void *newp, size_t newlen);
size_t malloc_usable_size(void *ptr);
int main(void) {
    const char *v; size_t sz = sizeof v;
    if (mallctl("version", &v, &sz, NULL, 0) != 0) { puts("FAIL mallctl version"); return 1; }
    printf("version %s\n", v);
    size_t page; sz = sizeof page; mallctl("arenas.page", &page, &sz, NULL, 0);
    printf("arenas.page %zu\n", page);
    void *ps[2000]; unsigned bad = 0;
    for (int i = 0; i < 2000; i++) {
        size_t n = (size_t)1 << (i % 22); n += (size_t)i;
        ps[i] = malloc(n);
        if (!ps[i] || malloc_usable_size(ps[i]) < n) bad++;
        else memset(ps[i], i & 0xff, n);
    }
    for (int i = 0; i < 2000; i++) free(ps[i]);
    void *a = aligned_alloc(4096, 12345);
    if (!a || ((uintptr_t)a & 4095)) bad++;
    free(a);
    char *r = NULL; for (int i = 1; i < 100000; i *= 3) { r = realloc(r, i); if (!r) bad++; else r[i-1] = 1; }
    free(r);
    uint64_t epoch = 1; sz = sizeof epoch; mallctl("epoch", &epoch, &sz, &epoch, sz);
    size_t allocated; sz = sizeof allocated;
    int st = mallctl("stats.allocated", &allocated, &sz, NULL, 0);
    printf("stats.allocated rc=%d\n", st);
    printf("%s bad=%u\n", bad ? "FAIL" : "ok", bad);
    return bad != 0;
}
