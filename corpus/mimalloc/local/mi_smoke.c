/* local/mi_smoke.c -- repository-authored test driver (not upstream). Why: test.sh links it against
 * the built libmimalloc.so.2.1 (natively / under qemu-user): it checks mi_version(), that plain
 * malloc/free are served by mimalloc (MI_OVERRIDE), and allocates/frees a range of sizes. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int mi_version(void);
int mi_is_in_heap_region(const void *p);
void *mi_malloc(size_t n);
void mi_free(void *p);
size_t mi_usable_size(const void *p);
int main(void) {
    unsigned bad = 0;
    printf("mi_version %d\n", mi_version());
    void *p = malloc(100);
    int ours = mi_is_in_heap_region(p);
    printf("malloc served by mimalloc: %d\n", ours);
    if (!ours) bad++;
    free(p);
    void *ps[2000];
    for (int i = 0; i < 2000; i++) {
        size_t n = ((size_t)1 << (i % 22)) + (size_t)i;
        ps[i] = (i & 1) ? malloc(n) : mi_malloc(n);
        if (!ps[i] || mi_usable_size(ps[i]) < n) bad++; else memset(ps[i], i & 0xff, n);
    }
    for (int i = 0; i < 2000; i++) { if (i & 1) free(ps[i]); else mi_free(ps[i]); }
    void *a = aligned_alloc(4096, 12345); if (!a || ((uintptr_t)a & 4095)) bad++; free(a);
    char *r = NULL; for (int i = 1; i < 100000; i *= 3) { r = realloc(r, i); if (!r) bad++; else r[i-1] = 1; }
    free(r);
    printf("%s bad=%u\n", bad ? "FAIL" : "ok", bad);
    return bad != 0;
}
