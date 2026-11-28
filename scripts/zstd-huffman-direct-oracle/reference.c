#include <stdio.h>

#include "common/huf.h"

int main(void) {
    unsigned char wire[131072];
    unsigned char weights[HUF_SYMBOLVALUE_MAX + 1];
    unsigned ranks[HUF_TABLELOG_MAX + 1];
    unsigned depth, count;
    size_t length = fread(wire, 1, sizeof(wire), stdin);
    if (ferror(stdin) || fgetc(stdin) != EOF) return 2;
    size_t used = HUF_readStats(weights, sizeof(weights), ranks, &count, &depth, wire, length);
    if (HUF_isError(used)) return 3;
    printf("%zu %u %u\n", used, depth, count);
    for (unsigned i = 0; i < count; ++i)
        printf("%s%u", i ? " " : "", (unsigned)weights[i]);
    putchar('\n');
    return 0;
}
