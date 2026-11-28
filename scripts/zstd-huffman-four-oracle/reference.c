#include <stdio.h>
#include <stdlib.h>

#include "common/huf.h"

int main(int argc, char **argv) {
    unsigned char wire[131072], output[131072];
    unsigned workspace[HUF_DECOMPRESS_WORKSPACE_SIZE_U32];
    HUF_CREATE_STATIC_DTABLEX1(table, 11);
    if (argc != 2) return 2;
    char *end;
    unsigned long expected = strtoul(argv[1], &end, 10);
    if (*end || expected < 6 || expected > sizeof(output)) return 2;
    size_t size = fread(wire, 1, sizeof(wire), stdin);
    if (ferror(stdin) || fgetc(stdin) != EOF) return 2;
    size_t used = HUF_readDTableX1_wksp(table, wire, size, workspace, sizeof(workspace), 0);
    if (HUF_isError(used) || used >= size) return 3;
    size_t got = HUF_decompress4X_usingDTable(output, expected, wire + used, size - used, table, 0);
    if (HUF_isError(got) || got != expected) return 3;
    return fwrite(output, 1, got, stdout) == got ? 0 : 2;
}
