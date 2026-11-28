#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "common/huf.h"

int main(int argc, char **argv) {
    unsigned char wire[131072], decoded[131072], weights[HUF_SYMBOLVALUE_MAX + 1];
    unsigned ranks[HUF_TABLELOG_MAX + 1], count, depth;
    unsigned workspace[HUF_DECOMPRESS_WORKSPACE_SIZE_U32];
    HUF_CREATE_STATIC_DTABLEX1(table, 11);
    if (argc != 2) return 2;
    size_t length = fread(wire, 1, sizeof(wire), stdin);
    if (ferror(stdin) || fgetc(stdin) != EOF) return 2;
    size_t used = HUF_readStats(weights, sizeof(weights), ranks, &count, &depth, wire, length);
    if (HUF_isError(used) || !depth || depth > 11) return 3;

    if (!strcmp(argv[1], "table")) {
        /* Match the encoded depth, disabling native lookup-table rescaling. */
        table[0] = (depth - 1) * 0x01000001U;
        size_t status = HUF_readDTableX1_wksp(table, wire, used, workspace, sizeof(workspace), 0);
        if (HUF_isError(status) || status != used) return 3;
        size_t rows = 1U << depth;
        /* Pinned X1 rows are consecutive (number of bits, symbol) bytes. */
        return fwrite(table + 1, 2, rows, stdout) == rows ? 0 : 2;
    }

    char *end;
    unsigned long expected = strtoul(argv[1], &end, 10);
    if (*end || !expected || expected > sizeof(decoded)) return 2;
    size_t size = HUF_decompress1X1_DCtx_wksp(
        table, decoded, expected, wire, length, workspace, sizeof(workspace), 0);
    if (HUF_isError(size) || size != expected) return 3;
    return fwrite(decoded, 1, size, stdout) == size ? 0 : 2;
}
