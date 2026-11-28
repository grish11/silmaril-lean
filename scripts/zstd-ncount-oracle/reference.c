#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "common/zstd_internal.h"

static int checked_weights(const short *weights, unsigned count, unsigned log) {
    if (log < 5 || log > 9 || count > 256) return 0;
    unsigned mass = 0, active = 0;
    for (unsigned i = 0; i < count; ++i) {
        if (weights[i] < -1 || weights[i] > 512) return 0;
        mass += weights[i] == -1 ? 1 : (unsigned)weights[i];
        active += weights[i] != 0;
    }
    return active >= 2 && mass == (1U << log);
}

static int write_counts(int argc, char **argv) {
    short weights[256];
    unsigned char wire[FSE_NCOUNTBOUND];
    char *end;
    if (argc < 5 || argc > 259) return 2;
    long log = strtol(argv[2], &end, 10);
    if (*end || log < 5 || log > 9) return 2;
    unsigned count = (unsigned)argc - 3;
    for (unsigned i = 0; i < count; ++i) {
        long weight = strtol(argv[3 + i], &end, 10);
        if (*end || weight < -1 || weight > 512) return 2;
        weights[i] = (short)weight;
    }
    if (!checked_weights(weights, count, (unsigned)log)) return 2;
    size_t size = FSE_writeNCount(wire, sizeof(wire), weights, count - 1, (unsigned)log);
    if (FSE_isError(size)) return 3;
    return fwrite(wire, 1, size, stdout) == size ? 0 : 1;
}

static int read_table(void) {
    unsigned char wire[2048];
    short weights[256];
    size_t length = fread(wire, 1, sizeof(wire), stdin);
    if (ferror(stdin) || !feof(stdin)) return 2;
    unsigned max_symbol = 255, log;
    size_t consumed = FSE_readNCount(weights, &max_symbol, &log, wire, length);
    if (FSE_isError(consumed)) return 3;
    unsigned count = max_symbol + 1;
    if (!checked_weights(weights, count, log)) return 4;

    FSE_DTable table[FSE_DTABLE_SIZE_U32(9)];
    unsigned workspace[FSE_BUILD_DTABLE_WKSP_SIZE_U32(9, 255)];
    size_t status = FSE_buildDTable_wksp(table, weights, max_symbol, log, workspace, sizeof(workspace));
    if (FSE_isError(status)) return 4;
    printf("%zu %u %u\n", consumed, log, count);
    for (unsigned i = 0; i < count; ++i) printf("%s%d", i ? " " : "", (int)weights[i]);
    putchar('\n');
    for (unsigned i = 0; i < (1U << log); ++i) {
        FSE_decode_t row;
        memcpy(&row, table + 1 + i, sizeof(row));
        printf("%u %u %u\n", (unsigned)row.symbol, (unsigned)row.nbBits, (unsigned)row.newState);
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc >= 2 && !strcmp(argv[1], "write")) return write_counts(argc, argv);
    if (argc == 2 && !strcmp(argv[1], "read")) return read_table();
    return 2;
}
