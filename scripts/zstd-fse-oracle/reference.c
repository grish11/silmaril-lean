#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "common/zstd_internal.h"

int main(int argc, char** argv) {
    const short* weights;
    short input[256];
    unsigned log, count;
    if (argc < 2 || argc > 258) return 2;
    if (argc == 2 && !strcmp(argv[1], "literal")) {
        weights = LL_defaultNorm;
        log = LL_defaultNormLog;
        count = MaxLL + 1;
    } else if (argc == 2 && !strcmp(argv[1], "offset")) {
        weights = OF_defaultNorm;
        log = OF_defaultNormLog;
        count = DefaultMaxOff + 1;
    } else if (argc == 2 && !strcmp(argv[1], "match")) {
        weights = ML_defaultNorm;
        log = ML_defaultNormLog;
        count = MaxML + 1;
    } else {
        char* end;
        long parsed = strtol(argv[1], &end, 10);
        if (*end || parsed < 5 || parsed > 9 || argc < 4) return 2;
        log = (unsigned)parsed;
        count = (unsigned)argc - 2;
        unsigned mass = 0, active = 0;
        for (unsigned symbol = 0; symbol < count; ++symbol) {
            long weight = strtol(argv[symbol + 2], &end, 10);
            if (*end || weight < -1 || weight > 512) return 2;
            input[symbol] = (short)weight;
            mass += weight == -1 ? 1 : (unsigned)weight;
            active += weight != 0;
        }
        if (mass != (1U << log) || active < 2) return 2;
        weights = input;
    }
    FSE_DTable table[FSE_DTABLE_SIZE_U32(9)];
    unsigned workspace[FSE_BUILD_DTABLE_WKSP_SIZE_U32(9, 255)];
    size_t status = FSE_buildDTable_wksp(table, weights, count - 1, log, workspace, sizeof(workspace));
    if (FSE_isError(status)) return 3;
    FSE_DTableHeader header;
    memcpy(&header, table, sizeof(header));
    if (header.tableLog != log) return 3;
    printf("%u\n", (unsigned)header.tableLog);
    for (unsigned state = 0; state < (1U << log); ++state) {
        FSE_decode_t row;
        memcpy(&row, table + 1 + state, sizeof(row));
        printf("%u %u %u\n", (unsigned)row.symbol, (unsigned)row.nbBits, (unsigned)row.newState);
    }
    return 0;
}
