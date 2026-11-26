#include <stdio.h>
#include <string.h>

#define FSE_STATIC_LINKING_ONLY
#include "common/fse.h"

enum { MAX_LOG = 6, MAX_SYMBOL = 11 };

static size_t remaining(const BIT_DStream_t *stream) {
    return 8 * ((size_t)(stream->ptr - stream->start) + sizeof(stream->bitContainer))
        - stream->bitsConsumed;
}

int main(void) {
    unsigned char wire[131072];
    size_t length = fread(wire, 1, sizeof(wire), stdin);
    if (ferror(stdin) || fgetc(stdin) != EOF) return 2;
    if (length == 0 || wire[0] == 0 || wire[0] >= 128 || length <= wire[0]) return 3;

    size_t bodySize = wire[0];
    short counts[MAX_SYMBOL + 1];
    unsigned maxSymbol = MAX_SYMBOL;
    unsigned log;
    size_t used = FSE_readNCount(counts, &maxSymbol, &log, wire + 1, bodySize);
    if (FSE_isError(used) || log > MAX_LOG || used >= bodySize) return 3;
    FSE_DTable table[FSE_DTABLE_SIZE_U32(MAX_LOG)];
    unsigned workspace[FSE_BUILD_DTABLE_WKSP_SIZE_U32(MAX_LOG, MAX_SYMBOL)];
    if (FSE_isError(FSE_buildDTable_wksp(table, counts, maxSymbol, log,
                                        workspace, sizeof(workspace)))) return 3;

    BIT_DStream_t stream;
    size_t opened = BIT_initDStream(&stream, wire + 1 + used, bodySize - used);
    if (FSE_isError(opened) || remaining(&stream) < 2 * log) return 3;
    FSE_DState_t first, second;
    FSE_initDState(&first, &stream, table);
    FSE_initDState(&second, &stream, table);
    size_t unread = remaining(&stream);
    printf("%zu %zu %u %zu %zu %zu\n", 1 + bodySize, used, log, first.state, second.state, unread);
    for (unsigned i = 0; i <= maxSymbol; ++i) printf("%s%d", i ? " " : "", (int)counts[i]);
    putchar('\n');
    for (unsigned i = 0; i < 1U << log; ++i) {
        FSE_decode_t row;
        memcpy(&row, table + 1 + i, sizeof(row));
        printf("%u %u %u\n", (unsigned)row.symbol, (unsigned)row.nbBits, (unsigned)row.newState);
    }
    for (size_t i = 0; i < unread; ++i) {
        BIT_reloadDStream(&stream);
        putchar('0' + (int)BIT_readBits(&stream, 1));
    }
    putchar('\n');
    return BIT_endOfDStream(&stream) ? 0 : 2;
}
