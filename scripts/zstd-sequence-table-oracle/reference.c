#include <stdio.h>
#include <string.h>

#include "decompress/zstd_decompress_internal.h"
#include "decompress/zstd_decompress_block.h"

static void print_table(const ZSTD_seqSymbol *entries) {
    ZSTD_seqSymbol_header header;
    memcpy(&header, entries, sizeof(header));
    printf("%u\n", (unsigned)header.tableLog);
    for (unsigned i = 1; i <= (1U << header.tableLog); ++i) {
        const ZSTD_seqSymbol *row = &entries[i];
        printf("%u %u %u %u\n", (unsigned)row->nextState, (unsigned)row->nbBits,
               (unsigned)row->baseValue, (unsigned)row->nbAdditionalBits);
    }
}

int main(void) {
    unsigned char wire[131072];
    size_t length = fread(wire, 1, sizeof(wire), stdin);
    if (ferror(stdin) || fgetc(stdin) != EOF) return 2;
    ZSTD_DCtx *ctx = ZSTD_createDCtx();
    if (!ctx) return 2;
    size_t status = ZSTD_decompressBegin(ctx);
    int count = 0;
    if (!ZSTD_isError(status)) status = ZSTD_decodeSeqHeaders(ctx, &count, wire, length);
    if (ZSTD_isError(status)) {
        ZSTD_freeDCtx(ctx);
        return 3;
    }
    printf("%zu %d\n", status, count);
    if (count) {
        print_table(ctx->LLTptr);
        print_table(ctx->OFTptr);
        print_table(ctx->MLTptr);
    }
    ZSTD_freeDCtx(ctx);
    return 0;
}
