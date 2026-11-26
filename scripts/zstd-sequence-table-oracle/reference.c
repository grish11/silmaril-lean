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

static int read_section(ZSTD_DCtx *ctx, const unsigned char *wire, size_t length) {
    int count = 0;
    size_t consumed = ZSTD_decodeSeqHeaders(ctx, &count, wire, length);
    if (ZSTD_isError(consumed)) return 3;
    printf("%zu %d\n", consumed, count);
    if (count) {
        print_table(ctx->LLTptr);
        print_table(ctx->OFTptr);
        print_table(ctx->MLTptr);
        /* Model accepting this section's payload. Full frames independently
           exercise libzstd's real payload acceptance and state update. */
        ctx->fseEntropy = 1;
    }
    return 0;
}

static int read_input(ZSTD_DCtx *ctx, int series) {
    unsigned char wire[131072];
    if (!series) {
        size_t length = fread(wire, 1, sizeof(wire), stdin);
        if (ferror(stdin) || fgetc(stdin) != EOF) return 2;
        return read_section(ctx, wire, length);
    }
    for (;;) {
        unsigned char size[4];
        size_t got = fread(size, 1, sizeof(size), stdin);
        if (!got && feof(stdin)) return 0;
        if (got != sizeof(size)) return 2;
        size_t length = (size_t)size[0] | (size_t)size[1] << 8 |
                        (size_t)size[2] << 16 | (size_t)size[3] << 24;
        if (length > sizeof(wire) || fread(wire, 1, length, stdin) != length) return 2;
        int status = read_section(ctx, wire, length);
        if (status) return status;
        putchar('\n');
    }
}

int main(int argc, char **argv) {
    int series = argc == 2 && !strcmp(argv[1], "--series");
    if (argc != 1 && !series) return 2;
    ZSTD_DCtx *ctx = ZSTD_createDCtx();
    if (!ctx) return 2;
    size_t status = ZSTD_decompressBegin(ctx);
    int result = ZSTD_isError(status) ? 2 : read_input(ctx, series);
    ZSTD_freeDCtx(ctx);
    return result;
}
