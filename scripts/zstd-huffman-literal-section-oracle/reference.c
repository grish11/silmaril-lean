#include <stdio.h>

#define ZSTD_STATIC_LINKING_ONLY
#include "decompress/zstd_decompress_internal.h"

size_t ZSTD_decodeLiteralsBlock_wrapper(ZSTD_DCtx *context, const void *source, size_t size,
                                        void *destination, size_t capacity);

int main(void) {
    unsigned char wire[ZSTD_BLOCKSIZE_MAX], output[ZSTD_BLOCKSIZE_MAX];
    size_t size = fread(wire, 1, sizeof(wire), stdin);
    if (ferror(stdin) || fgetc(stdin) != EOF) return 2;

    ZSTD_DCtx *context = ZSTD_createDCtx();
    if (context == NULL) return 2;
    if (ZSTD_isError(ZSTD_decompressBegin(context))) {
        ZSTD_freeDCtx(context);
        return 2;
    }

    size_t consumed = ZSTD_decodeLiteralsBlock_wrapper(context, wire, size, output, sizeof(output));
    if (ZSTD_isError(consumed)) {
        ZSTD_freeDCtx(context);
        return 3;
    }
    printf("%zu %zu\n", consumed, context->litSize);
    size_t written = fwrite(context->litPtr, 1, context->litSize, stdout);
    int status = written == context->litSize ? 0 : 2;
    ZSTD_freeDCtx(context);
    return status;
}
