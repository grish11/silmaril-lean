#include <stdio.h>
#include <string.h>

#define ZSTD_STATIC_LINKING_ONLY
#include "decompress/zstd_decompress_internal.h"
#include "zstd_errors.h"

size_t ZSTD_decodeLiteralsBlock_wrapper(ZSTD_DCtx *context, const void *source, size_t size,
                                        void *destination, size_t capacity);

static unsigned char input[262144], output[262144], second[ZSTD_BLOCKSIZE_MAX];

struct block {
    size_t offset;
    size_t size;
    const unsigned char *body;
};

static size_t literals(ZSTD_DCtx *context, const struct block *block) {
    return ZSTD_decodeLiteralsBlock_wrapper(context, block->body, block->size,
                                           output, sizeof(output));
}

static int pair(size_t size) {
    ZSTD_frameHeader frame;
    size_t status = ZSTD_getFrameHeader(&frame, input, size);
    if (status != 0 || frame.frameType != ZSTD_frame || frame.dictID != 0 || frame.checksumFlag != 0) return 2;

    size_t at = frame.headerSize;
    struct block blocks[2];
    for (unsigned i = 0; i < 2; ++i) {
        if (at + 3 >= size) return 2;
        unsigned header = input[at] + 256u * input[at + 1] + 65536u * input[at + 2];
        if ((header & 7) != (4 | i)) return 2; /* Two compressed blocks, the second marked last. */
        blocks[i] = (struct block){at, header >> 3, input + at + 3};
        at += 3 + blocks[i].size;
        if (at > size || blocks[i].size == 0 || (blocks[i].body[0] & 3) != 2 + i) return 2;
    }
    if (at != size) return 2;

    ZSTD_DCtx *context = ZSTD_createDCtx();
    if (context == NULL) return 2;
    int ret = 2;
    if (ZSTD_isError(ZSTD_decompressBegin(context))) goto done;
    printf("%u %u %u\n", frame.headerSize, frame.dictID, frame.blockSizeMax);
    size_t secondSize = 0;
    for (unsigned i = 0; i < 2; ++i) {
        size_t used = literals(context, &blocks[i]);
        if (ZSTD_isError(used) || used >= blocks[i].size || context->litSize > sizeof(second)) goto done;
        printf("%zu %zu %u %u %zu %zu\n", blocks[i].offset, blocks[i].size,
               (unsigned)(blocks[i].body[0] & 3), (unsigned)((blocks[i].body[0] >> 2) & 3),
               used, context->litSize);
        if (fwrite(context->litPtr, 1, context->litSize, stdout) != context->litSize) goto done;
        if (i == 1) {
            secondSize = context->litSize;
            memcpy(second, context->litPtr, secondSize);
        }
    }

    if (ZSTD_isError(ZSTD_decompressBegin(context))) goto done;
    if (ZSTD_getErrorCode(literals(context, &blocks[1])) != ZSTD_error_dictionary_corrupted) goto done;

    if (ZSTD_isError(ZSTD_decompressBegin(context)) || ZSTD_isError(literals(context, &blocks[0]))) goto done;
    const unsigned char raw[] = {8, 'a', 0};
    const unsigned char rle[] = {25, 'b', 0};
    if (ZSTD_decodeLiteralsBlock_wrapper(context, raw, sizeof(raw), output, sizeof(output)) != 2 ||
        context->litSize != 1 || context->litPtr[0] != 'a') goto done;
    if (ZSTD_decodeLiteralsBlock_wrapper(context, rle, sizeof(rle), output, sizeof(output)) != 2 ||
        context->litSize != 3 || memcmp(context->litPtr, "bbb", 3) != 0) goto done;
    if (ZSTD_isError(literals(context, &blocks[1])) || context->litSize != secondSize ||
        memcmp(context->litPtr, second, secondSize) != 0) goto done;

    puts("reset=dictionary_corrupted raw-rle=preserved");
    ret = 0;
done:
    ZSTD_freeDCtx(context);
    return ret;
}

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    size_t size = fread(input, 1, sizeof(input), stdin);
    if (ferror(stdin) || fgetc(stdin) != EOF) return 2;
    if (!strcmp(argv[1], "pair")) return pair(size);

    size_t result;
    if (!strcmp(argv[1], "compress")) result = ZSTD_compress(output, sizeof(output), input, size, 3);
    else if (!strcmp(argv[1], "decode")) result = ZSTD_decompress(output, sizeof(output), input, size);
    else return 2;
    if (ZSTD_isError(result)) return 3;
    return fwrite(output, 1, result, stdout) == result ? 0 : 2;
}
