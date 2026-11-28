#include <stdio.h>
#include <string.h>

#define ZSTD_STATIC_LINKING_ONLY
#include "zstd.h"

static unsigned char wire[131072], decoded[262144], full[262144];

int main(void) {
    size_t size = fread(wire, 1, sizeof(wire), stdin);
    if (ferror(stdin) || fgetc(stdin) != EOF) return 2;
    ZSTD_frameHeader frame;
    if (ZSTD_getFrameHeader(&frame, wire, size) != 0 || frame.frameType != ZSTD_frame ||
        frame.dictID != 0 || frame.checksumFlag != 0) return 2;
    size_t fullSize = ZSTD_decompress(full, sizeof(full), wire, size);
    if (ZSTD_isError(fullSize)) return 3;
    printf("%u %u %llu %u %zu\n", frame.headerSize, frame.dictID, frame.windowSize,
           frame.blockSizeMax, fullSize);

    ZSTD_DCtx *context = ZSTD_createDCtx();
    if (context == NULL) return 2;
    int ret = 3;
    if (ZSTD_isError(ZSTD_decompressBegin(context))) goto done;
    size_t at = frame.headerSize, offsets[2], sizes[2];
    for (unsigned i = 0; i < 2; ++i) {
        if (at + 3 >= size) goto done;
        unsigned header = wire[at] + 256u * wire[at + 1] + 65536u * wire[at + 2];
        size_t bodySize = header >> 3;
        if ((header & 7) != (4 | i) || bodySize == 0 || at + 3 + bodySize > size) goto done;
        offsets[i] = at;
        sizes[i] = bodySize;
        at += 3 + bodySize;
    }
    if (at != size) goto done;

    size_t pos = 0, written = 0, needed;
    unsigned block = 0;
    while ((needed = ZSTD_nextSrcSizeToDecompress(context)) != 0) {
        if (needed > size - pos) goto done;
        size_t count = ZSTD_decompressContinue(context, decoded + written, sizeof(decoded) - written,
                                              wire + pos, needed);
        if (ZSTD_isError(count)) goto done;
        if (block < 2 && pos == offsets[block] + 3) {
            if (needed != sizes[block] || count == 0) goto done;
            printf("%zu %zu %zu\n", offsets[block], sizes[block], count);
            ++block;
        } else if (count != 0) goto done;
        pos += needed;
        written += count;
    }
    if (block != 2 || pos != size || written != fullSize || memcmp(decoded, full, fullSize) != 0) goto done;
    ret = fwrite(decoded, 1, written, stdout) == written ? 0 : 2;
done:
    ZSTD_freeDCtx(context);
    return ret;
}
