#include <stdio.h>

#define FSE_STATIC_LINKING_ONLY
#include "common/fse.h"

int main(void) {
    unsigned char wire[131072];
    size_t length = fread(wire, 1, sizeof(wire), stdin);
    if (ferror(stdin) || fgetc(stdin) != EOF) return 2;
    if (length == 0 || wire[0] == 0 || wire[0] >= 128 || length <= wire[0]) return 3;

    unsigned workspace[FSE_DECOMPRESS_WKSP_SIZE_U32(6, FSE_MAX_SYMBOL_VALUE)];
    unsigned char weights[512];
    size_t used = FSE_decompress_wksp_bmi2(weights, sizeof(weights), wire + 1, wire[0], 6,
                                          workspace, sizeof(workspace), 0);
    if (FSE_isError(used)) return 3;
    return fwrite(weights, 1, used, stdout) == used ? 0 : 2;
}
