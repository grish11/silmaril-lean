#include <stdio.h>

#include "c/common/context.h"

int main(void) {
  for (unsigned mode = 0; mode < 4; ++mode) {
    const uint8_t* lut = BROTLI_CONTEXT_LUT(mode);
    for (unsigned first = 0; first < 256; ++first) {
      for (unsigned second = 0; second < 256; ++second) {
        if (putchar(BROTLI_CONTEXT(first, second, lut)) == EOF) return 1;
      }
    }
  }
  return 0;
}
