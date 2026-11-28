/* Emit one complex prefix description using the unmodified pinned writer. */
#include <stdint.h>
#include <stdio.h>
#include "c/enc/brotli_bit_stream.h"

int main(void) {
  const uint8_t depths[8] = {3, 3, 3, 3, 3, 3, 3, 3};
  HuffmanTree scratch[2 * BROTLI_CODE_LENGTH_CODES + 1];
  uint8_t wire[32] = {0};
  size_t bits = 0;
  BrotliStoreHuffmanTree(depths, 8, scratch, &bits, wire);
  fprintf(stderr, "%zu\n", bits);
  return fwrite(wire, 1, (bits + 7) / 8, stdout) == (bits + 7) / 8 ? 0 : 1;
}
