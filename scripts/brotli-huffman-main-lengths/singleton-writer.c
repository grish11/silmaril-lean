/* Emit complex tables whose code-length alphabet is a singleton. */
#include <stdint.h>
#include <stdio.h>
#include "c/enc/brotli_bit_stream.h"

int main(int argc, char** argv) {
  const size_t alphabet = argc == 1 ? 8 : 256;
  const uint8_t width = argc == 1 ? 3 : 8;
  uint8_t depths[256];
  HuffmanTree scratch[2 * BROTLI_CODE_LENGTH_CODES + 1];
  uint8_t wire[32] = {0};
  size_t bits = 0, i;
  (void)argv;
  for (i = 0; i < alphabet; ++i) depths[i] = width;
  BrotliStoreHuffmanTree(depths, alphabet, scratch, &bits, wire);
  fprintf(stderr, "%zu\n", bits);
  return fwrite(wire, 1, (bits + 7) / 8, stdout) == (bits + 7) / 8 ? 0 : 1;
}
