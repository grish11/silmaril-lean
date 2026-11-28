#include <stdio.h>

#include "c/dec/prefix.h"

int main(void) {
  for (unsigned i = 0; i < BROTLI_NUM_COMMAND_SYMBOLS; ++i) {
    const CmdLutElement row = kCmdLut[i];
    printf("%u %u %u %u %u %u\n", i, (unsigned)row.insert_len_offset,
           (unsigned)row.insert_len_extra_bits, (unsigned)row.copy_len_offset,
           (unsigned)row.copy_len_extra_bits, (unsigned)(row.distance_code != 0));
  }
  return 0;
}
