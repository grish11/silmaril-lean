/* Encode a file with explicit RFC distance parameters through the public API. */
#include <brotli/encode.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv) {
  BrotliEncoderState* encoder = NULL;
  uint8_t input[65536];
  uint8_t* output = NULL;
  size_t in_size, out_size;
  const uint8_t* in;
  uint8_t* out;
  int status = 1;
  if (argc != 3) return 2;
  in_size = fread(input, 1, sizeof(input), stdin);
  if (!feof(stdin) || ferror(stdin)) return 2;
  out_size = BrotliEncoderMaxCompressedSize(in_size);
  output = malloc(out_size);
  encoder = BrotliEncoderCreateInstance(NULL, NULL, NULL);
  if (!encoder || !output) goto done;
  if (!BrotliEncoderSetParameter(encoder, BROTLI_PARAM_QUALITY, 7) ||
      !BrotliEncoderSetParameter(encoder, BROTLI_PARAM_LGWIN, 18) ||
      !BrotliEncoderSetParameter(encoder, BROTLI_PARAM_NPOSTFIX, (uint32_t)strtoul(argv[1], NULL, 10)) ||
      !BrotliEncoderSetParameter(encoder, BROTLI_PARAM_NDIRECT, (uint32_t)strtoul(argv[2], NULL, 10))) goto done;
  in = input;
  out = output;
  if (!BrotliEncoderCompressStream(encoder, BROTLI_OPERATION_FINISH,
                                   &in_size, &in, &out_size, &out, NULL) ||
      !BrotliEncoderIsFinished(encoder) || in_size != 0) goto done;
  if (fwrite(output, 1, (size_t)(out - output), stdout) == (size_t)(out - output)) status = 0;
done:
  if (encoder) BrotliEncoderDestroyInstance(encoder);
  free(output);
  return status;
}
