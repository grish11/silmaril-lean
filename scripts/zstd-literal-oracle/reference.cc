#include <cstdint>
#include <iostream>
#include <iterator>
#include <string>

#define ZSTD_STATIC_LINKING_ONLY
#include "zstd.h"
extern "C" size_t ZSTD_noCompressLiterals(void*, size_t, const void*, size_t);
extern "C" size_t ZSTD_compressRleLiteralsBlock(void*, size_t, const void*, size_t);

int main(int argc, char** argv) {
  if (argc < 2 || argc > 3) return 2;
  const std::string mode(argv[1]);
  const std::string input((std::istreambuf_iterator<char>(std::cin)),
                          std::istreambuf_iterator<char>());
  const size_t capacity = argc == 3 ? std::stoul(argv[2]) : 131072;
  const size_t storage = mode == "compress" ? ZSTD_compressBound(input.size()) : capacity;
  std::string output(storage == 0 ? 1 : storage, '\0');
  size_t size;
  if (mode == "raw") {
    size = ZSTD_noCompressLiterals(&output[0], output.size(), input.data(), input.size());
  } else if (mode == "rle") {
    if (input.empty()) return 2;
    size = ZSTD_compressRleLiteralsBlock(&output[0], output.size(), input.data(), input.size());
  } else if (mode == "decode") {
    size = ZSTD_decompress(&output[0], capacity, input.data(), input.size());
  } else if (mode == "compress") {
    size = ZSTD_compress(&output[0], output.size(), input.data(), input.size(), 3);
  } else if (mode == "first-block") {
    const size_t at = ZSTD_frameHeaderSize(input.data(), input.size());
    if (ZSTD_isError(at) || at + 3 > input.size()) return 2;
    const auto* bytes = reinterpret_cast<const unsigned char*>(input.data() + at);
    const uint32_t header = bytes[0] + 256u * bytes[1] + 65536u * bytes[2];
    if ((header & 7) != 5 || at + 3 + (header >> 3) != input.size()) return 2;
    std::cout.write(input.data() + at + 3, header >> 3);
    return std::cout ? 0 : 1;
  } else {
    return 2;
  }
  if (ZSTD_isError(size)) return 3;
  std::cout.write(output.data(), size);
  return std::cout ? 0 : 1;
}
