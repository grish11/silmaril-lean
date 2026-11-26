#include <iostream>
#include <iterator>
#include <string>

#include "snappy.h"

int main(int argc, char** argv) {
  if (argc != 2) return 2;
  const std::string mode(argv[1]);
  const std::string input((std::istreambuf_iterator<char>(std::cin)),
                          std::istreambuf_iterator<char>());
  std::string output;
  if (mode == "encode") {
    snappy::Compress(input.data(), input.size(), &output);
  } else if (mode == "decode") {
    if (!snappy::Uncompress(input.data(), input.size(), &output)) return 1;
  } else {
    return 2;
  }
  std::cout.write(output.data(), output.size());
  return std::cout ? 0 : 1;
}
