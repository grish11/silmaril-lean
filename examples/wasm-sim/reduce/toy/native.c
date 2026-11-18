// Native reference for the toy: prints f(a, b) (examples/wasm-sim/reduce/toy/toy.S).
#include <stdio.h>
#include <stdlib.h>
long f(long a, long b);
int main(int argc, char **argv) {
  if (argc != 3) return 2;
  printf("%ld\n", f(strtol(argv[1], 0, 0), strtol(argv[2], 0, 0)));
  return 0;
}
