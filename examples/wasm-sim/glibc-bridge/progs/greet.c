/* glibc-linked: puts, strlen, write, memcpy, memset, and main's return value as exit code. */
#include <stdio.h>
#include <string.h>
#include <unistd.h>
int main(int argc, char **argv) {
  char buf[64];
  memset(buf, '-', sizeof buf);
  unsigned long total = 0;
  for (int i = 1; i < argc; i++) {
    unsigned long n = strlen(argv[i]);
    if (n > 60) n = 60;
    memcpy(buf, argv[i], n);
    buf[n] = '\n';
    write(1, buf, n + 1);
    total += n;
  }
  puts("done");
  return (int)(total & 63);
}
