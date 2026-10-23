/* Run a fuzz target on one input file: ./run_X file */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: %s FILE\n", argv[0]); return 2; }
  FILE *f = fopen(argv[1], "rb");
  if (!f) { perror(argv[1]); return 2; }
  static uint8_t buf[1 << 20];
  size_t n = fread(buf, 1, sizeof buf, f);
  fclose(f);
  uint8_t *exact = malloc(n ? n : 1);           /* exact size: ASan redzone after it */
  for (size_t i = 0; i < n; i++) exact[i] = buf[i];
  LLVMFuzzerTestOneInput(exact, n);
  printf("ok: %zu bytes, no crash\n", n);
  return 0;
}
