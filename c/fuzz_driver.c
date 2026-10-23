/* A deliberately simple random fuzzer: no coverage feedback, no mutation.
 * Link it with any LLVMFuzzerTestOneInput and -fsanitize=address.
 *
 *   ./fuzz_X [iterations] [max_len] [alphabet] [seed]
 *
 * alphabet = how many distinct byte values to draw from (1..256). A small
 * alphabet makes long runs *more* likely -- we're trying to help it.
 * If you have libFuzzer (clang -fsanitize=fuzzer), use that instead: it's
 * coverage-guided and far better. The point here is to see what *sampling*
 * finds and what it doesn't. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

int main(int argc, char **argv) {
  long iters   = argc > 1 ? atol(argv[1]) : 100000;
  long max_len = argc > 2 ? atol(argv[2]) : 600;
  int alphabet = argc > 3 ? atoi(argv[3]) : 256;
  unsigned seed = argc > 4 ? (unsigned)atol(argv[4]) : 1;
  if (alphabet < 1 || alphabet > 256) alphabet = 256;
  srand(seed);
  for (long it = 0; it < iters; it++) {
    size_t len = (size_t)(rand() % (max_len + 1));
    /* exact-size heap buffer, so ASan's redzone sits right after the input */
    uint8_t *buf = malloc(len ? len : 1);
    for (size_t i = 0; i < len; i++) buf[i] = (uint8_t)(rand() % alphabet);
    LLVMFuzzerTestOneInput(buf, len);
    free(buf);
  }
  printf("%ld inputs (max_len=%ld, alphabet=%d): no crash\n", iters, max_len, alphabet);
  return 0;
}
