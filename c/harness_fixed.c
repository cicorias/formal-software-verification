/* Stage 7: a fuzz harness with the off-by-one fixed.
 * Record format: [n][payload: n bytes]. Sum the payload.
 * (A real OSS-Fuzz harness returns 0; we return the sum so the compiler keeps
 * the loop, and so Stage 8's functional spec has something to observe.) */
#include <stdint.h>
#include <stddef.h>

uint32_t LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  if (size == 0) return 0;
  size_t n = data[0];
  if (n >= size) return 0;         /* FIXED */
  uint32_t s = 0;
  for (size_t i = 0; i < n; i++) s += data[1 + i];
  return s;
}
