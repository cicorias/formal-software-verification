/* Stage 5/6 exercises: the C behind countZerosProg, maxByteProg, lastByteProg. */
#include <stdint.h>
#include <stddef.h>

uint32_t count_zeros(const uint8_t *p, size_t len) {
  uint32_t c = 0;
  for (size_t i = 0; i < len; i++) c += (p[i] == 0);
  return c;
}

uint32_t max_byte(const uint8_t *p, size_t len) {
  uint32_t m = 0;
  for (size_t i = 0; i < len; i++) if (p[i] > m) m = p[i];
  return m;
}

/* Reads p[-1] when len == 0. */
uint32_t last_byte(const uint8_t *p, size_t len) {
  return p[len - 1];
}
