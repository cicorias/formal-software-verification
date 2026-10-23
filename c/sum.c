/* Stage 6: the function whose RISC-V binary we prove never crashes.
 * `make asm` regenerates build/sum.s; compare it with `sumProg` in
 * Metal/S06_NoCrash.lean. */
#include <stdint.h>
#include <stddef.h>

uint32_t sum(const uint8_t *p, uint32_t len) {
  uint32_t s = 0;
  for (uint32_t i = 0; i < len; i++) s += p[i];
  return s;
}
