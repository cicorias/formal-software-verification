/* Stage 3: the RLE codec, in C, as a fuzz target with a round-trip property.
 *
 * Build with -DRLE_BUG to get the encoder that lets a run counter overflow
 * (a run of 256 equal bytes encodes with count 0). The property check is
 * `if (!cond) abort();` -- never assert(), which NDEBUG silently deletes. */
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* A property failure must be loud and fatal in every build mode. */
static void fail(const char *what) {
  fprintf(stderr, "PROPERTY FAILED: %s\n", what);
  abort();
}

/* out must have room for 2*len bytes. Returns encoded length. */
static size_t rle_encode(const uint8_t *in, size_t len, uint8_t *out) {
  size_t o = 0, i = 0;
  while (i < len) {
    uint8_t cur = in[i];
    uint32_t cnt = 1;
#ifdef RLE_BUG
    while (i + cnt < len && in[i + cnt] == cur) cnt++;              /* no cap */
#else
    while (i + cnt < len && in[i + cnt] == cur && cnt < 255) cnt++;
#endif
    out[o++] = (uint8_t)cnt;                                      /* wraps at 256 */
    out[o++] = cur;
    i += cnt;
  }
  return o;
}

/* Returns decoded length, or (size_t)-1 if it would exceed cap. */
static size_t rle_decode(const uint8_t *in, size_t len, uint8_t *out, size_t cap) {
  size_t o = 0;
  for (size_t i = 0; i + 1 < len; i += 2) {
    size_t n = in[i];
    if (n > cap - o) return (size_t)-1;
    memset(out + o, in[i + 1], n);
    o += n;
  }
  return o;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  uint8_t *enc = malloc(2 * size + 2);
  uint8_t *dec = malloc(size + 1);
  if (!enc || !dec) fail("out of memory");
  size_t elen = rle_encode(data, size, enc);
  /* Property 1 (size bound): encoding at most doubles the input. */
  if (elen > 2 * size) fail("size bound");
  size_t dlen = rle_decode(enc, elen, dec, size);
  /* Property 2 (round trip): decode(encode(x)) == x. */
  if (dlen != size || memcmp(dec, data, size) != 0) fail("round trip");
  free(enc);
  free(dec);
  return 0;
}
