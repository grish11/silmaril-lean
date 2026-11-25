#include <stdint.h>

uint32_t sha256_round_a(uint32_t a, uint32_t b, uint32_t c, uint32_t e,
                        uint32_t f, uint32_t g, uint32_t h, uint32_t k, uint32_t w);
uint32_t sha256_round_e(uint32_t d, uint32_t e, uint32_t f,
                        uint32_t g, uint32_t h, uint32_t k, uint32_t w);

/* out has space for eight uint32_t values. Scalar inputs are passed by value. */
void sha256_round(uint32_t out[8], uint32_t a, uint32_t b, uint32_t c,
                  uint32_t d, uint32_t e, uint32_t f, uint32_t g, uint32_t h,
                  uint32_t k, uint32_t w) {
    out[0] = sha256_round_a(a, b, c, e, f, g, h, k, w);
    out[1] = a;
    out[2] = b;
    out[3] = c;
    out[4] = sha256_round_e(d, e, f, g, h, k, w);
    out[5] = e;
    out[6] = f;
    out[7] = g;
}
