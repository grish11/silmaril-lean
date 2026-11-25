#include <stdint.h>

/* FIPS 180-4 section 6.2.2. Return the new working word e. */
uint32_t sha256_round_e(uint32_t d, uint32_t e, uint32_t f,
                        uint32_t g, uint32_t h, uint32_t k, uint32_t w) {
    uint32_t sigma1 = __builtin_rotateright32(e, 6) ^
                      __builtin_rotateright32(e, 11) ^
                      __builtin_rotateright32(e, 25);
    uint32_t choose = g ^ (e & (f ^ g));
    return d + (h + sigma1 + choose + k + w);
}
