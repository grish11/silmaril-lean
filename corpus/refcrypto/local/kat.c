/* local/kat.c -- repository-authored known-answer test driver (OURS, not upstream).
 * Why: shows that each libref_*.so built for an architecture computes the standard answers. It is
 * linked against the seven libraries by test.sh and run natively (x86_64) or under qemu-user
 * (aarch64); it is not itself a corpus object. The prototypes below restate the upstream APIs so the
 * driver needs no upstream headers. Vectors (all public, from the cited standards):
 *   SHA-1/256/512 "abc" (FIPS 180-4 examples); HMAC-SHA-256 RFC 4231 test case 2; HKDF-SHA-256
 *   RFC 5869 test case 1; SHA3-256/512 "abc", SHAKE128/256 "" (FIPS 202 examples, NIST CSRC);
 *   BLAKE2b-512/BLAKE2s-256 "abc" (RFC 7693 appendices A, B); AES-128/192/256 (FIPS 197 C.1-C.3);
 *   ChaCha20 block with zero key/nonce (RFC 8439 A.1 #1) and the "sunscreen" encryption (RFC 8439
 *   2.4.2; DJB's 64-bit-nonce layout equals RFC 8439's when the first nonce word is 0);
 *   Poly1305 (RFC 8439 2.5.2); Ed25519 (RFC 8032 7.1 TEST 1, TEST 2); X25519 (RFC 7748 5.2, 6.1). */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stddef.h>

/* RFC 6234 (libref_sha2.so) */
enum SHAversion { SHA1, SHA224, SHA256, SHA384, SHA512 };
int USHAHashSizeBits(enum SHAversion);
typedef struct { uint64_t opaque[64]; } USHAContextBig;   /* at least as large and aligned as USHAContext */
int USHAReset(void *ctx, enum SHAversion);
int USHAInput(void *ctx, const uint8_t *bytes, unsigned int len);
int USHAResult(void *ctx, uint8_t *digest);
int hmac(enum SHAversion, const unsigned char *text, int text_len, const unsigned char *key, int key_len, uint8_t *digest);
int hkdf(enum SHAversion, const unsigned char *salt, int salt_len, const unsigned char *ikm, int ikm_len,
         const unsigned char *info, int info_len, uint8_t *okm, int okm_len);
/* XKCP (libref_sha3.so) */
void FIPS202_SHAKE128(const unsigned char *in, unsigned int inlen, unsigned char *out, int outlen);
void FIPS202_SHAKE256(const unsigned char *in, unsigned int inlen, unsigned char *out, int outlen);
void FIPS202_SHA3_256(const unsigned char *in, unsigned int inlen, unsigned char *out);
void FIPS202_SHA3_512(const unsigned char *in, unsigned int inlen, unsigned char *out);
/* BLAKE2 (libref_blake2.so) */
int blake2b(void *out, size_t outlen, const void *in, size_t inlen, const void *key, size_t keylen);
int blake2s(void *out, size_t outlen, const void *in, size_t inlen, const void *key, size_t keylen);
/* rijndael-alg-fst (libref_aes.so) */
int rijndaelKeySetupEnc(uint32_t rk[], const uint8_t key[], int keyBits);
int rijndaelKeySetupDec(uint32_t rk[], const uint8_t key[], int keyBits);
void rijndaelEncrypt(const uint32_t rk[], int Nr, const uint8_t pt[16], uint8_t ct[16]);
void rijndaelDecrypt(const uint32_t rk[], int Nr, const uint8_t ct[16], uint8_t pt[16]);
/* SUPERCOP chacha20 e/ref + poly1305-donna (libref_chacha_poly.so) */
int crypto_stream_chacha20(unsigned char *c, unsigned long long clen, const unsigned char *n, const unsigned char *k);
int crypto_stream_chacha20_xor(unsigned char *c, const unsigned char *m, unsigned long long mlen, const unsigned char *n, const unsigned char *k);
void poly1305_auth(unsigned char mac[16], const unsigned char *m, size_t bytes, const unsigned char key[32]);
/* orlp/ed25519 (libref_ed25519.so) */
void ed25519_create_keypair(unsigned char *public_key, unsigned char *private_key, const unsigned char *seed);
void ed25519_sign(unsigned char *signature, const unsigned char *message, size_t message_len, const unsigned char *public_key, const unsigned char *private_key);
int ed25519_verify(const unsigned char *signature, const unsigned char *message, size_t message_len, const unsigned char *public_key);
/* SUPERCOP curve25519 ref10 (libref_x25519.so) */
int crypto_scalarmult_curve25519(unsigned char *q, const unsigned char *n, const unsigned char *p);
int crypto_scalarmult_curve25519_base(unsigned char *q, const unsigned char *n);

static int fails, total;
static size_t unhex(uint8_t *out, const char *h) {
    size_t n = 0;
    for (; h[0] && h[1]; h += 2) { unsigned v; sscanf(h, "%2x", &v); out[n++] = (uint8_t)v; }
    return n;
}
static void expect(const char *name, const uint8_t *got, size_t len, const char *want_hex) {
    uint8_t want[512]; size_t wl = unhex(want, want_hex);
    int ok = wl == len && memcmp(got, want, len) == 0;
    total++; if (!ok) fails++;
    printf("%s %s\n", ok ? "PASS" : "FAIL", name);
    if (!ok) { printf("  got  "); for (size_t i = 0; i < len; i++) printf("%02x", got[i]); printf("\n  want %s\n", want_hex); }
}
#define S(x) (const unsigned char *)(x), (unsigned)strlen(x)

int main(void) {
    uint8_t out[512], b[512], k[64], n[64], m[512];
    USHAContextBig ctx;
    /* SHA-1/2 via the RFC 6234 USHA interface */
    struct { enum SHAversion v; const char *name, *hex; } sv[] = {
        { SHA1, "SHA-1(abc) [RFC 6234]", "a9993e364706816aba3e25717850c26c9cd0d89d" },
        { SHA224, "SHA-224(abc) [RFC 6234]", "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7" },
        { SHA256, "SHA-256(abc) [RFC 6234]", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" },
        { SHA384, "SHA-384(abc) [RFC 6234]", "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7" },
        { SHA512, "SHA-512(abc) [RFC 6234]", "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f" },
    };
    for (unsigned i = 0; i < sizeof sv / sizeof sv[0]; i++) {
        USHAReset(&ctx, sv[i].v); USHAInput(&ctx, (const uint8_t *)"abc", 3); USHAResult(&ctx, out);
        expect(sv[i].name, out, (size_t)USHAHashSizeBits(sv[i].v) / 8, sv[i].hex);
    }
    hmac(SHA256, S("what do ya want for nothing?"), S("Jefe"), out);
    expect("HMAC-SHA-256 RFC 4231 TC2 [RFC 6234]", out, 32, "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843");
    memset(k, 0x0b, 22); unhex(b, "000102030405060708090a0b0c"); unhex(n, "f0f1f2f3f4f5f6f7f8f9");
    hkdf(SHA256, b, 13, k, 22, n, 10, out, 42);
    expect("HKDF-SHA-256 RFC 5869 TC1 [RFC 6234]", out, 42, "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865");
    /* SHA-3 */
    FIPS202_SHA3_256((const unsigned char *)"abc", 3, out);
    expect("SHA3-256(abc) [XKCP compact]", out, 32, "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532");
    FIPS202_SHA3_512((const unsigned char *)"abc", 3, out);
    expect("SHA3-512(abc) [XKCP compact]", out, 64, "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0");
    FIPS202_SHAKE128((const unsigned char *)"", 0, out, 32);
    expect("SHAKE128('',256 bits) [XKCP compact]", out, 32, "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26");
    FIPS202_SHAKE256((const unsigned char *)"", 0, out, 64);
    expect("SHAKE256('',512 bits) [XKCP compact]", out, 64, "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762fd75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be");
    /* BLAKE2 */
    blake2b(out, 64, "abc", 3, NULL, 0);
    expect("BLAKE2b-512(abc) RFC 7693 A [BLAKE2 ref]", out, 64, "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923");
    blake2s(out, 32, "abc", 3, NULL, 0);
    expect("BLAKE2s-256(abc) RFC 7693 B [BLAKE2 ref]", out, 32, "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982");
    /* AES */
    {
        static const char *ct[3] = { "69c4e0d86a7b0430d8cdb78070b4c55a", "dda97ca4864cdfe06eaf70a0ec0d7191", "8ea2b7ca516745bfeafc49904b496089" };
        uint32_t rk[60]; uint8_t pt[16], key[32], back[16]; char name[64];
        unhex(pt, "00112233445566778899aabbccddeeff");
        for (int i = 0; i < 32; i++) key[i] = (uint8_t)i;
        for (int j = 0; j < 3; j++) {
            int bits = 128 + 64 * j;
            int nr = rijndaelKeySetupEnc(rk, key, bits); rijndaelEncrypt(rk, nr, pt, out);
            snprintf(name, sizeof name, "AES-%d encrypt FIPS 197 C.%d [rijndael-alg-fst]", bits, j + 1);
            expect(name, out, 16, ct[j]);
            nr = rijndaelKeySetupDec(rk, key, bits); rijndaelDecrypt(rk, nr, out, back);
            snprintf(name, sizeof name, "AES-%d decrypt FIPS 197 C.%d [rijndael-alg-fst]", bits, j + 1);
            expect(name, back, 16, "00112233445566778899aabbccddeeff");
        }
    }
    /* ChaCha20 */
    memset(k, 0, 32); memset(n, 0, 8);
    crypto_stream_chacha20(out, 64, n, k);
    expect("ChaCha20 block, zero key/nonce, RFC 8439 A.1 #1 [SUPERCOP e/ref]", out, 64, "76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586");
    {
        const char *pt = "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
        size_t len = strlen(pt);
        for (int i = 0; i < 32; i++) k[i] = (uint8_t)i;
        unhex(n, "0000004a00000000");          /* RFC nonce 00000000 0000004a 00000000: word 0 = counter high */
        memset(m, 0, 64); memcpy(m + 64, pt, len);  /* skip block 0: RFC 2.4.2 starts at counter 1 */
        crypto_stream_chacha20_xor(b, m, 64 + len, n, k);
        expect("ChaCha20 encrypt RFC 8439 2.4.2 [SUPERCOP e/ref]", b + 64, len, "6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d");
    }
    unhex(k, "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b");
    poly1305_auth(out, (const unsigned char *)"Cryptographic Forum Research Group", 34, k);
    expect("Poly1305 RFC 8439 2.5.2 [poly1305-donna]", out, 16, "a8061dc1305136c6c22b8baf0c0127a9");
    /* Ed25519 */
    {
        uint8_t pk[32], sk[64], sig[64], msg[1];
        unhex(n, "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
        ed25519_create_keypair(pk, sk, n);
        expect("Ed25519 RFC 8032 TEST 1 public key [orlp/ed25519]", pk, 32, "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
        ed25519_sign(sig, msg, 0, pk, sk);
        expect("Ed25519 RFC 8032 TEST 1 signature [orlp/ed25519]", sig, 64, "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b");
        uint8_t r = (uint8_t)ed25519_verify(sig, msg, 0, pk); expect("Ed25519 RFC 8032 TEST 1 verify == 1 [orlp/ed25519]", &r, 1, "01");
        sig[0] ^= 1; r = (uint8_t)ed25519_verify(sig, msg, 0, pk); expect("Ed25519 corrupted signature rejected [orlp/ed25519]", &r, 1, "00");
        unhex(n, "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb"); msg[0] = 0x72;
        ed25519_create_keypair(pk, sk, n); ed25519_sign(sig, msg, 1, pk, sk);
        expect("Ed25519 RFC 8032 TEST 2 signature [orlp/ed25519]", sig, 64, "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00");
    }
    /* X25519 */
    unhex(k, "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    unhex(n, "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
    crypto_scalarmult_curve25519(out, k, n);
    expect("X25519 RFC 7748 5.2 vector 1 [SUPERCOP ref10]", out, 32, "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552");
    {
        uint8_t a[32], bb[32], apub[32], bpub[32], s1[32], s2[32];
        unhex(a, "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a");
        unhex(bb, "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb");
        crypto_scalarmult_curve25519_base(apub, a); crypto_scalarmult_curve25519_base(bpub, bb);
        expect("X25519 RFC 7748 6.1 Alice public [SUPERCOP ref10]", apub, 32, "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a");
        expect("X25519 RFC 7748 6.1 Bob public [SUPERCOP ref10]", bpub, 32, "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f");
        crypto_scalarmult_curve25519(s1, a, bpub); crypto_scalarmult_curve25519(s2, bb, apub);
        expect("X25519 RFC 7748 6.1 shared (Alice) [SUPERCOP ref10]", s1, 32, "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742");
        expect("X25519 RFC 7748 6.1 shared (Bob) [SUPERCOP ref10]", s2, 32, "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742");
    }
    printf("%d/%d known-answer tests passed\n", total - fails, total);
    return fails != 0;
}
