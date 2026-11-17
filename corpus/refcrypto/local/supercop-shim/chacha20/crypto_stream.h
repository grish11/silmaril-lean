/* local/supercop-shim/chacha20/crypto_stream.h -- repository-authored (ours, not upstream).
 * Why: SUPERCOP generates this header at benchmark time (its "do" script); it is not in the tarball.
 * It supplies what upstream/supercop-20261018/include/estream-convert-api.h expects when compiling
 * crypto_stream/chacha20/e/ref/api.c (built with -DCRYPTO_NAMESPACE(name)=crypto_stream_chacha20_e_ref_##name
 * on the command line, as SUPERCOP does, for the internal ECRYPT_* names): the public names of the primitive
 * (crypto_stream_chacha20 / crypto_stream_chacha20_xor) and the key/nonce sizes from api.h. */
#ifndef crypto_stream_H
#define crypto_stream_H
#define crypto_stream crypto_stream_chacha20
#define crypto_stream_xor crypto_stream_chacha20_xor
#define crypto_stream_KEYBYTES 32
#define crypto_stream_NONCEBYTES 8
int crypto_stream(unsigned char *c, unsigned long long clen, const unsigned char *n, const unsigned char *k);
int crypto_stream_xor(unsigned char *c, const unsigned char *m, unsigned long long mlen, const unsigned char *n, const unsigned char *k);
#endif
