/* local/supercop-shim/x25519/crypto_scalarmult.h -- repository-authored (ours, not upstream).
 * Why: SUPERCOP generates this header at benchmark time; it is not in the tarball. It supplies what
 * crypto_scalarmult/curve25519/ref10/{scalarmult,base}.c expect: the public names of the primitive
 * (crypto_scalarmult_curve25519 / crypto_scalarmult_curve25519_base) and the sizes from api.h. The
 * internal fe_* names get SUPERCOP's prefix from -DCRYPTO_NAMESPACE(name)=crypto_scalarmult_curve25519_ref10_##name
 * on the compiler command line, as SUPERCOP itself does. */
#ifndef crypto_scalarmult_H
#define crypto_scalarmult_H
#define crypto_scalarmult crypto_scalarmult_curve25519
#define crypto_scalarmult_base crypto_scalarmult_curve25519_base
#define crypto_scalarmult_BYTES 32
#define crypto_scalarmult_SCALARBYTES 32
int crypto_scalarmult(unsigned char *q, const unsigned char *n, const unsigned char *p);
int crypto_scalarmult_base(unsigned char *q, const unsigned char *n);
#endif
