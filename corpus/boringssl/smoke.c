/* Repository-authored observations of this build's libcrypto/libssl. No proof
 * or FIPS-validation claim. Known answers, signature verification and an actual
 * TLS 1.3 handshake/application transfer over an in-memory BIO pair. */
#include <openssl/aes.h>
#include <openssl/bio.h>
#include <openssl/ec.h>
#include <openssl/crypto.h>
#include <openssl/evp.h>
#include <openssl/nid.h>
#include <openssl/sha.h>
#include <openssl/ssl.h>
#include <openssl/x509.h>
#include <stdio.h>
#include <string.h>

#define REQUIRE(x) do { if (!(x)) { fprintf(stderr, "failed at line %d: %s\n", __LINE__, #x); return 1; } } while (0)

static int advance(SSL *ssl) {
    int result = SSL_do_handshake(ssl);
    if (result == 1) return 1;
    int error = SSL_get_error(ssl, result);
    return error == SSL_ERROR_WANT_READ || error == SSL_ERROR_WANT_WRITE;
}

int main(void) {
    const unsigned char digest_expected[32] = {
        0xba,0x78,0x16,0xbf,0x8f,0x01,0xcf,0xea,0x41,0x41,0x40,0xde,0x5d,0xae,0x22,0x23,
        0xb0,0x03,0x61,0xa3,0x96,0x17,0x7a,0x9c,0xb4,0x10,0xff,0x61,0xf2,0x00,0x15,0xad};
    unsigned char digest[32];
    REQUIRE(SHA256((const unsigned char *)"abc", 3, digest));
    REQUIRE(memcmp(digest, digest_expected, 32) == 0);
    puts("SHA256 known answer passed");

    unsigned char key[16], plain[16], encrypted[16];
    const unsigned char aes_expected[16] = {0x69,0xc4,0xe0,0xd8,0x6a,0x7b,0x04,0x30,0xd8,0xcd,0xb7,0x80,0x70,0xb4,0xc5,0x5a};
    for (int i = 0; i < 16; ++i) { key[i] = i; plain[i] = i * 0x11; }
    AES_KEY aes;
    REQUIRE(AES_set_encrypt_key(key, 128, &aes) == 0);
    AES_encrypt(plain, encrypted, &aes);
    REQUIRE(memcmp(encrypted, aes_expected, 16) == 0);
    puts("AES128 known answer passed");

    unsigned char seed[32] = {1}, signature[64];
    size_t signature_size = sizeof(signature);
    EVP_PKEY *ed = EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519, NULL, seed, sizeof(seed));
    EVP_MD_CTX *sign = EVP_MD_CTX_new(), *verify = EVP_MD_CTX_new();
    REQUIRE(ed && sign && verify);
    REQUIRE(EVP_DigestSignInit(sign, NULL, NULL, NULL, ed));
    REQUIRE(EVP_DigestSign(sign, signature, &signature_size, (const unsigned char *)"abc", 3));
    REQUIRE(EVP_DigestVerifyInit(verify, NULL, NULL, NULL, ed));
    REQUIRE(EVP_DigestVerify(verify, signature, signature_size, (const unsigned char *)"abc", 3) == 1);
    signature[0] ^= 1;
    REQUIRE(EVP_DigestVerify(verify, signature, signature_size, (const unsigned char *)"abc", 3) == 0);
    EVP_MD_CTX_free(sign); EVP_MD_CTX_free(verify); EVP_PKEY_free(ed);
    puts("Ed25519 sign verify and rejection passed");

    EC_KEY *ec = EC_KEY_new_by_curve_name(NID_X9_62_prime256v1);
    EVP_PKEY *pkey = EVP_PKEY_new();
    X509 *cert = X509_new();
    REQUIRE(ec && pkey && cert && EC_KEY_generate_key(ec));
    REQUIRE(EVP_PKEY_assign_EC_KEY(pkey, ec));
    REQUIRE(X509_set_version(cert, 2));
    REQUIRE(ASN1_INTEGER_set(X509_get_serialNumber(cert), 1));
    REQUIRE(X509_gmtime_adj(X509_get_notBefore(cert), -60));
    REQUIRE(X509_gmtime_adj(X509_get_notAfter(cert), 3600));
    REQUIRE(X509_set_pubkey(cert, pkey));
    X509_NAME *subject = X509_get_subject_name(cert);
    REQUIRE(X509_NAME_add_entry_by_txt(subject, "CN", MBSTRING_ASC, (const unsigned char *)"localhost", -1, -1, 0));
    REQUIRE(X509_set_issuer_name(cert, subject));
    REQUIRE(X509_sign(cert, pkey, EVP_sha256()) > 0 && X509_verify(cert, pkey) == 1);
    SSL_CTX *client_ctx = SSL_CTX_new(TLS_client_method()), *server_ctx = SSL_CTX_new(TLS_server_method());
    REQUIRE(client_ctx && server_ctx);
    REQUIRE(SSL_CTX_set_min_proto_version(client_ctx, TLS1_3_VERSION));
    REQUIRE(SSL_CTX_set_max_proto_version(client_ctx, TLS1_3_VERSION));
    REQUIRE(SSL_CTX_use_certificate(server_ctx, cert) && SSL_CTX_use_PrivateKey(server_ctx, pkey));
    SSL *client = SSL_new(client_ctx), *server = SSL_new(server_ctx);
    BIO *client_bio, *server_bio;
    REQUIRE(client && server && BIO_new_bio_pair(&client_bio, 0, &server_bio, 0));
    SSL_set_bio(client, client_bio, client_bio); SSL_set_bio(server, server_bio, server_bio);
    SSL_set_connect_state(client); SSL_set_accept_state(server);
    for (int i = 0; i < 10000 && (!SSL_is_init_finished(client) || !SSL_is_init_finished(server)); ++i) {
        REQUIRE(advance(client)); REQUIRE(advance(server));
    }
    REQUIRE(SSL_is_init_finished(client) && SSL_is_init_finished(server));
    REQUIRE(SSL_version(client) == TLS1_3_VERSION && SSL_version(server) == TLS1_3_VERSION);
    char message[4];
    REQUIRE(SSL_write(client, "ping", 4) == 4 && SSL_read(server, message, 4) == 4);
    REQUIRE(memcmp(message, "ping", 4) == 0);
    SSL_free(client); SSL_free(server); SSL_CTX_free(client_ctx); SSL_CTX_free(server_ctx);
    X509_free(cert); EVP_PKEY_free(pkey);
    puts("TLS1.3 certificate signature handshake and application transfer passed");
    printf("FIPS research configuration flag: %d\n", FIPS_mode());
    return 0;
}
