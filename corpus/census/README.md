# Static ELF census

Tool-derived evidence for **54 canonical ELFs**, 10 projects, x86-64 and AArch64.
All are the existing single-version, `-O2`, unstripped artifacts; this census does
not deliver the requested additional versions, optimization levels or assembly builds.

Reports preserve the artifact receipt's build image and record the analysis image
separately. The rebuilt analysis image's installed-package list matches
`corpus/toolchain/lock.txt` exactly. Rebuild commands and evidence limits:
[scripts/corpus/README.md](../../scripts/corpus/README.md).

243 executable sections: **10,983,167 decoded bytes**, **0 undecoded bytes reported**,
**4,080 unreported bytes** (for example, objdump's skipped zero runs). No syscall
instruction sites were reported by this linear decode; this does not establish
absence of syscalls or dependencies. Extension matches are a bounded exact-mnemonic
classifier, not a complete ISA census. No dynamic execution was measured.

Measured full-census run: 12.252 s wall, 11.060 s user CPU, 1.430 s system CPU,
152,152 KiB peak RSS, one sequential worker. The measurement ran inside the pinned
container with an 8 CPU / 32 GiB limit. This is a single run with unspecified cache
state, not a performance comparison. Acquisition, builds, Lean checks and database
regeneration are excluded. The run receipt is retained with the generated evidence.

| project | version | target | artifact/report | decoded bytes | unreported bytes | extension matches |
|---|---|---|---|---:|---:|---|
| cjson | 1.7.19 | aarch64 | [libcjson.so.1](cjson/aarch64/libcjson.so.1.json) | 15940 | 0 | none matched |
| cjson | 1.7.19 | aarch64 | [libcjson_utils.so.1](cjson/aarch64/libcjson_utils.so.1.json) | 8012 | 0 | none matched |
| cjson | 1.7.19 | x86_64 | [libcjson.so.1](cjson/x86_64/libcjson.so.1.json) | 14819 | 0 | none matched |
| cjson | 1.7.19 | x86_64 | [libcjson_utils.so.1](cjson/x86_64/libcjson_utils.so.1.json) | 8114 | 0 | none matched |
| coreutils | 9.12 | aarch64 | [cat](coreutils/aarch64/cat.json) | 42808 | 0 | none matched |
| coreutils | 9.12 | aarch64 | [echo](coreutils/aarch64/echo.json) | 34088 | 0 | none matched |
| coreutils | 9.12 | aarch64 | [head](coreutils/aarch64/head.json) | 45688 | 0 | none matched |
| coreutils | 9.12 | aarch64 | [sha256sum](coreutils/aarch64/sha256sum.json) | 52776 | 0 | none matched |
| coreutils | 9.12 | aarch64 | [sort](coreutils/aarch64/sort.json) | 96904 | 0 | none matched |
| coreutils | 9.12 | aarch64 | [true](coreutils/aarch64/true.json) | 32856 | 0 | none matched |
| coreutils | 9.12 | aarch64 | [wc](coreutils/aarch64/wc.json) | 52488 | 0 | none matched |
| coreutils | 9.12 | x86_64 | [cat](coreutils/x86_64/cat.json) | 23814 | 0 | none matched |
| coreutils | 9.12 | x86_64 | [echo](coreutils/x86_64/echo.json) | 19334 | 0 | none matched |
| coreutils | 9.12 | x86_64 | [head](coreutils/x86_64/head.json) | 25462 | 0 | none matched |
| coreutils | 9.12 | x86_64 | [sha256sum](coreutils/x86_64/sha256sum.json) | 37174 | 0 | none matched |
| coreutils | 9.12 | x86_64 | [sort](coreutils/x86_64/sort.json) | 79846 | 0 | none matched |
| coreutils | 9.12 | x86_64 | [true](coreutils/x86_64/true.json) | 18038 | 0 | none matched |
| coreutils | 9.12 | x86_64 | [wc](coreutils/x86_64/wc.json) | 38406 | 0 | none matched |
| darkhttpd | 1.17 | aarch64 | [darkhttpd](darkhttpd/aarch64/darkhttpd.json) | 21576 | 0 | none matched |
| darkhttpd | 1.17 | x86_64 | [darkhttpd](darkhttpd/x86_64/darkhttpd.json) | 23532 | 0 | none matched |
| jemalloc | 5.3.0 | aarch64 | [libjemalloc.so.2](jemalloc/aarch64/libjemalloc.so.2.json) | 390884 | 0 | none matched |
| jemalloc | 5.3.0 | x86_64 | [libjemalloc.so.2](jemalloc/x86_64/libjemalloc.so.2.json) | 534404 | 0 | none matched |
| mimalloc | 2.1.9 | aarch64 | [libmimalloc.so.2.1](mimalloc/aarch64/libmimalloc.so.2.1.json) | 68728 | 0 | none matched |
| mimalloc | 2.1.9 | x86_64 | [libmimalloc.so.2.1](mimalloc/x86_64/libmimalloc.so.2.1.json) | 70985 | 0 | none matched |
| openssl | 3.5.9 | aarch64 | [libcrypto.so.3](openssl/aarch64/libcrypto.so.3.json) | 2177592 | 0 | none matched |
| openssl | 3.5.9 | aarch64 | [libssl.so.3](openssl/aarch64/libssl.so.3.json) | 590080 | 0 | none matched |
| openssl | 3.5.9 | aarch64 | [openssl](openssl/aarch64/openssl.json) | 442868 | 4080 | none matched |
| openssl | 3.5.9 | x86_64 | [libcrypto.so.3](openssl/x86_64/libcrypto.so.3.json) | 2260246 | 0 | none matched |
| openssl | 3.5.9 | x86_64 | [libssl.so.3](openssl/x86_64/libssl.so.3.json) | 630726 | 0 | none matched |
| openssl | 3.5.9 | x86_64 | [openssl](openssl/x86_64/openssl.json) | 483151 | 0 | none matched |
| refcrypto | 2026-11-17 | aarch64 | [libref_aes.so](refcrypto/aarch64/libref_aes.so.json) | 3608 | 0 | none matched |
| refcrypto | 2026-11-17 | aarch64 | [libref_blake2.so](refcrypto/aarch64/libref_blake2.so.json) | 14196 | 0 | none matched |
| refcrypto | 2026-11-17 | aarch64 | [libref_chacha_poly.so](refcrypto/aarch64/libref_chacha_poly.so.json) | 4264 | 0 | none matched |
| refcrypto | 2026-11-17 | aarch64 | [libref_ed25519.so](refcrypto/aarch64/libref_ed25519.so.json) | 21504 | 0 | none matched |
| refcrypto | 2026-11-17 | aarch64 | [libref_sha2.so](refcrypto/aarch64/libref_sha2.so.json) | 9800 | 0 | none matched |
| refcrypto | 2026-11-17 | aarch64 | [libref_sha3.so](refcrypto/aarch64/libref_sha3.so.json) | 2080 | 0 | none matched |
| refcrypto | 2026-11-17 | aarch64 | [libref_x25519.so](refcrypto/aarch64/libref_x25519.so.json) | 5140 | 0 | none matched |
| refcrypto | 2026-11-17 | x86_64 | [libref_aes.so](refcrypto/x86_64/libref_aes.so.json) | 3387 | 0 | none matched |
| refcrypto | 2026-11-17 | x86_64 | [libref_blake2.so](refcrypto/x86_64/libref_blake2.so.json) | 13903 | 0 | none matched |
| refcrypto | 2026-11-17 | x86_64 | [libref_chacha_poly.so](refcrypto/x86_64/libref_chacha_poly.so.json) | 5339 | 0 | none matched |
| refcrypto | 2026-11-17 | x86_64 | [libref_ed25519.so](refcrypto/x86_64/libref_ed25519.so.json) | 29828 | 0 | none matched |
| refcrypto | 2026-11-17 | x86_64 | [libref_sha2.so](refcrypto/x86_64/libref_sha2.so.json) | 12204 | 0 | none matched |
| refcrypto | 2026-11-17 | x86_64 | [libref_sha3.so](refcrypto/x86_64/libref_sha3.so.json) | 2320 | 0 | none matched |
| refcrypto | 2026-11-17 | x86_64 | [libref_x25519.so](refcrypto/x86_64/libref_x25519.so.json) | 7424 | 0 | none matched |
| sqlite | 3.54.1 | aarch64 | [libsqlite3.so](sqlite/aarch64/libsqlite3.so.json) | 814796 | 0 | none matched |
| sqlite | 3.54.1 | aarch64 | [sqlite3](sqlite/aarch64/sqlite3.json) | 220248 | 0 | none matched |
| sqlite | 3.54.1 | x86_64 | [libsqlite3.so](sqlite/x86_64/libsqlite3.so.json) | 867507 | 0 | none matched |
| sqlite | 3.54.1 | x86_64 | [sqlite3](sqlite/x86_64/sqlite3.json) | 238254 | 0 | none matched |
| tcp-pingpong | bgnet-34fb9d78 | aarch64 | [pingpong-client](tcp-pingpong/aarch64/pingpong-client.json) | 1560 | 0 | none matched |
| tcp-pingpong | bgnet-34fb9d78 | aarch64 | [pingpong-server](tcp-pingpong/aarch64/pingpong-server.json) | 1904 | 0 | none matched |
| tcp-pingpong | bgnet-34fb9d78 | x86_64 | [pingpong-client](tcp-pingpong/x86_64/pingpong-client.json) | 1389 | 0 | none matched |
| tcp-pingpong | bgnet-34fb9d78 | x86_64 | [pingpong-server](tcp-pingpong/x86_64/pingpong-server.json) | 1773 | 0 | none matched |
| tinycc | 0.9.27 | aarch64 | [tcc](tinycc/aarch64/tcc.json) | 174104 | 0 | none matched |
| tinycc | 0.9.27 | x86_64 | [tcc](tinycc/x86_64/tcc.json) | 185296 | 0 | none matched |
