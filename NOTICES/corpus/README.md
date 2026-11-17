# The ELF corpus (`corpus/`)

`corpus/<pkg>/upstream/` holds unmodified files of upstream releases, and `corpus/elf/<pkg>/` holds the
ELF files built from them by `corpus/<pkg>/build.sh`. Each package keeps its own licence. The licence
texts are in its `upstream/` tree (`package.toml`: `license`, `license_files`), and the corresponding
source of every ELF file is that `upstream/` tree, its `generated/` files and its `local/` files.

| package | licence (SPDX) |
|---|---|
| sqlite | blessing (public domain) |
| coreutils | GPL-3.0-or-later |
| openssl | Apache-2.0 |
| jemalloc | BSD-2-Clause |
| mimalloc | MIT |
| cjson | MIT |
| refcrypto | per algorithm: BSD-2-Clause (RFC 6234, IETF Trust), CC0-1.0 (XKCP, BLAKE2), public domain (Rijndael fst, SUPERCOP, poly1305-donna), Zlib (orlp/ed25519) |
| tcp-pingpong | public domain (Beej's Guide example code); `local/pingpong.patch` is ours |
| darkhttpd | ISC |
| tinycc | LGPL-2.1-or-later |

Files in `local/` are written for this repository and fall under its licence.
