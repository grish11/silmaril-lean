#!/usr/bin/env bash
# Download every refcrypto input into $CORPUS_CACHE and check sha256s (see package.toml for provenance).
. "$(dirname "$0")/../fetch-lib.sh"
fetch https://www.rfc-editor.org/rfc/rfc6234.txt rfc6234.txt 8f39f02a57bfd1da15634706724a585766e6223f77ecdaf243cad16cd3a1aa1b
fetch https://github.com/XKCP/XKCP/archive/d20c8fcaecc543f816a0721d0dfc13b4cf27c14d.tar.gz XKCP-d20c8fcaecc543f816a0721d0dfc13b4cf27c14d.tar.gz 5a277d4dd8d83f7a3b411c7d22ede4c584a9c95ae5b81724f8f1db6197ea8776
fetch https://github.com/BLAKE2/BLAKE2/archive/ed1974ea83433eba7b2d95c5dcd9ac33cb847913.tar.gz BLAKE2-ed1974ea83433eba7b2d95c5dcd9ac33cb847913.tar.gz e1d1194cde9fec0f150961cca8f3d9bdf7c5a5cbe020d1cdfb962b4887793124
fetch 'https://web.archive.org/web/20051217122133id_/http://www.esat.kuleuven.ac.be/~rijmen/rijndael/rijndael-fst-3.0.zip' rijndael-fst-3.0.zip a6ed142ac0bffcd10d0fdc82f9fe7e768fc4aac91aa2797ea9974252e09e998f
fetch https://bench.cr.yp.to/supercop/supercop-20261018.tar.xz supercop-20261018.tar.xz 9a44c3e619632d140cbad436f5cebbea5f2b8d6efe752946c3e367c4c2ac8288
fetch https://github.com/floodyberry/poly1305-donna/archive/e6ad6e091d30d7f4ec2d4f978be1fcfcbce72781.tar.gz poly1305-donna-e6ad6e091d30d7f4ec2d4f978be1fcfcbce72781.tar.gz 78442221554769d557d2eb73583b409d88d83226d498c4e7caa1cc97b0488e4b
fetch https://github.com/orlp/ed25519/archive/b1f19fab4aebe607805620d25a5e42566ce46a0e.tar.gz ed25519-b1f19fab4aebe607805620d25a5e42566ce46a0e.tar.gz aedb26c46d3dc3b721ab37c5248d5c923142e4d56009a9605c470383f32ce77a
