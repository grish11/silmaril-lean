#!/usr/bin/env bash
# Download GNU coreutils 9.12 and its detached signature into $CORPUS_CACHE and check sha256s. If gpgv
# and a GNU keyring (https://ftp.gnu.org/gnu/gnu-keyring.gpg) are available, also verify the signature.
. "$(dirname "$0")/../fetch-lib.sh"
fetch https://ftp.gnu.org/gnu/coreutils/coreutils-9.12.tar.xz coreutils-9.12.tar.xz a480198559733e9b3da999e90543ac6f888a2caa544d8d664c5a1f17e528e210
fetch https://ftp.gnu.org/gnu/coreutils/coreutils-9.12.tar.xz.sig coreutils-9.12.tar.xz.sig e28e1ee5d29f88bd88bedf64bbbf033106eb28eb2efc9ffc4a0c3c92a80ac353
fetch https://ftp.gnu.org/gnu/gnu-keyring.gpg gnu-keyring.gpg 8013de59880f7a59f53b6bd207f4d2a408d67b84a82fa9cba1dbbf443428e2db || true
if command -v gpgv >/dev/null && [ -f "$CORPUS_CACHE/gnu-keyring.gpg" ]; then
  gpgv --keyring "$CORPUS_CACHE/gnu-keyring.gpg" "$CORPUS_CACHE/coreutils-9.12.tar.xz.sig" "$CORPUS_CACHE/coreutils-9.12.tar.xz"
fi
