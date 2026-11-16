#!/bin/sh
# Rebuild toy.elf byte for byte in a pinned container and compare it with the committed file.
# Receipt (2026-11-16): Debian 13.7 (debian:trixie at the digest below), clang-19 1:19.1.7-3+b1,
# binutils 2.44-3 -> toy.elf sha256 518e07bb1a311210f28af5fc5cf9f263bbc2670b23852a712237c3c3c32d1010.
# The apt packages are pinned by version; if the Debian archive drops them, the build fails
# rather than producing a different file.
set -e
cd "$(dirname "$0")"
image=debian@sha256:9c6e381421d0f48d1b8133e573f33c185ee16cbf505eda9c4a8a4791b25ea8a6
docker run --rm --network host -v "$PWD:/w:ro" -v "${TMPDIR:-/tmp}:/out" -w /w "$image" sh -c '
  apt-get update -qq >/dev/null &&
  apt-get install -y -qq --no-install-recommends clang-19=1:19.1.7-3+b1 binutils=2.44-3 >/dev/null &&
  clang-19 --target=x86_64-linux-gnu -c toy.S -o /tmp/toy.o &&
  ld -static -e f -Ttext=0x401000 /tmp/toy.o -o /out/toy-pinned.elf'
want=518e07bb1a311210f28af5fc5cf9f263bbc2670b23852a712237c3c3c32d1010
got=$(sha256sum "${TMPDIR:-/tmp}/toy-pinned.elf" | cut -d' ' -f1)
cmp "${TMPDIR:-/tmp}/toy-pinned.elf" toy.elf
echo "toy.elf reproduced byte for byte (sha256 $got)"
[ "$got" = "$want" ]
