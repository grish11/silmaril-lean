#!/usr/bin/env bash
# The pinned ELF files of the ELF reader examples (examples/elf/README.md).
#   examples/elf/pin.sh --check   the committed files have the pinned sha256
#   examples/elf/pin.sh --fetch   download the package, verify it, extract the file
set -euo pipefail
cd "$(dirname "$0")"
DEB_URL=https://launchpad.net/ubuntu/+archive/primary/+files/coreutils_9.4-3ubuntu6.3_amd64.deb
DEB_URL_MIRROR=http://archive.ubuntu.com/ubuntu/pool/main/c/coreutils/coreutils_9.4-3ubuntu6.3_amd64.deb
DEB_SHA=e1e9a17892be0cc83b7cea747edf331ffeb6d6c010b4db296e60d888e8e9274c
SHA256SUM_SHA=4d2db56c867e5324e0084c9e897f6360d37517de77ac96f2bd31494223d69a60
check() { echo "$2  $1" | sha256sum --check --quiet; }
case "${1:-}" in
  --check)
    check pinned/gnu-sha256sum "$SHA256SUM_SHA"
    for h in hello-gcc hello-clang; do check "../dyn/pinned/$h" "$(awk -v h="$h" '$1 == h {print $2}' ../dyn/pins.txt)"; done
    echo "pin.sh: ok" ;;
  --fetch)
    tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
    curl -fsSL -o "$tmp/coreutils.deb" "$DEB_URL" || curl -fsSL -o "$tmp/coreutils.deb" "$DEB_URL_MIRROR"
    check "$tmp/coreutils.deb" "$DEB_SHA"
    mkdir "$tmp/x"
    if command -v dpkg-deb >/dev/null; then dpkg-deb --fsys-tarfile "$tmp/coreutils.deb" > "$tmp/data.tar"
    else (cd "$tmp" && ar x coreutils.deb data.tar.zst && zstd -q -d data.tar.zst -o data.tar); fi
    tar -xf "$tmp/data.tar" -C "$tmp/x" ./usr/bin/sha256sum
    check "$tmp/x/usr/bin/sha256sum" "$SHA256SUM_SHA"
    install -m 0644 "$tmp/x/usr/bin/sha256sum" pinned/gnu-sha256sum
    echo "pin.sh: wrote pinned/gnu-sha256sum" ;;
  *) echo "usage: $0 --check | --fetch" >&2; exit 2 ;;
esac
