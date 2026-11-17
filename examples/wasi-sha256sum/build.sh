#!/usr/bin/env bash
# Build dist/sha256sum.wasm (Rust 1.99.1, target wasm32-unknown-unknown, no dependencies) and
# check it against dist/SHA256SUMS.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
target=${CARGO_TARGET_DIR:-$(mktemp -d)}
CARGO_TARGET_DIR=$target cargo build --manifest-path "$here/Cargo.toml" --release \
  --target wasm32-unknown-unknown
mkdir -p "$here/dist"
cp "$target/wasm32-unknown-unknown/release/wasi_sha256sum.wasm" "$here/dist/sha256sum.wasm"
cd "$here/dist" && sha256sum -c SHA256SUMS
