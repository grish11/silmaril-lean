#!/usr/bin/env bash
# Download the mimalloc v2.1.9 tag archive into $CORPUS_CACHE (same pin as sources/alloc).
. "$(dirname "$0")/../fetch-lib.sh"
fetch https://github.com/microsoft/mimalloc/archive/refs/tags/v2.1.9.tar.gz mimalloc-2.1.9.tar.gz dd8ff701691f19bf4e225d42ef0d3d5e6ca0e03498ee4f044a0402e4697e4a20
