#!/usr/bin/env bash
# Download the jemalloc 5.3.0 release tarball into $CORPUS_CACHE (same pin as sources/alloc).
. "$(dirname "$0")/../fetch-lib.sh"
fetch https://github.com/jemalloc/jemalloc/releases/download/5.3.0/jemalloc-5.3.0.tar.bz2 jemalloc-5.3.0.tar.bz2 2db82d1e7119df3e71b7640219b6dfe84789bc0537983c3b7ac4f7189aecfeaa
