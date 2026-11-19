#!/usr/bin/env bash
# Download the darkhttpd v1.17 tag archive (commit 3075d35e1d2deb65ed8b079137c4ae1213de4b48) into $CORPUS_CACHE.
. "$(dirname "$0")/../fetch-lib.sh"
fetch https://github.com/emikulic/darkhttpd/archive/refs/tags/v1.17.tar.gz darkhttpd-1.17.tar.gz 4fee9927e2d8bb0a302f0dd62f9ff1e075748fa9f5162c9481a7a58b41462b56
