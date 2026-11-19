#!/usr/bin/env bash
# Download the OpenSSL 3.5.9 release tarball (GitHub release asset) into $CORPUS_CACHE and check its
# sha256 (equal to the published openssl-3.5.9.tar.gz.sha256).
. "$(dirname "$0")/../fetch-lib.sh"
fetch https://github.com/openssl/openssl/releases/download/openssl-3.5.9/openssl-3.5.9.tar.gz openssl-3.5.9.tar.gz 603f5602e2eef00d77fbd429d34dcd5822bb301757a1bc9cdb24c670f1eb859a
