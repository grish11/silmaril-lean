#!/usr/bin/env bash
# Download the bgnet repository archive at commit 34fb9d78 (Beej's Guide sources incl. examples) into $CORPUS_CACHE.
. "$(dirname "$0")/../fetch-lib.sh"
fetch https://github.com/beejjorgensen/bgnet/archive/34fb9d781a3643bc1e2a36ba6e77e0d347ffe2c9.tar.gz bgnet-34fb9d781a3643bc1e2a36ba6e77e0d347ffe2c9.tar.gz 13df988f5f202b550c078a81d9b94c294ef7946d684a6013aaae8f638c5982ce
