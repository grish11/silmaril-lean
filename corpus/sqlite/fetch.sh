#!/usr/bin/env bash
# Download the SQLite 3.54.1 amalgamation into $CORPUS_CACHE and check its sha256.
. "$(dirname "$0")/../fetch-lib.sh"
. "$(dirname "$0")/release.sh"
fetch "$URL" "$ROOT.zip" "$SHA256"
