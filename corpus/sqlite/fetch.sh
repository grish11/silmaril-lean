#!/usr/bin/env bash
# Download the SQLite 3.54.1 amalgamation into $CORPUS_CACHE and check its sha256.
. "$(dirname "$0")/../fetch-lib.sh"
fetch https://sqlite.org/2026/sqlite-amalgamation-3540100.zip sqlite-amalgamation-3540100.zip 0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9
