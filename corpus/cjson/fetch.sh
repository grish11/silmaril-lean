#!/usr/bin/env bash
# Download the cJSON v1.7.19 tag archive (commit c859b25da02955fef659d658b8f324b5cde87be3) into $CORPUS_CACHE.
. "$(dirname "$0")/../fetch-lib.sh"
fetch https://github.com/DaveGamble/cJSON/archive/refs/tags/v1.7.19.tar.gz cJSON-1.7.19.tar.gz 7fa616e3046edfa7a28a32d5f9eacfd23f92900fe1f8ccd988c1662f30454562
