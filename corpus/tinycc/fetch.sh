#!/usr/bin/env bash
# Download the TinyCC 0.9.27 release tarball (the latest release; savannah) into $CORPUS_CACHE.
. "$(dirname "$0")/../fetch-lib.sh"
fetch https://download.savannah.gnu.org/releases/tinycc/tcc-0.9.27.tar.bz2 tcc-0.9.27.tar.bz2 de23af78fca90ce32dff2dd45b3432b2334740bb9bb7b05bf60fdbfc396ceb9c
