#!/usr/bin/env bash
# Repository-authored acquisition of one immutable upstream revision.
. "$(dirname "$0")/../fetch-lib.sh"
fetch https://codeload.github.com/google/boringssl/tar.gz/ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6 boringssl-ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6.tar.gz 75ee588268ae3d7552f5be7e0849bdcc8e4159f22547dbfb4aae997784fdd345
