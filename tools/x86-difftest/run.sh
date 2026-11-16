#!/bin/sh
# Differential tests of the Str9G x86-64 model against this processor (untrusted tooling).
#   tools/x86-difftest/run.sh insn [--per N] [--seed S]   single instructions vs the host CPU
#   tools/x86-difftest/run.sh strlen DIR                   __strlen_sse2 of a pinned glibc on Str9G.step
# DIR holds ubuntu_2_39_0ubuntu8_9/libc.so.6 (Ubuntu 24.04 libc6 2.39-0ubuntu8.9 amd64, the pin of
# docs/projects/ptmalloc.md). Run from the repository root.
set -e
case "$1" in
  insn)
    shift
    python3 -I tools/x86-difftest/difftest.py "$@"
    lake env lean tools/x86-difftest/Check.lean ;;
  strlen)
    f="$2/ubuntu_2_39_0ubuntu8_9/libc.so.6"
    echo "3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf  $f" | sha256sum -c -
    GLIBC_PINS="$2" lake env lean tools/x86-difftest/StrlenRun.lean ;;
  *) sed -n '2,6p' "$0"; exit 2 ;;
esac
