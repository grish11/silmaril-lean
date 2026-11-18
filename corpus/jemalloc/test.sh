#!/usr/bin/env bash
# test.sh ARCH OBJDIR -- link local/je_smoke.c against the built libjemalloc.so.2 and run it
# (natively or under qemu-user).
. "$(dirname "$0")/../common.sh"
start_test jemalloc "$1" "$2"
t=$(mktemp -d); cp "$OBJ/libjemalloc.so.2" "$t/"; ln -s libjemalloc.so.2 "$t/libjemalloc.so"
$CC -O2 "$CORPUS/jemalloc/local/je_smoke.c" -o "$t/je_smoke" -L"$t" -ljemalloc
r() { if [ "$ARCH" = aarch64 ]; then "${RUN[@]}" -E LD_LIBRARY_PATH="$t" "$@"; else LD_LIBRARY_PATH="$t" "$@"; fi; }
rc=0; out=$(r "$t/je_smoke" 2>&1) || rc=$?
check "${RUNS}je_smoke (local/je_smoke.c linked against libjemalloc.so.2): exit status" 0 "$rc"
record "${RUNS}je_smoke output" "$(printf %s "$out" | tr '\n' ' ')"
if [ "$ARCH" = x86_64 ]; then
  rc=0; out=$(LD_PRELOAD="$t/libjemalloc.so.2" MALLOC_CONF=stats_print:true /usr/bin/perl -e 1 2>&1) || rc=$?
  check "LD_PRELOAD=libjemalloc.so.2 MALLOC_CONF=stats_print:true perl -e 1 (first stats line; coreutils programs close stderr before jemalloc's atexit)" \
    "___ Begin jemalloc statistics ___" "$(printf %s "$out" | grep -m1 'Begin jemalloc statistics')"
fi
rm -rf "$t"
exit $TEST_FAILED
