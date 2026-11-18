#!/usr/bin/env bash
# test.sh ARCH OBJDIR -- link local/mi_smoke.c against the built libmimalloc.so.2.1 and run it
# (natively or under qemu-user); on x86_64 also LD_PRELOAD it into /bin/ls with MIMALLOC_VERBOSE=1.
. "$(dirname "$0")/../common.sh"
start_test mimalloc "$1" "$2"
t=$(mktemp -d); cp "$OBJ/libmimalloc.so.2.1" "$t/"; ln -s libmimalloc.so.2.1 "$t/libmimalloc.so.2"; ln -s libmimalloc.so.2 "$t/libmimalloc.so"
$CC -O2 "$CORPUS/mimalloc/local/mi_smoke.c" -o "$t/mi_smoke" -L"$t" -lmimalloc
r() { if [ "$ARCH" = aarch64 ]; then "${RUN[@]}" -E LD_LIBRARY_PATH="$t" "$@"; else LD_LIBRARY_PATH="$t" "$@"; fi; }
rc=0; out=$(r "$t/mi_smoke" 2>&1) || rc=$?
check "${RUNS}mi_smoke (local/mi_smoke.c linked against libmimalloc.so.2.1): exit status" 0 "$rc"
record "${RUNS}mi_smoke output" "$(printf %s "$out" | tr '\n' ' ')"
if [ "$ARCH" = x86_64 ]; then
  rc=0; out=$(LD_PRELOAD="$t/libmimalloc.so.2.1" MIMALLOC_VERBOSE=1 /bin/ls / 2>&1) || rc=$?
  check "LD_PRELOAD=libmimalloc.so.2.1 MIMALLOC_VERBOSE=1 /bin/ls / (mimalloc banner seen)" "mimalloc: process init" \
    "$(printf %s "$out" | grep -o -m1 'mimalloc: process init')"
fi
rm -rf "$t"
exit $TEST_FAILED
