#!/usr/bin/env bash
# test.sh ARCH OBJDIR -- link upstream's example program test.c and our local/utils_smoke.c against the
# built libcjson.so.1 / libcjson_utils.so.1 and run them (natively or under qemu-user).
. "$(dirname "$0")/../common.sh"
start_test cjson "$1" "$2"
t=$(mktemp -d); A=$CORPUS_CACHE/cJSON-1.7.19.tar.gz
tar -C "$t" -xzf "$A" cJSON-1.7.19/test.c cJSON-1.7.19/cJSON.h cJSON-1.7.19/cJSON_Utils.h
cp "$OBJ"/libcjson.so.1 "$OBJ"/libcjson_utils.so.1 "$t/"; ln -s libcjson.so.1 "$t/libcjson.so"; ln -s libcjson_utils.so.1 "$t/libcjson_utils.so"
S=$t/cJSON-1.7.19
$CC -O2 -I"$S" "$S/test.c" -o "$t/cjson_test" -L"$t" -lcjson
$CC -O2 -I"$S" "$CORPUS/cjson/local/utils_smoke.c" -o "$t/utils_smoke" -L"$t" -lcjson_utils -lcjson
r() { if [ "$ARCH" = aarch64 ]; then "${RUN[@]}" -E LD_LIBRARY_PATH="$t" "$@"; else LD_LIBRARY_PATH="$t" "$@"; fi; }
rc=0; out=$(r "$t/cjson_test" 2>&1) || rc=$?
check "${RUNS}cjson_test (upstream test.c linked against libcjson.so.1): exit status" 0 "$rc"
record "${RUNS}cjson_test output: $(printf %s "$out" | wc -l) lines, sha256 $(printf %s "$out" | sha256sum | cut -c1-64)" "$(printf %s "$out" | head -n 8 | tr '\n' ' ')"
rc=0; out=$(r "$t/utils_smoke" 2>&1) || rc=$?
check "${RUNS}utils_smoke (local/utils_smoke.c against libcjson_utils.so.1 + libcjson.so.1)" "0 4 ok" "$rc $(grep -c '^ok' <<<"$out") ok"
record "${RUNS}utils_smoke output" "$(printf %s "$out" | tr '\n' ' ')"
rm -rf "$t"
exit $TEST_FAILED
