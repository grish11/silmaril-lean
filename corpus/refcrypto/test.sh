#!/usr/bin/env bash
# test.sh ARCH OBJDIR -- link local/kat.c (ours) against the seven libref_*.so and run it; also build
# RFC 6234's own test driver shatest.c (cut out of the RFC by local/extract-rfc6234.py) against
# libref_sha2.so and run its SHA, HMAC (-m) and HKDF (-d) suites. Natively or under qemu-user.
. "$(dirname "$0")/../common.sh"
start_test refcrypto "$1" "$2"
t=$(mktemp -d); cp "$OBJ"/libref_*.so "$t/"
python3 -I "$CORPUS/refcrypto/local/extract-rfc6234.py" "$CORPUS_CACHE/rfc6234.txt" "$t/rfc" >/dev/null
$CC -O2 "$CORPUS/refcrypto/local/kat.c" -o "$t/kat" "$t"/libref_*.so
$CC -O2 -I"$t/rfc" "$t/rfc/shatest.c" -o "$t/shatest" "$t/libref_sha2.so"
r() { if [ "$ARCH" = aarch64 ]; then "${RUN[@]}" -E LD_LIBRARY_PATH="$t" "$@"; else LD_LIBRARY_PATH="$t" "$@"; fi; }
rc=0; out=$(r "$t/kat" 2>&1) || rc=$?
check "${RUNS}kat (local/kat.c against libref_*.so): exit status and summary" "0 $(grep -c '^PASS\|^FAIL' <<<"$out")/$(grep -c '^PASS\|^FAIL' <<<"$out") known-answer tests passed" "$rc $(tail -n1 <<<"$out")"
record "${RUNS}kat output" "$(tr '\n' '|' <<<"$out")"
for opt in "" -m -d; do
  rc=0; out=$(r "$t/shatest" $opt 2>&1) || rc=$?
  check "${RUNS}shatest $opt (RFC 6234 test driver against libref_sha2.so): exit status, FAILED count, PASSED count>0" \
    "0 0 yes" "$rc $(grep -c 'FAILED' <<<"$out" || true) $([ "$(grep -c 'PASSED' <<<"$out")" -gt 0 ] && echo yes || echo no)"
  record "${RUNS}shatest $opt: PASSED lines" "$(grep -c PASSED <<<"$out")"
done
rm -rf "$t"
exit $TEST_FAILED
