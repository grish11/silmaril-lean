#!/usr/bin/env bash
# Repository-authored known-answer, signature and TLS observations; not validation.
. "$(dirname "$0")/../common.sh"
start_test boringssl "$1" "$2"
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
src=/build/boringssl/boringssl-ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6
"$CC" -std=c11 -I"$src/include" "$CORPUS/boringssl/smoke.c" -L"$OBJ" -lssl -lcrypto -o "$t/smoke"
run() {
  if [ "$ARCH" = aarch64 ]; then "${RUN[@]}" -E LD_LIBRARY_PATH="$OBJ" "$@"
  else LD_LIBRARY_PATH="$OBJ" "$@"; fi
}
fips=0; [ "${CORPUS_BORINGSSL_CONFIG:-no-asm}" != fips-shared ] || fips=1
check "${RUNS}libcrypto/libssl known answers, signature acceptance/rejection, TLS1.3 BIO handshake + transfer" \
  "$(printf '%s\n' 'SHA256 known answer passed' 'AES128 known answer passed' 'Ed25519 sign verify and rejection passed' 'TLS1.3 certificate signature handshake and application transfer passed' "FIPS research configuration flag: $fips")" \
  "$(run "$t/smoke")"
check "printf abc | ${RUNS}bssl sha256sum" \
  ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad \
  "$(printf abc | run "$OBJ/bssl" sha256sum | cut -d' ' -f1)"
check "${RUNS}bssl ciphers DEFAULT (ECDHE-RSA AES128-GCM suite available)" 1 \
  "$(run "$OBJ/bssl" ciphers DEFAULT | grep -c TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256)"
exit "$TEST_FAILED"
