#!/usr/bin/env bash
# test.sh ARCH OBJDIR -- run the built openssl CLI against the built libcrypto.so.3 / libssl.so.3
# (natively or under qemu-user): version, digests, AES round trip, Ed25519 and EC sign/verify, and a
# TLS 1.3 handshake between s_server and s_client on 127.0.0.1 (both from this build).
. "$(dirname "$0")/../common.sh"
start_test openssl "$1" "$2"
case $ARCH in x86_64) PORT=18443 ;; aarch64) PORT=18444 ;; esac
t=$(mktemp -d); cp "$OBJ/libcrypto.so.3" "$OBJ/libssl.so.3" "$OBJ/openssl" "$t/"; cd "$t"
o() { if [ "$ARCH" = aarch64 ]; then "${RUN[@]}" -E LD_LIBRARY_PATH="$t" -E OPENSSL_CONF=/dev/null "$t/openssl" "$@"; else LD_LIBRARY_PATH="$t" OPENSSL_CONF=/dev/null "$t/openssl" "$@"; fi; }
check "${RUNS}openssl version" "OpenSSL 3.5.9" "$(o version | cut -d' ' -f1-2)"
check "${RUNS}openssl version -f (compiler flags baked in)" "1" "$(o version -f | grep -c -- '-O2 -g0')"
check "printf abc | ${RUNS}openssl dgst -sha256 -r" "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad *stdin" "$(printf abc | o dgst -sha256 -r)"
check "printf abc | ${RUNS}openssl dgst -sha3-256 -r" "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532 *stdin" "$(printf abc | o dgst -sha3-256 -r)"
check "printf abc | ${RUNS}openssl dgst -blake2b512 -r" "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923 *stdin" "$(printf abc | o dgst -blake2b512 -r)"
check "${RUNS}openssl enc -aes-128-ecb -K 000102..0f -nopad (FIPS 197 C.1)" "69c4e0d86a7b0430d8cdb78070b4c55a" \
  "$(printf '\x00\x11\x22\x33\x44\x55\x66\x77\x88\x99\xaa\xbb\xcc\xdd\xee\xff' | o enc -aes-128-ecb -K 000102030405060708090a0b0c0d0e0f -nopad | od -An -tx1 | tr -d ' \n')"
head -c 5000 /dev/urandom > data.bin
o enc -aes-256-cbc -pbkdf2 -pass pass:silmaril -in data.bin -out data.enc
o enc -d -aes-256-cbc -pbkdf2 -pass pass:silmaril -in data.enc -out data.dec
check "${RUNS}openssl enc -aes-256-cbc -pbkdf2 encrypt + decrypt round trip (5000 random bytes)" ok "$(cmp -s data.bin data.dec && echo ok || echo differ)"
o genpkey -algorithm ED25519 -out ed.key 2>/dev/null; o pkey -in ed.key -pubout -out ed.pub
o pkeyutl -sign -inkey ed.key -rawin -in data.bin -out ed.sig
check "${RUNS}openssl genpkey ED25519; pkeyutl -sign; pkeyutl -verify" "Signature Verified Successfully" "$(o pkeyutl -verify -pubin -inkey ed.pub -rawin -in data.bin -sigfile ed.sig 2>&1)"
o ecparam -name prime256v1 -genkey -noout -out ec.key
o req -x509 -new -key ec.key -subj /CN=localhost -days 2 -out ec.crt 2>/dev/null
check "${RUNS}openssl req -x509 (self-signed P-256 cert) | x509 -noout -subject" "subject=CN=localhost" "$(o x509 -in ec.crt -noout -subject)"
if [ "$ARCH" = aarch64 ]; then
  "${RUN[@]}" -E LD_LIBRARY_PATH="$t" -E OPENSSL_CONF=/dev/null "$t/openssl" s_server -accept 127.0.0.1:$PORT -cert ec.crt -key ec.key -tls1_3 -naccept 1 -rev > srv.log 2>&1 &
else
  LD_LIBRARY_PATH="$t" OPENSSL_CONF=/dev/null "$t/openssl" s_server -accept 127.0.0.1:$PORT -cert ec.crt -key ec.key -tls1_3 -naccept 1 -rev > srv.log 2>&1 &
fi
pid=$!
for i in $(seq 100); do grep -q ACCEPT srv.log && break; sleep 0.2; done
out=$( (printf 'ping\n'; sleep $([ $ARCH = aarch64 ] && echo 15 || echo 3)) | o s_client -connect 127.0.0.1:$PORT -CAfile ec.crt -verify_return_error -servername localhost 2>&1)
kill $pid 2>/dev/null || true; wait $pid 2>/dev/null || true
check "${RUNS}openssl s_server -tls1_3 -rev / ${RUNS}openssl s_client 127.0.0.1:$PORT: protocol, verify, reversed reply" \
  "TLSv1.3|Verify return code: 0 (ok)|gnip" \
  "$(grep -o -m1 'Protocol *: *TLSv1.3\|New, TLSv1.3' <<<"$out" | grep -o 'TLSv1.3')|$(grep -o -m1 'Verify return code: 0 (ok)' <<<"$out")|$(grep -o -m1 '^gnip' <<<"$out")"
record "s_client transcript (selected lines)" "$(grep -E 'Protocol|Cipher is|Verify return|^gnip|subject=' <<<"$out" | head -8 | tr '\n' '|')"
cd /; rm -rf "$t"
exit $TEST_FAILED
