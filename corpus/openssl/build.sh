#!/usr/bin/env bash
# build.sh ARCH OUTDIR -- OpenSSL 3.5.9 (LTS) with its own Configure + make:
#   ./Configure linux-x86_64 | linux-aarch64 --cross-compile-prefix=aarch64-linux-gnu-
#               no-asm shared no-tests --prefix=/usr/local --openssldir=/usr/local/ssl
#               --libdir=lib CFLAGS='-O2 -g0 -ffile-prefix-map=/build/openssl=.'
# no-asm: no perlasm/assembly modules, so every function in the outputs comes from C (wanted by the
# later translation-validation step). Builds libcrypto.so.3, libssl.so.3 and apps/openssl only
# (make build_libs apps/openssl); providers/engines modules are not built.
. "$(dirname "$0")/../common.sh"
start_build openssl "$1" "$2"
ROOT=openssl-3.5.9
A=$(archive $ROOT.tar.gz 603f5602e2eef00d77fbd429d34dcd5822bb301757a1bc9cdb24c670f1eb859a https://github.com/openssl/openssl/releases/download/openssl-3.5.9/$ROOT.tar.gz)
extract "$A" "$BUILD"; pristine "$A"
cd "$BUILD/$ROOT"
case $ARCH in
  x86_64)  TARGET=(linux-x86_64) ;;
  aarch64) TARGET=(linux-aarch64 --cross-compile-prefix=aarch64-linux-gnu-) ;;
esac
unset CC CXX AR RANLIB NM   # Configure derives the tools from --cross-compile-prefix
CFLAGS="$BASE_CFLAGS"
CONF=("${TARGET[@]}" no-asm shared no-tests --prefix=/usr/local --openssldir=/usr/local/ssl --libdir=lib "CFLAGS=$CFLAGS")
info cflags "$CFLAGS (replaces Configure's default -O3; Configure adds -fPIC/-pthread/-m64 etc.: see command lines)"
info ldflags ""
info configure_args "./Configure ${CONF[*]}"
perl ./Configure "${CONF[@]}" > configure.log 2>&1 || { cat configure.log; exit 1; }
make -j"$JOBS" build_libs > make-libs.log 2>&1 || { tail -50 make-libs.log; exit 1; }
make -j"$JOBS" apps/openssl > make-apps.log 2>&1 || { tail -50 make-apps.log; exit 1; }
grep -m1 -- '-c -o crypto/libcrypto-shlib-cryptlib.o' make-libs.log | while IFS= read -r l; do info command "$l"; done
for pat in "libcrypto.so.3:make-libs.log" "libssl.so.3:make-libs.log" "apps/openssl:make-apps.log"; do
  info command "$(grep -m1 -B1 -A3 -- "-o ${pat%%:*} " "${pat#*:}" | tr -d '\t\\' | tr '\n' ' ' | tr -s ' ')"
done
cp libcrypto.so.3 libssl.so.3 apps/openssl "$OUTDIR/"
{ depfiles "$BUILD/$ROOT"; printf '%s\n' "$BUILD/$ROOT/LICENSE.txt" "$BUILD/$ROOT/README.md" "$BUILD/$ROOT/AUTHORS.md" "$BUILD/$ROOT/NOTICE" "$BUILD/$ROOT/configdata.pm" "$BUILD/$ROOT/crypto/buildinf.h"; } | collect "$BUILD/$ROOT" $ROOT
