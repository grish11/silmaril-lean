#!/usr/bin/env bash
# build.sh ARCH OUTDIR -- TinyCC 0.9.27 with its own ./configure + make: the `tcc` compiler driver
# (the whole compiler, libtcc.a linked in), for the host architecture it runs on
# (x86_64: TCC_TARGET_X86_64; aarch64: --cpu=aarch64 cross-built, TCC_TARGET_ARM64).
. "$(dirname "$0")/../common.sh"
start_build tinycc "$1" "$2"
ROOT=tcc-0.9.27
A=$(archive $ROOT.tar.bz2 de23af78fca90ce32dff2dd45b3432b2334740bb9bb7b05bf60fdbfc396ceb9c https://download.savannah.gnu.org/releases/tinycc/$ROOT.tar.bz2)
extract "$A" "$BUILD"; pristine "$A"
cd "$BUILD/$ROOT"
case $ARCH in
  x86_64)  CONF=() ;;
  aarch64) CONF=(--cpu=aarch64 --cross-prefix=aarch64-linux-gnu- --triplet=aarch64-linux-gnu) ;;
esac
unset CC
CFLAGS="$BASE_CFLAGS -MMD"
info cflags "$CFLAGS (configure adds -Wdeclaration-after-statement -fno-strict-aliasing -Wno-pointer-sign -Wno-sign-compare -Wno-unused-result)"
info ldflags ""
info configure_args "./configure ${CONF[*]} --extra-cflags='$CFLAGS'"
./configure "${CONF[@]}" --extra-cflags="$CFLAGS" > configure.log 2>&1 || { cat configure.log; exit 1; }
make -j"$JOBS" tcc > make.log 2>&1 || { tail -40 make.log; exit 1; }
while IFS= read -r l; do case $l in *gcc*) info command "$l" ;; esac; done < make.log
cp tcc "$OUTDIR/"
{ depfiles "$BUILD/$ROOT"; printf '%s\n' "$BUILD/$ROOT/COPYING" "$BUILD/$ROOT/README" "$BUILD/$ROOT/config.h" "$BUILD/$ROOT/config.mak"; } | collect "$BUILD/$ROOT" $ROOT
