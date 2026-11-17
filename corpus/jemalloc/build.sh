#!/usr/bin/env bash
# build.sh ARCH OUTDIR -- jemalloc 5.3.0: lib/libjemalloc.so.2 via upstream's own configure + make.
# configure is the one shipped in the release tarball (not regenerated). Page sizes are given
# explicitly so that nothing depends on the build host: x86_64 --with-lg-page=12; aarch64
# --with-lg-page=16 (64 KiB, as Debian's arm64 package does, works on 4K/16K/64K kernels);
# both --with-lg-hugepage=21. configure adds -O3 -funroll-loops -g3 to CONFIGURE_CFLAGS; our CFLAGS
# come later on every compile line, so -O2 and -g0 win (-funroll-loops stays, as upstream intends).
. "$(dirname "$0")/../common.sh"
start_build jemalloc "$1" "$2"
ROOT=jemalloc-5.3.0
A=$(archive $ROOT.tar.bz2 2db82d1e7119df3e71b7640219b6dfe84789bc0537983c3b7ac4f7189aecfeaa https://github.com/jemalloc/jemalloc/releases/download/5.3.0/$ROOT.tar.bz2)
extract "$A" "$BUILD"; pristine "$A"
cd "$BUILD/$ROOT"
case $ARCH in x86_64) LGP=12 ;; aarch64) LGP=16 ;; esac
CFLAGS="$BASE_CFLAGS"
CONF="--build=x86_64-linux-gnu --host=$TRIPLE --disable-cxx --with-lg-page=$LGP --with-lg-hugepage=21"
info cflags "$CFLAGS (after configure's own: -std=gnu11 -Wall ... -O3 -funroll-loops -g3 ...; see command lines)"
info ldflags ""
info configure_args "$CONF CC=$CC CFLAGS='$CFLAGS'"
./configure $CONF CC="$CC" CFLAGS="$CFLAGS" > configure.log
make -j"$JOBS" V=1 lib/libjemalloc.so.2 | tee make.log
grep -m1 -- '-o src/jemalloc.pic.o' make.log | sed "s/^/compile line: /" | while IFS= read -r l; do info command "$l"; done
grep -m1 -- '-shared' make.log | while IFS= read -r l; do info command "$l"; done
cp lib/libjemalloc.so.2 "$OUTDIR/"
{ depfiles "$BUILD/$ROOT" "$BUILD/$ROOT/src"; echo "$BUILD/$ROOT/COPYING"; echo "$BUILD/$ROOT/README"; echo "$BUILD/$ROOT/include/jemalloc/internal/jemalloc_internal_defs.h"; echo "$BUILD/$ROOT/include/jemalloc/jemalloc.h"; } | collect "$BUILD/$ROOT" $ROOT
