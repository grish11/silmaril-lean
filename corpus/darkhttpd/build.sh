#!/usr/bin/env bash
# build.sh ARCH OUTDIR -- darkhttpd 1.17 via upstream's Makefile (`make CC=... CFLAGS=...`, which runs
# $(CC) $(CFLAGS) darkhttpd.c -o darkhttpd).
. "$(dirname "$0")/../common.sh"
start_build darkhttpd "$1" "$2"
ROOT=darkhttpd-1.17
A=$(archive $ROOT.tar.gz 4fee9927e2d8bb0a302f0dd62f9ff1e075748fa9f5162c9481a7a58b41462b56 https://github.com/emikulic/darkhttpd/archive/refs/tags/v1.17.tar.gz)
extract "$A" "$BUILD"; pristine "$A"
cd "$BUILD/$ROOT"
CFLAGS="$BASE_CFLAGS -MMD"
info cflags "$CFLAGS"; info ldflags ""; info configure_args "(none: make CC=$CC CFLAGS='$CFLAGS' darkhttpd)"
make CC="$CC" CFLAGS="$CFLAGS" darkhttpd | tee make.log
while IFS= read -r l; do info command "$l"; done < make.log
cp darkhttpd "$OUTDIR/"
{ depfiles "$BUILD/$ROOT"; echo "$BUILD/$ROOT/COPYING"; echo "$BUILD/$ROOT/README.md"; } | collect "$BUILD/$ROOT" $ROOT
