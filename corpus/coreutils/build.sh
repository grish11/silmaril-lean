#!/usr/bin/env bash
# build.sh ARCH OUTDIR -- GNU coreutils 9.12, genuine GNU build: ./configure && make, cross for aarch64
# (--host=aarch64-linux-gnu). Builds $(BUILT_SOURCES) and then only the seven programs of the corpus:
# true echo cat wc head sort sha256sum (unstripped; no install step).
. "$(dirname "$0")/../common.sh"
start_build coreutils "$1" "$2"
ROOT=coreutils-9.12
A=$(archive $ROOT.tar.xz a480198559733e9b3da999e90543ac6f888a2caa544d8d664c5a1f17e528e210 https://ftp.gnu.org/gnu/coreutils/$ROOT.tar.xz)
extract "$A" "$BUILD"; pristine "$A"
cd "$BUILD/$ROOT"
PROGS="true echo cat wc head sort sha256sum"
CFLAGS="$BASE_CFLAGS"
CONF="--build=x86_64-linux-gnu --host=$TRIPLE --disable-nls --without-selinux --without-openssl --without-libgmp --disable-acl --disable-xattr --disable-libcap --disable-libsmack --without-systemd --disable-rpath"
info cflags "$CFLAGS"; info ldflags ""; info configure_args "FORCE_UNSAFE_CONFIGURE=1 ./configure $CONF CC=$CC CFLAGS='$CFLAGS'"
export FORCE_UNSAFE_CONFIGURE=1   # the image builds as root; native coreutils configure refuses root otherwise
./configure $CONF CC="$CC" CFLAGS="$CFLAGS" > configure.log
# cross builds: record which configure checks were guessed instead of run (no cache variables are
# supplied: configure succeeds with gnulib's default "conservative" cross guesses)
grep -i 'guess\|cross' configure.log > configure-cross-guesses.txt || true
info notes "configure: $(grep -c 'guessing' configure-cross-guesses.txt || true) checks guessed (cross compilation: $( [ $ARCH = x86_64 ] && echo no || echo yes)); see generated/$ARCH/configure-cross-guesses.txt"
BS=$(make -s -f Makefile -f "$CORPUS/coreutils/local/print-var.mk" print-BUILT_SOURCES)
make -j"$JOBS" $BS > make-built-sources.log
targets=; for p in $PROGS; do targets="$targets src/$p"; done
make -j"$JOBS" V=1 $targets | tee make.log
grep -E -- ' -c .*src/wc\.c|-o src/wc( |$)' make.log | head -2 | sed 's/ *&&\\$//' | while IFS= read -r l; do info command "$l"; done
for p in $PROGS; do cp "src/$p" "$OUTDIR/"; done
{ depfiles "$BUILD/$ROOT"; echo "$BUILD/$ROOT/COPYING"; echo "$BUILD/$ROOT/README"; echo "$BUILD/$ROOT/AUTHORS"; echo "$BUILD/$ROOT/THANKS.in"; echo "$BUILD/$ROOT/configure-cross-guesses.txt"; } | collect "$BUILD/$ROOT" $ROOT
