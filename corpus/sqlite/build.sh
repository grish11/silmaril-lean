#!/usr/bin/env bash
# build.sh ARCH OUTDIR -- SQLite 3.54.1 amalgamation: libsqlite3.so (soname libsqlite3.so.0) and the
# sqlite3 shell (shell.c, dynamically linked against that library). Runs inside the toolchain image.
. "$(dirname "$0")/../common.sh"
start_build sqlite "$1" "$2"
ROOT=sqlite-amalgamation-3540100
A=$(archive $ROOT.zip 0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9 https://sqlite.org/2026/$ROOT.zip)
extract "$A" "$BUILD"; pristine "$A"
cd "$BUILD/$ROOT"
DEFS="-DSQLITE_THREADSAFE=1"
CFLAGS="$BASE_CFLAGS $DEFS -MMD"
LDFLAGS=""
info cflags "$CFLAGS"; info ldflags "$LDFLAGS"; info configure_args "(none: amalgamation compiled directly)"
set -x
$CC $CFLAGS -fPIC -c sqlite3.c -o sqlite3.o
$CC $LDFLAGS -shared -Wl,-soname,libsqlite3.so.0 -o libsqlite3.so sqlite3.o -lm
$CC $CFLAGS -c shell.c -o shell.o
$CC $LDFLAGS -o sqlite3 shell.o -L. -lsqlite3 -lm
set +x
info command "$CC $CFLAGS -fPIC -c sqlite3.c -o sqlite3.o"
info command "$CC -shared -Wl,-soname,libsqlite3.so.0 -o libsqlite3.so sqlite3.o -lm"
info command "$CC $CFLAGS -c shell.c -o shell.o"
info command "$CC -o sqlite3 shell.o -L. -lsqlite3 -lm"
cp libsqlite3.so sqlite3 "$OUTDIR/"
depfiles "$BUILD/$ROOT" | collect "$BUILD/$ROOT" $ROOT
