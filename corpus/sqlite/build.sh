#!/usr/bin/env bash
# build.sh ARCH OUTDIR -- SQLite 3.54.1 amalgamation: libsqlite3.so (soname libsqlite3.so.0) and the
# sqlite3 shell (shell.c, dynamically linked against that library). Runs inside the toolchain image.
. "$(dirname "$0")/../common.sh"
start_build sqlite "$1" "$2"
. "$(dirname "$0")/release.sh"
info version "$VERSION"
A=$(archive "$ROOT.zip" "$SHA256" "$URL")
extract "$A" "$BUILD"; pristine "$A"
cd "$BUILD/$ROOT"
DEFS="-DSQLITE_THREADSAFE=1"
case ${CORPUS_SQLITE_CONFIG:-default} in
  default) ;;
  fts5-rtree) DEFS="$DEFS -DSQLITE_ENABLE_FTS5 -DSQLITE_ENABLE_RTREE" ;;
  small) DEFS="-DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION -DSQLITE_DEFAULT_MEMSTATUS=0" ;;
  *) echo 'unsupported SQLite configuration' >&2; exit 2 ;;
esac
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
