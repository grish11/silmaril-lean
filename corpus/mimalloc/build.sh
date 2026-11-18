#!/usr/bin/env bash
# build.sh ARCH OUTDIR -- mimalloc 2.1.9: libmimalloc.so.2.1 (soname libmimalloc.so.2). No CMake in the
# image: the commands are those upstream's CMakeLists.txt issues on Linux/gcc for the shared target
# with default options (MI_OVERRIDE=ON, MI_OPT_ARCH=ON -> -march=armv8.1-a on arm64 only), with the
# Release flags (-O3 -DNDEBUG) replaced by -O2 -DNDEBUG (same as sources/alloc/build.sh).
. "$(dirname "$0")/../common.sh"
start_build mimalloc "$1" "$2"
ROOT=mimalloc-2.1.9
A=$(archive $ROOT.tar.gz dd8ff701691f19bf4e225d42ef0d3d5e6ca0e03498ee4f044a0402e4697e4a20 https://github.com/microsoft/mimalloc/archive/refs/tags/v2.1.9.tar.gz)
extract "$A" "$BUILD"; pristine "$A"
cd "$BUILD/$ROOT"
ARCHF=; [ "$ARCH" = aarch64 ] && ARCHF=-march=armv8.1-a
CFLAGS="$BASE_CFLAGS -DNDEBUG -fPIC -Wall -Wextra -Wno-unknown-pragmas -fvisibility=hidden -Wstrict-prototypes -ftls-model=initial-exec -fno-builtin-malloc $ARCHF -Iinclude -DMI_SHARED_LIB -DMI_SHARED_LIB_EXPORT -DMI_MALLOC_OVERRIDE -MMD"
LDFLAGS="-shared -Wl,-soname,libmimalloc.so.2"
info cflags "$CFLAGS"; info ldflags "$LDFLAGS -lpthread -lrt"; info configure_args "(none: CMake defaults written out as gcc commands)"
mkdir -p obj
objs=()
for s in alloc alloc-aligned alloc-posix arena bitmap heap init libc options os page random segment segment-map stats prim/prim; do
  o=obj/${s//\//_}.o
  c="$CC $CFLAGS -c src/$s.c -o $o"; echo "+ $c"; $c; info command "$c"; objs+=("$o")
done
c="$CC -O2 $LDFLAGS -o libmimalloc.so.2.1 ${objs[*]} -lpthread -lrt"; echo "+ $c"; $c; info command "$c"
cp libmimalloc.so.2.1 "$OUTDIR/"
{ depfiles "$BUILD/$ROOT" "$BUILD/$ROOT/obj"; echo "$BUILD/$ROOT/LICENSE"; } | collect "$BUILD/$ROOT" $ROOT
