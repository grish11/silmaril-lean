#!/usr/bin/env bash
# build.sh ARCH OUTDIR -- pingpong-server / pingpong-client: Beej's server.c / client.c (verbatim from
# the pinned bgnet commit) with local/pingpong.patch applied, each compiled to one executable.
. "$(dirname "$0")/../common.sh"
start_build tcp-pingpong "$1" "$2"
ROOT=bgnet-34fb9d781a3643bc1e2a36ba6e77e0d347ffe2c9
A=$(archive $ROOT.tar.gz 13df988f5f202b550c078a81d9b94c294ef7946d684a6013aaae8f638c5982ce https://github.com/beejjorgensen/bgnet/archive/34fb9d781a3643bc1e2a36ba6e77e0d347ffe2c9.tar.gz)
tar -C "$BUILD" -xzf "$A" $ROOT/source/examples/server.c $ROOT/source/examples/client.c
pristine "$A"
[ -n "${CORPUS_COLLECT:-}" ] && printf '%s\n' "$BUILD/$ROOT/source/examples/server.c" "$BUILD/$ROOT/source/examples/client.c" | collect "$BUILD/$ROOT" $ROOT
cd "$BUILD/$ROOT/source/examples"
patch -p1 --no-backup-if-mismatch < "$CORPUS/tcp-pingpong/local/pingpong.patch"
CFLAGS="$BASE_CFLAGS -Wall"
info cflags "$CFLAGS"; info ldflags ""; info configure_args "(none)"
info input "local/pingpong.patch $(sha256sum < "$CORPUS/tcp-pingpong/local/pingpong.patch" | cut -c1-64)"
for c in "$CC $CFLAGS server.c -o pingpong-server" "$CC $CFLAGS client.c -o pingpong-client"; do
  echo "+ $c"; $c; info command "$c"
done
cp pingpong-server pingpong-client "$OUTDIR/"
