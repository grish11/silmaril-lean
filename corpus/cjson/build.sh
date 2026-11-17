#!/usr/bin/env bash
# build.sh ARCH OUTDIR -- cJSON 1.7.19: libcjson.so.1 (cJSON.c) and libcjson_utils.so.1 (cJSON_Utils.c,
# linked against libcjson.so.1). The commands are those of upstream's CMakeLists.txt with its default
# options (ENABLE_CUSTOM_COMPILER_FLAGS: -std=c89 -fstack-protector-strong + warnings; ENABLE_PUBLIC_SYMBOLS:
# -fvisibility=hidden -DCJSON_EXPORT_SYMBOLS -DCJSON_API_VISIBILITY; ENABLE_LOCALES: -DENABLE_LOCALES;
# ENABLE_CJSON_UTILS turned on), written out as plain gcc commands (no CMake in the image).
. "$(dirname "$0")/../common.sh"
start_build cjson "$1" "$2"
ROOT=cJSON-1.7.19
A=$(archive $ROOT.tar.gz 7fa616e3046edfa7a28a32d5f9eacfd23f92900fe1f8ccd988c1662f30454562 https://github.com/DaveGamble/cJSON/archive/refs/tags/v1.7.19.tar.gz)
extract "$A" "$BUILD"; pristine "$A"
cd "$BUILD/$ROOT"
CFLAGS="$BASE_CFLAGS -std=c89 -pedantic -Wall -fstack-protector-strong -fvisibility=hidden -DCJSON_EXPORT_SYMBOLS -DCJSON_API_VISIBILITY -DENABLE_LOCALES -fPIC -MMD"
info cflags "$CFLAGS"; info ldflags "-shared"; info configure_args "(none: CMake defaults reproduced as gcc commands, ENABLE_CJSON_UTILS=On)"
cmds=(
  "$CC $CFLAGS -c cJSON.c -o cJSON.o"
  "$CC -shared -Wl,-soname,libcjson.so.1 -o libcjson.so.1 cJSON.o -lm"
  "ln -sf libcjson.so.1 libcjson.so"
  "$CC $CFLAGS -c cJSON_Utils.c -o cJSON_Utils.o"
  "$CC -shared -Wl,-soname,libcjson_utils.so.1 -o libcjson_utils.so.1 cJSON_Utils.o -L. -lcjson"
)
for c in "${cmds[@]}"; do echo "+ $c"; $c; info command "$c"; done
cp libcjson.so.1 libcjson_utils.so.1 "$OUTDIR/"
{ depfiles "$BUILD/$ROOT"; echo "$BUILD/$ROOT/LICENSE"; echo "$BUILD/$ROOT/test.c"; } | collect "$BUILD/$ROOT" $ROOT
