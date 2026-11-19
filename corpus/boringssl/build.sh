#!/usr/bin/env bash
# Upstream CMake/Ninja build; independent clean source/build trees per repeat.
. "$(dirname "$0")/../common.sh"
start_build boringssl "$1" "$2"
ROOT=boringssl-ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6
A=$(archive "$ROOT.tar.gz" 75ee588268ae3d7552f5be7e0849bdcc8e4159f22547dbfb4aae997784fdd345 https://codeload.github.com/google/boringssl/tar.gz/ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6)
extract "$A" "$BUILD"; pristine "$A"
cd "$BUILD/$ROOT"
CONFIG=${CORPUS_BORINGSSL_CONFIG:-no-asm}
# No network toolchain/module download or inherited build caches. RESET deletes
# these directories before every profile in each independently initialized worker.
export CGO_ENABLED=0 GOTOOLCHAIN=local GOPROXY=off GOSUMDB=off GOMAXPROCS=3
export GOCACHE=/tmp/go-build GOMODCACHE=/tmp/go-mod
info cflags "$BASE_CFLAGS; Release=-g0 -DNDEBUG; upstream adds its own warning/C++/ASM options (see compile_commands.json)"
info ldflags 'upstream CMake shared crypto/ssl and bssl target link commands; see ninja-commands.txt'
info configure_args "upstream CMake; configuration=$CONFIG; shared libraries; BUILD_TESTING=OFF; research build, no FIPS validation"
info command "python3 -I /corpus/boringssl/configure.py '$TP' '$BASE_CFLAGS' '$CONFIG'"
python3 -I "$CORPUS/boringssl/configure.py" "$TP" "$BASE_CFLAGS" "$CONFIG" > configure.log 2>&1 || { tail -60 configure.log; exit 1; }
info command "cmake --build build --target crypto ssl bssl --parallel $JOBS --verbose"
cmake --build build --target crypto ssl bssl --parallel "$JOBS" --verbose > build.log 2>&1 || { tail -60 build.log; exit 1; }
ninja -C build -t commands crypto ssl bssl > build/ninja-commands.txt
ninja -C build -t deps > build/ninja-deps.txt
cp build/libcrypto.so build/libssl.so build/bssl "$OUTDIR/"
mkdir "$OUTDIR/supplementary"
if [ "$CONFIG" = fips-shared ]; then
  cp build/bcm.o "$OUTDIR/supplementary/boringcrypto-bcm.o"
  cp build/libbcm_library.a "$OUTDIR/supplementary/"
  info command 'upstream FIPS_SHARED: linker -r with fips_shared.lds; Go inject_hash rewrites libcrypto.so (executed commands in build.log)'
else
  # Preserve the actual upstream object boundary as a supplementary ET_REL. This
  # packaging command is ours; upstream CMake links the original objects directly.
  mapfile -d '' objects < <(find build/CMakeFiles/fipsmodule.dir -type f -name '*.o' -print0 | sort -z)
  [ "${#objects[@]}" -gt 0 ]
  "${TP}ld" -r -o "$OUTDIR/supplementary/boringcrypto-bcm.o" "${objects[@]}"
  info command "${TP}ld -r -o supplementary/boringcrypto-bcm.o [sorted actual upstream CMakeFiles/fipsmodule.dir/*.o]"
fi
"${TP}readelf" -hSWsr "$OUTDIR/supplementary/boringcrypto-bcm.o" > "$OUTDIR/supplementary/boringcrypto-bcm.readelf.txt"
"${TP}nm" -u "$OUTDIR/supplementary/boringcrypto-bcm.o" > "$OUTDIR/supplementary/boringcrypto-bcm.undefined.txt"
python3 -I "$CORPUS/boringssl/configure.py" --inputs | collect "$PWD" "$ROOT"
