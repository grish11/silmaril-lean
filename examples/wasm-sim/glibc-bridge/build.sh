#!/bin/sh
# Build the glibc-bridge modules and test programs into build/.
#  * glibc.wasm, glibcrun.wasm (wat/);
#  * loader-glibc.wasm: ../proc/wat/loader.wat with the foreign table replaced by the
#    glibc-subset table (index i <-> EXT_BASE + 16 i, as in wat/glibc.wat);
#  * progs/hello-glibc: progs/hello.c, standard gcc + glibc, dynamically linked, -no-pie
#    (the loader maps ET_EXEC only).
set -eu
D="$(cd "$(dirname "$0")" && pwd)"; cd "$D"
[ -f ../proc/build/extrun.wasm ] || ../proc/build.sh
mkdir -p build
for f in glibc glibcrun; do wat2wasm wat/$f.wat -o build/$f.wasm; done
[ -f build/sys2wasi.wasm ] || wat2wasm ../wasi-bridge/wat/sys2wasi.wat -o build/sys2wasi.wasm
sed -e 's|(data (i32.const 16384) "puts\\00strlen\\00putchar\\00\\00")|(data (i32.const 17408) "puts\\00strlen\\00putchar\\00__libc_start_main\\00exit\\00write\\00memcpy\\00memset\\00\\00")|' \
    -e 's|(local.set $p (i32.const 16384))|(local.set $p (i32.const 17408))|' \
    ../proc/wat/loader.wat > build/loader-glibc.wat
grep -q '17408) "puts' build/loader-glibc.wat && grep -q 'local.set $p (i32.const 17408)' build/loader-glibc.wat \
  || { echo "build.sh: loader.wat changed; update the sed" >&2; exit 1; }
wat2wasm build/loader-glibc.wat -o build/loader-glibc.wasm
gcc -O2 -no-pie -o progs/hello-glibc progs/hello.c
# greet with the distribution defaults needs fs:0x28 (stack-protector canary, TLS set up by
# the elided start-up) and SSE (inlined memset): neither is in the simulators (status 2).
gcc -O2 -no-pie -fno-stack-protector -mgeneral-regs-only -Wno-unused-result -o progs/greet-glibc progs/greet.c
