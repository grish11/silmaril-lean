#!/bin/sh
# Build the static test programs (x86-64 ELF). Requires GNU as/ld and gcc.
set -eu
cd "$(dirname "$0")"
as -o hello.o hello.S && ld -static -o hello hello.o && rm hello.o
as -o threads.o threads.S && ld -static -o threads threads.o && rm threads.o
CF="-O2 -nostdlib -static -fno-pie -no-pie -fno-stack-protector -fcf-protection=none -fno-asynchronous-unwind-tables -fno-builtin"
gcc $CF -o hello_c hello_c.c
gcc $CF -falign-loops=1 -falign-jumps=1 -falign-labels=1 -falign-functions=1 -o bench bench.c
# System V test functions: an ELF for the simulator, and a native driver.
CF2="-O2 -fno-pie -no-pie -fno-stack-protector -fcf-protection=none -fno-asynchronous-unwind-tables"
as -o sysv_fns.o sysv_fns.S
gcc $CF2 -c -o sysv_c.o sysv_c.c
ld -static -e add2 -o sysv_fns sysv_fns.o sysv_c.o
gcc $CF2 -o sysv_native sysv_native.c sysv_fns.o sysv_c.o
rm -f sysv_fns.o sysv_c.o
# Dynamically linked program + its native foreign library (eager binding, BIND_NOW).
gcc -O2 -fPIC -shared -nostdlib -fno-stack-protector -fcf-protection=none -fno-builtin -o libstub.so stub.c
gcc $CF -c -o dyn.o dyn.c
ld -o dyn dyn.o -L. -lstub -dynamic-linker /lib64/ld-linux-x86-64.so.2 -z now -rpath '$ORIGIN'
rm -f dyn.o
# the x86 test functions (examples/wasm-sim/x86/tests/funcs.S), if present
if [ -f ../../x86/tests/funcs.S ]; then
  as -o x86_funcs.o ../../x86/tests/funcs.S
  ld -static -e add2 -z noexecstack -o x86_funcs x86_funcs.o
  gcc $CF2 -z noexecstack -o x86_native x86_native.c x86_funcs.o
  rm -f x86_funcs.o
fi
