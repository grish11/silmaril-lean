#!/bin/bash
# Compare stdout and exit status of native execution with the all-Wasm stack (run-wasi.sh),
# for each simulator (mini = stub, g/m = the x86-64 simulators).
set -u
cd "$(dirname "$0")/progs"
fail=0
POST=cat
check() { # sim ext prog args...
  sim="$1"; ext="$2"; p="$3"; shift 3
  T=$(mktemp)
  env -i bash -c 'exec -a "$0" "./$0" "$@"' "$p" "$@" > $T; nrc=$?; nout=$($POST < $T)
  WSIM_SIM=$sim WSIM_EXT=$ext ../run-wasi.sh "$p" "$@" > $T; wrc=$?; wout=$($POST < $T)
  rm -f $T
  if [ "$nout" = "$wout" ] && [ $nrc = $wrc ]; then echo "ok   [$sim${WSIM_SCHED:+ $WSIM_SCHED}] $p $* (rc=$nrc)";
  else echo "FAIL [$sim] $p $*: native rc=$nrc wasm rc=$wrc"; echo "$nout" | head -5; echo ---; echo "$wout" | head -5; fail=1; fi
}
for sim in ${SIMS:-mini g m}; do
  check $sim ffi-none hello
  check $sim ffi-none hello_c
  check $sim ffi-none hello_c a bc "d e"
  check $sim libc dyn
  check $sim libc dyn x yy zzz
  # threads: the interleaving depends on the schedule; compare the sorted output
  for pol in rr rand; do POST=sort WSIM_SCHED=$pol check $sim ffi-none threads; done
done
exit $fail
