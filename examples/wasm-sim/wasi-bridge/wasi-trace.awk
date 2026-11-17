# Lift a `WASMTIME_LOG=wasmtime_wasi=trace` log to the observable WASI p1 event list:
# one line "FUNCTION PARAMS -> RESULT" per call, guest pointers dropped (the data they point to
# is observed through stdout/stdin), launch events of the simulator stack (args_*, path_open,
# calls on preopened/opened fds >= 3: the loader reading the ELF file) dropped.
/wiggle abi\{module="wasi_snapshot_preview1"/ {
  match($0, /function="[a-z_]+"/); f = substr($0, RSTART + 10, RLENGTH - 11)
  msg = $0; sub(/.*wasi_snapshot_preview1: /, "", msg)
  if (msg ~ /^result=/) {
    if (pending == f) { if (!skip) print f " " params " -> " substr(msg, 8); pending = "" }
    next
  }
  gsub(/[a-z_]+=\*guest 0x[0-9a-f]+(\/[0-9]+)?/, "", msg); gsub(/  +/, " ", msg); sub(/ $/, "", msg)
  params = msg; pending = f
  skip = (f ~ /^(args_sizes_get|args_get|environ_sizes_get|environ_get|path_open)$/) || (msg ~ /fd=Fd\(([3-9]|[1-9][0-9]+)\)/)
  if (f == "proc_exit") { print f " " params; pending = "" }
}
