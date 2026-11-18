;; x86-64 subset simulator: imports (environment), see docs/wasm-sim-abi.md.
;; Assembled by `wasm-sim gen-x86`: header ++ mem-import ++ state-{g,m} ++ core ++ decode ++ ")".
(module
  (import "sys" "syscall" (func $syscall (param i64 i64 i64 i64 i64 i64 i64) (result i64)))
  (import "nd" "undef" (func $undef (param i32) (result i64)))
