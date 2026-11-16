;; P-data fetch: code words of [code_base, code_base + code_len) are read from
;; the simulator's own memory `$code`, initialised by a data segment that the
;; translator appends (`wasm-sim-rv run-pdata`). Other pcs fall
;; back to the `mem.load32` import. Sound only for programs that do not write
;; their own code (the reference fetch reads the current memory).
(import "mem" "load32" (func $mem_load32 (param i64) (result i64)))
;;@body
(memory $code 16)
(func $fetch (param $pc i64) (result i64)
  (local $off i64)
  (local.set $off (i64.sub (local.get $pc) (global.get $code_base)))
  (if (result i64) (i64.lt_u (local.get $off) (global.get $code_len))
    (then (i64.load32_u $code (i32.wrap_i64 (local.get $off))))
    (else (call $mem_load32 (local.get $pc)))))
