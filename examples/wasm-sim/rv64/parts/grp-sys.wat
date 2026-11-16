;; Group `sys`: ECALL (not in the Lean Ext model; a documented extension).
;; Linux convention: nr = a7, arguments a0..a5, result -> a0, pc += 4.
;; exit (93) / exit_group (94): the import is called (so the environment sees
;; the status in a0), then the simulator halts with status 1 and no state change.
(import "sys" "syscall" (func $sys_syscall (param i64 i64 i64 i64 i64 i64 i64) (result i64)))
;;@body
(func $d_ecall (param $w i32) (result i32) (call $x_ecall))
(func $x_ecall (export "i_ecall") (result i32)
  (local $nr i64) (local $r i64)
  (local.set $nr (call $rget (i32.const 17)))
  (local.set $r (call $sys_syscall (local.get $nr)
    (call $rget (i32.const 10)) (call $rget (i32.const 11)) (call $rget (i32.const 12))
    (call $rget (i32.const 13)) (call $rget (i32.const 14)) (call $rget (i32.const 15))))
  (if (i32.or (i64.eq (local.get $nr) (i64.const 93)) (i64.eq (local.get $nr) (i64.const 94)))
    (then (return (i32.const 1))))
  (call $rset (i32.const 10) (local.get $r))
  (call $next)
  (i32.const 0))
