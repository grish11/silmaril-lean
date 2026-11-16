;; Memory for closed problem modules: an IMPORTED memory `env.mem` (2 pages; its contents are
;; chosen by the environment, i.e. universally quantified). Page 0 is the guest window
;; [0x100000, 0x110000); any other guest address traps (= fault). Page 1 is scratch for the
;; wrapper's frame check (a snapshot of the window). Same signatures as the mem.* imports.
  (import "env" "mem" (memory $mem 2))
  (func $off (param $a i64) (param $n i64) (result i32)
    (if (i64.lt_u (local.get $a) (i64.const 0x100000)) (then (unreachable)))
    (if (i64.gt_u (i64.add (i64.sub (local.get $a) (i64.const 0x100000)) (local.get $n)) (i64.const 0x10000))
      (then (unreachable)))
    (i32.wrap_i64 (i64.sub (local.get $a) (i64.const 0x100000))))
  (func $load8 (param $a i64) (result i64) (i64.load8_u (call $off (local.get $a) (i64.const 1))))
  (func $load16 (param $a i64) (result i64) (i64.load16_u (call $off (local.get $a) (i64.const 2))))
  (func $load32 (param $a i64) (result i64) (i64.load32_u (call $off (local.get $a) (i64.const 4))))
  (func $load64 (param $a i64) (result i64) (i64.load (call $off (local.get $a) (i64.const 8))))
  (func $store8 (param $a i64) (param $v i64) (i64.store8 (call $off (local.get $a) (i64.const 1)) (local.get $v)))
  (func $store16 (param $a i64) (param $v i64) (i64.store16 (call $off (local.get $a) (i64.const 2)) (local.get $v)))
  (func $store32 (param $a i64) (param $v i64) (i64.store32 (call $off (local.get $a) (i64.const 4)) (local.get $v)))
  (func $store64 (param $a i64) (param $v i64) (i64.store (call $off (local.get $a) (i64.const 8)) (local.get $v)))
