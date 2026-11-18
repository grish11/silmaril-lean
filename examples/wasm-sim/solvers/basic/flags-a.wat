;; A tiny G-representation fragment: 16 i64 registers, CF/ZF/SF/OF as i32 globals,
;; `i_add_rr dst src` = x86 `add r64, r64` (flags straightforwardly).
(module
  (global $r0 (mut i64) (i64.const 0)) (global $r1 (mut i64) (i64.const 0))
  (global $r2 (mut i64) (i64.const 0)) (global $r3 (mut i64) (i64.const 0))
  (global $cf (mut i32) (i32.const 0)) (global $zf (mut i32) (i32.const 0))
  (global $sf (mut i32) (i32.const 0)) (global $of (mut i32) (i32.const 0))
  (func $rget (param $r i32) (result i64)
    (block $3 (block $2 (block $1 (block $0
      (br_table $0 $1 $2 $3 (local.get $r)))
      (return (global.get $r0))) (return (global.get $r1))) (return (global.get $r2)))
    (global.get $r3))
  (func $rset (param $r i32) (param $v i64)
    (block $3 (block $2 (block $1 (block $0
      (br_table $0 $1 $2 $3 (local.get $r)))
      (global.set $r0 (local.get $v)) (return)) (global.set $r1 (local.get $v)) (return))
      (global.set $r2 (local.get $v)) (return))
    (global.set $r3 (local.get $v)))
  (func (export "i_add_rr") (param $d i32) (param $s i32)
    (local $a i64) (local $b i64) (local $r i64)
    (local.set $a (call $rget (local.get $d)))
    (local.set $b (call $rget (local.get $s)))
    (local.set $r (i64.add (local.get $a) (local.get $b)))
    (global.set $cf (i64.lt_u (local.get $r) (local.get $a)))
    (global.set $zf (i64.eqz (local.get $r)))
    (global.set $sf (i32.wrap_i64 (i64.shr_u (local.get $r) (i64.const 63))))
    (global.set $of (i32.wrap_i64 (i64.shr_u
       (i64.and (i64.xor (local.get $a) (local.get $r)) (i64.xor (local.get $b) (local.get $r)))
       (i64.const 63))))
    (call $rset (local.get $d) (local.get $r))))
