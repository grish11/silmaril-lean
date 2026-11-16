;; GENERATED from src-state-g.wat (x86 simulator): the five state accessors of representation G.
(module
;; State representation G: one mutable global per location.
;; Provides $rget/$rset (loc 0..16: GPRs, rip), $fget/$fset (loc 17..23: flags, i32 0/1),
;; $fset6 (cf pf af zf sf of).
  (global $r0 (mut i64) (i64.const 0))
  (global $r1 (mut i64) (i64.const 0))
  (global $r2 (mut i64) (i64.const 0))
  (global $r3 (mut i64) (i64.const 0))
  (global $r4 (mut i64) (i64.const 0))
  (global $r5 (mut i64) (i64.const 0))
  (global $r6 (mut i64) (i64.const 0))
  (global $r7 (mut i64) (i64.const 0))
  (global $r8 (mut i64) (i64.const 0))
  (global $r9 (mut i64) (i64.const 0))
  (global $r10 (mut i64) (i64.const 0))
  (global $r11 (mut i64) (i64.const 0))
  (global $r12 (mut i64) (i64.const 0))
  (global $r13 (mut i64) (i64.const 0))
  (global $r14 (mut i64) (i64.const 0))
  (global $r15 (mut i64) (i64.const 0))
  (global $rip (mut i64) (i64.const 0))
  (global $cf (mut i32) (i32.const 0))
  (global $pf (mut i32) (i32.const 0))
  (global $af (mut i32) (i32.const 0))
  (global $zf (mut i32) (i32.const 0))
  (global $sf (mut i32) (i32.const 0))
  (global $of (mut i32) (i32.const 0))
  (global $df (mut i32) (i32.const 0))
  (func $rget (param $r i32) (result i64)
    (block $default
    (block $L16
    (block $L15
    (block $L14
    (block $L13
    (block $L12
    (block $L11
    (block $L10
    (block $L9
    (block $L8
    (block $L7
    (block $L6
    (block $L5
    (block $L4
    (block $L3
    (block $L2
    (block $L1
    (block $L0
      (br_table $L0 $L1 $L2 $L3 $L4 $L5 $L6 $L7 $L8 $L9 $L10 $L11 $L12 $L13 $L14 $L15 $L16 $default (local.get $r)))
      (return (global.get $r0)))
      (return (global.get $r1)))
      (return (global.get $r2)))
      (return (global.get $r3)))
      (return (global.get $r4)))
      (return (global.get $r5)))
      (return (global.get $r6)))
      (return (global.get $r7)))
      (return (global.get $r8)))
      (return (global.get $r9)))
      (return (global.get $r10)))
      (return (global.get $r11)))
      (return (global.get $r12)))
      (return (global.get $r13)))
      (return (global.get $r14)))
      (return (global.get $r15)))
      (return (global.get $rip)))
    (unreachable))
  (func $rset (param $r i32) (param $v i64)
    (block $default
    (block $L16
    (block $L15
    (block $L14
    (block $L13
    (block $L12
    (block $L11
    (block $L10
    (block $L9
    (block $L8
    (block $L7
    (block $L6
    (block $L5
    (block $L4
    (block $L3
    (block $L2
    (block $L1
    (block $L0
      (br_table $L0 $L1 $L2 $L3 $L4 $L5 $L6 $L7 $L8 $L9 $L10 $L11 $L12 $L13 $L14 $L15 $L16 $default (local.get $r)))
      (global.set $r0 (local.get $v)) (return))
      (global.set $r1 (local.get $v)) (return))
      (global.set $r2 (local.get $v)) (return))
      (global.set $r3 (local.get $v)) (return))
      (global.set $r4 (local.get $v)) (return))
      (global.set $r5 (local.get $v)) (return))
      (global.set $r6 (local.get $v)) (return))
      (global.set $r7 (local.get $v)) (return))
      (global.set $r8 (local.get $v)) (return))
      (global.set $r9 (local.get $v)) (return))
      (global.set $r10 (local.get $v)) (return))
      (global.set $r11 (local.get $v)) (return))
      (global.set $r12 (local.get $v)) (return))
      (global.set $r13 (local.get $v)) (return))
      (global.set $r14 (local.get $v)) (return))
      (global.set $r15 (local.get $v)) (return))
      (global.set $rip (local.get $v)) (return))
    (unreachable))
  (func $fget (param $f i32) (result i32)
    (block $default
    (block $L6
    (block $L5
    (block $L4
    (block $L3
    (block $L2
    (block $L1
    (block $L0
      (br_table $L0 $L1 $L2 $L3 $L4 $L5 $L6 $default (i32.sub (local.get $f) (i32.const 17))))
      (return (global.get $cf)))
      (return (global.get $pf)))
      (return (global.get $af)))
      (return (global.get $zf)))
      (return (global.get $sf)))
      (return (global.get $of)))
      (return (global.get $df)))
    (unreachable))
  (func $fset (param $f i32) (param $v i32)
    (block $default
    (block $L6
    (block $L5
    (block $L4
    (block $L3
    (block $L2
    (block $L1
    (block $L0
      (br_table $L0 $L1 $L2 $L3 $L4 $L5 $L6 $default (i32.sub (local.get $f) (i32.const 17))))
      (global.set $cf (local.get $v)) (return))
      (global.set $pf (local.get $v)) (return))
      (global.set $af (local.get $v)) (return))
      (global.set $zf (local.get $v)) (return))
      (global.set $sf (local.get $v)) (return))
      (global.set $of (local.get $v)) (return))
      (global.set $df (local.get $v)) (return))
    (unreachable))
  (func $fset6 (param $c i32) (param $p i32) (param $a i32) (param $z i32) (param $s i32) (param $o i32)
    (global.set $cf (local.get $c)) (global.set $pf (local.get $p)) (global.set $af (local.get $a))
    (global.set $zf (local.get $z)) (global.set $sf (local.get $s)) (global.set $of (local.get $o)))
  (export "rget" (func $rget)) (export "rset" (func $rset)) (export "fget" (func $fget))
  (export "fset" (func $fset)) (export "fset6" (func $fset6))
)
