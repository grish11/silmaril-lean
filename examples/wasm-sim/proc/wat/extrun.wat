;; extrun: foreign calls (dynamic linking) for ANY simulator following docs/wasm-sim-abi.md, outside the simulator.
;;
;; Wraps a simulator `core` and re-exports its get/set/modelled, so it can stand in for the simulator
;; (preload it as "sim"). `run(fuel)` steps the core; when rip is in the foreign range
;; [lo, hi) set by `set_ext`, instead of stepping it marshals a System V call by value:
;;   s := ffi.call(rip, rdi, rsi, rdx, rcx, r8, r9);  rax := ffi.ret();  ret
;; (status s /= 0 stops with s). The foreign library never calls back into the simulator, so
;; there is no module cycle and no component reentrancy (contrast the simulator ABI's `ext.call`,
;; which reads/writes state through the simulator's exports).
;; The sentinel return address 0xFFFF_FFFF_FFFF_F000 stops with status 1.
(module
  (import "core" "get" (func $get (param i32) (result i64)))
  (import "core" "set" (func $set (param i32 i64)))
  (import "core" "modelled" (func $modelled (param i32) (result i32)))
  (import "core" "step" (func $step (result i32)))
  (import "ffi" "call" (func $ffi_call (param i64 i64 i64 i64 i64 i64 i64) (result i32)))
  (import "ffi" "ret" (func $ffi_ret (result i64)))
  (import "mem" "load64" (func $ld64 (param i64) (result i64)))
  (export "get" (func $get))
  (export "set" (func $set))
  (export "modelled" (func $modelled))
  (global $lo (mut i64) (i64.const 0))
  (global $hi (mut i64) (i64.const 0))
  (func (export "set_ext") (param $lo i64) (param $hi i64)
    (global.set $lo (local.get $lo)) (global.set $hi (local.get $hi)))
  (func $stepx (export "step") (result i32)
    (local $rip i64) (local $s i32) (local $sp i64)
    (local.set $rip (call $get (i32.const 16)))
    (if (i64.eq (local.get $rip) (i64.const 0xFFFFFFFFFFFFF000)) (then (return (i32.const 1))))
    (if (i32.and (i64.ge_u (local.get $rip) (global.get $lo)) (i64.lt_u (local.get $rip) (global.get $hi)))
      (then
        (local.set $s (call $ffi_call (local.get $rip)
          (call $get (i32.const 7)) (call $get (i32.const 6)) (call $get (i32.const 2))
          (call $get (i32.const 1)) (call $get (i32.const 8)) (call $get (i32.const 9))))
        (if (local.get $s) (then (return (local.get $s))))
        (call $set (i32.const 0) (call $ffi_ret))
        (local.set $sp (call $get (i32.const 4)))
        (call $set (i32.const 16) (call $ld64 (local.get $sp)))
        (call $set (i32.const 4) (i64.add (local.get $sp) (i64.const 8)))
        (return (i32.const 0))))
    (call $step))
  (func (export "run") (param $fuel i64) (result i32)
    (local $s i32)
    (loop $l
      (if (i64.eqz (local.get $fuel)) (then (return (i32.const 4))))
      (local.set $s (call $stepx))
      (if (local.get $s) (then (return (local.get $s))))
      (local.set $fuel (i64.sub (local.get $fuel) (i64.const 1)))
      (br $l))
    (i32.const 0))
)
