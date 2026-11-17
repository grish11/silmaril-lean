;; glibcrun: `extrun` (../../proc/wat/extrun.wat) plus the start-up contract of a glibc-linked
;; program, for any simulator following docs/projects/wasm-sim-abi.md. Foreign calls ([lo, hi) set by `set_ext`) go to the
;; `ffi` library by value (SysV: rdi rsi rdx rcx r8 r9 -> rax, then `ret`), except:
;;
;;   START   = EXT_BASE + 16*3  (`__libc_start_main`, called by crt1's `_start`):
;;             main := rdi, argc := rsi, argv := rdx;  rdi := argc, rsi := argv,
;;             rdx := argv + 8 (argc + 1) (envp), [rsp] := MAINRET, rip := main.
;;             I.e. `__libc_start_main(main, argc, argv, ...) = exit(main(argc, argv, envp))`
;;             with NOTHING else of glibc's start-up.
;;   MAINRET = EXT_BASE + 0xff0: main returned; `ffi.call(EXIT, rax)` (= `exit(rax)`).
;;
;; The sentinel return address 0xFFFF_FFFF_FFFF_F000 stops with status 1.
(module
  (import "core" "get" (func $get (param i32) (result i64)))
  (import "core" "set" (func $set (param i32 i64)))
  (import "core" "modelled" (func $modelled (param i32) (result i32)))
  (import "core" "step" (func $step (result i32)))
  (import "ffi" "call" (func $ffi_call (param i64 i64 i64 i64 i64 i64 i64) (result i32)))
  (import "ffi" "ret" (func $ffi_ret (result i64)))
  (import "mem" "load64" (func $ld64 (param i64) (result i64)))
  (import "mem" "store64" (func $st64 (param i64 i64)))
  (export "get" (func $get))
  (export "set" (func $set))
  (export "modelled" (func $modelled))
  (global $lo (mut i64) (i64.const 0))
  (global $hi (mut i64) (i64.const 0))
  (global $START i64 (i64.const 0x7f0000000030))
  (global $EXIT i64 (i64.const 0x7f0000000040))
  (global $MAINRET i64 (i64.const 0x7f0000000ff0))
  (func (export "set_ext") (param $lo i64) (param $hi i64)
    (global.set $lo (local.get $lo)) (global.set $hi (local.get $hi)))
  (func $stepx (export "step") (result i32)
    (local $rip i64) (local $s i32) (local $sp i64) (local $argc i64) (local $argv i64)
    (local.set $rip (call $get (i32.const 16)))
    (if (i64.eq (local.get $rip) (i64.const 0xFFFFFFFFFFFFF000)) (then (return (i32.const 1))))
    (if (i64.eq (local.get $rip) (global.get $START))
      (then
        (local.set $argc (call $get (i32.const 6)))
        (local.set $argv (call $get (i32.const 2)))
        (call $set (i32.const 16) (call $get (i32.const 7)))
        (call $set (i32.const 7) (local.get $argc))
        (call $set (i32.const 6) (local.get $argv))
        (call $set (i32.const 2) (i64.add (local.get $argv)
          (i64.shl (i64.add (local.get $argc) (i64.const 1)) (i64.const 3))))
        (call $st64 (call $get (i32.const 4)) (global.get $MAINRET))
        (return (i32.const 0))))
    (if (i64.eq (local.get $rip) (global.get $MAINRET))
      (then
        (local.set $s (call $ffi_call (global.get $EXIT) (call $get (i32.const 0))
          (i64.const 0) (i64.const 0) (i64.const 0) (i64.const 0) (i64.const 0)))
        (return (select (local.get $s) (i32.const 1) (local.get $s)))))
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
