;; sysv: the System V AMD64 call wrapper (docs/wasm-sim-abi.md) over any simulator
;; with the simulator ABI, docs/wasm-sim-abi.md and a memory model.
;;
;; Descriptor at `desc` (>= 16; bytes 0..15 hold constants) in the exported memory (u64 LE words):
;;   +0 target, +8 nint (<= 6), +16 int_args[6], +64 nstack, +72 stack_args[nstack],
;;   then the result area: rax, rdx, status.
;;
;; sysv_call(desc) -> rax:
;;   1. reads the caller's rsp R from the simulator; places the stack arguments at
;;      S = (R - 8*nstack) & ~15 (so the first stack argument is 16-byte aligned) and the
;;      sentinel return address 0xFFFF_FFFF_FFFF_F000 at S - 8; rsp := S - 8 (≡ 8 mod 16);
;;   2. rdi rsi rdx rcx r8 r9 := int_args[0..nint) (the others keep their values);
;;   3. records rbx rbp r12 r13 r14 r15; checks AbiEntry by reading back [rsp];
;;   4. rip := target; runs the simulator (fuel set by `set_fuel`, default 2^32 steps);
;;   5. writes rax, rdx and a status word, restores rsp := R.
;; Status bits (0 = the call meets AbiReturn, see docs/wasm-sim-abi.md):
;;   bit 0      the simulator stopped elsewhere than at the sentinel (sim status in bits 8..15)
;;   bit 1      rsp after the return /= entry rsp + 8
;;   bits 2..7  rbx rbp r12 r13 r14 r15 not preserved (one bit each)
;;   bit 16     malformed descriptor (nint > 6)
;;   bit 17     AbiEntry check failed (entry rsp mod 16 /= 8 or [rsp] /= sentinel)
(module
  (import "sim" "get" (func $get (param i32) (result i64)))
  (import "sim" "set" (func $set (param i32 i64)))
  (import "sim" "run" (func $run (param i64) (result i32)))
  (import "mem" "load64" (func $ld64 (param i64) (result i64)))
  (import "mem" "store64" (func $st64 (param i64 i64)))
  (memory (export "memory") 1)
  (global $fuel (mut i64) (i64.const 0x100000000))
  (global $SENTINEL i64 (i64.const 0xFFFFFFFFFFFFF000))
  ;; callee-saved locations in status-bit order: rbx rbp r12 r13 r14 r15
  (data (i32.const 0) "\03\05\0c\0d\0e\0f")
  ;; argument registers: rdi rsi rdx rcx r8 r9
  (data (i32.const 8) "\07\06\02\01\08\09")

  (func (export "set_fuel") (param $f i64) (global.set $fuel (local.get $f)))

  (func (export "sysv_call") (param $d i32) (result i64)
    (local $nint i32) (local $nstack i32) (local $res i32) (local $i i32)
    (local $r i64) (local $s i64) (local $entry i64) (local $st i64) (local $sim i32)
    (local $saved0 i64) (local $saved1 i64) (local $saved2 i64)
    (local $saved3 i64) (local $saved4 i64) (local $saved5 i64)
    (local.set $nint (i32.wrap_i64 (i64.load offset=8 (local.get $d))))
    (local.set $nstack (i32.wrap_i64 (i64.load offset=64 (local.get $d))))
    (local.set $res (i32.add (i32.add (local.get $d) (i32.const 72)) (i32.shl (local.get $nstack) (i32.const 3))))
    (if (i32.gt_u (local.get $nint) (i32.const 6))
      (then (i64.store offset=16 (local.get $res) (i64.const 0x10000)) (return (i64.const 0))))
    ;; 1. stack
    (local.set $r (call $get (i32.const 4)))
    (local.set $s (i64.and (i64.sub (local.get $r) (i64.extend_i32_u (i32.shl (local.get $nstack) (i32.const 3)))) (i64.const -16)))
    (local.set $i (i32.const 0))
    (block $o (loop $l
      (br_if $o (i32.ge_u (local.get $i) (local.get $nstack)))
      (call $st64 (i64.add (local.get $s) (i64.extend_i32_u (i32.shl (local.get $i) (i32.const 3))))
                  (i64.load offset=72 (i32.add (local.get $d) (i32.shl (local.get $i) (i32.const 3)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (local.set $entry (i64.sub (local.get $s) (i64.const 8)))
    (call $st64 (local.get $entry) (global.get $SENTINEL))
    (call $set (i32.const 4) (local.get $entry))
    ;; 2. integer arguments
    (local.set $i (i32.const 0))
    (block $o (loop $l
      (br_if $o (i32.ge_u (local.get $i) (local.get $nint)))
      (call $set (i32.load8_u offset=8 (local.get $i))
                 (i64.load offset=16 (i32.add (local.get $d) (i32.shl (local.get $i) (i32.const 3)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    ;; 3. callee-saved snapshot, AbiEntry
    (local.set $saved0 (call $get (i32.const 3)))  (local.set $saved1 (call $get (i32.const 5)))
    (local.set $saved2 (call $get (i32.const 12))) (local.set $saved3 (call $get (i32.const 13)))
    (local.set $saved4 (call $get (i32.const 14))) (local.set $saved5 (call $get (i32.const 15)))
    (if (i32.or (i64.ne (i64.and (call $get (i32.const 4)) (i64.const 15)) (i64.const 8))
                (i64.ne (call $ld64 (call $get (i32.const 4))) (global.get $SENTINEL)))
      (then (local.set $st (i64.or (local.get $st) (i64.const 0x20000)))))
    ;; 4. run
    (call $set (i32.const 16) (i64.load (local.get $d)))
    (local.set $sim (call $run (global.get $fuel)))
    ;; 5. checks
    (if (i32.or (i32.ne (local.get $sim) (i32.const 1)) (i64.ne (call $get (i32.const 16)) (global.get $SENTINEL)))
      (then (local.set $st (i64.or (local.get $st)
              (i64.or (i64.const 1) (i64.shl (i64.extend_i32_u (i32.and (local.get $sim) (i32.const 0xff))) (i64.const 8)))))))
    (if (i64.ne (call $get (i32.const 4)) (i64.add (local.get $entry) (i64.const 8)))
      (then (local.set $st (i64.or (local.get $st) (i64.const 2)))))
    (if (i64.ne (call $get (i32.const 3)) (local.get $saved0)) (then (local.set $st (i64.or (local.get $st) (i64.const 4)))))
    (if (i64.ne (call $get (i32.const 5)) (local.get $saved1)) (then (local.set $st (i64.or (local.get $st) (i64.const 8)))))
    (if (i64.ne (call $get (i32.const 12)) (local.get $saved2)) (then (local.set $st (i64.or (local.get $st) (i64.const 16)))))
    (if (i64.ne (call $get (i32.const 13)) (local.get $saved3)) (then (local.set $st (i64.or (local.get $st) (i64.const 32)))))
    (if (i64.ne (call $get (i32.const 14)) (local.get $saved4)) (then (local.set $st (i64.or (local.get $st) (i64.const 64)))))
    (if (i64.ne (call $get (i32.const 15)) (local.get $saved5)) (then (local.set $st (i64.or (local.get $st) (i64.const 128)))))
    (i64.store (local.get $res) (call $get (i32.const 0)))
    (i64.store offset=8 (local.get $res) (call $get (i32.const 2)))
    (i64.store offset=16 (local.get $res) (local.get $st))
    (call $set (i32.const 4) (local.get $r))
    (call $get (i32.const 0)))
)
