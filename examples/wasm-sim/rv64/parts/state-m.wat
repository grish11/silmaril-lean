;; State representation M (docs/projects/wasm-sim-abi.md): exported memory
;; `state` holding Linux arch/riscv `struct user_regs_struct` (32 x u64:
;; pc, ra, sp, gp, tp, t0-2, s0-1, a0-7, s2-11, t3-6), i.e. byte offset 0 = pc
;; and byte offset 8*i = x_i for i = 1..31. The u64 valid mask follows at
;; offset 256: bit loc set = location defined. x0 (bit 0) is always defined.
;; The slot at offset 0 is pc, not x0: x0 reads 0 and its writes are discarded.
;;
;; Validity: `set` and every register write by an instruction set the bit;
;; `step` does not consult the mask (it reads 0 for a never-written register).
(memory $state (export "state") 1)
(data (memory $state) (i32.const 256) "\01")

(func $rget (param $r i32) (result i64)
  (if (result i64) (local.get $r)
    (then (i64.load $state (i32.shl (local.get $r) (i32.const 3))))
    (else (i64.const 0))))
(func $rset (param $r i32) (param $v i64)
  (if (local.get $r)
    (then
      (i64.store $state (i32.shl (local.get $r) (i32.const 3)) (local.get $v))
      (i64.store $state offset=256 (i32.const 0)
        (i64.or (i64.load $state offset=256 (i32.const 0))
                (i64.shl (i64.const 1) (i64.extend_i32_u (local.get $r))))))))
(func $pc_get (result i64) (i64.load $state (i32.const 0)))
(func $pc_set (param $v i64) (i64.store $state (i32.const 0) (local.get $v)))

;; ABI: locations 0..31 = x0..x31, 32 = pc.
(func (export "get") (param $loc i32) (result i64)
  (if (result i64) (i32.lt_u (local.get $loc) (i32.const 32))
    (then (call $rget (local.get $loc)))
    (else (if (result i64) (i32.eq (local.get $loc) (i32.const 32))
      (then (call $pc_get)) (else (i64.const 0))))))
(func (export "set") (param $loc i32) (param $v i64)
  (if (i32.lt_u (local.get $loc) (i32.const 32))
    (then (call $rset (local.get $loc) (local.get $v)))
    (else (if (i32.eq (local.get $loc) (i32.const 32))
      (then
        (call $pc_set (local.get $v))
        (i64.store $state offset=256 (i32.const 0)
          (i64.or (i64.load $state offset=256 (i32.const 0)) (i64.const 0x100000000))))))))
(func (export "modelled") (param $loc i32) (result i32)
  (i32.le_u (local.get $loc) (i32.const 32)))
