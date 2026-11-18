;; Core of every RV64 simulator: fetch / decode dispatch (`step`), `run`, and the
;; instruction-field helpers. Decoding mirrors Silmaril.RiscV.Ext.decode: a word
;; is accepted iff it is the canonical encoding of an instruction of the
;; included groups; everything else (including FENCE, CSR*, compressed words)
;; is status 2 with no state change.
;;
;; Status: 0 ok, 1 halted (EBREAK = Lean `stopped`; pc = sentinel; exit
;; syscall), 2 undecodable/unsupported, 3 fault (misaligned pc, branch/jump
;; target or data address, as in Ext.MState.step; a trap in a `mem.*` import is
;; a fault reported by the embedder), 4 out of fuel.

(global $fuel_left (export "fuel_left") (mut i64) (i64.const 0))

(func $rd (param $w i32) (result i32) (i32.and (i32.shr_u (local.get $w) (i32.const 7)) (i32.const 31)))
(func $rs1 (param $w i32) (result i32) (i32.and (i32.shr_u (local.get $w) (i32.const 15)) (i32.const 31)))
(func $rs2 (param $w i32) (result i32) (i32.and (i32.shr_u (local.get $w) (i32.const 20)) (i32.const 31)))
(func $f3 (param $w i32) (result i32) (i32.and (i32.shr_u (local.get $w) (i32.const 12)) (i32.const 7)))
(func $f7 (param $w i32) (result i32) (i32.shr_u (local.get $w) (i32.const 25)))
;; sign-extended I, S, B, J, U immediates as i64
(func $immI (param $w i32) (result i64) (i64.extend_i32_s (i32.shr_s (local.get $w) (i32.const 20))))
(func $immS (param $w i32) (result i64)
  (i64.extend_i32_s (i32.or
    (i32.shl (i32.shr_s (local.get $w) (i32.const 25)) (i32.const 5))
    (i32.and (i32.shr_u (local.get $w) (i32.const 7)) (i32.const 31)))))
(func $immB (param $w i32) (result i64)
  (i64.extend_i32_s (i32.or (i32.or
    (i32.shl (i32.shr_s (local.get $w) (i32.const 31)) (i32.const 12))
    (i32.shl (i32.and (i32.shr_u (local.get $w) (i32.const 7)) (i32.const 1)) (i32.const 11)))
    (i32.or
      (i32.shl (i32.and (i32.shr_u (local.get $w) (i32.const 25)) (i32.const 63)) (i32.const 5))
      (i32.shl (i32.and (i32.shr_u (local.get $w) (i32.const 8)) (i32.const 15)) (i32.const 1))))))
(func $immJ (param $w i32) (result i64)
  (i64.extend_i32_s (i32.or (i32.or
    (i32.shl (i32.shr_s (local.get $w) (i32.const 31)) (i32.const 20))
    (i32.and (local.get $w) (i32.const 0xFF000)))
    (i32.or
      (i32.shl (i32.and (i32.shr_u (local.get $w) (i32.const 20)) (i32.const 1)) (i32.const 11))
      (i32.shl (i32.and (i32.shr_u (local.get $w) (i32.const 21)) (i32.const 0x3FF)) (i32.const 1))))))
(func $immU (param $w i32) (result i64)
  (i64.extend_i32_s (i32.and (local.get $w) (i32.const 0xFFFFF000))))

;; pc := pc + 4 (sequential retirement)
(func $next (call $pc_set (i64.add (call $pc_get) (i64.const 4))))

(func $step (export "step") (result i32)
  (local $pc i64) (local $w i32)
  (local.set $pc (call $pc_get))
  ;; sentinel return address (docs/projects/wasm-sim-abi.md): halted
  (if (i64.eq (local.get $pc) (i64.const 0xFFFFFFFFFFFFF000)) (then (return (i32.const 1))))
  ;; Ext.fetch: pc must be four-byte aligned (no C extension)
  (if (i32.wrap_i64 (i64.and (local.get $pc) (i64.const 3))) (then (return (i32.const 3))))
  (local.set $w (i32.wrap_i64 (call $fetch (local.get $pc))))
  (if (i32.ne (i32.and (local.get $w) (i32.const 3)) (i32.const 3)) (then (return (i32.const 2))))
  (block $bad (block $system (block $jal (block $jalr (block $branch (block $op32 (block $lui
  (block $op (block $store (block $opimm32 (block $auipc (block $opimm (block $load
    (br_table
      $load $bad $bad $bad $opimm $auipc $opimm32 $bad
      $store $bad $bad $bad $op $lui $op32 $bad
      $bad $bad $bad $bad $bad $bad $bad $bad
      $branch $jalr $bad $jal $system $bad $bad $bad
      (i32.and (i32.shr_u (local.get $w) (i32.const 2)) (i32.const 31))))
    (return (call $d_load (local.get $w))))      ;; 0x03
    (return (call $d_opimm (local.get $w))))     ;; 0x13
    (return (call $d_auipc (local.get $w))))     ;; 0x17
    (return (call $d_opimm32 (local.get $w))))   ;; 0x1B
    (return (call $d_store (local.get $w))))     ;; 0x23
    (return (if (result i32) (i32.eq (call $f7 (local.get $w)) (i32.const 1))  ;; 0x33
      (then (call $d_mul (local.get $w))) (else (call $d_op (local.get $w))))))
    (return (call $d_lui (local.get $w))))       ;; 0x37
    (return (if (result i32) (i32.eq (call $f7 (local.get $w)) (i32.const 1))  ;; 0x3B
      (then (call $d_mul32 (local.get $w))) (else (call $d_op32 (local.get $w))))))
    (return (call $d_branch (local.get $w))))    ;; 0x63
    (return (call $d_jalr (local.get $w))))      ;; 0x67
    (return (call $d_jal (local.get $w))))       ;; 0x6F
    ;; 0x73 SYSTEM: only the exact words of EBREAK and ECALL
    (if (i32.eq (local.get $w) (i32.const 0x00100073)) (then (return (call $d_ebreak (local.get $w)))))
    (if (i32.eq (local.get $w) (i32.const 0x00000073)) (then (return (call $d_ecall (local.get $w)))))
    (return (i32.const 2)))
  (i32.const 2))

(func $run (export "run") (param $fuel i64) (result i32)
  (local $s i32)
  (global.set $fuel_left (local.get $fuel))
  (loop $l
    (if (i64.eqz (global.get $fuel_left)) (then (return (i32.const 4))))
    (local.set $s (call $step))
    (if (local.get $s) (then (return (local.get $s))))
    (global.set $fuel_left (i64.sub (global.get $fuel_left) (i64.const 1)))
    (br $l))
  (unreachable))

;; low32 of a register (Ext.low32)
(func $lo32 (param $r i32) (result i32) (i32.wrap_i64 (call $rget (local.get $r))))
