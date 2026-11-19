;; RV64 simulator: state G, fetch Import, groups ["base", "word", "mul"]
;; assembled by tools/wasm-sim (rv64) from examples/wasm-sim/rv64/parts
(module
;; ---- fetch-import.wat (imports)
;; P-mem fetch: the instruction word is read through the `mem.load32` import,
;; like every data access (Silmaril.RiscV.Ext.fetch reads the current memory, so
;; stores to code are visible to later fetches).
(import "mem" "load32" (func $mem_load32 (param i64) (result i64)))

;; ---- state-g.wat (imports)

;; ---- core.wat (imports)

;; ---- grp-base.wat (imports)

;; ---- grp-word.wat (imports)

;; ---- grp-mul.wat (imports)

;; ---- fetch-import.wat

(func $fetch (param $pc i64) (result i64) (call $mem_load32 (local.get $pc)))

;; ---- state-g.wat
;; State representation G (docs/projects/wasm-sim-abi.md): one mutable i64
;; global per location: x1..x31 and pc (loc 32). x0 has no global: it reads 0 and
;; writes are discarded, as in Silmaril.RiscV.State.read/write.
;; Generated once by a short script, then kept as source.
(global $x1 (mut i64) (i64.const 0))
(global $x2 (mut i64) (i64.const 0))
(global $x3 (mut i64) (i64.const 0))
(global $x4 (mut i64) (i64.const 0))
(global $x5 (mut i64) (i64.const 0))
(global $x6 (mut i64) (i64.const 0))
(global $x7 (mut i64) (i64.const 0))
(global $x8 (mut i64) (i64.const 0))
(global $x9 (mut i64) (i64.const 0))
(global $x10 (mut i64) (i64.const 0))
(global $x11 (mut i64) (i64.const 0))
(global $x12 (mut i64) (i64.const 0))
(global $x13 (mut i64) (i64.const 0))
(global $x14 (mut i64) (i64.const 0))
(global $x15 (mut i64) (i64.const 0))
(global $x16 (mut i64) (i64.const 0))
(global $x17 (mut i64) (i64.const 0))
(global $x18 (mut i64) (i64.const 0))
(global $x19 (mut i64) (i64.const 0))
(global $x20 (mut i64) (i64.const 0))
(global $x21 (mut i64) (i64.const 0))
(global $x22 (mut i64) (i64.const 0))
(global $x23 (mut i64) (i64.const 0))
(global $x24 (mut i64) (i64.const 0))
(global $x25 (mut i64) (i64.const 0))
(global $x26 (mut i64) (i64.const 0))
(global $x27 (mut i64) (i64.const 0))
(global $x28 (mut i64) (i64.const 0))
(global $x29 (mut i64) (i64.const 0))
(global $x30 (mut i64) (i64.const 0))
(global $x31 (mut i64) (i64.const 0))
(global $pc (mut i64) (i64.const 0))

;; Read register r (0..31) by dynamic index.
(func $rget (param $r i32) (result i64)
  (block $dflt (block $c31 (block $c30 (block $c29 (block $c28 (block $c27 (block $c26 (block $c25 (block $c24 (block $c23 (block $c22 (block $c21 (block $c20 (block $c19 (block $c18 (block $c17 (block $c16 (block $c15 (block $c14 (block $c13 (block $c12 (block $c11 (block $c10 (block $c9 (block $c8 (block $c7 (block $c6 (block $c5 (block $c4 (block $c3 (block $c2 (block $c1 (block $c0 (br_table $c0 $c1 $c2 $c3 $c4 $c5 $c6 $c7 $c8 $c9 $c10 $c11 $c12 $c13 $c14 $c15 $c16 $c17 $c18 $c19 $c20 $c21 $c22 $c23 $c24 $c25 $c26 $c27 $c28 $c29 $c30 $c31 $dflt (local.get $r)))
  (return (i64.const 0)))
  (return (global.get $x1)))
  (return (global.get $x2)))
  (return (global.get $x3)))
  (return (global.get $x4)))
  (return (global.get $x5)))
  (return (global.get $x6)))
  (return (global.get $x7)))
  (return (global.get $x8)))
  (return (global.get $x9)))
  (return (global.get $x10)))
  (return (global.get $x11)))
  (return (global.get $x12)))
  (return (global.get $x13)))
  (return (global.get $x14)))
  (return (global.get $x15)))
  (return (global.get $x16)))
  (return (global.get $x17)))
  (return (global.get $x18)))
  (return (global.get $x19)))
  (return (global.get $x20)))
  (return (global.get $x21)))
  (return (global.get $x22)))
  (return (global.get $x23)))
  (return (global.get $x24)))
  (return (global.get $x25)))
  (return (global.get $x26)))
  (return (global.get $x27)))
  (return (global.get $x28)))
  (return (global.get $x29)))
  (return (global.get $x30)))
  (return (global.get $x31)))
  (unreachable))
;; Write register r (0..31); x0 discarded.
(func $rset (param $r i32) (param $v i64)
  (block $dflt (block $c31 (block $c30 (block $c29 (block $c28 (block $c27 (block $c26 (block $c25 (block $c24 (block $c23 (block $c22 (block $c21 (block $c20 (block $c19 (block $c18 (block $c17 (block $c16 (block $c15 (block $c14 (block $c13 (block $c12 (block $c11 (block $c10 (block $c9 (block $c8 (block $c7 (block $c6 (block $c5 (block $c4 (block $c3 (block $c2 (block $c1 (block $c0 (br_table $c0 $c1 $c2 $c3 $c4 $c5 $c6 $c7 $c8 $c9 $c10 $c11 $c12 $c13 $c14 $c15 $c16 $c17 $c18 $c19 $c20 $c21 $c22 $c23 $c24 $c25 $c26 $c27 $c28 $c29 $c30 $c31 $dflt (local.get $r)))
  (return))
  (global.set $x1 (local.get $v)) (return))
  (global.set $x2 (local.get $v)) (return))
  (global.set $x3 (local.get $v)) (return))
  (global.set $x4 (local.get $v)) (return))
  (global.set $x5 (local.get $v)) (return))
  (global.set $x6 (local.get $v)) (return))
  (global.set $x7 (local.get $v)) (return))
  (global.set $x8 (local.get $v)) (return))
  (global.set $x9 (local.get $v)) (return))
  (global.set $x10 (local.get $v)) (return))
  (global.set $x11 (local.get $v)) (return))
  (global.set $x12 (local.get $v)) (return))
  (global.set $x13 (local.get $v)) (return))
  (global.set $x14 (local.get $v)) (return))
  (global.set $x15 (local.get $v)) (return))
  (global.set $x16 (local.get $v)) (return))
  (global.set $x17 (local.get $v)) (return))
  (global.set $x18 (local.get $v)) (return))
  (global.set $x19 (local.get $v)) (return))
  (global.set $x20 (local.get $v)) (return))
  (global.set $x21 (local.get $v)) (return))
  (global.set $x22 (local.get $v)) (return))
  (global.set $x23 (local.get $v)) (return))
  (global.set $x24 (local.get $v)) (return))
  (global.set $x25 (local.get $v)) (return))
  (global.set $x26 (local.get $v)) (return))
  (global.set $x27 (local.get $v)) (return))
  (global.set $x28 (local.get $v)) (return))
  (global.set $x29 (local.get $v)) (return))
  (global.set $x30 (local.get $v)) (return))
  (global.set $x31 (local.get $v)) (return))
  (unreachable))
(func $pc_get (result i64) (global.get $pc))
(func $pc_set (param $v i64) (global.set $pc (local.get $v)))

;; ABI: locations 0..31 = x0..x31, 32 = pc.
(func (export "get") (param $loc i32) (result i64)
  (if (result i64) (i32.lt_u (local.get $loc) (i32.const 32))
    (then (call $rget (local.get $loc)))
    (else (if (result i64) (i32.eq (local.get $loc) (i32.const 32))
      (then (global.get $pc)) (else (i64.const 0))))))
(func (export "set") (param $loc i32) (param $v i64)
  (if (i32.lt_u (local.get $loc) (i32.const 32))
    (then (call $rset (local.get $loc) (local.get $v)))
    (else (if (i32.eq (local.get $loc) (i32.const 32))
      (then (global.set $pc (local.get $v)))))))
(func (export "modelled") (param $loc i32) (result i32)
  (i32.le_u (local.get $loc) (i32.const 32)))

;; ---- core.wat
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

;; ---- grp-base.wat
;; Group `base`: exactly the 21 instructions of Silmaril.RiscV.Instr
;; (Silmaril/Raw/Machine/RiscV/Basic.lean): OP-IMM (ADDI SLTI SLTIU XORI ORI ANDI
;; SLLI SRLI SRAI), OP with funct7 0/0x20 (ADD SUB SLL SLT SLTU XOR SRL SRA OR
;; AND), LUI, AUIPC. Each `i_*` method is `RiscV.step` for one instruction:
;; operands read from the incoming state, rd written (x0 discarded), pc += 4.
;; Method immediates are the sign-extended 64-bit values (`imm.signExtend 64`);
;; shift amounts are taken mod 64 (Lean: 6-bit `amount`).

(func $d_opimm (param $w i32) (result i32)
  (local $rd i32) (local $rs1 i32) (local $imm i64)
  (local.set $rd (call $rd (local.get $w)))
  (local.set $rs1 (call $rs1 (local.get $w)))
  (local.set $imm (call $immI (local.get $w)))
  (block $bad (block $f7 (block $f6 (block $f5 (block $f4 (block $f3 (block $f2 (block $f1 (block $f0
    (br_table $f0 $f1 $f2 $f3 $f4 $f5 $f6 $f7 (call $f3 (local.get $w))))
    (call $x_addi (local.get $rd) (local.get $rs1) (local.get $imm)) (return (i32.const 0)))
    ;; SLLI: funct6 = 0
    (br_if $bad (i32.shr_u (local.get $w) (i32.const 26)))
    (call $x_slli (local.get $rd) (local.get $rs1) (i64.and (local.get $imm) (i64.const 63))) (return (i32.const 0)))
    (call $x_slti (local.get $rd) (local.get $rs1) (local.get $imm)) (return (i32.const 0)))
    (call $x_sltiu (local.get $rd) (local.get $rs1) (local.get $imm)) (return (i32.const 0)))
    (call $x_xori (local.get $rd) (local.get $rs1) (local.get $imm)) (return (i32.const 0)))
    ;; SRLI funct6 = 0, SRAI funct6 = 0x10
    (if (i32.eqz (i32.shr_u (local.get $w) (i32.const 26)))
      (then (call $x_srli (local.get $rd) (local.get $rs1) (i64.and (local.get $imm) (i64.const 63)))
            (return (i32.const 0))))
    (if (i32.eq (i32.shr_u (local.get $w) (i32.const 26)) (i32.const 0x10))
      (then (call $x_srai (local.get $rd) (local.get $rs1) (i64.and (local.get $imm) (i64.const 63)))
            (return (i32.const 0))))
    (br $bad))
    (call $x_ori (local.get $rd) (local.get $rs1) (local.get $imm)) (return (i32.const 0)))
    (call $x_andi (local.get $rd) (local.get $rs1) (local.get $imm)) (return (i32.const 0)))
  (i32.const 2))

;; OP with funct7 != 1 (funct7 = 1 is the M extension, dispatched by core)
(func $d_op (param $w i32) (result i32)
  (local $rd i32) (local $rs1 i32) (local $rs2 i32) (local $f7 i32)
  (local.set $rd (call $rd (local.get $w)))
  (local.set $rs1 (call $rs1 (local.get $w)))
  (local.set $rs2 (call $rs2 (local.get $w)))
  (local.set $f7 (call $f7 (local.get $w)))
  (if (i32.eq (local.get $f7) (i32.const 0x20))
    (then
      (if (i32.eqz (call $f3 (local.get $w)))
        (then (call $x_sub (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0))))
      (if (i32.eq (call $f3 (local.get $w)) (i32.const 5))
        (then (call $x_sra (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0))))
      (return (i32.const 2))))
  (if (local.get $f7) (then (return (i32.const 2))))
  (block $f7 (block $f6 (block $f5 (block $f4 (block $f3 (block $f2 (block $f1 (block $f0
    (br_table $f0 $f1 $f2 $f3 $f4 $f5 $f6 $f7 (call $f3 (local.get $w))))
    (call $x_add (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_sll (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_slt (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_sltu (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_xor (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_srl (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_or (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
  (call $x_and (local.get $rd) (local.get $rs1) (local.get $rs2)) (i32.const 0))

(func $d_lui (param $w i32) (result i32)
  (call $x_lui (call $rd (local.get $w)) (call $immU (local.get $w))) (i32.const 0))
(func $d_auipc (param $w i32) (result i32)
  (call $x_auipc (call $rd (local.get $w)) (call $immU (local.get $w))) (i32.const 0))

;; ImmOp.eval / ShiftOp.eval
(func $x_addi (export "i_addi") (param $rd i32) (param $rs1 i32) (param $imm i64)
  (call $rset (local.get $rd) (i64.add (call $rget (local.get $rs1)) (local.get $imm))) (call $next))
(func $x_slti (export "i_slti") (param $rd i32) (param $rs1 i32) (param $imm i64)
  (call $rset (local.get $rd) (i64.extend_i32_u (i64.lt_s (call $rget (local.get $rs1)) (local.get $imm)))) (call $next))
(func $x_sltiu (export "i_sltiu") (param $rd i32) (param $rs1 i32) (param $imm i64)
  (call $rset (local.get $rd) (i64.extend_i32_u (i64.lt_u (call $rget (local.get $rs1)) (local.get $imm)))) (call $next))
(func $x_xori (export "i_xori") (param $rd i32) (param $rs1 i32) (param $imm i64)
  (call $rset (local.get $rd) (i64.xor (call $rget (local.get $rs1)) (local.get $imm))) (call $next))
(func $x_ori (export "i_ori") (param $rd i32) (param $rs1 i32) (param $imm i64)
  (call $rset (local.get $rd) (i64.or (call $rget (local.get $rs1)) (local.get $imm))) (call $next))
(func $x_andi (export "i_andi") (param $rd i32) (param $rs1 i32) (param $imm i64)
  (call $rset (local.get $rd) (i64.and (call $rget (local.get $rs1)) (local.get $imm))) (call $next))
(func $x_slli (export "i_slli") (param $rd i32) (param $rs1 i32) (param $sh i64)
  (call $rset (local.get $rd) (i64.shl (call $rget (local.get $rs1)) (local.get $sh))) (call $next))
(func $x_srli (export "i_srli") (param $rd i32) (param $rs1 i32) (param $sh i64)
  (call $rset (local.get $rd) (i64.shr_u (call $rget (local.get $rs1)) (local.get $sh))) (call $next))
(func $x_srai (export "i_srai") (param $rd i32) (param $rs1 i32) (param $sh i64)
  (call $rset (local.get $rd) (i64.shr_s (call $rget (local.get $rs1)) (local.get $sh))) (call $next))
;; RegOp.eval (Wasm shifts use the count mod 64 = Lean's `y.setWidth 6`)
(func $x_add (export "i_add") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.add (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_sub (export "i_sub") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.sub (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_sll (export "i_sll") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.shl (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_slt (export "i_slt") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_u (i64.lt_s (call $rget (local.get $rs1)) (call $rget (local.get $rs2))))) (call $next))
(func $x_sltu (export "i_sltu") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_u (i64.lt_u (call $rget (local.get $rs1)) (call $rget (local.get $rs2))))) (call $next))
(func $x_xor (export "i_xor") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.xor (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_srl (export "i_srl") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.shr_u (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_sra (export "i_sra") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.shr_s (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_or (export "i_or") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.or (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_and (export "i_and") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.and (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
;; UpperOp.eval: `imm` is the sign-extended (imm20 << 12)
(func $x_lui (export "i_lui") (param $rd i32) (param $imm i64)
  (call $rset (local.get $rd) (local.get $imm)) (call $next))
(func $x_auipc (export "i_auipc") (param $rd i32) (param $imm i64)
  (call $rset (local.get $rd) (i64.add (call $pc_get) (local.get $imm))) (call $next))

;; ---- grp-word.wat
;; Group `word`: RV64I word forms of Silmaril.RiscV.Ext.Compute: ADDIW,
;; SLLIW/SRLIW/SRAIW (`shiftW`, 5-bit amount, funct7 0 / 0x20), ADDW SUBW SLLW
;; SRLW SRAW (`regW`). Results are `sext32` of a 32-bit operation on `low32`.

(func $d_opimm32 (param $w i32) (result i32)
  (local $rd i32) (local $rs1 i32) (local $f3 i32) (local $f7 i32)
  (local.set $rd (call $rd (local.get $w)))
  (local.set $rs1 (call $rs1 (local.get $w)))
  (local.set $f3 (call $f3 (local.get $w)))
  (local.set $f7 (call $f7 (local.get $w)))
  (if (i32.eqz (local.get $f3))
    (then (call $x_addiw (local.get $rd) (local.get $rs1) (call $immI (local.get $w))) (return (i32.const 0))))
  (if (i32.and (i32.eq (local.get $f3) (i32.const 1)) (i32.eqz (local.get $f7)))
    (then (call $x_slliw (local.get $rd) (local.get $rs1) (i64.extend_i32_u (call $rs2 (local.get $w))))
          (return (i32.const 0))))
  (if (i32.eq (local.get $f3) (i32.const 5))
    (then
      (if (i32.eqz (local.get $f7))
        (then (call $x_srliw (local.get $rd) (local.get $rs1) (i64.extend_i32_u (call $rs2 (local.get $w))))
              (return (i32.const 0))))
      (if (i32.eq (local.get $f7) (i32.const 0x20))
        (then (call $x_sraiw (local.get $rd) (local.get $rs1) (i64.extend_i32_u (call $rs2 (local.get $w))))
              (return (i32.const 0))))))
  (i32.const 2))

;; OP-32 with funct7 != 1
(func $d_op32 (param $w i32) (result i32)
  (local $rd i32) (local $rs1 i32) (local $rs2 i32) (local $f3 i32) (local $f7 i32)
  (local.set $rd (call $rd (local.get $w)))
  (local.set $rs1 (call $rs1 (local.get $w)))
  (local.set $rs2 (call $rs2 (local.get $w)))
  (local.set $f3 (call $f3 (local.get $w)))
  (local.set $f7 (call $f7 (local.get $w)))
  (if (i32.eqz (local.get $f7))
    (then
      (if (i32.eqz (local.get $f3))
        (then (call $x_addw (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0))))
      (if (i32.eq (local.get $f3) (i32.const 1))
        (then (call $x_sllw (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0))))
      (if (i32.eq (local.get $f3) (i32.const 5))
        (then (call $x_srlw (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0))))
      (return (i32.const 2))))
  (if (i32.eq (local.get $f7) (i32.const 0x20))
    (then
      (if (i32.eqz (local.get $f3))
        (then (call $x_subw (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0))))
      (if (i32.eq (local.get $f3) (i32.const 5))
        (then (call $x_sraw (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0))))))
  (i32.const 2))


(func $x_addiw (export "i_addiw") (param $rd i32) (param $rs1 i32) (param $imm i64)
  (call $rset (local.get $rd) (i64.extend_i32_s (i32.add (call $lo32 (local.get $rs1)) (i32.wrap_i64 (local.get $imm)))))
  (call $next))
;; shift amounts are taken mod 32 (Lean: 5-bit `amount`)
(func $x_slliw (export "i_slliw") (param $rd i32) (param $rs1 i32) (param $sh i64)
  (call $rset (local.get $rd) (i64.extend_i32_s (i32.shl (call $lo32 (local.get $rs1)) (i32.wrap_i64 (local.get $sh)))))
  (call $next))
(func $x_srliw (export "i_srliw") (param $rd i32) (param $rs1 i32) (param $sh i64)
  (call $rset (local.get $rd) (i64.extend_i32_s (i32.shr_u (call $lo32 (local.get $rs1)) (i32.wrap_i64 (local.get $sh)))))
  (call $next))
(func $x_sraiw (export "i_sraiw") (param $rd i32) (param $rs1 i32) (param $sh i64)
  (call $rset (local.get $rd) (i64.extend_i32_s (i32.shr_s (call $lo32 (local.get $rs1)) (i32.wrap_i64 (local.get $sh)))))
  (call $next))
(func $x_addw (export "i_addw") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_s (i32.add (call $lo32 (local.get $rs1)) (call $lo32 (local.get $rs2)))))
  (call $next))
(func $x_subw (export "i_subw") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_s (i32.sub (call $lo32 (local.get $rs1)) (call $lo32 (local.get $rs2)))))
  (call $next))
(func $x_sllw (export "i_sllw") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_s (i32.shl (call $lo32 (local.get $rs1)) (call $lo32 (local.get $rs2)))))
  (call $next))
(func $x_srlw (export "i_srlw") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_s (i32.shr_u (call $lo32 (local.get $rs1)) (call $lo32 (local.get $rs2)))))
  (call $next))
(func $x_sraw (export "i_sraw") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_s (i32.shr_s (call $lo32 (local.get $rs1)) (call $lo32 (local.get $rs2)))))
  (call $next))

;; ---- grp-mul.wat
;; Group `mul`: the M extension (Ext.MulOp / Ext.MulWOp). Division never traps:
;; divS/divU by zero give all ones, remS/remU by zero give the dividend, and
;; signed overflow (intMin / -1) gives intMin with remainder 0. Wasm's
;; div_s traps on that overflow, so it is special-cased.

(func $d_mul (param $w i32) (result i32)
  (local $rd i32) (local $rs1 i32) (local $rs2 i32)
  (local.set $rd (call $rd (local.get $w)))
  (local.set $rs1 (call $rs1 (local.get $w)))
  (local.set $rs2 (call $rs2 (local.get $w)))
  (block $f7 (block $f6 (block $f5 (block $f4 (block $f3 (block $f2 (block $f1 (block $f0
    (br_table $f0 $f1 $f2 $f3 $f4 $f5 $f6 $f7 (call $f3 (local.get $w))))
    (call $x_mul (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_mulh (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_mulhsu (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_mulhu (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_div (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_divu (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_rem (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
  (call $x_remu (local.get $rd) (local.get $rs1) (local.get $rs2)) (i32.const 0))

(func $d_mul32 (param $w i32) (result i32)
  (local $rd i32) (local $rs1 i32) (local $rs2 i32)
  (local.set $rd (call $rd (local.get $w)))
  (local.set $rs1 (call $rs1 (local.get $w)))
  (local.set $rs2 (call $rs2 (local.get $w)))
  (block $bad (block $f7 (block $f6 (block $f5 (block $f4 (block $f0
    (br_table $f0 $bad $bad $bad $f4 $f5 $f6 $f7 (call $f3 (local.get $w))))
    (call $x_mulw (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_divw (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_divuw (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_remw (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
    (call $x_remuw (local.get $rd) (local.get $rs1) (local.get $rs2)) (return (i32.const 0)))
  (i32.const 2))

;; high 64 bits of the unsigned 128-bit product, by 32-bit limbs
(func $mulhu64 (param $a i64) (param $b i64) (result i64)
  (local $al i64) (local $ah i64) (local $bl i64) (local $bh i64)
  (local $ll i64) (local $lh i64) (local $hl i64) (local $mid i64)
  (local.set $al (i64.and (local.get $a) (i64.const 0xFFFFFFFF)))
  (local.set $ah (i64.shr_u (local.get $a) (i64.const 32)))
  (local.set $bl (i64.and (local.get $b) (i64.const 0xFFFFFFFF)))
  (local.set $bh (i64.shr_u (local.get $b) (i64.const 32)))
  (local.set $ll (i64.mul (local.get $al) (local.get $bl)))
  (local.set $lh (i64.mul (local.get $al) (local.get $bh)))
  (local.set $hl (i64.mul (local.get $ah) (local.get $bl)))
  (local.set $mid (i64.add (i64.add (i64.shr_u (local.get $ll) (i64.const 32))
                                    (i64.and (local.get $lh) (i64.const 0xFFFFFFFF)))
                           (i64.and (local.get $hl) (i64.const 0xFFFFFFFF))))
  (i64.add (i64.add (i64.mul (local.get $ah) (local.get $bh))
                    (i64.add (i64.shr_u (local.get $lh) (i64.const 32)) (i64.shr_u (local.get $hl) (i64.const 32))))
           (i64.shr_u (local.get $mid) (i64.const 32))))
;; signed x signed: mulhu - (a<0 ? b : 0) - (b<0 ? a : 0)
(func $mulh64 (param $a i64) (param $b i64) (result i64)
  (i64.sub (i64.sub (call $mulhu64 (local.get $a) (local.get $b))
    (i64.and (i64.shr_s (local.get $a) (i64.const 63)) (local.get $b)))
    (i64.and (i64.shr_s (local.get $b) (i64.const 63)) (local.get $a))))
;; signed x unsigned: mulhu - (a<0 ? b : 0)
(func $mulhsu64 (param $a i64) (param $b i64) (result i64)
  (i64.sub (call $mulhu64 (local.get $a) (local.get $b))
    (i64.and (i64.shr_s (local.get $a) (i64.const 63)) (local.get $b))))
(func $divs64 (param $a i64) (param $b i64) (result i64)
  (if (i64.eqz (local.get $b)) (then (return (i64.const -1))))
  (if (i32.and (i64.eq (local.get $a) (i64.const 0x8000000000000000)) (i64.eq (local.get $b) (i64.const -1)))
    (then (return (local.get $a))))
  (i64.div_s (local.get $a) (local.get $b)))
(func $divu64 (param $a i64) (param $b i64) (result i64)
  (if (result i64) (i64.eqz (local.get $b)) (then (i64.const -1)) (else (i64.div_u (local.get $a) (local.get $b)))))
(func $rems64 (param $a i64) (param $b i64) (result i64)
  (if (i64.eqz (local.get $b)) (then (return (local.get $a))))
  (if (i64.eq (local.get $b) (i64.const -1)) (then (return (i64.const 0))))
  (i64.rem_s (local.get $a) (local.get $b)))
(func $remu64 (param $a i64) (param $b i64) (result i64)
  (if (result i64) (i64.eqz (local.get $b)) (then (local.get $a)) (else (i64.rem_u (local.get $a) (local.get $b)))))
(func $divs32 (param $a i32) (param $b i32) (result i32)
  (if (i32.eqz (local.get $b)) (then (return (i32.const -1))))
  (if (i32.and (i32.eq (local.get $a) (i32.const 0x80000000)) (i32.eq (local.get $b) (i32.const -1)))
    (then (return (local.get $a))))
  (i32.div_s (local.get $a) (local.get $b)))
(func $divu32 (param $a i32) (param $b i32) (result i32)
  (if (result i32) (i32.eqz (local.get $b)) (then (i32.const -1)) (else (i32.div_u (local.get $a) (local.get $b)))))
(func $rems32 (param $a i32) (param $b i32) (result i32)
  (if (i32.eqz (local.get $b)) (then (return (local.get $a))))
  (if (i32.eq (local.get $b) (i32.const -1)) (then (return (i32.const 0))))
  (i32.rem_s (local.get $a) (local.get $b)))
(func $remu32 (param $a i32) (param $b i32) (result i32)
  (if (result i32) (i32.eqz (local.get $b)) (then (local.get $a)) (else (i32.rem_u (local.get $a) (local.get $b)))))

(func $x_mul (export "i_mul") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.mul (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_mulh (export "i_mulh") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (call $mulh64 (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_mulhsu (export "i_mulhsu") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (call $mulhsu64 (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_mulhu (export "i_mulhu") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (call $mulhu64 (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_div (export "i_div") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (call $divs64 (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_divu (export "i_divu") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (call $divu64 (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_rem (export "i_rem") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (call $rems64 (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_remu (export "i_remu") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (call $remu64 (call $rget (local.get $rs1)) (call $rget (local.get $rs2)))) (call $next))
(func $x_mulw (export "i_mulw") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_s (i32.mul (call $lo32 (local.get $rs1)) (call $lo32 (local.get $rs2))))) (call $next))
(func $x_divw (export "i_divw") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_s (call $divs32 (call $lo32 (local.get $rs1)) (call $lo32 (local.get $rs2))))) (call $next))
(func $x_divuw (export "i_divuw") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_s (call $divu32 (call $lo32 (local.get $rs1)) (call $lo32 (local.get $rs2))))) (call $next))
(func $x_remw (export "i_remw") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_s (call $rems32 (call $lo32 (local.get $rs1)) (call $lo32 (local.get $rs2))))) (call $next))
(func $x_remuw (export "i_remuw") (param $rd i32) (param $rs1 i32) (param $rs2 i32)
  (call $rset (local.get $rd) (i64.extend_i32_s (call $remu32 (call $lo32 (local.get $rs1)) (call $lo32 (local.get $rs2))))) (call $next))

;; ---- stubs
(func $d_load (param i32) (result i32) (i32.const 2)) ;; group `mem` absent
(func $d_store (param i32) (result i32) (i32.const 2)) ;; group `mem` absent
(func $d_branch (param i32) (result i32) (i32.const 2)) ;; group `ctrl` absent
(func $d_jal (param i32) (result i32) (i32.const 2)) ;; group `ctrl` absent
(func $d_jalr (param i32) (result i32) (i32.const 2)) ;; group `ctrl` absent
(func $d_ebreak (param i32) (result i32) (i32.const 2)) ;; group `ctrl` absent
(func $d_ecall (param i32) (result i32) (i32.const 2)) ;; group `sys` absent
)
