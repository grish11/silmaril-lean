;; RV64 simulator: state M, fetch Import, groups ["base"]
;; assembled by tools/wasm-sim (rv64) from examples/wasm-sim/rv64/parts
(module
;; ---- fetch-import.wat (imports)
;; P-mem fetch: the instruction word is read through the `mem.load32` import,
;; like every data access (Silmaril.RiscV.Ext.fetch reads the current memory, so
;; stores to code are visible to later fetches).
(import "mem" "load32" (func $mem_load32 (param i64) (result i64)))

;; ---- state-m.wat (imports)

;; ---- core.wat (imports)

;; ---- grp-base.wat (imports)

;; ---- fetch-import.wat

(func $fetch (param $pc i64) (result i64) (call $mem_load32 (local.get $pc)))

;; ---- state-m.wat
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

;; ---- stubs
(func $d_opimm32 (param i32) (result i32) (i32.const 2)) ;; group `word` absent
(func $d_op32 (param i32) (result i32) (i32.const 2)) ;; group `word` absent
(func $d_mul (param i32) (result i32) (i32.const 2)) ;; group `mul` absent
(func $d_mul32 (param i32) (result i32) (i32.const 2)) ;; group `mul` absent
(func $d_load (param i32) (result i32) (i32.const 2)) ;; group `mem` absent
(func $d_store (param i32) (result i32) (i32.const 2)) ;; group `mem` absent
(func $d_branch (param i32) (result i32) (i32.const 2)) ;; group `ctrl` absent
(func $d_jal (param i32) (result i32) (i32.const 2)) ;; group `ctrl` absent
(func $d_jalr (param i32) (result i32) (i32.const 2)) ;; group `ctrl` absent
(func $d_ebreak (param i32) (result i32) (i32.const 2)) ;; group `ctrl` absent
(func $d_ecall (param i32) (result i32) (i32.const 2)) ;; group `sys` absent
)
