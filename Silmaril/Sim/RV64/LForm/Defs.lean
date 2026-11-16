module

public import Silmaril.Sim.RV64.Mem.Defs

/-!
# Specialised per-instruction code (the L-form) for the memory-state RV64 simulator

For a register-register ALU instruction `op rd, rs1, rs2` with `op ∈ {add, sub, xor, or, and}`,
`lReg op rd rs1 rs2` is the straight-line Wasm code that `step` specialises to on that word: no
fetch, no decode, no dispatch: `x[rd] := x[rs1] op x[rs2]` (a source `x0` is the constant `0`, a
destination `x0` writes nothing) and `pc := pc + 4`, on the same memory layout.
`Silmaril.Proofs.Sim.RV64.LForm` proves it has the specialised semantics of `step` (one reference
step, same frame), so programs can be compiled to chains of such chunks (L) and still be
related to M and to the reference.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.LForm

open Silmaril.Wasm (Instr IntBinOp)
open Silmaril.RiscV (RegOp Reg)

/-- `i64.load` / `i64.store` at a constant address, memory `0`, alignment 3. -/
abbrev ld : Instr := .intLoad .i64 none ⟨0⟩ ⟨3, 0⟩
abbrev st : Instr := .intStore .i64 none ⟨0⟩ ⟨3, 0⟩
abbrev c32 (n : Nat) : Instr := .intConst .i32 (BitVec.ofNat 32 n)
abbrev c64 (n : Nat) : Instr := .intConst .i64 (BitVec.ofNat 64 n)

/-- The supported operators and their Wasm instruction. -/
def binop : RegOp → Option IntBinOp
  | .add => some .add
  | .sub => some .sub
  | .xor => some .xor
  | .or => some .or
  | .and => some .and
  | _ => none

/-- Push `x[r]`. -/
def opnd (r : Reg) : List Instr := if r = 0#5 then [c64 0] else [c32 (8 * r.toNat), ld]

/-- `pc := pc + 4`. -/
def bumpPc : List Instr := [c32 0, c32 0, ld, c64 4, .intBinOp .i64 .add, st]

/-- A chunk writing the value computed by `ops` to `rd` (nothing for `x0`), then `pc += 4`. -/
def lAlu (rd : Reg) (ops : List Instr) : List Instr :=
  (if rd = 0#5 then [] else [c32 (8 * rd.toNat)] ++ ops ++ [st]) ++ bumpPc

/-- **The L-form chunk** of `op rd, rs1, rs2` (`b` the Wasm `i64` operator of `op`). -/
def lReg (b : IntBinOp) (rd rs1 rs2 : Reg) : List Instr :=
  lAlu rd (opnd rs1 ++ opnd rs2 ++ [.intBinOp .i64 b])

/-- The supported immediate operators. -/
def immop : Silmaril.RiscV.ImmOp → Option IntBinOp
  | .add => some .add
  | .xor => some .xor
  | .or => some .or
  | .and => some .and
  | _ => none

/-- The L-form chunk of `op rd, rs1, imm`. -/
def lImm (b : IntBinOp) (rd rs1 : Reg) (imm : BitVec 12) : List Instr :=
  lAlu rd (opnd rs1 ++ [c64 (imm.signExtend 64).toNat, .intBinOp .i64 b])

/-- The L-form chunk of `lui rd, imm`. -/
def lLui (rd : Reg) (imm : BitVec 20) : List Instr :=
  lAlu rd [c64 ((imm ++ 0#12).signExtend 64).toNat]

/-- **The L-form of one instruction** (`none`: not supported by the L-form). -/
def lInstr : Silmaril.RiscV.Instr → Option (List Instr)
  | .reg op rd rs1 rs2 => (binop op).map fun b => lReg b rd rs1 rs2
  | .imm op rd rs1 imm => (immop op).map fun b => lImm b rd rs1 imm
  | .upper .lui rd imm => some (lLui rd imm)
  | _ => none

/-- **The L-form of a straight-line program**: the chunks in sequence. -/
def lProg : List Silmaril.RiscV.Instr → Option (List Instr)
  | [] => some []
  | i :: is => (lInstr i).bind fun c => (lProg is).map fun r => c ++ r

end Silmaril.Sim.RV64.LForm
