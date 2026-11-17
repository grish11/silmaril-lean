module

public import Silmaril.Sim.RV64.Sym.Defs

/-!
# Cut points: symbolic blocks of RV64 functions with loops (Ext model): definitions

`Silmaril.Sim.RV64.Sym.extSym` unrolls every path, so it cannot handle loops. Here a function is cut
at **cut points** (the plan's loop headers): `cfgSym code cuts n pc regs` executes symbolically
from `pc` (a cut point or the entry) and stops at the next cut point (`goto pc' rs`, the register
expressions there) or at the return (`ret a0`). It also handles `jal x0` (a jump). At every leaf
it checks that `ra` and the callee-saved registers are unchanged in the block.

`Tree2.run σ` evaluates a block for the block-entry values `σ` to an outcome `Out` (a return
value, or the next cut point with its register values). `Reach m₀ pc σ`: a run from `m₀`
reaches `pc` with the register values `σ`, the memory unchanged and the leaf ABI kept so far.
`Silmaril.Proofs.Sim.RV64.Cfg` proves the block steps sound once (`reach_goto`, `reach_ret`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Cfg

open Silmaril.RiscV.Ext
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Sym

/-- The leaves of a block: a return with `a0`, or the next cut point with all 32 registers. -/
inductive Leaf where
  | ret (a0 : E)
  | goto (pc : W64) (rs : List E)
  deriving DecidableEq, Repr

inductive Tree2 where
  | leaf (l : Leaf)
  | br (op : BranchOp) (a b : E) (t f : Tree2)
  deriving DecidableEq, Repr

/-- The 32 register expressions, as a list. -/
def regList (regs : Reg → E) : List E := (List.range 32).map fun i => regs (BitVec.ofNat 5 i)

/-- `ra` and the callee-saved registers are unchanged. -/
def abiOK (regs : Reg → E) : Bool :=
  regs 1#5 == .var 1#5 && calleeSaved.all (fun r => regs r == .var r)

/-- **The symbolic block executor** (`first`: at the block's own start, where a cut point does not
stop). -/
def cfgSym (code : Code) (cuts : List W64) : Nat → Bool → W64 → (Reg → E) → Option Tree2
  | 0, _, _, _ => none
  | n + 1, first, pc, regs =>
    if !first && cuts.contains pc then
      if abiOK regs then some (.leaf (.goto pc (regList regs))) else none
    else
    (code pc).bind fun w => (decode w).bind fun i =>
      match i with
      | .compute c =>
        (symValue c pc regs).bind fun e => cfgSym code cuts n false (pc + 4) (upd regs c.dest e)
      | .branch op rs1 rs2 half =>
        if (pc + branchOffset half).toNat % 4 = 0 then
          (cfgSym code cuts n false (pc + branchOffset half) regs).bind fun t =>
            (cfgSym code cuts n false (pc + 4) regs).map fun f => .br op (regs rs1) (regs rs2) t f
        else none
      | .jal rd half =>
        if rd = 0#5 ∧ (pc + jalOffset half).toNat % 4 = 0 then
          cfgSym code cuts n false (pc + jalOffset half) regs
        else none
      | .jalr rd rs1 off =>
        if rd = 0#5 ∧ rs1 = 1#5 ∧ off = 0#12 ∧ abiOK regs then some (.leaf (.ret (regs 10#5)))
        else none
      | _ => none

/-- Outcomes of a block. -/
inductive Out where
  | ret (v : W64)
  | goto (pc : W64) (σ : Reg → W64)

/-- The register values at a `goto` leaf. -/
def Leaf.vals (rs : List E) (σ : Reg → W64) : Reg → W64 := fun r => (rs.getD r.toNat (.var r)).eval σ

def Tree2.run (σ : Reg → W64) : Tree2 → Out
  | .leaf (.ret a0) => .ret (a0.eval σ)
  | .leaf (.goto pc rs) => .goto pc (Leaf.vals rs σ)
  | .br op a b t f => if op.eval (a.eval σ) (b.eval σ) then t.run σ else f.run σ

/-- A run from `m₀` reaches `pc` with register values `σ`, memory unchanged, `ra` and the
callee-saved registers at their entry values. -/
def Reach (m₀ : MState) (pc : W64) (σ : Reg → W64) : Prop :=
  ∃ k m, Silmaril.Machine.Execution.run MState.stepOpt k m₀ = some m ∧ m.memory = m₀.memory ∧
    m.core.pc = pc ∧ (∀ r, m.core.read r = σ r) ∧ σ 1#5 = m₀.core.read 1#5 ∧
    ∀ r ∈ calleeSaved, σ r = m₀.core.read r

/-- The machine returns from `m₀` with `a0 = v` and the leaf ABI kept. -/
def Returns (m₀ : MState) (v : W64) : Prop :=
  ∃ k m', Silmaril.Machine.Execution.run MState.stepOpt k m₀ = some m' ∧
    m'.core.pc = m₀.core.read 1#5 ∧ m'.core.read 10#5 = v ∧
    ∀ r ∈ calleeSaved, m'.core.read r = m₀.core.read r

end Silmaril.Sim.RV64.Cfg
