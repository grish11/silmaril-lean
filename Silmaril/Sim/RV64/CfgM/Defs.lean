module

public import Silmaril.Sim.RV64.Cfg.Defs

/-!
# Cut points with memory reads: definitions

`Silmaril.Sim.RV64.Cfg` extended with 64-bit loads (`ld`): register expressions `ME` may read memory
(`ME.ld a`, the doubleword at the value of `a`), so their values are partial (`ME.eval σ M`:
`none` when the address is misaligned or the bytes are not readable, where `Ext` faults). Blocks
(`cfgSymM`) and their outcomes (`Tree2M.run`, an `Option Out`) are as in `Cfg`; the memory is
unchanged (no stores), so `Silmaril.Sim.RV64.Cfg.Reach` is reused.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.CfgM

open Silmaril.RiscV.Ext
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Sym Silmaril.Sim.RV64.Cfg

/-- Register expressions that may read memory. -/
inductive ME where
  | var (r : Reg)
  | const (v : W64)
  | bin (op : Bin) (a b : ME)
  | ld (a : ME)
  deriving DecidableEq, Repr

/-- The doubleword `ld` reads at `p` (aligned and readable), as `Ext` does. -/
def ld64 (M : Silmaril.Process.Memory) (p : W64) : Option W64 :=
  if p.toNat % LoadOp.ld.width = 0 then (M.readBytes p.toNat LoadOp.ld.width).map LoadOp.ld.value
  else none

def ME.eval (σ : Reg → W64) (M : Silmaril.Process.Memory) : ME → Option W64
  | .var r => some (σ r)
  | .const v => some v
  | .bin op a b => (a.eval σ M).bind fun x => (b.eval σ M).map fun y => op.eval x y
  | .ld a => (a.eval σ M).bind (ld64 M)

inductive LeafM where
  | ret (a0 : ME)
  | goto (pc : W64) (rs : List ME)
  deriving DecidableEq, Repr

inductive TreeM where
  | leaf (l : LeafM)
  | br (op : BranchOp) (a b : ME) (t f : TreeM)
  /-- A load: its value must be defined (aligned, readable), else the machine faults. -/
  | chk (e : ME) (t : TreeM)
  deriving DecidableEq, Repr

def regListM (regs : Reg → ME) : List ME := (List.range 32).map fun i => regs (BitVec.ofNat 5 i)

def abiOKM (regs : Reg → ME) : Bool :=
  regs 1#5 == .var 1#5 && calleeSaved.all (fun r => regs r == .var r)

def symValueM (c : Compute) (pc : W64) (regs : Reg → ME) : Option ME :=
  match c with
  | .base (.imm op _ rs1 imm) => some (.bin (immBin op) (regs rs1) (.const (imm.signExtend 64)))
  | .base (.reg op _ rs1 rs2) => some (.bin (regBin op) (regs rs1) (regs rs2))
  | .base (.shift op _ rs1 amt) => some (.bin (shiftBin op) (regs rs1) (.const (amt.setWidth 64)))
  | .base (.upper op _ imm) => some (.const (Silmaril.RiscV.UpperOp.eval op pc imm))
  | .mulDiv .mul _ rs1 rs2 => some (.bin .mul (regs rs1) (regs rs2))
  | .mulDiv .remu _ rs1 rs2 => some (.bin .remu (regs rs1) (regs rs2))
  | _ => none

def updM (regs : Reg → ME) (d : Reg) (e : ME) : Reg → ME :=
  if d = 0#5 then regs else fun r => if r = d then e else regs r

def regs0M : Reg → ME := fun r => if r = 0#5 then .const 0 else .var r

/-- **The block executor with loads.** -/
def cfgSymM (code : Code) (cuts : List W64) : Nat → Bool → W64 → (Reg → ME) → Option TreeM
  | 0, _, _, _ => none
  | n + 1, first, pc, regs =>
    if !first && cuts.contains pc then
      if abiOKM regs then some (.leaf (.goto pc (regListM regs))) else none
    else
    (code pc).bind fun w => (decode w).bind fun i =>
      match i with
      | .compute c =>
        (symValueM c pc regs).bind fun e => cfgSymM code cuts n false (pc + 4) (updM regs c.dest e)
      | .load .ld rd rs1 off =>
        (cfgSymM code cuts n false (pc + 4)
          (updM regs rd (.ld (.bin .add (regs rs1) (.const (off.signExtend 64)))))).map
          (.chk (.ld (.bin .add (regs rs1) (.const (off.signExtend 64)))))
      | .branch op rs1 rs2 half =>
        if (pc + branchOffset half).toNat % 4 = 0 then
          (cfgSymM code cuts n false (pc + branchOffset half) regs).bind fun t =>
            (cfgSymM code cuts n false (pc + 4) regs).map fun f => .br op (regs rs1) (regs rs2) t f
        else none
      | .jal rd half =>
        if rd = 0#5 ∧ (pc + jalOffset half).toNat % 4 = 0 then
          cfgSymM code cuts n false (pc + jalOffset half) regs
        else none
      | .jalr rd rs1 off =>
        if rd = 0#5 ∧ rs1 = 1#5 ∧ off = 0#12 ∧ abiOKM regs then some (.leaf (.ret (regs 10#5)))
        else none
      | _ => none

/-- The register values at a `goto` leaf (all must be defined). -/
def LeafM.vals (rs : List ME) (σ : Reg → W64) (M : Silmaril.Process.Memory) :
    Option (Reg → W64) :=
  (rs.mapM fun e : ME => e.eval σ M).map fun vs r => vs.getD r.toNat (σ r)

def TreeM.run (σ : Reg → W64) (M : Silmaril.Process.Memory) : TreeM → Option Out
  | .leaf (.ret a0) => (a0.eval σ M).map .ret
  | .leaf (.goto pc rs) => (LeafM.vals rs σ M).map (.goto pc)
  | .br op a b t f => (a.eval σ M).bind fun x => (b.eval σ M).bind fun y =>
      if op.eval x y then t.run σ M else f.run σ M
  | .chk e t => (e.eval σ M).bind fun _ => t.run σ M

end Silmaril.Sim.RV64.CfgM
