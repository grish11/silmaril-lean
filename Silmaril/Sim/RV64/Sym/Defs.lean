module

public import Silmaril.Sim.RV64.Ref.Defs
public import Silmaril.Machine.RiscV.Ext.Defs

/-!
# A symbolic executor for RV64 leaf functions (Ext model): definitions

`extSym code fuel pc regs` runs `Silmaril.RiscV.Ext` instructions **symbolically** from `pc`,
over register expressions `E` (initially `var r`), following both arms of every conditional
branch, until `jalr x0, 0(ra)` (the return). It covers the register-only instructions (all of
`Silmaril.RiscV.Instr`, `mul`) and the six conditional branches; anything else (memory, `jal`,
other `jalr`s, other M-extension instructions) makes it fail (`none`). At a return it **checks**
the RISC-V calling convention for leaf functions: `ra` and the callee-saved registers
(`sp`, `s0`–`s11`) hold their entry values; the result is then the expression of `a0`.

The result is a decision tree `Tree` (`ret a0` leaves, `br` nodes on branch conditions). It is
computable, so for a concrete function `extSym … = some T` is checked by `decide`;
`Silmaril.Proofs.Sim.RV64.Sym` proves it **sound once**: every concrete run from a state
matching the entry takes the path of `T`, returns to `ra`, preserves the callee-saved registers
and leaves `a0 = T.eval σ`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Sym

open Silmaril.RiscV.Ext

abbrev Reg := Silmaril.RiscV.Reg
abbrev W64 := Silmaril.RiscV.Word

/-- Binary operators of register expressions. -/
inductive Bin where
  | add | sub | xor | or | and | sll | srl | sra | slt | sltu | mul | remu
  deriving DecidableEq, Repr

/-- Register expressions over the entry values of the registers. -/
inductive E where
  | var (r : Reg)
  | const (v : W64)
  | bin (op : Bin) (a b : E)
  deriving DecidableEq, Repr

def Bin.eval : Bin → W64 → W64 → W64
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .xor, x, y => x ^^^ y
  | .or, x, y => x ||| y
  | .and, x, y => x &&& y
  | .sll, x, y => x <<< (y.setWidth 6).toNat
  | .srl, x, y => x >>> (y.setWidth 6).toNat
  | .sra, x, y => x.sshiftRight (y.setWidth 6).toNat
  | .slt, x, y => Silmaril.RiscV.boolWord (x.slt y)
  | .sltu, x, y => Silmaril.RiscV.boolWord (x.ult y)
  | .mul, x, y => x * y
  | .remu, x, y => remU x y

/-- The value of an expression for the entry register values `σ`. -/
def E.eval (σ : Reg → W64) : E → W64
  | .var r => σ r
  | .const v => v
  | .bin op a b => op.eval (a.eval σ) (b.eval σ)

/-- The register variables of an expression. -/
def E.vars : E → List Reg
  | .var r => [r]
  | .const _ => []
  | .bin _ a b => a.vars ++ b.vars

/-- Decision trees: the result `a0` at a return, or a branch on a condition. -/
inductive Tree where
  | ret (a0 : E)
  | br (op : BranchOp) (a b : E) (t f : Tree)
  deriving DecidableEq, Repr

def Tree.eval (σ : Reg → W64) : Tree → W64
  | .ret a0 => a0.eval σ
  | .br op a b t f => if op.eval (a.eval σ) (b.eval σ) then t.eval σ else f.eval σ

/-- All register variables of a tree are among `ps`. -/
def Tree.varsIn (ps : List Reg) : Tree → Bool
  | .ret a0 => a0.vars.all (· ∈ ps)
  | .br _ a b t f => a.vars.all (· ∈ ps) && b.vars.all (· ∈ ps) && t.varsIn ps && f.varsIn ps

def immBin : Silmaril.RiscV.ImmOp → Bin
  | .add => .add | .slt => .slt | .sltu => .sltu | .and => .and | .or => .or | .xor => .xor

def regBin : Silmaril.RiscV.RegOp → Bin
  | .add => .add | .sub => .sub | .slt => .slt | .sltu => .sltu | .and => .and | .or => .or
  | .xor => .xor | .sll => .sll | .srl => .srl | .sra => .sra

def shiftBin : Silmaril.RiscV.ShiftOp → Bin
  | .sll => .sll | .srl => .srl | .sra => .sra

/-- The value expression of a register-only instruction at `pc`. -/
def symValue (c : Compute) (pc : W64) (regs : Reg → E) : Option E :=
  match c with
  | .base (.imm op _ rs1 imm) => some (.bin (immBin op) (regs rs1) (.const (imm.signExtend 64)))
  | .base (.reg op _ rs1 rs2) => some (.bin (regBin op) (regs rs1) (regs rs2))
  | .base (.shift op _ rs1 amt) => some (.bin (shiftBin op) (regs rs1) (.const (amt.setWidth 64)))
  | .base (.upper op _ imm) => some (.const (Silmaril.RiscV.UpperOp.eval op pc imm))
  | .mulDiv .mul _ rs1 rs2 => some (.bin .mul (regs rs1) (regs rs2))
  | .mulDiv .remu _ rs1 rs2 => some (.bin .remu (regs rs1) (regs rs2))
  | _ => none

/-- Write `e` to `d` (writes to `x0` are discarded). -/
def upd (regs : Reg → E) (d : Reg) (e : E) : Reg → E :=
  if d = 0#5 then regs else fun r => if r = d then e else regs r

/-- The registers a leaf function must preserve: `sp`, `s0`–`s11` (and `ra`, checked apart). -/
def calleeSaved : List Reg := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The entry register file: `x0` is `0`, every other register its entry value. -/
def regs0 : Reg → E := fun r => if r = 0#5 then .const 0 else .var r

/-- **The symbolic executor.** -/
def extSym (code : Code) : Nat → W64 → (Reg → E) → Option Tree
  | 0, _, _ => none
  | n + 1, pc, regs =>
    (code pc).bind fun w => (decode w).bind fun i =>
      match i with
      | .compute c =>
        (symValue c pc regs).bind fun e => extSym code n (pc + 4) (upd regs c.dest e)
      | .branch op rs1 rs2 half =>
        if (pc + branchOffset half).toNat % 4 = 0 then
          (extSym code n (pc + branchOffset half) regs).bind fun t =>
            (extSym code n (pc + 4) regs).map fun f => .br op (regs rs1) (regs rs2) t f
        else none
      | .jalr rd rs1 off =>
        if rd = 0#5 ∧ rs1 = 1#5 ∧ off = 0#12 ∧ regs 1#5 = .var 1#5 ∧
            calleeSaved.all (fun r => regs r == .var r) then some (.ret (regs 10#5))
        else none
      | _ => none

end Silmaril.Sim.RV64.Sym
