module

public import Silmaril.SSA.MLIR.SCF.LetIter.Defs
public import Mathlib.Logic.Relation

/-! # Observations of the region boundary

The native LetIter semantics supplies the behaviour of each individual region.
The boundary has its own control rules: test the condition tag, pass the payload,
follow yields back to the before region, and enter the parent on a false condition.
-/

@[expose] public section

universe u v w

namespace Silmaril.MLIR.SCF.LetIter

open Silmaril.Isotope
open Silmaril.Isotope.Institution.Observational (Model Observation noFree)
open Silmaril.Isotope.LetIter.Semantics

namespace RegionLoop

variable {Φ : Type u} {n : Nat} (M : Model.{u, v, w} Φ n) (p : RegionLoop Φ n)

/-- The current before value and the separate operational machine state. -/
abbrev Entry := Value M.α × M.σ

/-- A false condition completes the loop, transmitting its payload to the parent. -/
def Exit (c : Entry M) (out : Value M.α) (s : M.σ) : Prop :=
  Eval M.instr noFree (extend M.bound c.1) p.condition c.2 (.inl out) s

/-- A true condition sends its payload to the after region, whose yield supplies
the next before value. -/
def Backedge (c c' : Entry M) : Prop :=
  ∃ payload mid, Eval M.instr noFree (extend M.bound c.1) p.condition c.2 (.inr payload) mid ∧
    Eval M.instr noFree (extend M.bound payload) p.afterRegion mid c'.1 c'.2

/-- A fault inside either region of the current iteration. -/
def IterationFault (c : Entry M) (s : M.σ) : Prop :=
  Fault M.instr M.faults noFree (extend M.bound c.1) p.condition c.2 s ∨
    ∃ payload mid, Eval M.instr noFree (extend M.bound c.1) p.condition c.2 (.inr payload) mid ∧
      Fault M.instr M.faults noFree (extend M.bound payload) p.afterRegion mid s

/-- Divergence inside either region of the current iteration. -/
def IterationDiverges (c : Entry M) : Prop :=
  External.Diverges M.instr noFree M.prim (.term (extend M.bound c.1) p.condition c.2) ∨
    ∃ payload mid, Eval M.instr noFree (extend M.bound c.1) p.condition c.2 (.inr payload) mid ∧
      External.Diverges M.instr noFree M.prim (.term (extend M.bound payload) p.afterRegion mid)

/-- A finite sequence of backedges followed by a false condition. -/
def LoopReturns (c : Entry M) (out : Value M.α) (s : M.σ) : Prop :=
  ∃ d, Relation.ReflTransGen (p.Backedge M) c d ∧ p.Exit M d out s

/-- A finite sequence of backedges followed by a fault. -/
def LoopFaults (c : Entry M) (s : M.σ) : Prop :=
  ∃ d, Relation.ReflTransGen (p.Backedge M) c d ∧ p.IterationFault M d s

/-- Each entry can diverge inside the current iteration or take another backedge
to an entry in the same divergence relation. -/
def LoopDiverges (c : Entry M) : Prop :=
  ∃ R : Entry M → Prop, R c ∧
    ∀ d, R d → p.IterationDiverges M d ∨ ∃ e, p.Backedge M d e ∧ R e

/-- Full answers at the parent boundary, with the native observational vocabulary. -/
def observe : Set (Observation (Value M.α) M.σ) :=
  {o | o.Holds
    (fun s v s' => ∃ initial start out mid,
      Eval M.instr noFree M.bound p.init s initial start ∧ p.LoopReturns M (initial, start) out mid ∧
        Eval M.instr noFree (extend M.bound out) p.parent mid v s')
    (fun s s' => Fault M.instr M.faults noFree M.bound p.init s s' ∨
      ∃ initial start, Eval M.instr noFree M.bound p.init s initial start ∧
        (p.LoopFaults M (initial, start) s' ∨ ∃ out mid, p.LoopReturns M (initial, start) out mid ∧
          Fault M.instr M.faults noFree (extend M.bound out) p.parent mid s'))
    (fun s => External.Diverges M.instr noFree M.prim (.term M.bound p.init s) ∨
      ∃ initial start, Eval M.instr noFree M.bound p.init s initial start ∧
        (p.LoopDiverges M (initial, start) ∨ ∃ out mid, p.LoopReturns M (initial, start) out mid ∧
          External.Diverges M.instr noFree M.prim (.term (extend M.bound out) p.parent mid)))}

end RegionLoop
end Silmaril.MLIR.SCF.LetIter
