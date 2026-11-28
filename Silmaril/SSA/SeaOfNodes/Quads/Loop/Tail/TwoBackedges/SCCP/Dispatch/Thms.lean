module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Correctness

/-! The specialized dispatcher preserves native execution at the same block budget. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch

open Diamond (Model Signature ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open Blocks (Bank)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {p : Program Op regs out} [BankDecidableEq m.value (dataPorts regs)]
variable {input : Tuple (Fact m.value) (dataPorts regs)} {concrete : Bank (regs := regs) m}

attribute [local irreducible] SCCP.solve

theorem admitWith_eq (marks : Marked) (agrees : marks = (solve m p input).1) :
    admitWith m p input marks agrees = admit m p input := by
  subst marks
  rfl

theorem admit_bothMarked_iff :
    admit m p input = .error .bothMarked ↔
      incomingIndex (.feedback true) ∈ (solve m p input).1 ∧
      incomingIndex (.feedback false) ∈ (solve m p input).1 := by
  by_cases onTrue : incomingIndex (.feedback true) ∈ (solve m p input).1 <;>
    by_cases onFalse : incomingIndex (.feedback false) ∈ (solve m p input).1 <;>
    simp [admit, admitWith, onTrue, onFalse]

theorem admit_neitherMarked_iff :
    admit m p input = .error .neitherMarked ↔
      incomingIndex (.feedback true) ∉ (solve m p input).1 ∧
      incomingIndex (.feedback false) ∉ (solve m p input).1 := by
  by_cases onTrue : incomingIndex (.feedback true) ∈ (solve m p input).1 <;>
    by_cases onFalse : incomingIndex (.feedback false) ∈ (solve m p input).1 <;>
    simp [admit, admitWith, onTrue, onFalse]

theorem check_none_of_both_marked
    (onTrue : incomingIndex (.feedback true) ∈ (solve m p input).1)
    (onFalse : incomingIndex (.feedback false) ∈ (solve m p input).1) :
    check m p input = none := by
  rw [check, admit_bothMarked_iff.mpr ⟨onTrue, onFalse⟩]
  rfl

/-- The replacement is an unconditional jump to the original selected block. -/
theorem Checked.source_at_dispatch (checked : Checked m p input) :
    checked.source 2 = ⟨[], .transfer (.jump (feedbackBlock checked.side))⟩ := rfl

theorem Checked.source_at_other (checked : Checked m p input) (index : Fin 5) (outside : index ≠ 2) :
    checked.source index = p.source index := by simp [Checked.source, specialize, outside]

/-- The selected side agrees at every reached dispatch, including in a
nonreturning execution. -/
theorem Checked.dispatch_eq (checked : Checked m p input) (covered : TupleCovers input concrete)
    {via : Incoming} {count : Nat} {old : Bank (regs := regs) m}
    (arrived : p.Arrives m concrete via count old)
    (continues : ((p.header.eval m old).get p.again).down = true) :
    ((p.header.eval m old).get p.select).down = checked.side :=
  Proofs.dispatch_eq checked covered arrived continues

/-- The source and specialization return the same value or exhaust at the
same native block budget on covered inputs. -/
theorem Checked.runFrom_eq (checked : Checked m p input) (covered : TupleCovers input concrete) (fuel : Nat) :
    checked.source.runFrom m fuel 0 concrete = p.source.runFrom m fuel 0 concrete :=
  Proofs.runFrom_eq checked covered fuel

theorem Checked.returns_iff (checked : Checked m p input) (covered : TupleCovers input concrete)
    (result : sortValue m.value out) :
    (∃ fuel, checked.source.runFrom m fuel 0 concrete = some result) ↔
      ∃ fuel, p.source.runFrom m fuel 0 concrete = some result := by
  simp only [checked.runFrom_eq covered]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch
