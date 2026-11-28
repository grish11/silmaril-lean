module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Correctness

/-! Exact remapping and source execution after removing the dead route. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute

open Diamond (Model Signature ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open Blocks (Bank)
open RVSDG (Tuple)

universe u v w

theorem keptBlock_injective (side : Bool) : Function.Injective (keptBlock side) := by
  show ∀ i j : Fin 4, keptBlock side i = keptBlock side j → i = j
  cases side <;> decide

/-- The compact indices cover exactly the blocks other than the excluded arm. -/
theorem keptBlock_range_iff (side : Bool) :
    ∀ index : Fin 5, (∃ retained, keptBlock side retained = index) ↔ index ≠ feedbackBlock (!side) := by
  cases side <;> decide

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {p : Program Op regs out} [BankDecidableEq m.value (dataPorts regs)]
variable {input : Tuple (Fact m.value) (dataPorts regs)} {concrete : Bank (regs := regs) m}

theorem retained_body (checked : Checked m p input) (index : Fin 4) :
    (compact checked index).body = (checked.source (keptBlock checked.side index)).body := rfl

/-- Embed every live jump target and preserve the exact test and return ports. -/
theorem terminator_map (checked : Checked m p input) (index : Fin 4) :
    mapTerminator (keptBlock checked.side) (compact checked index).terminator =
      (checked.source (keptBlock checked.side index)).terminator :=
  Proofs.terminator_map checked index

/-- The two compact header arrivals map to entry and the selected original
feedback occurrence. Each still targets the header at compact index 1. -/
theorem header_predecessor (checked : Checked m p input) (edge : SeaOfNodes.Loop.Incoming) :
    keptBlock checked.side (predecessor edge) = originalPredecessor (originalOccurrence checked.side edge) ∧
      (compact checked (predecessor edge)).terminator = .transfer (.jump 1) := by
  cases edge <;> exact ⟨rfl, rfl⟩

/-- The full typed bank delivered by each compact predecessor is preserved. -/
theorem predecessor_bank (checked : Checked m p input) (edge : SeaOfNodes.Loop.Incoming)
    (bank : Bank (regs := regs) m) :
    (compact checked (predecessor edge)).body.eval m bank =
      (checked.source (originalPredecessor (originalOccurrence checked.side edge))).body.eval m bank := by
  rw [← (header_predecessor checked edge).1]
  rfl

/-- On a covered continuing arrival, the retained body supplies the full
bank of the original selected feedback step. -/
theorem feedback_arrival (checked : Checked m p input) (covered : TupleCovers input concrete)
    {via : Incoming} {count : Nat} {old : Bank (regs := regs) m}
    (arrived : p.Arrives m concrete via count old)
    (continues : ((p.header.eval m old).get p.again).down = true) :
    p.step m old =
      .inr (checked.side, (compact checked (predecessor .backedge)).body.eval m (p.header.eval m old)) :=
  Proofs.feedback_arrival checked covered arrived continues

/-- The compact source and the checked five-block source consume the same
budget from every retained block and every bank. -/
theorem runFrom_retained (checked : Checked m p input) (fuel : Nat) (index : Fin 4)
    (bank : Bank (regs := regs) m) :
    (compact checked).runFrom m fuel index bank =
      checked.source.runFrom m fuel (keptBlock checked.side index) bank :=
  Proofs.runFrom_retained checked fuel index bank

theorem runFrom_eq (checked : Checked m p input) (covered : TupleCovers input concrete) (fuel : Nat) :
    (compact checked).runFrom m fuel 0 concrete = p.source.runFrom m fuel 0 concrete :=
  (runFrom_retained checked fuel 0 concrete).trans (checked.runFrom_eq covered fuel)

theorem rewrite_eq_none_iff : rewrite m p input = none ↔ check m p input = none :=
  Option.map_eq_none_iff

theorem rewrite_none_of_both_marked
    (onTrue : incomingIndex (.feedback true) ∈ (solve m p input).1)
    (onFalse : incomingIndex (.feedback false) ∈ (solve m p input).1) :
    rewrite m p input = none :=
  rewrite_eq_none_iff.mpr (check_none_of_both_marked onTrue onFalse)

variable {clean : Tail.Source Op regs out 4}

/-- The composed rewrite preserves return or exhaustion at every budget
on each concrete entry covered by the abstract contract. -/
theorem rewrite_runFrom_eq (success : rewrite m p input = some clean)
    (covered : TupleCovers input concrete) (fuel : Nat) :
    clean.runFrom m fuel 0 concrete = p.source.runFrom m fuel 0 concrete := by
  obtain ⟨checked, _, rfl⟩ := Option.map_eq_some_iff.mp success
  exact runFrom_eq checked covered fuel

theorem rewrite_returns_iff (success : rewrite m p input = some clean) (covered : TupleCovers input concrete)
    (result : sortValue m.value out) :
    (∃ fuel, clean.runFrom m fuel 0 concrete = some result) ↔
      ∃ fuel, p.source.runFrom m fuel 0 concrete = some result := by
  simp only [rewrite_runFrom_eq success covered]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute
