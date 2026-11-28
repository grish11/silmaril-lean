module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Thms

/-! The compact quad loop can skip its empty dispatcher on continuing activations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass

open Diamond (Model Signature ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open Blocks (Bank)
open RVSDG (Tuple)

universe u v w

theorem retainedBlock_range_iff :
    ∀ i : Fin 4, (∃ j, retainedBlock j = i) ↔ i ≠ 2 := by decide

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {p : Program Op regs out} [BankDecidableEq m.value (dataPorts regs)]
variable {input : Tuple (Fact m.value) (dataPorts regs)} {concrete : Bank (regs := regs) m}

/-- Admission fixes the skipped block to an empty body and direct jump. -/
theorem compact_dispatcher (checked : Checked m p input) :
    compact checked 2 = ⟨[], .transfer (.jump 3)⟩ := rfl

theorem dispatcher_step (checked : Checked m p input) (fuel : Nat) (bank : Bank (regs := regs) m) :
    (compact checked).runFrom m (fuel + 1) 2 bank = (compact checked).runFrom m fuel 3 bank := rfl

theorem retained_body (checked : Checked m p input) (index : Fin 3) :
    (bypass checked index).body = (compact checked (retainedBlock index)).body := rfl

theorem header_branch (checked : Checked m p input) :
    (bypass checked 1).terminator = .branch p.again (.jump 2) (.ret p.result) := rfl

/-- Both header predecessors retain their identities through compaction. -/
theorem header_predecessor (checked : Checked m p input) (edge : SeaOfNodes.Loop.Incoming) :
    retainedBlock (predecessor edge) = DeleteRoute.predecessor edge ∧
      keptBlock checked.side (retainedBlock (predecessor edge)) =
        originalPredecessor (originalOccurrence checked.side edge) ∧
      (bypass checked (predecessor edge)).terminator = .transfer (.jump 1) := by
  cases edge <;> exact ⟨rfl, rfl, rfl⟩

theorem predecessor_bank (checked : Checked m p input) (edge : SeaOfNodes.Loop.Incoming)
    (bank : Bank (regs := regs) m) :
    (bypass checked (predecessor edge)).body.eval m bank =
      (checked.source (originalPredecessor (originalOccurrence checked.side edge))).body.eval m bank := by
  rw [retained_body, (header_predecessor checked edge).1]
  exact DeleteRoute.predecessor_bank checked edge bank

theorem feedback_arrival (checked : Checked m p input) (covered : TupleCovers input concrete)
    {via : Incoming} {count : Nat} {old : Bank (regs := regs) m}
    (arrived : p.Arrives m concrete via count old)
    (continues : ((p.header.eval m old).get p.again).down = true) :
    p.step m old =
      .inr (checked.side, (bypass checked (predecessor .backedge)).body.eval m (p.header.eval m old)) :=
  DeleteRoute.feedback_arrival checked covered arrived continues

theorem run_compact_iff (checked : Checked m p input) (covered : TupleCovers input concrete)
    (fuel : Nat) (result : sortValue m.value out) :
    (compact checked).runFrom m fuel 0 concrete = some result ↔
      ∃ n, ReturnsAfter p m n (p.preheader.eval m concrete) result ∧ 3 * n + 2 ≤ fuel :=
  Proofs.run_compact_iff checked covered fuel result

theorem run_bypass_iff (checked : Checked m p input) (covered : TupleCovers input concrete)
    (fuel : Nat) (result : sortValue m.value out) :
    (bypass checked).runFrom m fuel 0 concrete = some result ↔
      ∃ n, ReturnsAfter p m n (p.preheader.eval m concrete) result ∧ 2 * n + 2 ≤ fuel :=
  Proofs.run_bypass_iff checked covered fuel result

/-- For an actual return after `count` feedback steps, the bypass saves
exactly `count` block visits. Both runners exhaust below their own cutoff. -/
theorem return_budgets (checked : Checked m p input) (covered : TupleCovers input concrete)
    {count : Nat} {result : sortValue m.value out}
    (trace : ReturnsAfter p m count (p.preheader.eval m concrete) result) (fuel : Nat) :
    (compact checked).runFrom m fuel 0 concrete = (if 3 * count + 2 ≤ fuel then some result else none) ∧
      (bypass checked).runFrom m fuel 0 concrete = (if 2 * count + 2 ≤ fuel then some result else none) :=
  Proofs.return_budgets checked covered trace fuel

/-- At budgets allowing the same number of feedback steps, both sources
agree on return or exhaustion, even without a finite return. -/
theorem feedback_budget_eq (checked : Checked m p input) (covered : TupleCovers input concrete) (limit : Nat) :
    (bypass checked).runFrom m (2 * limit + 2) 0 concrete =
      (compact checked).runFrom m (3 * limit + 2) 0 concrete :=
  Proofs.feedback_budget_eq checked covered limit

theorem returns_iff (checked : Checked m p input) (covered : TupleCovers input concrete)
    (result : sortValue m.value out) :
    (∃ fuel, (bypass checked).runFrom m fuel 0 concrete = some result) ↔
      ∃ fuel, (compact checked).runFrom m fuel 0 concrete = some result :=
  Proofs.returns_iff checked covered result

theorem noFiniteReturn_iff (checked : Checked m p input) (covered : TupleCovers input concrete) :
    (¬ ∃ result fuel, (bypass checked).runFrom m fuel 0 concrete = some result) ↔
      (¬ ∃ result fuel, (compact checked).runFrom m fuel 0 concrete = some result) := by
  simp only [returns_iff checked covered]

theorem rewrite_eq_none_iff : rewrite m p input = none ↔ check m p input = none :=
  Option.map_eq_none_iff

variable {clean : Tail.Source Op regs out}

theorem rewrite_returns_iff (success : rewrite m p input = some clean) (covered : TupleCovers input concrete)
    (result : sortValue m.value out) :
    (∃ fuel, clean.runFrom m fuel 0 concrete = some result) ↔
      ∃ fuel, p.source.runFrom m fuel 0 concrete = some result := by
  obtain ⟨checked, _, rfl⟩ := Option.map_eq_some_iff.mp success
  simpa only [DeleteRoute.runFrom_eq checked covered] using returns_iff checked covered result

theorem rewrite_noFiniteReturn_iff (success : rewrite m p input = some clean)
    (covered : TupleCovers input concrete) :
    (¬ ∃ result fuel, clean.runFrom m fuel 0 concrete = some result) ↔
      (¬ ∃ result fuel, p.source.runFrom m fuel 0 concrete = some result) := by
  simp only [rewrite_returns_iff success covered]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass
