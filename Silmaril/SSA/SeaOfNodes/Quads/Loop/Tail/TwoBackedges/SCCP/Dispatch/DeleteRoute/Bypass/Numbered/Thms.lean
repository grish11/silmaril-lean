module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Thms

/-! Entry selection, θ packets, and exact source observations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered

open SeaOfNodes.Diamond (Model Signature ValueSort dataPorts sortValue)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Tuple)
open Join (model)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {p : Program Op regs out} [BankDecidableEq m.value (dataPorts regs)]
variable {facts : Tuple (Fact m.value) (dataPorts regs)}
variable {input : Bank (regs := regs) m}

/-- One θ body receives the full bank of a continuing header. Its packet
tags the next header's predicate and supplies that header's entire bank. -/
theorem packet_run (checked : Checked m p facts) (fuel : Nat) (bank : Bank (regs := regs) m) :
    (thetaBody checked).toGraph.run (model m) fuel bank =
      let next := p.header.eval m ((bypass checked 2).body.eval m bank)
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) :=
  Proofs.packet_run checked fuel bank

/-- The exit arm projects the original result from the first header bank.
It can return even at θ bound zero. -/
theorem lower_exit (checked : Checked m p facts) (fuel : Nat) (input : Bank (regs := regs) m)
    (stop : ((p.header.eval m (p.preheader.eval m input)).get p.again).down = false) :
    (lower checked).run (model m) fuel input =
      some (.cons ((p.header.eval m (p.preheader.eval m input)).get p.result) .nil) :=
  Proofs.lower_exit checked fuel input stop

/-- The θ bound counts taken feedback visits. The bypassed source needs its
preheader, first header, and two more block visits per admitted feedback. -/
theorem lower_run (checked : Checked m p facts) (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower checked).run (model m) fuel input =
      ((bypass checked).runFrom m (2 * fuel + 2) 0 input).map (fun value => .cons value .nil) :=
  Proofs.lower_run checked fuel input

/-- A finite original trace fits the θ bound exactly when its count of taken
feedback occurrences fits. Immediate exit has count zero. -/
theorem run_count_iff (checked : Checked m p facts) (covered : TupleCovers facts input)
    (fuel : Nat) (value : sortValue m.value out) :
    (lower checked).run (model m) fuel input = some (.cons value .nil) ↔
      ∃ n, ReturnsAfter p m n (p.preheader.eval m input) value ∧ n ≤ fuel :=
  Proofs.run_count_iff checked covered fuel value

variable {target : Target p}

/-- Compare the actual numbered run with the original at the corresponding
block budget, including exhaustion. -/
theorem compile_run (success : compile m p facts = some target) (covered : TupleCovers facts input)
    (fuel : Nat) :
    target.run (model m) fuel input =
      (p.source.runFrom m (3 * fuel + 2) 0 input).map (fun value => .cons value .nil) := by
  obtain ⟨checked, _, rfl⟩ := Option.map_eq_some_iff.mp success
  exact Proofs.lower_run_original checked covered fuel

theorem compile_returns_iff (success : compile m p facts = some target) (covered : TupleCovers facts input)
    (value : sortValue m.value out) :
    target.Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, p.source.runFrom m fuel 0 input = some value := by
  obtain ⟨checked, _, rfl⟩ := Option.map_eq_some_iff.mp success
  exact Proofs.returns_iff_original checked covered value

theorem compile_noReturn_iff (success : compile m p facts = some target) (covered : TupleCovers facts input) :
    (∀ fuel, target.run (model m) fuel input = none) ↔
      ¬ ∃ value fuel, p.source.runFrom m fuel 0 input = some value := by
  obtain ⟨checked, _, rfl⟩ := Option.map_eq_some_iff.mp success
  exact Proofs.no_return_iff_original checked covered

theorem compile_none_of_both_marked
    (onTrue : incomingIndex (.feedback true) ∈ (solve m p facts).1)
    (onFalse : incomingIndex (.feedback false) ∈ (solve m p facts).1) :
    compile m p facts = none :=
  Option.map_eq_none_iff.mpr (check_none_of_both_marked onTrue onFalse)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered
