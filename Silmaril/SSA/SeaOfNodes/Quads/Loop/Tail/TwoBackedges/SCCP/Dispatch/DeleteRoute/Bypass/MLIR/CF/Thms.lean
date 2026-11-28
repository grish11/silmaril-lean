module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Thms

/-! Frame and observation laws for the checked header-tested CF loop. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width Env)
open RVSDG (Tuple)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width}
variable {p : Program Op regs (.data result)} [BankDecidableEq Word (dataPorts regs)]
variable {facts : Tuple (Fact Word) (dataPorts regs)}
variable {input : Bank (regs := regs) model}

/-- Entry passes the bank produced by the original preheader. -/
theorem entry_frame (checked : Checked model p facts) (input : Bank (regs := regs) model) :
    (lower checked).entry.eval evalOp (fun term env => term.eval env) (encodeValues input) =
      .inl ⟨.header, encodeValues (p.preheader.eval model input)⟩ :=
  Proofs.entry_frame checked input

/-- Test the post-header bank before entering feedback. The false edge
passes only the header's return word. -/
theorem header_frame (checked : Checked model p facts) (input old : Bank (regs := regs) model) :
    ((lower checked).block .header).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      let next := p.header.eval model old
      .inl (if (next.get p.again).down then ⟨.feedback, encodeValues next⟩
        else ⟨.exit, .cons (next.get p.result) .nil⟩) :=
  Proofs.header_frame checked input old

/-- The retained feedback branch passes the entire updated bank to the header. -/
theorem feedback_frame (checked : Checked model p facts) (input old : Bank (regs := regs) model) :
    ((lower checked).block .feedback).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      .inl ⟨.header, encodeValues ((p.feedback checked.side).eval model old)⟩ :=
  Proofs.feedback_frame checked input old

/-- The CF return block accounts for one additional visit after bypass. -/
theorem lower_run (checked : Checked model p facts) (input : Bank (regs := regs) model) (fuel : Nat) :
    (lower checked).run evalOp (fuel + 1) (encodeValues input) =
      ((bypass checked).runFrom model fuel 0 input).map (fun value => Env.cons value .nil) :=
  Proofs.lower_run checked input fuel

/-- An original trace with `n` feedback visits needs exactly `2 * n + 3`
CF block visits, including the explicit return block. -/
theorem run_count_iff (checked : Checked model p facts) (covered : TupleCovers facts input)
    (fuel : Nat) (value : Word result) :
    (lower checked).run evalOp fuel (encodeValues input) = some (.cons value .nil) ↔
      ∃ n, ReturnsAfter p model n (p.preheader.eval model input) value ∧ 2 * n + 3 ≤ fuel :=
  Proofs.run_count_iff checked covered fuel value

variable {target : Target regs result}

/-- Budgets permitting the same number of feedback steps agree on both
return and exhaustion, even when no return exists. -/
theorem compile_run (success : compile p facts = some target) (covered : TupleCovers facts input)
    (limit : Nat) :
    target.run evalOp (2 * limit + 3) (encodeValues input) =
      (p.source.runFrom model (3 * limit + 2) 0 input).map (fun value => Env.cons value .nil) := by
  obtain ⟨checked, _, rfl⟩ := Option.map_eq_some_iff.mp success
  exact Proofs.feedback_budget_eq checked covered limit

theorem compile_returns_iff (success : compile p facts = some target) (covered : TupleCovers facts input)
    (value : Word result) :
    (∃ fuel, target.run evalOp fuel (encodeValues input) = some (.cons value .nil)) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some value := by
  obtain ⟨checked, _, rfl⟩ := Option.map_eq_some_iff.mp success
  exact Proofs.returns_iff_original checked covered value

theorem compile_diverges_iff (success : compile p facts = some target) (covered : TupleCovers facts input) :
    target.Diverges evalOp (encodeValues input) ↔
      ¬ ∃ value fuel, p.source.runFrom model fuel 0 input = some value := by
  obtain ⟨checked, _, rfl⟩ := Option.map_eq_some_iff.mp success
  exact Proofs.diverges_iff_original checked covered

theorem compile_none_of_both_marked
    (onTrue : incomingIndex (.feedback true) ∈ (solve model p facts).1)
    (onFalse : incomingIndex (.feedback false) ∈ (solve model p facts).1) :
    compile p facts = none :=
  Option.map_eq_none_iff.mpr (check_none_of_both_marked onTrue onFalse)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF
