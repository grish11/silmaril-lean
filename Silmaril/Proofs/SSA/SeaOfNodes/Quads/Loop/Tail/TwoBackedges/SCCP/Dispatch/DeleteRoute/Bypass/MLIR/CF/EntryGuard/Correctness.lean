module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Coverage
import Silmaril.SSA.MLIR.CF.EntryBranch.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.SCCP (BankDecidableEq decideTupleCovers)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF.EntryBranch (run_entry)
open RVSDG (Tuple)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width} [BankDecidableEq Word (dataPorts regs)]
variable {p : Program Op regs (.data result)} {facts : Tuple (Fact Word) (dataPorts regs)}
variable {target : Target regs result} {input : Bank (regs := regs) model}

theorem lower_run_arm (checked : Checked model p facts) (input : Bank (regs := regs) model) (fuel : Nat) :
    (lower checked).run evalOp (fuel + 1) (encodeValues input) =
      (arms checked (@decide _ (decideTupleCovers facts input))).run evalOp fuel (encodeValues input) := by
  apply run_entry
  have routes := entry_eval (Labels := Silmaril.MLIR.CF.EntryBranch.Label (Arms regs result))
    (Result := [result])
    (.entry true) (.entry false) facts input
  cases covered : @decide _ (decideTupleCovers facts input) <;> simpa [covered] using routes

private theorem specialized_of_compile (success : compile p facts = .ok target) :
    ∃ checked : Checked model p facts,
      target = lower checked ∧ Bypass.MLIR.CF.compile p facts = some (Bypass.MLIR.CF.lower checked) := by
  cases admitted : Backends.Worklist.admit model p facts with
  | error reason => simp [compile, admitted, Except.map] at success
  | ok checked =>
    have simultaneous := (Backends.Worklist.admit_eq_simultaneous model p facts).symm.trans admitted
    have eq : lower checked = target := by simpa [compile, admitted, Except.map] using success
    exact ⟨checked, eq.symm, by
      rw [Bypass.MLIR.CF.compile, Dispatch.check, simultaneous]
      rfl⟩

theorem compile_run (success : compile p facts = .ok target) (input : Bank (regs := regs) model)
    (limit : Nat) :
    target.run evalOp (targetFuel facts input limit) (encodeValues input) =
      (p.source.runFrom model (3 * limit + 2) 0 input).map (fun value => Env.cons value .nil) := by
  obtain ⟨checked, rfl, specialized⟩ := specialized_of_compile success
  rw [targetFuel, lower_run_arm]
  cases covered : @decide _ (decideTupleCovers facts input)
  · exact TwoBackedges.MLIR.CF.lower_run p input (3 * limit + 2)
  · exact Bypass.MLIR.CF.compile_run specialized
      (@of_decide_eq_true (TupleCovers facts input) (decideTupleCovers facts input) covered) limit

private theorem returns_arm_iff (checked : Checked model p facts) (value : Word result) :
    (∃ fuel, (lower checked).run evalOp fuel (encodeValues input) = some (.cons value .nil)) ↔
      ∃ fuel, (arms checked (@decide _ (decideTupleCovers facts input))).run evalOp fuel
        (encodeValues input) = some (.cons value .nil) := by
  constructor
  · rintro ⟨fuel, returned⟩
    cases fuel with
    | zero => cases returned
    | succ fuel => exact ⟨fuel, (lower_run_arm checked input fuel).symm.trans returned⟩
  · rintro ⟨fuel, returned⟩
    exact ⟨fuel + 1, (lower_run_arm checked input fuel).trans returned⟩

theorem compile_returns_iff (success : compile p facts = .ok target)
    (input : Bank (regs := regs) model) (value : Word result) :
    (∃ fuel, target.run evalOp fuel (encodeValues input) = some (.cons value .nil)) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some value := by
  obtain ⟨checked, rfl, specialized⟩ := specialized_of_compile success
  refine (returns_arm_iff checked value).trans ?_
  cases covered : @decide _ (decideTupleCovers facts input)
  · exact TwoBackedges.MLIR.CF.returns_iff p input value
  · exact Bypass.MLIR.CF.compile_returns_iff specialized
      (@of_decide_eq_true (TupleCovers facts input) (decideTupleCovers facts input) covered) value

theorem compile_diverges_iff (success : compile p facts = .ok target) (input : Bank (regs := regs) model) :
    target.Diverges evalOp (encodeValues input) ↔
      ¬ ∃ value fuel, p.source.runFrom model fuel 0 input = some value := by
  constructor
  · rintro diverges ⟨value, fuel, returned⟩
    obtain ⟨budget, observed⟩ := (compile_returns_iff success input value).mpr ⟨fuel, returned⟩
    rw [diverges budget] at observed
    cases observed
  · intro absent budget
    cases observed : target.run evalOp budget (encodeValues input) with
    | none => rfl
    | some values =>
      cases values with
      | cons value tail =>
        cases tail
        exact (absent ⟨value, (compile_returns_iff success input value).mp ⟨budget, observed⟩⟩).elim

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Proofs
