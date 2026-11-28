module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Coverage
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Correctness

/-! The emitted guard decides entry coverage, and both linked paths refine the source. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq decideTupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width Env)
open RVSDG (Tuple)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width} [BankDecidableEq Word (dataPorts regs)]
variable {p : Program Op regs (.data result)} {facts : Tuple (Fact Word) (dataPorts regs)}
variable {target : Target regs result}

/-- The actual entry block branches according to the certified `TupleCovers`
decision, with no new arguments on either edge. -/
theorem entry_eval {Labels : List Width → Type} {Result : List Width} (accept reject : Labels [])
    (facts : Tuple (Fact Word) (dataPorts regs)) (input : Bank (regs := regs) model) :
    (entry (Result := Result) facts accept reject).eval evalOp (fun term env => term.eval env)
      (encodeValues input) =
      .inl (if @decide _ (decideTupleCovers facts input) then ⟨accept, .nil⟩ else ⟨reject, .nil⟩) :=
  Proofs.entry_eval accept reject facts input

/-- After the guard's one block visit, execution is exactly that of the
selected existing CFG, on the same encoded input bank. -/
theorem lower_run_arm (checked : Checked model p facts) (input : Bank (regs := regs) model) (fuel : Nat) :
    (lower checked).run evalOp (fuel + 1) (encodeValues input) =
      (arms checked (@decide _ (decideTupleCovers facts input))).run evalOp fuel (encodeValues input) :=
  Proofs.lower_run_arm checked input fuel

/-- At the source and target budgets for a shared feedback limit, returns and
exhaustion agree for every concrete entry. -/
theorem compile_run (success : compile p facts = .ok target) (input : Bank (regs := regs) model)
    (limit : Nat) :
    target.run evalOp (targetFuel facts input limit) (encodeValues input) =
      (p.source.runFrom model (3 * limit + 2) 0 input).map (fun value => Env.cons value .nil) :=
  Proofs.compile_run success input limit

/-- Finite returns agree with independently quantified source and target fuel. -/
theorem compile_returns_iff (success : compile p facts = .ok target)
    (input : Bank (regs := regs) model) (value : Word result) :
    (∃ fuel, target.run evalOp fuel (encodeValues input) = some (.cons value .nil)) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some value :=
  Proofs.compile_returns_iff success input value

theorem compile_diverges_iff (success : compile p facts = .ok target) (input : Bank (regs := regs) model) :
    target.Diverges evalOp (encodeValues input) ↔
      ¬ ∃ value fuel, p.source.runFrom model fuel 0 input = some value :=
  Proofs.compile_diverges_iff success input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard
