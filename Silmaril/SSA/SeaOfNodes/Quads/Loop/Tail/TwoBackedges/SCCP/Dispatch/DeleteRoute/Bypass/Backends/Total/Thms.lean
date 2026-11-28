module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered.Thms

/-! Exact outcome classification and the observations of the two-live artifacts. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width Env)
open RVSDG (Tuple)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width} {p : Program Op regs (.data result)}
variable [BankDecidableEq Word (dataPorts regs)] {facts : Tuple (Fact Word) (dataPorts regs)}
variable {targets : OriginalTargets p} (input : Bank (regs := regs) model)

theorem compile_specialized_iff (targets : Backends.Targets p) :
    compile p facts = .specialized targets ↔ Backends.compile p facts = .ok targets :=
  Proofs.compile_specialized_iff targets

theorem compile_twoLive_iff (targets : OriginalTargets p) :
    compile p facts = .twoLive targets ↔
      emitOriginal p = targets ∧
      incomingIndex (.feedback true) ∈ (solve model p facts).1 ∧
      incomingIndex (.feedback false) ∈ (solve model p facts).1 :=
  Proofs.compile_twoLive_iff targets

theorem compile_neitherMarked_iff (targets : OriginalTargets p) :
    compile p facts = .neitherMarked targets ↔
      emitOriginal p = targets ∧
      incomingIndex (.feedback true) ∉ (solve model p facts).1 ∧
      incomingIndex (.feedback false) ∉ (solve model p facts).1 :=
  Proofs.compile_neitherMarked_iff targets

/-- The unchanged source and both actual targets agree, including exhaustion.
The original artifacts work on every typed input. -/
theorem twoLive_run (success : compile p facts = .twoLive targets) (limit : Nat) :
    let observed := p.source.runFrom model (3 * limit + 2) 0 input
    targets.cf.run evalOp (3 * limit + 3) (encodeValues input) =
      observed.map (fun value => Env.cons value .nil) ∧
    targets.numbered.run (Join.model model) limit input =
      observed.map (fun value => (Tuple.cons value .nil : Tuple (Join.model model).Val [.value (.data result)])) := by
  obtain ⟨rfl, _, _⟩ := (compile_twoLive_iff targets).mp success
  exact ⟨TwoBackedges.MLIR.CF.lower_run p input (3 * limit + 2),
    TwoBackedges.Numbered.lower_run p model limit input⟩

theorem twoLive_returns_iff (success : compile p facts = .twoLive targets) (value : Word result) :
    let native := ∃ fuel, p.source.runFrom model fuel 0 input = some value
    ((∃ fuel, targets.cf.run evalOp fuel (encodeValues input) = some (.cons value .nil)) ↔ native) ∧
      (targets.numbered.Returns (Join.model model) input (.cons value .nil) ↔ native) := by
  obtain ⟨rfl, _, _⟩ := (compile_twoLive_iff targets).mp success
  exact ⟨TwoBackedges.MLIR.CF.returns_iff p input value, TwoBackedges.Numbered.returns_iff p model input value⟩

theorem twoLive_noReturn_iff (success : compile p facts = .twoLive targets) :
    let absent := ¬ ∃ value fuel, p.source.runFrom model fuel 0 input = some value
    (targets.cf.Diverges evalOp (encodeValues input) ↔ absent) ∧
      ((∀ fuel, targets.numbered.run (Join.model model) fuel input = none) ↔ absent) := by
  obtain ⟨rfl, _, _⟩ := (compile_twoLive_iff targets).mp success
  exact ⟨TwoBackedges.MLIR.CF.diverges_iff p input, TwoBackedges.Numbered.noReturn_iff p model input⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total
