module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends

open Diamond.MLIR.CF.Example (input width)
open SeaOfNodes.Loop.MLIR.CF (evalOp model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Example
  (fullHeader parallelInner parallelTrace report runAt sharedInnerArm skipsMerge source strideUse)

private def targets : Targets source 0 := ((compile source 0).toOption).get (by rfl)

example : Nested.check source 0 = some targets.program := compile_origin (by rfl)
example : targets.prepared.positions = [1, 0] := rfl
example : strideUse targets = some (3, true) := rfl
example : (report targets).predecessors = [3, 2, 4] := rfl

example : compile skipsMerge 0 = .error .shape := compile_shape_refusal rfl
example : (Nested.check fullHeader 0).isSome = true := rfl
example : compile fullHeader 0 = .error .headerProjection := rfl

example : (report targets).guardAndExit = [some (true, 7), some (true, 8), some (false, 16)] := by
  simp only [report, List.map_cons, List.map_nil, Targets.numbered_packet]
  rfl

example : runAt targets 14 15 3 = (some 16, some 16, some 16) := by
  unfold runAt
  rw [targets.cf_run input 14, targets.numbered_run input 3]
  rfl

example : runAt targets 13 14 2 = (none, none, none) := by
  unfold runAt
  rw [targets.cf_run input 13, targets.numbered_run input 2]
  rfl

example : (∃ cfFuel, targets.cf.run evalOp cfFuel (encodeValues input) = some (.cons (16 : Word width) .nil)) ∧
    targets.numbered.Returns (Join.model model) input (.cons (16 : Word width) .nil) := by
  have agreement := targets.returns_iff input (16 : Word width)
  exact ⟨agreement.1.mpr ⟨14, rfl⟩, agreement.2.mpr ⟨14, rfl⟩⟩

private def parallel : Targets parallelInner 0 := ((compile parallelInner 0).toOption).get (by rfl)

example : Nested.check parallelInner 0 = some parallel.program := compile_origin (by rfl)

private def parallelCFBranches : Bool :=
  let p := parallel.program
  let inner := MLIR.CF.siteFrame (carry := carry p) (merge := merge p) (atLatch := atLatch p) p p.inner input
  (parallel.cf.block inner.label).eval evalOp (fun term _ =>
    match term with
    | .condBr _ ⟨.base .merge, _⟩ ⟨.base .merge, _⟩ => true
    | _ => false) (inner.args.append (encodeValues input))

example : parallelCFBranches = true := rfl

example : parallelTrace parallel =
    [((2, 0), some (true, 6)), ((2, 1), some (true, 7)), ((3, 0), some (false, 14))] := by
  simp only [parallelTrace, List.map_cons, List.map_nil, Targets.numbered_packet]
  rfl

example : runAt parallel 13 14 3 = (some 14, some 14, some 14) := by
  unfold runAt
  rw [parallel.cf_run input 13, parallel.numbered_run input 3]
  rfl

example : runAt parallel 12 13 2 = (none, none, none) := by
  unfold runAt
  rw [parallel.cf_run input 12, parallel.numbered_run input 2]
  rfl

example : RVSDG.NestedTheta.Petri.Finishes (Join.model model) parallel.numbered input
    (.cons (14 : Word width) .nil) :=
  (parallel.petri_finishes_iff input (14 : Word width)).mpr ⟨13, rfl⟩

example : compile sharedInnerArm 0 = .error .shape := compile_shape_refusal rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends
