module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Lift
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms

/-! Actual guarded observations commute with both checked pulls. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Proofs

open SeaOfNodes.Diamond.SCCP (TupleCovers)
open Silmaril.MLIR.Arith (Width)
open Composition (thenMap reduct_thenMap)
open Identification (PortMap reduct compile_coverage compile_observe)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted Backend Sentence)
open Reindex.Guarded.Institution (Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {result : Width}
variable {first : PortMap S T} {second : PortMap T U}
variable {input : Valuation S} {mid : Valuation T} {fill target : Valuation U}

theorem coverage_at_lift (q : Compared first second result)
    (lifted : liftStaged first second input fill = some (mid, target)) :
    (TupleCovers (@Admitted.facts _ _ U.bankEq q.staged.source) target ↔
      TupleCovers (@Admitted.facts _ _ T.bankEq q.intermediate.source) mid) ∧
    (TupleCovers (@Admitted.facts _ _ T.bankEq q.intermediate.source) mid ↔
      TupleCovers (@Admitted.facts _ _ S.bankEq q.source) input) ∧
    (TupleCovers (@Admitted.facts _ _ U.bankEq q.direct.source) target ↔
      TupleCovers (@Admitted.facts _ _ S.bankEq q.source) input) := by
  obtain ⟨secondReduct, firstReduct, _⟩ := (liftStaged_spec first second input fill mid target).mp lifted
  exact ⟨by simpa only [secondReduct] using compile_coverage second _ q.secondOk target,
    by simpa only [firstReduct] using compile_coverage first _ q.firstOk mid,
    by simpa only [reduct_thenMap, secondReduct, firstReduct] using compile_coverage _ _ q.directOk target⟩

theorem observations_at_lift (q : Compared first second result)
    (lifted : liftStaged first second input fill = some (mid, target)) (backend : Backend) :
    backend.observe q.staged.artifacts target = backend.observe q.intermediate.artifacts mid ∧
    backend.observe q.intermediate.artifacts mid = @Admitted.observe _ _ S.bankEq q.source input ∧
    backend.observe q.direct.artifacts target = @Admitted.observe _ _ S.bankEq q.source input := by
  obtain ⟨secondReduct, firstReduct, _⟩ := (liftStaged_spec first second input fill mid target).mp lifted
  refine ⟨?_, ?_, ?_⟩
  · rw [compile_observe second _ q.secondOk backend, secondReduct, q.intermediate.generated]
    exact (@Backend.observe_eq_source _ _ T.bankEq backend q.intermediate.source mid).symm
  · rw [compile_observe first _ q.firstOk backend, firstReduct]
  · rw [compile_observe _ _ q.directOk backend, reduct_thenMap, secondReduct, firstReduct]

theorem satisfaction_at_lift (lifted : liftStaged first second input fill = some (mid, target))
    (backend : Backend) (sentence : Sentence (Compared first second result)) :
    ((sentence.map Compared.staged).Holds (fun q => backend.observe q.artifacts target) ↔
      (sentence.map Compared.intermediate).Holds (fun q => backend.observe q.artifacts mid)) ∧
    ((sentence.map Compared.intermediate).Holds (fun q => backend.observe q.artifacts mid) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ S.bankEq q.source input)) ∧
    ((sentence.map Compared.direct).Holds (fun q => backend.observe q.artifacts target) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ S.bankEq q.source input)) := by
  have toMiddle (q : Compared first second result) := (observations_at_lift q lifted backend).1
  have fromMiddle (q : Compared first second result) := (observations_at_lift q lifted backend).2.1
  have fromDirect (q : Compared first second result) := (observations_at_lift q lifted backend).2.2
  cases sentence <;> simp only [Sentence.map, Sentence.Holds, toMiddle, fromMiddle, fromDirect,
    iff_self, and_self]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Proofs
