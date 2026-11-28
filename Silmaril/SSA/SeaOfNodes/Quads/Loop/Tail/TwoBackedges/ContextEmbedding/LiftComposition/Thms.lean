module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Ports.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Lift
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Observation

/-! Composed typed lifts and truth at the original, intermediate, and final entries. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition

open SeaOfNodes.Diamond.SCCP (TupleCovers)
open Silmaril.MLIR.Arith (Width)
open Composition (thenMap)
open Factorization (Consistent liftChecked liftChecked_none_iff reduct_image_iff)
open Identification (PortMap reduct)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted Backend Sentence)
open Reindex.Guarded.Institution (Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {result : Width}

/-- The reduct and the unused values determine the checked lift uniquely. -/
theorem lift_spec (map : PortMap S T) (input : Valuation S) (fill target : Valuation T) :
    liftChecked map input fill = some target ↔
      reduct map target = input ∧ AgreesOnUnused map target fill :=
  Proofs.lift_spec map input fill target

theorem image_through_iff (first : PortMap S T) (second : PortMap T U) (input : Valuation S) :
    Consistent (thenMap first second) input ↔
      ∃ mid, reduct first mid = input ∧ Consistent second mid :=
  Proofs.image_through_iff first second input

theorem reduct_image_through_iff (first : PortMap S T) (second : PortMap T U) (input : Valuation S) :
    (∃ target, reduct (thenMap first second) target = input) ↔
      ∃ mid, reduct first mid = input ∧ Consistent second mid :=
  (reduct_image_iff _ _).trans (image_through_iff first second input)

/-- The two checked passes produce the same final valuation as the composed
lift, along with its exact pullback to the middle signature. -/
theorem liftStaged_eq_map (first : PortMap S T) (second : PortMap T U)
    (input : Valuation S) (fill : Valuation U) :
    liftStaged first second input fill =
      (liftChecked (thenMap first second) input fill).map (fun target => (reduct second target, target)) :=
  Proofs.liftStaged_eq_map first second input fill

theorem liftStaged_spec (first : PortMap S T) (second : PortMap T U) (input : Valuation S) (fill : Valuation U)
    (mid : Valuation T) (target : Valuation U) :
    liftStaged first second input fill = some (mid, target) ↔
      reduct second target = mid ∧ reduct first mid = input ∧ AgreesOnUnused (thenMap first second) target fill :=
  Proofs.liftStaged_spec first second input fill mid target

theorem liftStaged_none_iff (first : PortMap S T) (second : PortMap T U)
    (input : Valuation S) (fill : Valuation U) :
    liftStaged first second input fill = none ↔ ¬ Consistent (thenMap first second) input := by
  rw [liftStaged_eq_map, Option.map_eq_none_iff, liftChecked_none_iff]

variable {first : PortMap S T} {second : PortMap T U}
variable {input : Valuation S} {mid : Valuation T} {fill target : Valuation U}

theorem coverage_at_lift (q : Compared first second result)
    (lifted : liftStaged first second input fill = some (mid, target)) :
    (TupleCovers (@Admitted.facts _ _ U.bankEq q.staged.source) target ↔
      TupleCovers (@Admitted.facts _ _ T.bankEq q.intermediate.source) mid) ∧
    (TupleCovers (@Admitted.facts _ _ T.bankEq q.intermediate.source) mid ↔
      TupleCovers (@Admitted.facts _ _ S.bankEq q.source) input) ∧
    (TupleCovers (@Admitted.facts _ _ U.bankEq q.direct.source) target ↔
      TupleCovers (@Admitted.facts _ _ S.bankEq q.source) input) :=
  Proofs.coverage_at_lift q lifted

/-- Partial-word equality preserves every finite return and absence of a
finite return. Each backend uses its original witnesses. -/
theorem observations_at_lift (q : Compared first second result)
    (lifted : liftStaged first second input fill = some (mid, target)) (backend : Backend) :
    backend.observe q.staged.artifacts target = backend.observe q.intermediate.artifacts mid ∧
    backend.observe q.intermediate.artifacts mid = @Admitted.observe _ _ S.bankEq q.source input ∧
    backend.observe q.direct.artifacts target = @Admitted.observe _ _ S.bankEq q.source input :=
  Proofs.observations_at_lift q lifted backend

/-- Pull the existing equations and termination sentences through the actual
intermediate emission, or directly to the original valuation. -/
theorem satisfaction_at_lift (lifted : liftStaged first second input fill = some (mid, target))
    (backend : Backend) (sentence : Sentence (Compared first second result)) :
    ((sentence.map Compared.staged).Holds (fun q => backend.observe q.artifacts target) ↔
      (sentence.map Compared.intermediate).Holds (fun q => backend.observe q.artifacts mid)) ∧
    ((sentence.map Compared.intermediate).Holds (fun q => backend.observe q.artifacts mid) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ S.bankEq q.source input)) ∧
    ((sentence.map Compared.direct).Holds (fun q => backend.observe q.artifacts target) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ S.bankEq q.source input)) :=
  Proofs.satisfaction_at_lift lifted backend sentence

/-- Both lifts start at the same old input. Their unused values and backend
witnesses can vary independently. -/
theorem satisfaction_coherent {otherMid : Valuation T} {otherFill otherTarget : Valuation U}
    (staged : liftStaged first second input fill = some (mid, target))
    (direct : liftStaged first second input otherFill = some (otherMid, otherTarget))
    (stagedBackend directBackend : Backend) (sentence : Sentence (Compared first second result)) :
    (sentence.map Compared.staged).Holds (fun q => stagedBackend.observe q.artifacts target) ↔
      (sentence.map Compared.direct).Holds (fun q => directBackend.observe q.artifacts otherTarget) :=
  let path := satisfaction_at_lift staged stagedBackend sentence
  path.1.trans (path.2.1.trans (satisfaction_at_lift direct directBackend sentence).2.2.symm)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition
