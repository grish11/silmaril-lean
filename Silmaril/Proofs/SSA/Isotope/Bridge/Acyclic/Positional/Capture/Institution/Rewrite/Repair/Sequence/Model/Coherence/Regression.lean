module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Coherence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

open LambdaSSA (Region)
open LambdaSSA.Semantics.Categorical

attribute [local instance] traceInstructions

private abbrev U : Sorts := .unit

private def localTypes (A : Sorts) : Fin 1 → Sorts := fun _ => .coprod U A

private def entry : Region signature.Instr := .br 0 (.inl .unit)

private def blocks : Fin 1 → Region signature.Instr := fun _ =>
  .case (.var 0) (.br 1 (.op (.emit true) .unit)) (.br 0 (.inr (.var 0)))

private def loop : Region signature.Instr := .cfg entry 1 blocks

private theorem entryTy (A : Sorts) :
    Region.HasType [] entry (List.ofFn (localTypes A) ++ [U]) :=
  .br rfl (.inl .unit)

private theorem blockTy (A : Sorts) (i : Fin 1) :
    Region.HasType [localTypes A i] (blocks i) (List.ofFn (localTypes A) ++ [U]) :=
  .case (.var rfl) (.br rfl (.op .unit)) (.br rfl (.inr (.var rfl)))

private theorem loopTy (A : Sorts) : Region.HasType [] loop [U] :=
  .cfg (localTypes A) (entryTy A) (blockTy A)

private theorem loopWitness (A : Sorts) :
    ∃ f, RegionDenotes traceJ traceTypes (loopTy A) f := by
  obtain ⟨entryArrow, de⟩ := regionDenotes_exists traceJ traceTypes (entryTy A)
  let blockArrow := fun i => denoteRegion traceJ traceTypes (blockTy A i)
  obtain ⟨dispatch, dc⟩ := collectiveDenotes_exists_succ traceJ traceTypes
    0 [] (localTypes A) [U] blockArrow
  exact ⟨_, .cfg (entryTy A) (blockTy A) de
    (fun i => denoteRegion_spec traceJ traceTypes (blockTy A i)) dc⟩

-- These witnesses have the same outward interface. Their recursive
-- dispatchers may carry different right summands on the local label.
example : ∃ f g, RegionDenotes traceJ traceTypes (loopTy .unit) f ∧
    RegionDenotes traceJ traceTypes (loopTy .empty) g ∧ f = g := by
  obtain ⟨f, df⟩ := loopWitness .unit
  obtain ⟨g, dg⟩ := loopWitness .empty
  exact ⟨f, g, df, dg, traceRegionCoherent.denotes_eq df dg⟩

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence
