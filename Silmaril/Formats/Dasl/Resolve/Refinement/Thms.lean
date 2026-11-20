module

public import Silmaril.Formats.Dasl.Resolve.Thms
public import Silmaril.Formats.Dasl.Resolve.Refinement.Defs
public import Silmaril.Formats.Dasl.Thms
import Silmaril.Proofs.Formats.Dasl.Refinement

public section

namespace Silmaril.Formats.Dasl

variable {Name : Type} {store : Store Name}

/-- Every included partial observation of the same shallow value refines into
the finite full expansion. Unresolved links do not assert payload bindings. -/
theorem Expands.refines (bound : store.Binding) {observed : Partial Name} {source : Shallow Name} {target : Named Name}
    (expanded : Expands store source target) (view : observed.shallow = source) (included : observed.bindings.Subset store) :
    Extends observed target.embed :=
  Proofs.Formats.Dasl.Refinement.extends_full bound view included expanded

/-- A root's unique finite full expansion is the greatest of its partial
observations, not the only one. Only name-to-payload binding is required. -/
theorem FullNames.refines (bound : store.Binding) {root : Name} {observed : Partial Name} {target : Named Name}
    (full : FullNames store root target) (observation : PartialNames store root observed) : Extends observed target.embed := by
  obtain ⟨_, stored, expanded⟩ := full
  exact expanded.refines bound (bound.1 observation.1 stored) observation.2

/-- A nontrivial partial observation exists exactly when the stored root has
a direct, readable edge, regardless of cycles or missing deeper bindings. -/
theorem nontrivial_partial_iff (bound : store.Binding) (root : Name) :
    (∃ observed, PartialNames store root observed ∧ observed.HasKnownBinding) ↔
      ∃ source, store.objects root source ∧ source.HasReadableLink store :=
  Proofs.Formats.Dasl.Refinement.nontrivial_iff bound root

theorem partialOnly_iff (bound : store.Binding) (root : Name) :
    PartialOnly store root ↔ (∃ source, store.objects root source ∧ source.HasReadableLink store) ∧
      ¬ ∃ target, FullNames store root target :=
  (nontrivial_partial_iff bound root).and Iff.rfl

end Silmaril.Formats.Dasl
