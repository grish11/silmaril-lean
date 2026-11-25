module

public import Silmaril.Courses.Cambridge.L1.DenotationalInstitution
public import Silmaril.Courses.Cambridge.L1.EffectfulDenotational.Thms

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.EffectfulDenotational.Institution

open CategoryTheory Silmaril.Logic.Fragments Silmaril.Semantics.Operational

/-- Finite successful return atoms over the original L1 configurations. -/
def signature : AtomicSignature := ⟨Config × Config⟩

def model : AtomicModel signature := fun (source, target) =>
  (.ok target.expr, target.store) ∈ run (denote source.expr) source.store

theorem sat_iff (source target : Config) :
    (atomicInstitution.obj signature).Sat (Discrete.mk model) (source, target) ↔
      OperationalInstitution.semantics.May source (.returned target) :=
  return_iff.trans (OperationalInstitution.may_return_iff _ _).symm

/-- The existing read-only return sentences include into the full signature. -/
def includeReadOnly : DenotationalInstitution.signature ⟶ signature :=
  ⟨fun (source, target) => (source.val, target)⟩

/-- The full model restricts along the inclusion to the original read-only model. -/
theorem reduct_readOnly :
    (atomicInstitution.map includeReadOnly).mod.obj (Discrete.mk model) =
      Discrete.mk DenotationalInstitution.model := by
  exact congrArg Discrete.mk (funext fun ⟨source, target⟩ => propext
    ((sat_iff source.val target).trans (DenotationalInstitution.sat_iff source target).symm))

end Silmaril.Courses.Cambridge.L1.EffectfulDenotational.Institution
