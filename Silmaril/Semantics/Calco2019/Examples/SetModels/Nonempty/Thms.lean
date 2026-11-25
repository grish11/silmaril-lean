module

public import Silmaril.Semantics.Calco2019.Examples.SetModels.Nonempty.Defs
public import Silmaril.Semantics.Calco2019.Examples.TypeKleisli.Thms
import Silmaril.Proofs.Semantics.Calco2019.Examples.NonemptyPowerset

/-! # The guarded Elgot structure of the nonempty powerset -/

public section

universe u

namespace Silmaril.Calco2019.Examples.SetModels.NonemptyPowerset

instance : LawfulMonad (NonemptyPowerset.{u}) := Proofs.lawful

/-- Direct return satisfies all three guard axioms. -/
noncomputable def guard : TypeKleisli.Guard (NonemptyPowerset.{u}) :=
  Proofs.guard

theorem guard_holds_iff {X Y Z : Type u} (f : X → NonemptyPowerset (Y ⊕ Z)) :
    guard.holds f ↔ Guarded f := by
  unfold guard
  rfl

/-- Restrict the existing powerset solution to nonempty sets. -/
noncomputable def laws : TypeKleisli.Iteration (NonemptyPowerset.{u}) guard :=
  Proofs.laws

theorem laws_run {X Y : Type u} (f : X → NonemptyPowerset (Y ⊕ X)) (hf : guard.holds f) :
    laws.run f hf = nonemptyIter f ((guard_holds_iff f).mp hf) :=
  Proofs.laws_run f hf

/-- Examples 10(2) and 20(2) with fixpoint, all Conway laws, and pure uniformity. -/
noncomputable def guardedElgot : GuardedElgotMonad typeCoproducts.{u} :=
  TypeKleisli.assemble laws

end Silmaril.Calco2019.Examples.SetModels.NonemptyPowerset
