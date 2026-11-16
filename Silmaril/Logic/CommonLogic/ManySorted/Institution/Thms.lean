module

public import Silmaril.Logic.CommonLogic.ManySorted.Institution.Defs

/-! Global comparison uses decoder naturality; it does not assert naturality of chosen expansions. -/
@[expose] public section
noncomputable section

namespace Silmaril.Logic.CommonLogic.ManySorted.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic

@[simp] theorem reduct_id (S : FOL.Signature) : typedReduct (𝟙 S) = 𝟭 (TypedModel S) := by
  unfold typedReduct
  simp only [signatureMap_id]
  rfl

@[simp] theorem reduct_comp {S T U : FOL.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    typedReduct (f ≫ g) = typedReduct g ⋙ typedReduct f := by
  unfold typedReduct
  simp only [signatureMap_comp]
  rfl

theorem corridor_id (S : FOL.Signature) : corridor (𝟙 S) = 𝟙 (room S) := by
  apply Room.hom_ext
  · funext p
    change p.map (signatureMap (𝟙 S)) = p
    rw [signatureMap_id]
    exact Core.Formula.map_id p
  · exact reduct_id S

theorem corridor_comp {S T U : FOL.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    corridor (f ≫ g) = corridor f ≫ corridor g := by
  apply Room.hom_ext
  · funext p
    change p.map (signatureMap (f ≫ g)) = (p.map (signatureMap f)).map (signatureMap g)
    rw [signatureMap_comp]
    exact Core.Formula.map_comp (signatureMap f) (signatureMap g) p
  · exact reduct_comp f g

/-- All public FOL sort, operation and relation maps are admitted. -/
def institution : FOL.Signature ⥤ Room.{0, 0, 1} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

def inst : Inst.{1, 0, 0, 0, 1} := ⟨FOL.Signature, institution⟩

/-- The identity signature functor retains the full many-sorted source category.
Its target room at S has CL signature `signature S` and operation-typed CL models. -/
def comorphism : Inst.CoHom FOL.inst inst where
  Φ := 𝟭 FOL.Signature
  ρ :=
    { app := Expansion.comparison
      naturality := fun {_ _} f =>
        Room.hom_ext (funext fun p => (sentence_map f p).symm) (models_natural f).symm }

/-- Pointwise isomorphic recovery; literal equality of source model objects is not asserted. -/
theorem isoExpansive (S : FOL.Signature) :
    Corridor.IsoExpansive (comorphism.ρ.app S) := Expansion.isoExpansive S

theorem elemExpansive : comorphism.ElemExpansive := Expansion.elemExpansive

theorem faithful : comorphism.Faithful := elemExpansive.faithful

theorem entails_iff (S : FOL.Signature) (Γ : Set (FOL.Sentence S)) (p : FOL.Sentence S) :
    (FOL.room S).Entails Γ p ↔ (room S).Entails (sentence '' Γ) (sentence p) :=
  comorphism.entails_iff_of_elemExpansive elemExpansive S Γ p

theorem satisfiable_iff (S : FOL.Signature) (Γ : Set (FOL.Sentence S)) :
    (∃ M : FOL.Structure S, ∀ p ∈ Γ, p.Holds M) ↔
      ∃ N : TypedModel S, ∀ q ∈ sentence '' Γ, (room S).Sat N q :=
  Expansion.satisfiable_iff S Γ

theorem unsatisfiable_iff (S : FOL.Signature) (Γ : Set (FOL.Sentence S)) :
    (¬ ∃ M : FOL.Structure S, ∀ p ∈ Γ, p.Holds M) ↔
      ¬ ∃ N : TypedModel S, ∀ q ∈ sentence '' Γ, (room S).Sat N q :=
  not_congr (satisfiable_iff S Γ)

/-- Forget typing by the full model inclusion; the signature projection is `signatures`. -/
def forgetComparison (S : FOL.Signature) : Core.room (signature S) ⟶ room S :=
  ⟨id, (typed S).ι, fun _ _ => Iff.rfl⟩

/-- An institution morphism, with the honest model restriction from raw CL to typed rooms. -/
def typedForget : Inst.Hom inst Core.inst where
  Φ := signatures
  η :=
    { app := forgetComparison
      naturality := fun {_ _} _ => Room.hom_ext rfl rfl }

end Silmaril.Logic.CommonLogic.ManySorted.Institution
