module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Preservation

/-! # Guarded Paper functor into shaped stateful observations -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open CategoryTheory

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L K P : List (Ty κ)}
variable (M : Shape.Model.{u,v,w,x} Φ Γ)

theorem interpretHom_id :
    interpretHom M (LambdaSSA.Region.Paper.Hom.identity Γ L) =
      𝟙 (⟨L⟩ : Shape.Category.Interface M.raw.α M.raw.σ M.atomType) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.interpretHom_id M

theorem interpretHom_comp (f : LambdaSSA.Region.Paper.Hom (Φ := Φ) Γ L K)
    (g : LambdaSSA.Region.Paper.Hom (Φ := Φ) Γ K P) :
    interpretHom M (f.compose g) = interpretHom M f ≫ interpretHom M g :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.interpretHom_comp M f g

/-- The guarded continuation category at fixed capture interprets into the
category of shaped stateful observations for the same model. -/
noncomputable def interpretation :
    LambdaSSA.Region.Paper.Interface Φ Γ ⥤ Shape.Category.Interface M.raw.α M.raw.σ M.atomType where
  obj X := ⟨X.labels⟩
  map f := interpretHom M f
  map_id _ := interpretHom_id M
  map_comp := interpretHom_comp M

/-- Restrict the interpretation to the installed empty-capture singleton category. -/
noncomputable def singletonInterpretation (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ))) :
    LambdaSSA.Region.Paper.TypeCategory (τ := Ty κ) Φ ⥤
      Shape.Category.Interface M.raw.α M.raw.σ M.atomType :=
  inducedFunctor (fun A : Ty κ => (⟨[A]⟩ : LambdaSSA.Region.Paper.Interface Φ [])) ⋙ interpretation M

@[simp] theorem singletonInterpretation_map_ofRegion
    (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ)))
    {A B : Ty κ} {r : LambdaSSA.Region Φ} (hr : LambdaSSA.Region.ValueBranches [A] r [B])
    {a : Value M.raw.α} (ha : ValueTyped M.atomType a A) (s : M.raw.σ) :
    ((singletonInterpretation M).map (LambdaSSA.Region.Paper.TypeCategory.ofRegion hr)).run (0 : Fin 1) ⟨a, ha⟩ s =
      Shape.denote (.native ⟨r, hr.hasType⟩) (M.extend ha) s :=
  rfl

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
