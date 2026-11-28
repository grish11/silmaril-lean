module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Defs

/-! # Compare exact regions after routing their branch payloads -/

@[expose] public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

/-- The type of a sum with payload `A` on the selected side and `D` on the other. -/
def CaseTag.sumType {τ : Type u} [TypeFormers τ] (tag : CaseTag) (A D : τ) : τ :=
  match tag with
  | .inl => Silmaril.coprod A D
  | .inr => Silmaril.coprod D A

/-- The pure map of a selected payload into its original sum. -/
noncomputable def CaseTag.injection {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
    [HasFiniteCoproducts V] {τ : Type u} [TypeFormers τ] (tag : CaseTag) (M : TypeModel τ V)
    (A D : τ) : M.obj A ⟶ M.obj (tag.sumType A D) :=
  match tag with
  | .inl => coprod.inl ≫ (M.coprodIso A D).inv
  | .inr => coprod.inr ≫ (M.coprodIso D A).inv

end Silmaril.Isotope.LambdaSSA

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)]
  {L K : LCtx (Ty κ)} {Y : V} (left : labelObj M L ⟶ Y) (right : labelObj M K ⟶ Y)

/-- A loop-free pair of rows has the same determined computations. A branch
can route its original payload or inject it on either side in the second row.
The branch equations are pure equations of the indexed label injections. -/
inductive RegionConstructorRoutes : VCtx (Ty κ) → Region Φ → Region Φ → Prop where
  | br {Γ i j a A} (hl : At L i A) (hr : At K j A) (arg : DeterminedTerm Γ a A)
      (route : labelInject M i hl ≫ left = labelInject M j hr ≫ right) :
      RegionConstructorRoutes Γ (.br i a) (.br j a)
  | inl {Γ i j a A D} (hl : At L i A) (hr : At K j (Silmaril.coprod A D))
      (arg : DeterminedTerm Γ a A)
      (route : labelInject M i hl ≫ left =
        (coprod.inl ≫ (M.coprodIso A D).inv) ≫ labelInject M j hr ≫ right) :
      RegionConstructorRoutes Γ (.br i a) (.br j (.inl a))
  | inr {Γ i j a A D} (hl : At L i A) (hr : At K j (Silmaril.coprod D A))
      (arg : DeterminedTerm Γ a A)
      (route : labelInject M i hl ≫ left =
        (coprod.inr ≫ (M.coprodIso D A).inv) ≫ labelInject M j hr ≫ right) :
      RegionConstructorRoutes Γ (.br i a) (.br j (.inr a))
  | case {Γ a l r l' r' A D} (tag : TypeDetermined Γ a (Silmaril.coprod A D))
      (arg : DeterminedTerm Γ a (Silmaril.coprod A D))
      (yes : RegionConstructorRoutes (A :: Γ) l l') (no : RegionConstructorRoutes (D :: Γ) r r') :
      RegionConstructorRoutes Γ (.case a l r) (.case a l' r')

variable {C : Type u₂} [Category.{v₂} C]
  [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [InstructionModel J M Φ]

/-- The actual graph arrows agree after the two indicated outward maps. -/
def RegionDenotes.Routes (Γ : VCtx (Ty κ)) (r s : Region Φ) : Prop :=
  ∀ ⦃hr : r.HasType Γ L⦄ ⦃hs : s.HasType Γ K⦄
    ⦃f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)⦄
    ⦃g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)⦄,
    RegionDenotes J M hr f → RegionDenotes J M hs g → f ≫ J.map left = g ≫ J.map right

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
