module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open CategoryTheory.CartesianMonoidalCategory (snd toUnit isTerminalTensorUnit)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind extend duplicate)
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C)

local notation "U" => Functor.StrongPremonoidal.unitIso (J := J)
local notation "T" => Functor.StrongPremonoidal.tensorIso (J := J)

section Freyd

variable [FreydCategory J]

@[reassoc]
private theorem map_snd (R A : V) :
    (T R A).hom ≫ J.map (snd R A) =
      (J.map (toUnit R) ≫ (U).inv) ▷ J.obj A ≫ (λ_ (J.obj A)).hom := by
  rw [← CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom,
    J.map_comp, ← Category.assoc, ← Functor.StrongPremonoidal.tensor_naturality_left,
    Category.assoc, comp_whiskerRight, Category.assoc]
  have e := Functor.StrongPremonoidal.left_unitality (J := J) A
  rw [← e, ← comp_whiskerRight_assoc (U).inv (U).hom, (U).inv_hom_id]
  simp

private theorem extend_snd (h : IsCentral (U).hom) {R A : V}
    (f : J.obj R ⟶ J.obj A) :
    extend J f ≫ J.map (snd R A) = f := by
  have central := (FreydCategory.image_central J (toUnit R)).comp (IsCentral.inv U h)
  have slide := central.1 f
  change (J.map (toUnit R) ≫ (U).inv) ▷ J.obj R ≫ 𝟙_ C ◁ f =
    J.obj R ◁ f ≫ (J.map (toUnit R) ≫ (U).inv) ▷ J.obj A at slide
  simp only [extend, leftTensor, id_whiskerRight, Category.id_comp, Category.assoc]
  rw [map_snd, ← Category.assoc _ _ ((λ_ (J.obj A)).hom), ← slide,
    Category.assoc, leftUnitor_naturality, ← map_snd_assoc]
  rw [Iso.inv_hom_id_assoc, ← J.map_comp_assoc]
  simp [duplicate]

end Freyd

variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₅} [HasTy Φ τ] [InstructionModel J M Φ]

theorem denote_let_eta_proof (h : IsCentral (U).hom)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    denote J M (.let₁ d (.bv (ι := 0))) = denote J M d := by
  change bind J (denote J M d)
    (J.map (envSnocIso M Γ β A).hom ≫ J.map (boundVar M (Γ := Γ) (β := .snoc β A) 0)) =
    denote J M d
  have projection :
      (envSnocIso M Γ β A).hom ≫ boundVar M (Γ := Γ) (β := .snoc β A) 0 =
        snd (envObj M Γ β) (M.obj A) :=
    CartesianMonoidalCategory.associator_hom_snd_snd (ctxObj M Γ) (boundObj M β) (M.obj A)
  rw [← J.map_comp, projection]
  exact extend_snd J h _

theorem denote_unit_eta_proof (h : IsCentral (U).hom)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    (d : Derivation Φ Γ β t (unit : τ)) :
    denote J M (.let₁ d .unit) = denote J M d := by
  let A := (unit : τ)
  let R := envObj M Γ β
  change extend J (denote J M d) ≫
    (J.map (envSnocIso M Γ β A).hom ≫ J.map (toUnit _ ≫ M.unitIso.inv)) = denote J M d
  rw [← J.map_comp]
  have terminal : IsTerminal (M.obj A) := isTerminalTensorUnit.ofIso M.unitIso.symm
  have projection : (envSnocIso M Γ β A).hom ≫ (toUnit _ ≫ M.unitIso.inv) =
      snd R (M.obj A) := terminal.hom_ext _ _
  rw [projection]
  exact extend_snd J h _

end Silmaril.Isotope.LetIter.Semantics.Categorical
