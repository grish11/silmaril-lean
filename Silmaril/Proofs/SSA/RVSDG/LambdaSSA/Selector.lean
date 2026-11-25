module

public import Silmaril.SSA.RVSDG.LambdaSSA.Selector.Defs

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (lift toUnit)
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA (Tm)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj Denotes)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v d h c k
variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

theorem selector_typing [HasTy Φ τ] {Γ : List τ} (n : Nat) (i : Fin (n + 1)) :
    Tm.HasType Γ (selectorLiteral (Φ := Φ) n i) (selectorType n) := by
  induction n with
  | zero => exact .unit
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .inl .unit
    · exact .inr (ih j)

variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D] [HasFiniteCoproducts D]
variable (M : TypeModel τ D)

noncomputable def selectorCopair {Y : D} :
    (n : Nat) → (Fin (n + 1) → (𝟙_ D ⟶ Y)) → (M.obj (selectorType n) ⟶ Y)
  | 0, f => M.unitIso.hom ≫ f 0
  | n + 1, f => (M.coprodIso _ _).hom ≫
      coprod.desc (M.unitIso.hom ≫ f 0) (selectorCopair n (fun j => f j.succ))

set_option backward.isDefEq.respectTransparency false in
private theorem tag_copair {Y : D} (n : Nat) (f : Fin (n + 1) → (𝟙_ D ⟶ Y)) (i : Fin (n + 1)) :
    selectorTag M n i ≫ selectorCopair M n f = f i := by
  induction n with
  | zero =>
    rw [Fin.eq_zero i]
    simp [selectorTag, selectorCopair, selectorType]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [selectorTag, selectorCopair, selectorType, Category.assoc]
    · simp [selectorTag, selectorCopair, selectorType, Category.assoc, ih]

set_option backward.isDefEq.respectTransparency false in
private theorem tag_ext {Y : D} (n : Nat)
    {f g : M.obj (selectorType n) ⟶ Y} (h : ∀ i, selectorTag M n i ≫ f = selectorTag M n i ≫ g) :
    f = g := by
  induction n with
  | zero => exact (cancel_epi M.unitIso.inv).mp (h 0)
  | succ n ih =>
    apply (cancel_epi (M.coprodIso unit (selectorType n)).inv).mp
    apply coprod.hom_ext
    · apply (cancel_epi M.unitIso.inv).mp
      simpa only [selectorTag, selectorType, Fin.cases_zero, Category.assoc] using h 0
    · apply ih
      intro j
      simpa only [selectorTag, selectorType, Fin.cases_succ, Category.assoc] using h j.succ

noncomputable def ssa_selector_colimit (n : Nat) : IsColimit (ssaSelectorCofan M n) :=
  Cofan.IsColimit.mk _ (fun c => selectorCopair M n c.inj)
    (fun c i => tag_copair M n c.inj i)
    (fun c _ h => tag_ext M n (fun i => (h i).trans (tag_copair M n c.inj i).symm))

noncomputable def rv_selector_colimit (sel : Categorical.Selectors D) (n : Nat) :
    IsColimit (rvSelectorCofan sel n) :=
  (sel.colimit n (𝟙_ D)).ofIsoColimit (Cofan.ext (ρ_ (sel.obj n)) (fun i => by
    change Categorical.selectorLeg (sel.tag i) ≫ (ρ_ (sel.obj n)).hom = sel.tag i
    simp [Categorical.selectorLeg, CartesianMonoidalCategory.rightUnitor_hom]))

end Silmaril.SSA.RVSDG.LambdaSSA.Proofs
