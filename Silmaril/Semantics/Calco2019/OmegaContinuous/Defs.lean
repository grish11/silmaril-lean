module

public import Silmaril.Semantics.Calco2019.Defs
public import Silmaril.Semantics.Categories.Thms
public import Silmaril.Semantics.Domain.Kleene

/-! # Pointed ω-cpo enrichment for CALCO iteration

The enrichment and strength conditions are from Definition 5.5 of Goncharov,
Rauch, Schröder and Jakob, *Unguarded Recursion on Coinductive Resumptions*,
doi:10.23638/LMCS-14(3:10)2018.
-/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory
open scoped MonoidalCategory
open OmegaCompletePartialOrder Silmaril.Semantics.Domain

/-- Continuous composition and selected copairing on pointed ω-cpo homs,
with strict postcomposition. -/
structure OmegaEnrichment {K : Type u} [Category.{v} K] (Q : Coproducts K)
    [∀ X Y : K, OmegaCompletePartialOrder (X ⟶ Y)] [∀ X Y : K, OrderBot (X ⟶ Y)] :
    Prop where
  comp_continuous {X Y Z : K} : ωScottContinuous fun p : (X ⟶ Y) × (Y ⟶ Z) => p.1 ≫ p.2
  desc_continuous {X Y Z : K} : ωScottContinuous fun p : (X ⟶ Z) × (Y ⟶ Z) => Q.desc p.1 p.2
  bot_comp {X Y Z : K} (g : Y ⟶ Z) : (⊥ : X ⟶ Y) ≫ g = ⊥

/-- Whiskering a Kleisli map to the left using the tensorial strength. -/
def strengthWhisker {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {T : Monad C} [T.Strong] (A : C) {X Y : Kleisli T} (f : X ⟶ Y) :
    Kleisli.mk T (A ⊗ X.of) ⟶ Kleisli.mk T (A ⊗ Y.of) :=
  kleisliArrow ((A ◁ f.of) ≫ Monad.Strong.strength A Y.of)

/-- Definition 5.5's enrichment conditions on a strong monad with chosen
coproducts. The CALCO iteration laws also make sense without distributivity. -/
structure OmegaContinuousMonad {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (P : Coproducts C) (T : Monad C) [T.Strong]
    [∀ X Y : Kleisli T, OmegaCompletePartialOrder (X ⟶ Y)]
    [∀ X Y : Kleisli T, OrderBot (X ⟶ Y)] : Prop
    extends OmegaEnrichment (P.kleisli T) where
  strength_continuous (A : C) {X Y : Kleisli T} :
    ωScottContinuous (strengthWhisker (T := T) A (X := X) (Y := Y))
  strength_bot (A : C) {X Y : Kleisli T} :
    strengthWhisker A (⊥ : X ⟶ Y) = ⊥

namespace OmegaEnrichment

variable {K : Type u} [Category.{v} K] {Q : Coproducts K}
    [∀ X Y : K, OmegaCompletePartialOrder (X ⟶ Y)] [∀ X Y : K, OrderBot (X ⟶ Y)]
    (E : OmegaEnrichment Q)

/-- One unfolding, continuous by composition and copairing. -/
def unfolding {X Y : K} (f : X ⟶ Q.sum Y X) : (X ⟶ Y) →𝒄 (X ⟶ Y) :=
  ContinuousHom.ofFun (fun g => f ≫ Q.desc (𝟙 Y) g)
    (E.comp_continuous.comp (Prod.ωScottContinuous.prodMk ωScottContinuous.const
      (E.desc_continuous.comp
        (Prod.ωScottContinuous.prodMk ωScottContinuous.const ωScottContinuous.id))))

/-- Least-fixpoint iteration equips the selected coproducts with total guarded fixpoints. -/
noncomputable def fixpoints : (Guardedness.greatest Q).Fixpoints where
  iterate f _ := fix (E.unfolding f)
  fixpoint f _ := fix_eq (E.unfolding f)

end OmegaEnrichment
end Silmaril.Calco2019
