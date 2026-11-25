module

public import Silmaril.Semantics.Calco2019.OmegaContinuous.Defs
public import Silmaril.Semantics.Calco2019.Thms
import Silmaril.Proofs.Semantics.Calco2019.OmegaContinuous

/-! # Elgot iteration from pointed ω-cpo enrichment -/

public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory
open OmegaCompletePartialOrder Silmaril.Semantics.Domain

namespace OmegaEnrichment

variable {K : Type u} [Category.{v} K] {Q : Coproducts K}
    [∀ X Y : K, OmegaCompletePartialOrder (X ⟶ Y)] [∀ X Y : K, OrderBot (X ⟶ Y)]
    (E : OmegaEnrichment Q)

/-- Least-fixpoint iteration satisfies naturality and codiagonal. -/
theorem naturalCodiagonal : E.fixpoints.NaturalCodiagonal :=
  Proofs.OmegaContinuous.naturalCodiagonal E

/-- Least-fixpoint iteration is uniform along maps whose precomposition preserves bottom. -/
theorem uniformAt {X Z : K} (h : Z ⟶ X) (strict : ∀ Y, h ≫ (⊥ : X ⟶ Y) = ⊥) :
    E.fixpoints.UniformAt h :=
  Proofs.OmegaContinuous.uniformAt E h strict

end OmegaEnrichment

namespace OmegaContinuousMonad

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {P : Coproducts C}
    {T : Monad C} [T.Strong] [∀ X Y : Kleisli T, OmegaCompletePartialOrder (X ⟶ Y)]
    [∀ X Y : Kleisli T, OrderBot (X ⟶ Y)] (E : OmegaContinuousMonad P T)

include E in
/-- Strict strength and strict postcomposition imply strict precomposition by every pure map. -/
theorem pure_comp_bot {X Z : C} (h : X ⟶ Z) (Y : Kleisli T) :
    (Kleisli.Adjunction.toKleisli T).map h ≫ (⊥ : Kleisli.mk T Z ⟶ Y) = ⊥ :=
  Proofs.OmegaContinuous.pure_comp_bot E h Y

/-- The least solutions obey uniformity for all pure changes of state. -/
theorem uniform : E.toOmegaEnrichment.fixpoints.Uniform (Kleisli.Adjunction.toKleisli T) :=
  fun f g h => E.toOmegaEnrichment.uniformAt _ (E.pure_comp_bot h) f g

/-- Equip the monad with the total guard and its least-fixpoint Conway operator. -/
@[expose] noncomputable def toElgot : GuardedElgotMonad P where
  monad := T
  guard := Guardedness.greatest _
  iteration := {
    toFixpoints := E.toOmegaEnrichment.fixpoints
    naturalCodiagonal := E.toOmegaEnrichment.naturalCodiagonal
    dinaturality := E.toOmegaEnrichment.fixpoints.dinaturality_of_uniform
      (P.kleisliPreservesSelected T) (fun X => ⟨X.of, rfl⟩)
      E.toOmegaEnrichment.naturalCodiagonal E.uniform }
  uniformity := E.uniform

end OmegaContinuousMonad
end Silmaril.Calco2019
