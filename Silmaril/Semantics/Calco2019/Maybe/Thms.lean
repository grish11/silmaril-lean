module

public import Silmaril.Semantics.Calco2019.Maybe.Defs
import Silmaril.Proofs.Semantics.Calco2019.Maybe

/-! # The comparison from Maybe to a total Elgot monad -/

public section

universe u v

namespace Silmaril.Calco2019.Maybe

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (T : GuardedElgotMonad P) (total : T.IsElgot)

/-- Kleisli postcomposition preserves divergence by naturality of iteration. -/
theorem divergence_natural {X Y Z : C} (g : Y ⟶ T.monad.obj Z) :
    divergence T total X Y ≫ T.monad.map g ≫ T.monad.μ.app Z =
      divergence T total X Z :=
  Proofs.divergence_natural T total g

/-- Pure precomposition preserves divergence by uniformity of iteration. -/
theorem divergence_uniform {X Z Y : C} (h : Z ⟶ X) :
    h ≫ divergence T total X Y = divergence T total Z Y :=
  Proofs.divergence_uniform T total h

/-- Send returns to the unit and exceptions to divergence. For a terminal
exception object this is the candidate for the §1.3 Elgot comparison. -/
@[expose]
noncomputable def comparison (E : C) : monad P E ⟶ T.monad where
  app := interpret T total E
  naturality _ _ f := by exact Proofs.map_naturality T total E f
  app_η X := by
    change (P.inl ≫ 𝟙 (P.sum X E)) ≫ interpret T total E X = _
    simp [interpret]
  app_μ X := by exact Proofs.map_mul T total E X

/-- For any total iteration on (X \mapsto X + 1), the pure self-loop returns the failure value. -/
theorem divergence_eq_failure [HasInitial C] {E : C} (terminal : IsTerminal E)
    (S : GuardedElgotMonad P) (hs : S.IsElgot) (hm : S.monad = monad P E) (Y : C) :
    divergence S hs E Y ≫ eqToHom (congrArg (fun M : CategoryTheory.Monad C => M.obj Y) hm) =
      P.inr :=
  Proofs.maybe_divergence terminal S hs hm Y

/-- Any Elgot comparison from Maybe has the canonical components. This is
the uniqueness clause of initiality and applies to any total iteration on Maybe. -/
theorem comparison_unique [HasInitial C] {E : C} (terminal : IsTerminal E)
    (S : GuardedElgotMonad P) (hs : S.IsElgot) (hm : S.monad = monad P E)
    (m : GuardedElgotMonadHom P S T) (Y : C) :
    m.hom.app Y = eqToHom (congrArg (fun M : CategoryTheory.Monad C => M.obj Y) hm) ≫
      (comparison T total E).app Y :=
  Proofs.morphism_unique T total terminal S hs hm m Y

end Silmaril.Calco2019.Maybe
