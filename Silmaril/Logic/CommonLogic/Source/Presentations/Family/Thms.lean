module

public import Silmaril.Logic.CommonLogic.Source.Presentations.Family.Defs

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.Presentations.Family
open CategoryTheory Silmaril.Logic.Institution

/-- Both translations use the same full model categories as the fixed comparison. -/
theorem toCore_modelExpansive : toCore.ModelExpansive :=
  fun A => CLIF.toCore_modelExpansive A.names

theorem toFOL_modelExpansive : toFOL.ModelExpansive :=
  fun A => fixed_modelExpansive A.names

/-- The two routes in the comparison triangle are exactly the same corridor. -/
theorem comparison_triangle (A : Signature) :
    toFOL.ρ.app A = toCore.ρ.app A ≫ FiniteListFOL.comparison A.core := rfl

theorem core_square {A B : Signature} (f : A ⟶ B) :
    corridor f ≫ CLIF.toCore B.names = CLIF.toCore A.names ≫ Core.corridor f.symbols :=
  toCore.ρ.naturality f

theorem fol_square {A B : Signature} (f : A ⟶ B) :
    corridor f ≫ fixed B.names = fixed A.names ≫ FiniteListFOL.corridor f.symbols :=
  toFOL.ρ.naturality f

theorem consequence_iff (A : Signature) (Γ : Set (CLIF.Text A.names)) (text : CLIF.Text A.names) :
    (CLIF.room A.names).Entails Γ text ↔
      (FiniteListFOL.room A.core).Entails ((toFOL.ρ.app A).sen '' Γ) ((toFOL.ρ.app A).sen text) :=
  fixed_consequence_iff A.names Γ text

theorem sat_iff (A : Signature) (Γ : Set (CLIF.Text A.names)) :
    (∃ M : (CLIF.room A.names).Mod, ∀ p ∈ Γ, (CLIF.room A.names).Sat M p) ↔
    ∃ N : (FiniteListFOL.room A.core).Mod,
      ∀ p ∈ (toFOL.ρ.app A).sen '' Γ, (FiniteListFOL.room A.core).Sat N p :=
  fixed_sat_iff A.names Γ

theorem unsat_iff (A : Signature) (Γ : Set (CLIF.Text A.names)) :
    (¬ ∃ M : (CLIF.room A.names).Mod, ∀ p ∈ Γ, (CLIF.room A.names).Sat M p) ↔
    ¬ ∃ N : (FiniteListFOL.room A.core).Mod,
      ∀ p ∈ (toFOL.ρ.app A).sen '' Γ, (FiniteListFOL.room A.core).Sat N p :=
  not_congr (sat_iff A Γ)

end Silmaril.Logic.CommonLogic.Source.Presentations.Family
