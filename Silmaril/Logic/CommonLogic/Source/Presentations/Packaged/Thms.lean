module

public import Silmaril.Logic.CommonLogic.Source.Presentations.Packaged.Defs

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.Presentations.Packaged
open CategoryTheory Silmaril.Logic.Institution

theorem toCore_modelExpansive {I : Type} (A : Signature I) : (toCore A).ModelExpansive :=
  fun M => ⟨M, rfl⟩

theorem toFOL_modelExpansive {I : Type} (A : Signature I) : (toFOL A).ModelExpansive := by
  intro M
  exact FiniteListFOL.comparison_modelExpansive A.global M

theorem core_square {I : Type} {A B : Signature I} (f : A ⟶ B) :
    corridor f ≫ toCore B = toCore A ≫ Core.corridor f.global :=
  (comparison I).ρ.naturality f

theorem fol_square {I : Type} {A B : Signature I} (f : A ⟶ B) :
    corridor f ≫ toFOL B = toFOL A ≫ FiniteListFOL.corridor f.global :=
  (folComparison I).ρ.naturality f

theorem consequence_iff {I : Type} (A : Signature I) (Γ : Set (Text A)) (p : Text A) :
    (room A).Entails Γ p ↔
      (FiniteListFOL.room A.global).Entails ((toFOL A).sen '' Γ) ((toFOL A).sen p) :=
  (toFOL A).entails_map_iff (toFOL_modelExpansive A) Γ p

theorem sat_iff {I : Type} (A : Signature I) (Γ : Set (Text A)) :
    (∃ M : (room A).Mod, ∀ p ∈ Γ, (room A).Sat M p) ↔
    ∃ N : (FiniteListFOL.room A.global).Mod,
      ∀ p ∈ (toFOL A).sen '' Γ, (FiniteListFOL.room A.global).Sat N p := by
  constructor
  · rintro ⟨M, h⟩
    obtain ⟨N, rfl⟩ := toFOL_modelExpansive A M
    refine ⟨N, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact ((toFOL A).sat N p).mpr (h p hp)
  · rintro ⟨N, h⟩
    exact ⟨(toFOL A).mod.obj N, fun p hp => ((toFOL A).sat N p).mp (h _ ⟨p, hp, rfl⟩)⟩

theorem unsat_iff {I : Type} (A : Signature I) (Γ : Set (Text A)) :
    (¬ ∃ M : (room A).Mod, ∀ p ∈ Γ, (room A).Sat M p) ↔
    ¬ ∃ N : (FiniteListFOL.room A.global).Mod,
      ∀ p ∈ (toFOL A).sen '' Γ, (FiniteListFOL.room A.global).Sat N p :=
  not_congr (sat_iff A Γ)

end Silmaril.Logic.CommonLogic.Source.Presentations.Packaged
