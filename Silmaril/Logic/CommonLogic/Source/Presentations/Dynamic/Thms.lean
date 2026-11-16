module

public import Silmaril.Logic.CommonLogic.Source.Presentations.Dynamic.Defs

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.Presentations.Dynamic
open CategoryTheory Silmaril.Logic.Institution

theorem toCore_modelExpansive (A : Core.Signature) : (toCore A).ModelExpansive :=
  fun M => ⟨M, rfl⟩

theorem toFOL_modelExpansive (A : Core.Signature) : (toFOL A).ModelExpansive := by
  intro M
  exact FiniteListFOL.comparison_modelExpansive A M

theorem core_square {A B : Core.Signature} (f : A ⟶ B) :
    corridor f ≫ toCore B = toCore A ≫ liftCorridor (Core.corridor f) :=
  comparison.ρ.naturality f

theorem fol_square {A B : Core.Signature} (f : A ⟶ B) :
    corridor f ≫ toFOL B = toFOL A ≫ liftCorridor (FiniteListFOL.corridor f) :=
  folComparison.ρ.naturality f

theorem consequence_iff (A : Core.Signature) (Γ : Set (Text A)) (p : Text A) :
    (room A).Entails Γ p ↔
      (liftRoom (FiniteListFOL.room A)).Entails ((toFOL A).sen '' Γ) ((toFOL A).sen p) :=
  (toFOL A).entails_map_iff (toFOL_modelExpansive A) Γ p

theorem sat_iff (A : Core.Signature) (Γ : Set (Text A)) :
    (∃ M : (room A).Mod, ∀ p ∈ Γ, (room A).Sat M p) ↔
    ∃ N : (liftRoom (FiniteListFOL.room A)).Mod,
      ∀ p ∈ (toFOL A).sen '' Γ, (liftRoom (FiniteListFOL.room A)).Sat N p := by
  constructor
  · rintro ⟨M, h⟩
    obtain ⟨N, rfl⟩ := toFOL_modelExpansive A M
    refine ⟨N, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact ((toFOL A).sat N p).mpr (h p hp)
  · rintro ⟨N, h⟩
    exact ⟨(toFOL A).mod.obj N, fun p hp => ((toFOL A).sat N p).mp (h _ ⟨p, hp, rfl⟩)⟩

theorem unsat_iff (A : Core.Signature) (Γ : Set (Text A)) :
    (¬ ∃ M : (room A).Mod, ∀ p ∈ Γ, (room A).Sat M p) ↔
    ¬ ∃ N : (liftRoom (FiniteListFOL.room A)).Mod,
      ∀ p ∈ (toFOL A).sen '' Γ, (liftRoom (FiniteListFOL.room A)).Sat N p :=
  not_congr (sat_iff A Γ)

end Silmaril.Logic.CommonLogic.Source.Presentations.Dynamic
