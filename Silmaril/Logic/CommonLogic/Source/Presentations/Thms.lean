module

public import Silmaril.Logic.CommonLogic.Source.Presentations.Defs

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.Presentations
open Silmaril.Logic.Institution

theorem fixed_modelExpansive {S : Core.Signature} (names : Names S) :
    (fixed names).ModelExpansive :=
  (CLIF.toCore_modelExpansive names).comp (FiniteListFOL.comparison_modelExpansive S)

theorem fixed_consequence_iff {S : Core.Signature} (names : Names S)
    (Γ : Set (CLIF.Text names)) (text : CLIF.Text names) :
    (CLIF.room names).Entails Γ text ↔
      (FiniteListFOL.room S).Entails ((fixed names).sen '' Γ) ((fixed names).sen text) :=
  (fixed names).entails_map_iff (fixed_modelExpansive names) Γ text

/-- Every source theory, not merely a retained example, has the same SAT status. -/
theorem fixed_sat_iff {S : Core.Signature} (names : Names S) (Γ : Set (CLIF.Text names)) :
    (∃ M : (CLIF.room names).Mod, ∀ p ∈ Γ, (CLIF.room names).Sat M p) ↔
    ∃ N : (FiniteListFOL.room S).Mod,
      ∀ p ∈ (fixed names).sen '' Γ, (FiniteListFOL.room S).Sat N p := by
  constructor
  · rintro ⟨M,original⟩
    obtain ⟨N,rfl⟩ := fixed_modelExpansive names M
    refine ⟨N,?_⟩
    rintro p ⟨text,member,rfl⟩
    exact ((fixed names).sat N text).mpr (original text member)
  · rintro ⟨N,original⟩
    refine ⟨(fixed names).mod.obj N,?_⟩
    intro text member
    exact ((fixed names).sat N text).mp (original _ ⟨text,member,rfl⟩)

theorem fixed_unsat_iff {S : Core.Signature} (names : Names S) (Γ : Set (CLIF.Text names)) :
    (¬ ∃ M : (CLIF.room names).Mod, ∀ p ∈ Γ, (CLIF.room names).Sat M p) ↔
    ¬ ∃ N : (FiniteListFOL.room S).Mod,
      ∀ p ∈ (fixed names).sen '' Γ, (FiniteListFOL.room S).Sat N p :=
  not_congr (fixed_sat_iff names Γ)

end Silmaril.Logic.CommonLogic.Source.Presentations
