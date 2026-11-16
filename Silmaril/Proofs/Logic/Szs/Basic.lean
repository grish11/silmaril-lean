module

public import Silmaril.Logic.Szs.Defs
public import Mathlib.Computability.Language

/-! # Proofs: the SZS ontology (`Silmaril.Logic.Szs.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Szs

open Silmaril.Logic.Szs

universe u

variable {I : Type u}

theorem tau_iff_thm {P : Problem I} : Current.TAU P ↔ Current.THM P ∧ P.ax = Set.univ := by
  constructor
  · rintro ⟨ha, hc⟩; exact ⟨fun _ _ => hc ▸ Set.mem_univ _, ha⟩
  · rintro ⟨ht, ha⟩
    refine ⟨ha, Set.eq_univ_iff_forall.mpr fun i => ht ?_⟩
    rw [ha]; exact Set.mem_univ i

theorem thm_not_tau : ∃ P : Problem Bool, Current.THM P ∧ ¬ Current.TAU P := by
  refine ⟨⟨{true}, {true}⟩, le_rfl, fun ⟨ha, _⟩ => ?_⟩
  have : false ∈ ({true} : Set Bool) := by
    change false ∈ (⟨{true}, {true}⟩ : Problem Bool).ax; rw [ha]; exact Set.mem_univ false
  simp at this

theorem cax_iff_not_sat_and_not_csa {P : Problem I} :
    Current.CAX P ↔ ¬ Current.SAT P ∧ ¬ Current.CSA P := by
  constructor
  · intro h
    exact ⟨fun ⟨⟨i, hi⟩, _⟩ => by rw [Current.CAX] at h; rw [h] at hi; exact hi,
      fun ⟨⟨i, hi⟩, _⟩ => by rw [Current.CAX] at h; rw [h] at hi; exact hi⟩
  · rintro ⟨hs, hc⟩
    refine Set.eq_empty_iff_forall_notMem.mpr fun i hi => ?_
    by_cases hC : i ∈ P.conj
    · exact hs ⟨⟨i, hi⟩, i, hi, hC⟩
    · exact hc ⟨⟨i, hi⟩, i, hi, hC⟩

theorem forall_notMem_iff_eq_zero {α : Type u} {L : Language α} :
    (∀ w, w ∉ L) ↔ L = 0 := by
  constructor
  · intro h; ext w; simp [h w, Language.notMem_zero]
  · rintro rfl w; exact Language.notMem_zero w

end Silmaril.Proofs.Logic.Szs

end
