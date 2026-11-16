module

public import Silmaril.Logic.Smt.Fixed.Defs

/-! # Exact packaging of fixed-signature SMT problems as scripts

The SAT equivalence accounts for the change of model class explicitly. It does not assert
a corridor into the unrestricted whole-script room: an arbitrary assignment there need
not satisfy the fixed declarations, so no total identity reduct to sorted assignments
is available.
-/

@[expose] public section

namespace Silmaril.Logic.Smt.Fixed

@[simp] theorem package_decls (Γ : Signature) (φ : Sentence) :
    (package Γ φ).decls = Γ := by
  simp [package, Script.decls, List.filterMap_map, Function.comp_def]

@[simp] theorem package_asserts (Γ : Signature) (φ : Sentence) :
    (package Γ φ).asserts = φ := by
  simp [package, Script.asserts, List.filterMap_map, Function.comp_def]

theorem package_holds_iff (Γ : Signature) (φ : Sentence) (ρ : Model) :
    (package Γ φ).Holds ρ ↔
      (Γ.all fun d => (ρ d.1).hasSort d.2) = true ∧
      (φ.all fun t => t.eval Γ ρ == some (.bool true)) = true := by
  simp [Script.Holds]

theorem holds_iff (Γ : Signature) (φ : Sentence) (ρ : Assignment Γ) :
    Holds ρ φ ↔ (package Γ φ).Holds ρ.val := by
  rw [package_holds_iff]
  exact ⟨fun h => ⟨ρ.property, h⟩, fun h => h.2⟩

theorem sat_iff (Γ : Signature) (φ : Sentence) :
    Sat Γ φ ↔ (package Γ φ).Sat := by
  constructor
  · rintro ⟨ρ, h⟩
    exact ⟨ρ.val, (holds_iff Γ φ ρ).mp h⟩
  · rintro ⟨ρ, h⟩
    obtain ⟨hΓ, hφ⟩ := (package_holds_iff Γ φ ρ).mp h
    exact ⟨⟨ρ, hΓ⟩, hφ⟩

theorem unsat_iff (Γ : Signature) (φ : Sentence) :
    ¬ Sat Γ φ ↔ ¬ (package Γ φ).Sat := not_congr (sat_iff Γ φ)

end Silmaril.Logic.Smt.Fixed
