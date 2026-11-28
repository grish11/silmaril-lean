module

public import Silmaril.Logic.Abstraction.Propositional.Defs

public section

namespace Silmaril.Proofs.Logic.Abstraction.Propositional

open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Abstraction.Propositional

variable {P Q : Type}

theorem holds_toUFOL (M : UFOL.Structure (signature P)) (φ : PL.Formula P) :
    UFOL.Sentence.Holds M (toUFOL φ) ↔ φ.eval (valuation M) := by
  induction φ with
  | var p =>
    exact Iff.of_eq (congrArg (M.rel (n := 0) (⟨rfl⟩, p)) (Subsingleton.elim _ _))
  | bot => exact not_true
  | imp φ ψ ihφ ihψ =>
    change ¬ (UFOL.Sentence.Holds M (toUFOL φ) ∧ ¬ UFOL.Sentence.Holds M (toUFOL ψ)) ↔ _
    rw [ihφ, ihψ]
    exact ⟨fun h hφ => Classical.byContradiction fun hψ => h ⟨hφ, hψ⟩,
      fun h hφψ => hφψ.2 (h hφψ.1)⟩
  | and φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | or φ ψ ihφ ihψ =>
    change ¬ (¬ UFOL.Sentence.Holds M (toUFOL φ) ∧ ¬ UFOL.Sentence.Holds M (toUFOL ψ)) ↔ _
    rw [ihφ, ihψ, Classical.not_and_iff_not_or_not, Classical.not_not, Classical.not_not]
    rfl

theorem toUFOL_map (f : P ⟶ Q) (φ : PL.Formula P) :
    toUFOL (φ.rename f) = (toUFOL φ).map (signatureFunctor.map f) := by
  induction φ with
  | var p =>
    exact congrArg (UFOL.Formula.rel (Sg := signature Q) (k := 0) (n := 0) (⟨rfl⟩, f p))
      (Subsingleton.elim _ _)
  | bot => rfl
  | imp φ ψ ihφ ihψ =>
    exact congrArg UFOL.Formula.not (congrArg₂ UFOL.Formula.and ihφ (congrArg UFOL.Formula.not ihψ))
  | and φ ψ ihφ ihψ => exact congrArg₂ UFOL.Formula.and ihφ ihψ
  | or φ ψ ihφ ihψ =>
    exact congrArg UFOL.Formula.not (congrArg₂ UFOL.Formula.and
      (congrArg UFOL.Formula.not ihφ) (congrArg UFOL.Formula.not ihψ))

end Silmaril.Proofs.Logic.Abstraction.Propositional
