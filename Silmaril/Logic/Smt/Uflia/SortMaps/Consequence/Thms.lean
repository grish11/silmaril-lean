module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Comparisons.Thms
public import Silmaril.Logic.Inst.Satisfiability.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps
open CategoryTheory Silmaril.Logic.Institution

/-- A model of the entire translated theory gives one model of the source theory. -/
theorem satisfiable_of_map {A B : Signature} (f : A ⟶ B)
    {Γ : Set (Formula A.symbols)}
    (h : (room B).Satisfiable (Hom.formula f '' Γ)) : (room A).Satisfiable Γ :=
  (corridor f).satisfiable_of_map h

/-- Every source refutation remains a refutation after sort and symbol translation. -/
theorem unsatisfiable_map {A B : Signature} (f : A ⟶ B)
    {Γ : Set (Formula A.symbols)} (h : (room A).Unsatisfiable Γ) :
    (room B).Unsatisfiable (Hom.formula f '' Γ) :=
  (corridor f).unsatisfiable_map h

/-- Semantic consequence transports for arbitrary sets of assumptions. -/
theorem entails_map {A B : Signature} (f : A ⟶ B)
    {Γ : Set (Formula A.symbols)} {φ : Formula A.symbols}
    (h : (room A).Entails Γ φ) :
    (room B).Entails (Hom.formula f '' Γ) (Hom.formula f φ) :=
  (corridor f).entails_map h

namespace QuantifiedModels

/-- A model of the entire translated theory gives one model of the source theory. -/
theorem satisfiable_of_map {A B : Signature} (f : A ⟶ B)
    {Γ : Set (Quantified.Sentence A.symbols)}
    (h : (room B).Satisfiable (Hom.quantifiedSentence f '' Γ)) : (room A).Satisfiable Γ :=
  (corridor f).satisfiable_of_map h

/-- Every source refutation remains a refutation after sort and symbol translation. -/
theorem unsatisfiable_map {A B : Signature} (f : A ⟶ B)
    {Γ : Set (Quantified.Sentence A.symbols)} (h : (room A).Unsatisfiable Γ) :
    (room B).Unsatisfiable (Hom.quantifiedSentence f '' Γ) :=
  (corridor f).unsatisfiable_map h

/-- Semantic consequence transports for arbitrary sets of assumptions. -/
theorem entails_map {A B : Signature} (f : A ⟶ B)
    {Γ : Set (Quantified.Sentence A.symbols)} {φ : Quantified.Sentence A.symbols}
    (h : (room A).Entails Γ φ) :
    (room B).Entails (Hom.quantifiedSentence f '' Γ) (Hom.quantifiedSentence f φ) :=
  (corridor f).entails_map h

end QuantifiedModels

/-- The fixed-sort inclusion retains every model, so it preserves and reflects SAT. -/
theorem fixedSort_satisfiable_iff {U : Type} (A : Uflia.Signature U)
    (Γ : Set (Formula A)) :
    (HomModels.room A).Satisfiable Γ ↔ (room ⟨U, A⟩).Satisfiable Γ := Iff.rfl

theorem fixedSort_unsatisfiable_iff {U : Type} (A : Uflia.Signature U)
    (Γ : Set (Formula A)) :
    (HomModels.room A).Unsatisfiable Γ ↔ (room ⟨U, A⟩).Unsatisfiable Γ := Iff.rfl

theorem fixedSort_entails_iff {U : Type} (A : Uflia.Signature U)
    (Γ : Set (Formula A)) (φ : Formula A) :
    (HomModels.room A).Entails Γ φ ↔ (room ⟨U, A⟩).Entails Γ φ := Iff.rfl

/-- The fixed-sort inclusion retains every model, so it preserves and reflects SAT. -/
theorem fixedSortQuantified_satisfiable_iff {U : Type} (A : Uflia.Signature U)
    (Γ : Set (Quantified.Sentence A)) :
    (Quantified.HomModels.room A).Satisfiable Γ ↔ (QuantifiedModels.room ⟨U, A⟩).Satisfiable Γ := Iff.rfl

theorem fixedSortQuantified_unsatisfiable_iff {U : Type} (A : Uflia.Signature U)
    (Γ : Set (Quantified.Sentence A)) :
    (Quantified.HomModels.room A).Unsatisfiable Γ ↔ (QuantifiedModels.room ⟨U, A⟩).Unsatisfiable Γ := Iff.rfl

theorem fixedSortQuantified_entails_iff {U : Type} (A : Uflia.Signature U)
    (Γ : Set (Quantified.Sentence A)) (φ : Quantified.Sentence A) :
    (Quantified.HomModels.room A).Entails Γ φ ↔ (QuantifiedModels.room ⟨U, A⟩).Entails Γ φ := Iff.rfl

end Silmaril.Logic.Smt.Uflia.SortMaps
