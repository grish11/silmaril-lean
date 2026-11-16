module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Source.Defs
public import Silmaril.Logic.Inst.Satisfiability.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Source
open CategoryTheory Silmaril.Logic.Institution

/-- Decoding changes neither model objects nor ordinary model arrows. -/
theorem toQuantified_modelExpansive : toQuantified.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

theorem ofAcceptedCorridor_modelExpansive (checked : Uflia.SExpr.DeclarationPrefix) :
    (ofAcceptedCorridor checked).ModelExpansive := fun M => ⟨M, rfl⟩

/-- Arbitrarily many checked local declarations can share one ambient model. -/
def TheoryHolds {A : Signature} (M : Model A.symbols) (Γ : Set (Family A)) : Prop :=
  ∀ s ∈ Γ, s.Holds M

def Sat {A : Signature} (Γ : Set (Family A)) : Prop := (room A).Satisfiable Γ

def Unsat {A : Signature} (Γ : Set (Family A)) : Prop := (room A).Unsatisfiable Γ

theorem theory_holds_iff_decode {A : Signature} (M : Model A.symbols)
    (Γ : Set (Family A)) :
    TheoryHolds M Γ ↔ ∀ p ∈ Family.decode '' Γ, p.Holds M := by
  constructor
  · rintro h _ ⟨s, hs, rfl⟩
    exact (s.decode_holds M).mpr (h s hs)
  · intro h s hs
    exact (s.decode_holds M).mp (h _ ⟨s, hs, rfl⟩)

theorem satisfiable_iff_decode {A : Signature} (Γ : Set (Family A)) :
    Sat Γ ↔ (QuantifiedModels.room A).Satisfiable (Family.decode '' Γ) :=
  exists_congr fun M => theory_holds_iff_decode M Γ

theorem unsatisfiable_iff_decode {A : Signature} (Γ : Set (Family A)) :
    Unsat Γ ↔ (QuantifiedModels.room A).Unsatisfiable (Family.decode '' Γ) :=
  not_congr (satisfiable_iff_decode Γ)

theorem entails_iff_decode (A : Signature) (Γ : Set (Family A)) (s : Family A) :
    (room A).Entails Γ s ↔
      (QuantifiedModels.room A).Entails (Family.decode '' Γ) s.decode :=
  toQuantified.entails_iff toQuantified_modelExpansive A Γ s

/-- Satisfaction of translated theories reduces along the actual sort map. -/
theorem theory_holds_map {A B : Signature} (f : A ⟶ B)
    (M : Model B.symbols) (Γ : Set (Family A)) :
    TheoryHolds M (Family.map f '' Γ) ↔ TheoryHolds (Hom.reduct f M) Γ := by
  constructor
  · intro h s hs
    exact (Family.holds_map f M s).mp (h _ ⟨s, hs, rfl⟩)
  · rintro h _ ⟨s, hs, rfl⟩
    exact (Family.holds_map f M s).mpr (h s hs)

theorem satisfiable_of_map {A B : Signature} (f : A ⟶ B)
    {Γ : Set (Family A)} (h : Sat (Family.map f '' Γ)) : Sat Γ :=
  (corridor f).satisfiable_of_map h

theorem unsatisfiable_map {A B : Signature} (f : A ⟶ B)
    {Γ : Set (Family A)} (h : Unsat Γ) : Unsat (Family.map f '' Γ) :=
  (corridor f).unsatisfiable_map h

theorem entails_map {A B : Signature} (f : A ⟶ B)
    {Γ : Set (Family A)} {s : Family A} (h : (room A).Entails Γ s) :
    (room B).Entails (Family.map f '' Γ) (s.map f) :=
  (corridor f).entails_map h

/-- Reflection requires actual model expansion; arbitrary sort maps need not
supply it, including instantiation of a user sort by Bool. -/
theorem entails_map_iff {A B : Signature} (f : A ⟶ B)
    (hf : (corridor f).ModelExpansive) (Γ : Set (Family A)) (s : Family A) :
    (room A).Entails Γ s ↔ (room B).Entails (Family.map f '' Γ) (s.map f) :=
  (corridor f).entails_map_iff hf Γ s

/-- The fixed-source comparison is the identity on the full model category. -/
theorem ofAcceptedComparison_modelExpansive : ofAcceptedComparison.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

theorem checkedToQuantified_modelExpansive : checkedToQuantified.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

/-- The sentence side of the checked decoder square computes the original
accepted decoder result, despite passing through an ambient family. -/
theorem ofAccepted_decode (checked : Uflia.SExpr.DeclarationPrefix)
    (accepted : Quantified.SExpr.ByteAccepted checked.environment) :
    (Family.ofAccepted checked accepted).decode = accepted.sentence :=
  Hom.quantifiedSentence_id (A := localSignature checked) accepted.sentence

end Silmaril.Logic.Smt.Uflia.SortMaps.Source
