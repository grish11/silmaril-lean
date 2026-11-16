module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Source.Script.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Source.Script
open CategoryTheory Silmaril.Logic.Institution

theorem singleton_modelExpansive : singleton.ModelExpansive := fun _ M => ⟨M, rfl⟩

theorem singleton_satisfiable_iff (A : Signature)
    (Γ : Set (Quantified.Sentence A.symbols)) :
    (QuantifiedModels.room A).Satisfiable Γ ↔
      (Problem.room A).Satisfiable ((fun sentence => [sentence]) '' Γ) := by
  apply exists_congr
  intro M
  change (∀ sentence ∈ Γ, sentence.Holds M) ↔
    ∀ p ∈ (fun sentence => [sentence]) '' Γ, Problem.Holds M p
  constructor
  · rintro truth _ ⟨sentence, hs, rfl⟩
    simpa only [Problem.Holds, List.mem_singleton, forall_eq] using truth sentence hs
  · intro truth sentence hs
    have h := truth [sentence] ⟨sentence, hs, rfl⟩
    simpa only [Problem.Holds, List.mem_singleton, forall_eq] using h

theorem singleton_unsatisfiable_iff (A : Signature)
    (Γ : Set (Quantified.Sentence A.symbols)) :
    (QuantifiedModels.room A).Unsatisfiable Γ ↔
      (Problem.room A).Unsatisfiable ((fun sentence => [sentence]) '' Γ) :=
  not_congr (singleton_satisfiable_iff A Γ)

theorem singleton_entails_iff (A : Signature)
    (Γ : Set (Quantified.Sentence A.symbols)) (sentence : Quantified.Sentence A.symbols) :
    (QuantifiedModels.room A).Entails Γ sentence ↔
      (Problem.room A).Entails ((fun sentence => [sentence]) '' Γ) [sentence] :=
  singleton.entails_iff singleton_modelExpansive A Γ sentence

theorem toProblems_modelExpansive : toProblems.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- Different complete programs share a single ambient model, even when their
local declaration environments differ. -/
def TheoryHolds {A : Signature} (M : Model A.symbols) (Γ : Set (Family A)) : Prop :=
  ∀ s ∈ Γ, s.Holds M

def Sat {A : Signature} (Γ : Set (Family A)) : Prop := (room A).Satisfiable Γ

def Unsat {A : Signature} (Γ : Set (Family A)) : Prop := (room A).Unsatisfiable Γ

theorem theory_holds_iff_decode {A : Signature} (M : Model A.symbols)
    (Γ : Set (Family A)) :
    TheoryHolds M Γ ↔ ∀ p ∈ Family.decode '' Γ, Problem.Holds M p := by
  constructor
  · rintro h _ ⟨s, hs, rfl⟩
    exact (s.decode_holds M).mpr (h s hs)
  · intro h s hs
    exact (s.decode_holds M).mp (h _ ⟨s, hs, rfl⟩)

theorem satisfiable_iff_decode {A : Signature} (Γ : Set (Family A)) :
    Sat Γ ↔ (Problem.room A).Satisfiable (Family.decode '' Γ) :=
  exists_congr fun M => theory_holds_iff_decode M Γ

theorem unsatisfiable_iff_decode {A : Signature} (Γ : Set (Family A)) :
    Unsat Γ ↔ (Problem.room A).Unsatisfiable (Family.decode '' Γ) :=
  not_congr (satisfiable_iff_decode Γ)

theorem entails_iff_decode (A : Signature) (Γ : Set (Family A)) (s : Family A) :
    (room A).Entails Γ s ↔ (Problem.room A).Entails (Family.decode '' Γ) s.decode :=
  toProblems.entails_iff toProblems_modelExpansive A Γ s

theorem program_sat_iff_decode {A : Signature} (s : Family A) :
    (∃ M, s.Holds M) ↔ ∃ M, Problem.Holds M s.decode :=
  exists_congr fun M => (s.decode_holds M).symm

theorem program_unsat_iff_decode {A : Signature} (s : Family A) :
    (¬ ∃ M, s.Holds M) ↔ ¬ ∃ M, Problem.Holds M s.decode :=
  not_congr (program_sat_iff_decode s)

/-- Canonical packaging retains the original complete accepted program and
agrees with the earlier checker semantics at its own checked signature. -/
theorem ofAccepted_decode (s : Quantified.Script.Accepted) :
    (Family.ofAccepted s).decode = s.assertions.map (·.sentence) := by
  simp only [Family.decode, Family.ofAccepted, List.map_map,
    Function.comp_def, Hom.quantifiedSentence_id]

theorem ofAccepted_sat_iff (s : Quantified.Script.Accepted) :
    (∃ M, (Family.ofAccepted s).Holds M) ↔ s.Sat := by
  rw [program_sat_iff_decode, ofAccepted_decode]
  exact (Quantified.Script.sat_iff_fixed s).symm

theorem ofAccepted_unsat_iff (s : Quantified.Script.Accepted) :
    (¬ ∃ M, (Family.ofAccepted s).Holds M) ↔ s.Unsat :=
  not_congr (ofAccepted_sat_iff s)

/-- Actual signature maps give reduct satisfaction, not blanket model expansion. -/
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

theorem entails_map_iff {A B : Signature} (f : A ⟶ B)
    (hf : (corridor f).ModelExpansive) (Γ : Set (Family A)) (s : Family A) :
    (room A).Entails Γ s ↔ (room B).Entails (Family.map f '' Γ) (s.map f) :=
  (corridor f).entails_map_iff hf Γ s

end Silmaril.Logic.Smt.Uflia.SortMaps.Source.Script
