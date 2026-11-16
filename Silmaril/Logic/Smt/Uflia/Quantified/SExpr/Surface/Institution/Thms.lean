module

public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface.Institution.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
open Silmaril.Logic.Smt.Uflia.SExpr

/-- Every assertion is interpreted in the SAME arbitrary supplied model. -/
theorem theory_holds_iff {E : Environment} (assertions : List (SExpr.ByteAccepted E))
    (M : Model E.signature) :
    (∀ a ∈ assertions, (room E).Sat M a) ↔
      ∀ sentence ∈ assertions.map (fun a => a.sentence), Sentence.Holds sentence M := by
  constructor
  · intro h sentence member
    rcases List.mem_map.mp member with ⟨a, ha, rfl⟩
    exact (accepted_holds_iff M a).mp (h a ha)
  · intro h a ha
    exact (accepted_holds_iff M a).mpr (h a.sentence (List.mem_map.mpr ⟨a, ha, rfl⟩))

/-- This is one common model for the whole list, not separate model witnesses. -/
theorem theory_sat_iff {E : Environment} (assertions : List (SExpr.ByteAccepted E)) :
    (∃ M, ∀ a ∈ assertions, (room E).Sat M a) ↔
      ∃ M : Model E.signature,
        ∀ sentence ∈ assertions.map (fun a => a.sentence), Sentence.Holds sentence M := by
  constructor
  · rintro ⟨M, h⟩; exact ⟨M, (theory_holds_iff assertions M).mp h⟩
  · rintro ⟨M, h⟩; exact ⟨M, (theory_holds_iff assertions M).mpr h⟩

theorem theory_unsat_iff {E : Environment} (assertions : List (SExpr.ByteAccepted E)) :
    (¬ ∃ M, ∀ a ∈ assertions, (room E).Sat M a) ↔
      ¬ ∃ M : Model E.signature,
        ∀ sentence ∈ assertions.map (fun a => a.sentence), Sentence.Holds sentence M :=
  not_congr (theory_sat_iff assertions)

/-- Successful byte parsing supplies a retained source witness, not just a formula. -/
theorem byteAccepted_of_parsed {E : Environment} {bytes : List UInt8}
    {sentence : Sentence E.signature} (parsed : SExpr.parse? E bytes = some sentence) :
    ∃ a : SExpr.ByteAccepted E, a.bytes = bytes ∧ a.sentence = sentence := by
  cases reads : Silmaril.Logic.Smt.readForms bytes with
  | none => simp [SExpr.parse?, reads] at parsed
  | some forms =>
    cases forms with
    | nil => simp [SExpr.parse?, reads] at parsed
    | cons expression tail =>
      cases tail with
      | nil =>
        have decoded : SExpr.decodeSentence? E expression = some sentence := by
          simpa [SExpr.parse?, reads] using parsed
        exact ⟨⟨⟨expression, sentence, decoded⟩, bytes, reads⟩, rfl, rfl⟩
      | cons other tail => simp [SExpr.parse?, reads] at parsed

theorem sat_iff {E : Environment} (bytes : List UInt8) : Sat E bytes ↔ SExpr.Sat E bytes := by
  constructor
  · rintro ⟨a, rfl, M, truth⟩
    exact ⟨a.sentence, a.parsed, M, (accepted_holds_iff M a).mp truth⟩
  · rintro ⟨sentence, parsed, M, truth⟩
    obtain ⟨a, sameBytes, sameSentence⟩ := byteAccepted_of_parsed parsed
    refine ⟨a, sameBytes, M, (accepted_holds_iff M a).mpr ?_⟩
    change Sentence.Holds a.sentence M
    simpa only [sameSentence] using truth

theorem unsat_iff {E : Environment} (bytes : List UInt8) : Unsat E bytes ↔ SExpr.Unsat E bytes := by
  constructor
  · rintro ⟨a, rfl, noModel⟩
    refine ⟨a.sentence, a.parsed, ?_⟩
    rintro ⟨M, truth⟩
    exact noModel ⟨M, (accepted_holds_iff M a).mpr truth⟩
  · rintro ⟨sentence, parsed, noModel⟩
    obtain ⟨a, sameBytes, sameSentence⟩ := byteAccepted_of_parsed parsed
    refine ⟨a, sameBytes, ?_⟩
    rintro ⟨M, truth⟩
    apply noModel
    refine ⟨M, ?_⟩
    have typed := (accepted_holds_iff M a).mp truth
    change Sentence.Holds a.sentence M at typed
    simpa only [sameSentence] using typed

theorem rejected_neither {E : Environment} {bytes : List UInt8}
    (rejected : SExpr.parse? E bytes = none) : ¬ Sat E bytes ∧ ¬ Unsat E bytes := by
  constructor
  · rintro ⟨a, rfl, _⟩
    have h := a.parsed
    rw [rejected] at h
    cases h
  · rintro ⟨a, rfl, _⟩
    have h := a.parsed
    rw [rejected] at h
    cases h

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
