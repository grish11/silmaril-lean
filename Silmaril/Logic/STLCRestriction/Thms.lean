module

public import Silmaril.Logic.STLCRestriction.Defs
import Silmaril.Proofs.Logic.STLCRestriction.Models

@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCRestriction
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Algebraic.Lambda
variable {B : Type} {S T : STLCMatching.FixedSignature B}

/-- Forgetting the inhabited proof commutes with actual operator reducts. -/
theorem forget_naturality (f : S ⟶ T) :
    STLCMatching.FixedHom.pullFunctor f ⋙ forgetFunctor S =
      forgetFunctor T ⋙ pullFunctor f := rfl

theorem satisfaction (M : STLCMatching.Model S.source) (p : STLC.Sentence S.source) :
    (STLCMatching.sourceRoom S).Sat M p ↔
      (lambdaRoom S).Sat ((forgetFunctor S).obj M) p := Iff.rfl

/-- Exact source models in the reduct's image, not an assumed expansion result. -/
theorem expansion_iff (M : LambdaModel S.source) :
    (∃ N : STLCMatching.Model S.source, (forgetFunctor S).obj N = M) ↔
      ∀ b, Nonempty (M.toSetModel.base b) :=
  Silmaril.Proofs.Logic.STLCRestriction.expansion_iff M

/-- Empty base-type universes are the only case where every unrestricted model
has an exact expansion to the inhabited model class. -/
theorem modelExpansive_iff_isEmpty (B : Type) :
    (toInhabited B).ModelExpansive ↔ IsEmpty B :=
  Silmaril.Proofs.Logic.STLCRestriction.modelExpansive_iff_isEmpty B

theorem not_modelExpansive (B : Type) [Nonempty B] :
    ¬ (toInhabited B).ModelExpansive := by
  intro h
  obtain ⟨b⟩ := ‹Nonempty B›
  exact ((modelExpansive_iff_isEmpty B).mp h).false b

/-- The compiled matching endpoint has the same backward model component. -/
theorem matching_modelExpansive_iff_isEmpty (B : Type) :
    (toMatching B).ModelExpansive ↔ IsEmpty B :=
  modelExpansive_iff_isEmpty B

/-- Consequence transports from all models to the inhabited restriction. -/
theorem entails_preserved (H : Set (STLC.Sentence S.source)) (p : STLC.Sentence S.source)
    (h : (lambdaRoom S).Entails H p) : (STLCMatching.sourceRoom S).Entails H p := by
  intro M hM
  exact h ((forgetFunctor S).obj M) hM

/-- SAT witnesses reduce backwards; no expansion of an empty source is assumed. -/
theorem sat_reduces (H : Set (STLC.Sentence S.source))
    (h : ∃ M : STLCMatching.Model S.source, ∀ p ∈ H, STLC.Sat M.toSetModel p) :
    ∃ M : LambdaModel S.source, ∀ p ∈ H, STLC.Sat M.toSetModel p := by
  obtain ⟨M, hM⟩ := h
  exact ⟨(forgetFunctor S).obj M, hM⟩

/-- SAT in the target is exactly SAT with an inhabited source witness. This
qualifies the witnesses explicitly and does not assert unrestricted SAT iff. -/
theorem sat_iff_inhabited_source (H : Set (STLC.Sentence S.source)) :
    (∃ M : STLCMatching.Model S.source, ∀ p ∈ H, STLC.Sat M.toSetModel p) ↔
      ∃ M : LambdaModel S.source, (∀ b, Nonempty (M.toSetModel.base b)) ∧
        ∀ p ∈ H, STLC.Sat M.toSetModel p := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨(forgetFunctor S).obj M, M.nonempty, hM⟩
  · rintro ⟨M, hM, hs⟩
    exact ⟨⟨M.toSetModel, hM⟩, hs⟩

theorem unsat_preserved (H : Set (STLC.Sentence S.source))
    (h : ¬ ∃ M : LambdaModel S.source, ∀ p ∈ H, STLC.Sat M.toSetModel p) :
    ¬ ∃ M : STLCMatching.Model S.source, ∀ p ∈ H, STLC.Sat M.toSetModel p :=
  fun hM => h (sat_reduces H hM)

/-- Composition reaches actual native matching sentences with unchanged source
operator signatures and the existing structural S/K/I compiler. -/
theorem matching_satisfaction (M : STLCMatching.Model S.source)
    (p : STLC.Sentence S.source) :
    (STLCMatching.targetRoom S).Sat M (STLCMatching.translate p) ↔
      (lambdaRoom S).Sat ((forgetFunctor S).obj M) p :=
  STLCMatching.translate_satisfaction M p

theorem matching_entails_preserved (H : Set (STLC.Sentence S.source))
    (p : STLC.Sentence S.source) (h : (lambdaRoom S).Entails H p) :
    (STLCMatching.targetRoom S).Entails (STLCMatching.translate '' H) (STLCMatching.translate p) :=
  (STLCMatching.toMatching B).entails_map (entails_preserved H p h)

theorem matching_sat_reduces (H : Set (STLC.Sentence S.source))
    (h : ∃ M : STLCMatching.Model S.source,
      ∀ p ∈ H, (STLCMatching.targetRoom S).Sat M (STLCMatching.translate p)) :
    ∃ M : LambdaModel S.source, ∀ p ∈ H, STLC.Sat M.toSetModel p := by
  obtain ⟨M, hM⟩ := h
  exact ⟨(forgetFunctor S).obj M, fun p hp => (matching_satisfaction M p).mp (hM p hp)⟩

theorem matching_unsat_preserved (H : Set (STLC.Sentence S.source))
    (h : ¬ ∃ M : LambdaModel S.source, ∀ p ∈ H, STLC.Sat M.toSetModel p) :
    ¬ ∃ M : STLCMatching.Model S.source,
      ∀ p ∈ H, (STLCMatching.targetRoom S).Sat M (STLCMatching.translate p) :=
  fun hM => h (matching_sat_reduces H hM)

end Silmaril.Logic.STLCRestriction
