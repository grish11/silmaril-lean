module

public import Silmaril.Logic.STLCMatching.Naturality

@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCMatching
open CategoryTheory Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc

def truth {S : Signature} {k : Nat} {Γ : Fin k → Ty S.Base} (τ : Ty S.Base) :
    Matching.FirstOrder.Pattern (nativeSignature S).symbols Γ τ := .ex τ (.var 0)

def truthSentence {S : Signature} (τ : Ty S.Base) (b : Bool) :
    Matching.FirstOrder.Sentence (nativeSignature S).symbols :=
  ⟨0, Fin.elim0, τ, if b then truth τ else .neg (truth τ)⟩

theorem satisfies_truthSentence {S : Signature} (M : Model S) (τ : Ty S.Base) (b : Bool) :
    Matching.FirstOrder.Sentence.Satisfies (nativeModel M) (truthSentence τ b) ↔ b = true := by
  cases b with
  | true =>
      constructor
      · intro _; rfl
      · intro _ ρ x
        exact ⟨x, rfl⟩
  | false =>
      constructor
      · intro h
        obtain ⟨x⟩ := carrier_nonempty M τ
        exact (h (fun i => i.elim0) x ⟨x, rfl⟩).elim
      · intro h; cases h

def translate {S : Signature} : STLC.Sentence S →
    Matching.FirstOrder.Sentence (nativeSignature S).symbols
  | .typing Γ t τ => by
      classical
      exact truthSentence τ (decide (Raw.infer Γ t = some τ))
  | .equation t u => equationSentence t u

theorem translate_satisfaction {S : Signature} (M : Model S) (p : STLC.Sentence S) :
    Matching.FirstOrder.Sentence.Satisfies (nativeModel M) (translate p) ↔
      STLC.Sat M.toSetModel p := by
  classical
  cases p with
  | typing Γ t τ =>
      change Matching.FirstOrder.Sentence.Satisfies (nativeModel M)
        (truthSentence τ (decide (Raw.infer Γ t = some τ))) ↔ Raw.HasType Γ t τ
      rw [satisfies_truthSentence, decide_eq_true_eq, Raw.infer_eq_some]
  | equation t u => exact satisfies_equationSentence M t u

theorem translate_naturality {B : Type} {S T : FixedSignature B}
    (f : S ⟶ T) (p : STLC.Sentence S.source) :
    Matching.FirstOrder.Sentence.map (FixedHom.native (S := S) (T := T) f) (translate p) =
      translate (FixedHom.sentence f p) := by
  classical
  cases p with
  | typing Γ t τ =>
      simp only [FixedHom.sentence, translate, FixedHom.infer_raw]
      unfold truthSentence
      split <;> rfl
  | equation t u =>
      simp only [translate, FixedHom.sentence, equationSentence,
        Matching.FirstOrder.Sentence.map, equivalent, Matching.FirstOrder.Pattern.map,
        termPattern_map (S := S) (T := T) f t, termPattern_map (S := S) (T := T) f u]

end Silmaril.Logic.STLCMatching
