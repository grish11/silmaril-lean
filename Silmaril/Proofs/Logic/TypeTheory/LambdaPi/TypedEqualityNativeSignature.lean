module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature.Defs

public section
namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignature

open Silmaril.Logic.TypeTheory
open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature

/-- Compilation respects the native scope of its variable assignment. -/
theorem term_scoped {n m : ℕ} (t : NativeConversion.SourceTerm n)
    (σ : Fin n → LambdaPi.Term) (hσ : ∀ i, (σ i).Scoped m) :
    LambdaPi.Term.Scoped m (NativeConversion.term σ t) := by
  induction t generalizing m with
  | var i => exact hσ i
  | univ i => cases i with
    | zero => trivial
    | succ i => cases i <;> trivial
  | pi A B ihA ihB | lam A B ihA ihB =>
    refine ⟨ihA σ hσ, ihB (NativeConversion.lift σ) ?_⟩
    intro i
    refine Fin.cases (Nat.zero_lt_succ m) (fun j => ?_) i
    exact (hσ j).rename Nat.succ (fun _ h => Nat.succ_lt_succ h)
  | app f a ihf iha => exact ⟨ihf σ hσ, iha σ hσ⟩
  | _ => trivial

/-- Native declaration types are closed; globals never consume local binders. -/
theorem closed {n : ℕ} {S : Context n} {names : Fin n → String} {c : String} {T : LambdaPi.Term}
    (h : declarations S names c T) : T.Scoped 0 := by
  induction S with
  | nil => exact h.elim
  | snoc S A ih =>
    rcases h with ⟨_, rfl⟩ | h
    · exact term_scoped A _ (fun _ => True.intro)
    · exact ih h

/-- Closing a source lookup finds its actual native declaration type. -/
theorem lookup {n : ℕ} {S : Context n} {i : Fin n} {A : Term n}
    (h : Lookup S i A) (names : Fin n → String) :
    declarations S names (names i) (NativeConversion.term (globals names) A) := by
  induction h with
  | here =>
    apply Or.inl
    refine ⟨rfl, ?_⟩
    simp only [Term.weaken, NativeConversion.term_rename]
    rfl
  | there h ih =>
    apply Or.inr
    rw [Term.weaken, NativeConversion.term_rename]
    have assignment : globals names ∘ Fin.succ = globals (names ∘ Fin.succ) := rfl
    rw [assignment]
    exact ih (names ∘ Fin.succ)

/-- Each declaration name comes from a source signature position. -/
theorem index {n : ℕ} {S : Context n} {names : Fin n → String} {c : String} {T : LambdaPi.Term}
    (h : declarations S names c T) : ∃ i, names i = c := by
  induction S with
  | nil => exact h.elim
  | snoc S A ih =>
    rcases h with ⟨hc, _⟩ | h
    · exact ⟨0, hc.symm⟩
    · obtain ⟨i, hi⟩ := ih h
      exact ⟨i.succ, hi⟩

/-- Distinct source names prevent overloaded native constant declarations. -/
theorem unique {n : ℕ} {S : Context n} {names : Fin n → String}
    (hinj : Function.Injective names) {c : String} {T U : LambdaPi.Term}
    (hT : declarations S names c T) (hU : declarations S names c U) : T = U := by
  induction S with
  | nil => exact hT.elim
  | snoc S A ih =>
    rcases hT with ⟨hc, hT⟩ | hT
    · rcases hU with ⟨_, hU⟩ | hU
      · exact hT.trans hU.symm
      · obtain ⟨i, hi⟩ := index hU
        exact False.elim (Fin.succ_ne_zero i (hinj (hi.trans hc)))
    · rcases hU with ⟨hc, _⟩ | hU
      · obtain ⟨i, hi⟩ := index hT
        exact False.elim (Fin.succ_ne_zero i (hinj (hi.trans hc)))
      · exact ih (fun i j h => Fin.succ_injective _ (hinj h)) hT hU

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignature
