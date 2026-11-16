module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeTyping.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Regularity.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

public section
namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignatureRealization

open Silmaril.Logic.TypeTheory
open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
open NativeSignature

/-- Source signature formation constructs every native constant typing.
The only target premise is inclusion of the generated raw declarations. -/
theorem assignmentInto {n : ℕ} {S : Context n} (hS : SignatureFormed S)
    (names : Fin n → String) {declared : String → LambdaPi.Term → Prop}
    (hdecl : ∀ c T, declarations S names c T → declared c T) :
    NativeTyping.Assignment S declared [] (globals names) := by
  cases hS with
  | nil => intro i A hi; exact Fin.elim0 i
  | @snoc n S A s hS hA =>
    have previous : NativeTyping.Assignment S declared [] (globals (names ∘ Fin.succ)) :=
      assignmentInto hS (names ∘ Fin.succ) (fun c T h => hdecl c T (.inr h))
    have formed := (NativeTyping.endpoints hA .nil _ previous).1
    have constant : LambdaPi.Derives (LambdaPi.Calculus.lfBetaEta declared) ∅
        ⟨[], LambdaPi.Term.constant (names 0), NativeConversion.term (globals (names ∘ Fin.succ)) A⟩ := by
      fin_cases s
      all_goals exact .constant (hdecl _ _ (.inl ⟨rfl, rfl⟩)) formed
    intro i B hi
    cases hi with
    | here =>
      rw [Term.weaken, NativeConversion.term_rename]
      exact constant
    | there hi =>
      rw [Term.weaken, NativeConversion.term_rename]
      exact previous hi

/-- Every generated declaration originates from a source lookup, with the same closed type. -/
theorem sourceLookup {n : ℕ} {S : Context n} {names : Fin n → String} {c : String} {T : LambdaPi.Term}
    (h : declarations S names c T) :
    ∃ i A, Lookup S i A ∧ names i = c ∧ NativeConversion.term (globals names) A = T := by
  induction S with
  | nil => exact h.elim
  | snoc S A ih =>
    rcases h with ⟨rfl, rfl⟩ | h
    · refine ⟨0, A.weaken, .here, rfl, ?_⟩
      rw [Term.weaken, NativeConversion.term_rename]
      rfl
    · obtain ⟨i, B, hi, hc, hT⟩ := ih h
      refine ⟨i.succ, B.weaken, .there hi, hc, ?_⟩
      rw [Term.weaken, NativeConversion.term_rename]
      exact hT

/-- Actual native sorting of all closed declaration types follows from source formation. -/
theorem sorted {n : ℕ} {S : Context n} (hS : SignatureFormed S) (names : Fin n → String)
    {c : String} {T : LambdaPi.Term} (h : declarations S names c T) :
    ∃ s, LambdaPi.Derives (LambdaPi.Calculus.lfBetaEta (declarations S names)) ∅
      ⟨[], T, LambdaPi.Term.univ s⟩ := by
  obtain ⟨i, A, hi, _, hT⟩ := sourceLookup h
  obtain ⟨s, formed⟩ := hS.lookup hi
  have assigned : NativeTyping.Assignment S (declarations S names) [] (globals names) :=
    assignmentInto hS names (fun _ _ h => h)
  have result := (NativeTyping.endpoints formed .nil _ assigned).1
  rw [hT] at result
  fin_cases s
  · exact ⟨.type, result⟩
  · exact ⟨.kind, result⟩

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignatureRealization
