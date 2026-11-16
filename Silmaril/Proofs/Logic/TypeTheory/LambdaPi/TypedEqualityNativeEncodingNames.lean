module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding.Names.Defs
import Lean.Elab.Tactic.Omega

public section
namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncodingNames
open Silmaril.Logic.TypeTheory
open LambdaPi LambdaPi.TypedEquality NativeEncoding

@[simp] theorem name_length (i : ℕ) : (name i).length = i := by
  simp [name]

@[simp] theorem index_name (i : ℕ) : index (name i) = some i := by
  simp [index]

theorem names_injective (n : ℕ) : Function.Injective (names n) := by
  intro i j h
  apply Fin.ext
  simpa only [names, name_length] using congrArg String.length h

@[simp] theorem index_nonLF : index "__nonLF" = none := by decide

/-- Constant replacement commutes with the source compiler when it fixes the
placeholder for constructors that have no independent LF typing rules. -/
theorem naturality {n : ℕ} (F : ConstantAssignment)
    (hF : F.constants "__nonLF" = Term.constant "__nonLF")
    (t : IntensionalMLTT.Term n) (σ : Fin n → Term) :
    F.term (NativeConversion.term σ t) =
      NativeConversion.term (fun i => F.term (σ i)) t := by
  induction t with
  | var i => rfl
  | univ i => cases i with
    | zero => rfl
    | succ i => cases i <;> simp [NativeConversion.term, ConstantAssignment.term, hF]
  | pi A B ihA ihB | lam A B ihA ihB =>
    simp only [NativeConversion.term, ConstantAssignment.term]
    rw [ihA, ihB]
    congr 1
    apply congrArg (fun τ => NativeConversion.term τ B)
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact F.rename _ Nat.succ
  | app f a ihf iha => simp only [NativeConversion.term, ConstantAssignment.term, ihf, iha]
  | _ => exact hF

/-- Every finite image is closed because its variables are global constants. -/
theorem image_closed {S T : Institution.Signature} (F : Institution.Map S T) (c : String) :
    (image F c).Scoped 0 := by
  cases hindex : index c with
  | none => simp only [image, hindex]; trivial
  | some i =>
    by_cases hi : i < S.scope
    · simp only [image, hindex, dite_eq_left hi]
      refine NativeSignature.closed
        (S := T.context.snoc (F.terms ⟨i, hi⟩))
        (names := Fin.cons "" (names T.scope)) (c := "") ?_
      exact Or.inl ⟨rfl, rfl⟩
    · simp only [image, hindex, dite_eq_right hi]; trivial

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncodingNames
