module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding.Defs

public section
namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncoding
open Silmaril.Logic.TypeTheory
open LambdaPi LambdaPi.TypedEquality NativeEncoding

@[simp] theorem image_name {S T : Institution.Signature} (F : Institution.Map S T) (i : Fin S.scope) :
    image F (names S.scope i) = NativeConversion.term (NativeSignature.globals (names T.scope)) (F.terms i) := by
  simp [image, names, i.isLt]

@[simp] theorem assignment_nonLF {S T : Institution.Signature} (F : Institution.Map S T) :
    (assignment F).constants "__nonLF" = Term.constant "__nonLF" := by
  simp [assignment, image]

/-- Native translation of a compiled source term is its compiled source substitution. -/
theorem term_map {S T : Institution.Signature} (F : Institution.Map S T)
    (t : IntensionalMLTT.Term S.scope) :
    (assignment F).term (NativeConversion.term (NativeSignature.globals (names S.scope)) t) =
      NativeConversion.term (NativeSignature.globals (names T.scope)) (t.subst F.terms) := by
  rw [naturality _ (assignment_nonLF F), NativeConversion.term_subst]
  congr 1
  funext i
  exact image_name F i

/-- Source-typed finite substitution supplies actual native declaration images. -/
theorem declared {S T : Institution.Signature} (F : Institution.Map S T)
    {c : String} {A : Term} (h : (presentation S).calculus.declared c A) :
    Derives (presentation T).calculus ∅ ⟨[], (assignment F).constants c, (assignment F).term A⟩ := by
  obtain ⟨i, B, hi, hc, hB⟩ := NativeSignature.sourceLookup h
  rw [← hc, ← hB, term_map]
  simpa only [presentation, NativeSignature.presentation, assignment, image_name] using
    (NativeSignature.endpoints T.formed (names T.scope) (F.typed hi)).1

/-- The native eta schema contains no constants, so every assignment preserves it. -/
theorem rules {S T : Institution.Signature} (F : Institution.Map S T)
    (r : RewriteRule) (hr : r ∈ (presentation S).calculus.rules) :
    (presentation T).calculus.Conversion ((assignment F).term r.lhs) ((assignment F).term r.rhs) := by
  have same : r = etaRule := by
    simpa [presentation, NativeSignature.presentation, Calculus.lfBetaEta, Calculus.withEta, Calculus.lf] using hr
  subst r
  change (Calculus.lf (NativeSignature.declarations T.context (names T.scope))).withEta.Conversion
    (.lam (.var 0) (.app (.var 2) (.var 0))) (.var 1)
  exact (Calculus.lf _).eta (.var 0) (.var 1)

private theorem index_source {c : String} {i : ℕ} (h : index c = some i) : c = name i := by
  unfold index at h
  split at h
  · rename_i hc
    cases Option.some.inj h
    exact hc
  · cases h

/-- Canonical extension is identity on every name, including undeclared names. -/
theorem image_identity (S : Institution.Signature) (c : String) :
    image (Institution.Map.identity S) c = Term.constant c := by
  cases hindex : index c with
  | none => simp only [image, hindex]
  | some i =>
    have hc : c = name i := index_source hindex
    by_cases hi : i < S.scope
    · simp only [image, hindex, dite_eq_left hi, Institution.Map.identity, NativeConversion.term,
        NativeSignature.globals, names]
      exact congrArg Term.constant hc.symm
    · simp only [image, hindex, dite_eq_right hi]
      have arithmetic : i - S.scope + S.scope = i := by omega
      rw [arithmetic, hc]

/-- Unused canonical names shift past all target globals, making extension
commute with source composition even outside the declared source signature. -/
theorem image_comp {S T U : Institution.Signature} (F : Institution.Map S T)
    (G : Institution.Map T U) (c : String) :
    image (Institution.Map.comp F G) c = (assignment G).term (image F c) := by
  cases hindex : index c with
  | none => simp only [image, hindex, ConstantAssignment.term, assignment]
  | some i =>
    by_cases hi : i < S.scope
    · simp only [image, hindex, dite_eq_left hi, Institution.Map.comp]
      exact (term_map G (F.terms ⟨i, hi⟩)).symm
    · simp only [image, hindex, dite_eq_right hi]
      change Term.constant (name (i - S.scope + U.scope)) =
        image G (name (i - S.scope + T.scope))
      have ht : ¬ i - S.scope + T.scope < T.scope := by omega
      simp only [image, index_name, dite_eq_right ht]
      have arithmetic : i - S.scope + T.scope - T.scope + U.scope = i - S.scope + U.scope := by omega
      rw [arithmetic]

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncoding
