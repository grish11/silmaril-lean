module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeTyping.Thms
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignatureRealization

@[expose] public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature

/-- Source formation supplies actual native typings for the generated global constants. -/
theorem assignment {n : ℕ} {S : IntensionalMLTT.Context n} (hS : SignatureFormed S)
    (names : Fin n → String) :
    NativeTyping.Assignment S (declarations S names) [] (globals names) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignatureRealization.assignmentInto hS names
    (fun _ _ h => h)

/-- Every generated declaration comes from an actual source lookup. -/
theorem sourceLookup {n : ℕ} {S : IntensionalMLTT.Context n} {names : Fin n → String}
    {c : String} {T : LambdaPi.Term} (h : declarations S names c T) :
    ∃ i A, IntensionalMLTT.Lookup S i A ∧ names i = c ∧
      NativeConversion.term (globals names) A = T :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignatureRealization.sourceLookup h

/-- Every generated native declaration has an actual native sorting derivation. -/
theorem sorted {n : ℕ} {S : IntensionalMLTT.Context n} (hS : SignatureFormed S)
    (names : Fin n → String) {c : String} {T : LambdaPi.Term} (h : declarations S names c T) :
    ∃ s, Derives (Calculus.lfBetaEta (declarations S names)) ∅ ⟨[], T, LambdaPi.Term.univ s⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignatureRealization.sorted hS names h

/-- A source-formed signature gives an existing native typed presentation.
Admissibility, normalization and consistency remain separate metatheorems. -/
def presentation {n : ℕ} {S : IntensionalMLTT.Context n} (hS : SignatureFormed S)
    (names : Fin n → String) : TypedPresentation where
  calculus := Calculus.lfBetaEta (declarations S names)
  sorted := sorted hS names

/-- Equal source terms over a global signature have both native endpoint typings,
with the global interpretation constructed from source formation alone. -/
theorem endpoints {n : ℕ} {S : IntensionalMLTT.Context n} (hS : SignatureFormed S)
    (names : Fin n → String) {t u A : IntensionalMLTT.Term n} (h : Equality S S t u A) :
    Derives (Calculus.lfBetaEta (declarations S names)) ∅
      ⟨[], NativeConversion.term (globals names) t, NativeConversion.term (globals names) A⟩ ∧
    Derives (Calculus.lfBetaEta (declarations S names)) ∅
      ⟨[], NativeConversion.term (globals names) u, NativeConversion.term (globals names) A⟩ :=
  NativeTyping.endpoints h .nil _ (assignment hS names)

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature
