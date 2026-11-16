module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature.Defs
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignature

public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature

open Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Every generated declaration type is closed in native LF. -/
theorem closed {n : ℕ} {S : Context n} {names : Fin n → String} {c : String} {T : LambdaPi.Term}
    (h : declarations S names c T) : T.Scoped 0 :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignature.closed h

/-- Closing a source lookup yields its actual declaration in the native signature. -/
theorem lookup {n : ℕ} {S : Context n} {i : Fin n} {A : NativeConversion.SourceTerm n}
    (h : Silmaril.Logic.TypeTheory.IntensionalMLTT.Lookup S i A) (names : Fin n → String) :
    declarations S names (names i) (NativeConversion.term (globals names) A) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignature.lookup h names

/-- Injective source names yield a single native type for each declared constant. -/
theorem unique {n : ℕ} {S : Context n} {names : Fin n → String}
    (hinj : Function.Injective names) {c : String} {T U : LambdaPi.Term}
    (hT : declarations S names c T) (hU : declarations S names c U) : T = U :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeSignature.unique hinj hT hU

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeSignature
