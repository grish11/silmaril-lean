module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding.Names.Defs
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncodingNames

public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding

@[simp] theorem name_length (i : ℕ) : (name i).length = i :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncodingNames.name_length i

@[simp] theorem index_name (i : ℕ) : index (name i) = some i :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncodingNames.index_name i

theorem names_injective (n : ℕ) : Function.Injective (names n) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncodingNames.names_injective n

@[simp] theorem index_nonLF : index "__nonLF" = none :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncodingNames.index_nonLF

theorem naturality {n : ℕ} (F : ConstantAssignment)
    (hF : F.constants "__nonLF" = LambdaPi.Term.constant "__nonLF")
    (t : IntensionalMLTT.Term n) (σ : Fin n → LambdaPi.Term) :
    F.term (NativeConversion.term σ t) = NativeConversion.term (fun i => F.term (σ i)) t :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncodingNames.naturality F hF t σ

theorem image_closed {S T : Institution.Signature} (F : Institution.Map S T) (c : String) :
    (image F c).Scoped 0 :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEncodingNames.image_closed F c

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding
