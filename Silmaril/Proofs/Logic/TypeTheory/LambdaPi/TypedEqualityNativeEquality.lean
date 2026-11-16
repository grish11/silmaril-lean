module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEquality.Defs

public section
namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEquality
open CategoryTheory
open Silmaril.Logic.TypeTheory.LambdaPi
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEquality

theorem sentence_natural {S T : Institution.Signature} (F : S ⟶ T) (q : Institution.Sentence S) :
    sentence (F.sentence q) = (sentence q).map (NativeEncoding.encoding F) := by
  apply EqualityInstitution.Sentence.ext <;>
    exact (NativeEncoding.term_map F _).symm

theorem model_natural {S T : Institution.Signature} (F : S ⟶ T) (M : Institution.Model T) :
    model (F.reduce M) = EqualityInstitution.Model.reduce (NativeEncoding.encoding F) (model M) := by
  change EqualityInstitution.Model.mk _ (NativeEncoding.encoding (F ≫ M.assignment)) =
    EqualityInstitution.Model.mk _ (NativeEncoding.encoding F ≫ NativeEncoding.encoding M.assignment)
  exact congrArg (EqualityInstitution.Model.mk _) (NativeEncoding.functor.map_comp F M.assignment)

theorem sound {S : Institution.Signature} (M : Institution.Model S) (q : Institution.Sentence S)
    (h : M.Satisfies q) : (model M).Satisfies (sentence q) := by
  change EqualityInstitution.Holds (NativeEncoding.presentation M.target)
    ((sentence q).map (NativeEncoding.encoding M.assignment))
  rw [← sentence_natural]
  obtain ⟨hl, hr⟩ := NativeSignature.endpoints M.target.formed (NativeEncoding.names M.target.scope) h
  exact ⟨hl, hr, NativeConversion.equality_conversion h _ _⟩

theorem proof_sound {S : Institution.Signature} (q : Institution.Sentence S)
    (h : Equality S.context S.context q.left q.right q.carrier) :
    EqualityInstitution.Holds (NativeEncoding.presentation S) (sentence q) := by
  obtain ⟨hl, hr⟩ := NativeSignature.endpoints S.formed (NativeEncoding.names S.scope) h
  exact ⟨hl, hr, NativeConversion.equality_conversion h _ _⟩

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEquality
