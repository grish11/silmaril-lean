module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEquality.Defs
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEquality

public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEquality
open CategoryTheory

/-- Source substitution and actual native encoding give the same equality assertion. -/
theorem sentence_natural {S T : Institution.Signature} (F : S ⟶ T) (q : Institution.Sentence S) :
    sentence (F.sentence q) = (sentence q).map (NativeEncoding.encoding F) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEquality.sentence_natural F q

/-- Source and native model reductions commute with compilation. -/
theorem model_natural {S T : Institution.Signature} (F : S ⟶ T) (M : Institution.Model T) :
    model (F.reduce M) = EqualityInstitution.Model.reduce (NativeEncoding.encoding F) (model M) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEquality.model_natural F M

/-- Every actual source model satisfying an equality gives native endpoint
proofs and conversion in its compiled native model. This is a one-way theorem. -/
theorem sound {S : Institution.Signature} (M : Institution.Model S) (q : Institution.Sentence S)
    (h : M.Satisfies q) : (model M).Satisfies (sentence q) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEquality.sound M q h

/-- A source proof supplies an actual native typed equality at the original carrier. -/
theorem proof_sound {S : Institution.Signature} (q : Institution.Sentence S)
    (h : Equality S.context S.context q.left q.right q.carrier) :
    EqualityInstitution.Holds (NativeEncoding.presentation S) (sentence q) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeEquality.proof_sound q h

/-- Hence source theorems hold under every actual native encoding model,
including models which are not compiled source substitutions. -/
theorem proof_valid {S : Institution.Signature} (q : Institution.Sentence S)
    (h : Equality S.context S.context q.left q.right q.carrier)
    (M : EqualityInstitution.Model (NativeEncoding.presentation S)) :
    M.Satisfies (sentence q) := EqualityInstitution.sound (proof_sound q h) M

/-- The compiled source signature family uses the new native equality semantics. -/
noncomputable def institutions : Institution.Signature ⥤ Silmaril.Logic.Institution.CoIns.{0, 0, 0, 0, 0} :=
  NativeEncoding.functor ⋙ EqualityInstitution.institutions

/-- Native equality comorphisms along compiled source encodings; this is not
an asserted comorphism out of the different source substitution-model institution. -/
noncomputable def hets : Silmaril.Logic.Institution.LogicGraph.{0, 0, 0, 0, 0, 0, 0} :=
  Silmaril.Logic.Institution.IndexedCoInst.toLogicGraph institutions

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEquality
