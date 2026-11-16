module

public import Silmaril.Logic.TypeTheory.LambdaPi.EqualityInstitution.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding.Thms

@[expose] public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEquality

/-- Compile the actual equality assertion, including its original carrier. -/
def sentence {S : Institution.Signature} (q : Institution.Sentence S) : EqualityInstitution.Sentence :=
  let σ := NativeSignature.globals (NativeEncoding.names S.scope)
  ⟨NativeConversion.term σ q.left, NativeConversion.term σ q.right, NativeConversion.term σ q.carrier⟩

/-- Compile an actual source substitution model to an actual native encoding model. -/
def model {S : Institution.Signature} (M : Institution.Model S) :
    EqualityInstitution.Model (NativeEncoding.presentation S) :=
  ⟨NativeEncoding.presentation M.target, NativeEncoding.encoding M.assignment⟩

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEquality
