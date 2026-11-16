module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding.Names.Thms

@[expose] public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding

/-- Native constant replacement, including capture-avoiding unused-name shifts. -/
def assignment {S T : Institution.Signature} (F : Institution.Map S T) : ConstantAssignment :=
  ⟨image F, image_closed F⟩

/-- Canonically name the actual native presentation of a source signature. -/
def presentation (S : Institution.Signature) : TypedPresentation :=
  NativeSignature.presentation S.formed (names S.scope)

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeEncoding
