module

public import Silmaril.Logic.TypeTheory.LambdaPi.ContextConversion.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

/-- Convertibility of products entails convertibility of both components.

This property is proved for β-only LF. Arbitrary user rewrite schemas
need separate evidence; local rule typing alone is not this property.
-/
def Calculus.ProductCompatible (C : Calculus) : Prop :=
  ∀ {A B A' B'}, C.Conversion (.pi A B) (.pi A' B') → C.Conversion A A' ∧ C.Conversion B B'

end Silmaril.Logic.TypeTheory.LambdaPi
