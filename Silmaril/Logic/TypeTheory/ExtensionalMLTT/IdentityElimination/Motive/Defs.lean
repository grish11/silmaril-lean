module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination

/-- Package an arbitrary two-binder motive as its actual endpoint/path function. -/
def packageMotive (A a : ETm 0) (C : ETm 2) : ETm 0 :=
  .abs A (.abs (.id A.wk0 a.wk0 (.bv 0)) C)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination
