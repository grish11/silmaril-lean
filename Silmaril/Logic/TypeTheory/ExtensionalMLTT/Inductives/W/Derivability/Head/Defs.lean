module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Functions

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Tm

/-- A constant-result W step, ignoring child trees and recursive results. -/
def headStep (A : Tm 0) (B : Tm 1) (I : Tm 0) (g : Tm 1) : Tm 0 :=
  .abs A (.abs (.arr B ((.wtype A B : Tm 0).castLE (by decide)))
    ((Tm.abs (.arr B (I.castLE (by decide))) g.wk0).wk0))

def head (A : Tm 0) (B : Tm 1) (I : Tm 0) (g : Tm 1) (t : Tm 0) : Tm 0 :=
  .wrec A B I.wk0 (headStep A B I g) t

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Tm
