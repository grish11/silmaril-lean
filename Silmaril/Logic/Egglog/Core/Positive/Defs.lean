module

public import Silmaril.Logic.Egglog.Core.Defs

@[expose] public section

namespace Silmaril.Logic.Egglog.Core.Positive

/-- Every sort has one value; every relation and partial-table row is true.
Rows remain functional because there is only one possible result. -/
def singletonModel (S : Signature) : Model S where
  carrier _ := Unit
  op _ _ := ()
  rel _ _ := True
  row _ _ _ := True
  functional _ _ _ _ _ _ := Subsingleton.elim _ _

end Silmaril.Logic.Egglog.Core.Positive
