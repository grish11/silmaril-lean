module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Defs

/-! # The original selected packed endpoint in unextended Paper -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree

/-- Pack the original guarded elaboration directly in the Paper singleton category. -/
def Tree.defaultPacked (t : Tree 1) :=
  Paper.TypeCategory.ofRegion t.guarded_typed.packExits

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree
