module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.InstructionMap.Thms

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA

variable {Data : Type} {P Q : InstructionSet.{0,0} Data}

/-- Relabel the original primitive at its unchanged profile. The Boolean
case adapter belongs to the fixed structural vocabulary. -/
def Primitive.map (f : InstructionMap P Q) : Primitive P → Primitive Q
  | .call op => .call (f op)
  | .test => .test

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA
