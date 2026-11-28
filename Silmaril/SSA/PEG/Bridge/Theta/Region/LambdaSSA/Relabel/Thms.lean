module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Relabel.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Relabel.Compiler

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA

open RVSDG (Port)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)

variable {Data : Type} {P Q : InstructionSet.{0,0} Data}

theorem Primitive.map_types (f : InstructionMap P Q) :
    Isotope.LambdaSSA.InstructionMap.PreservesTypes (τ := Code Data) (Primitive.map (P := P) (Q := Q) f) :=
  ⟨fun op => by cases op <;> rfl, fun op => by cases op <;> rfl⟩

/-- Native lowering preserves the exact constructor tree under relabelling,
including both carried-packet orders and every CFG label. -/
theorem lower_map (f : InstructionMap P Q) {carried : List (Ty Data)} {n : Nat} {t : Ty Data}
    {g : Graph P carried carried n 1} {slot : Port carried t} {invariants : Bool}
    (b : Bundle g slot invariants) :
    lower (Region.Relabel.bundle f b) = (lower b).mapInstr (Primitive.map f) :=
  Relabel.Proofs.lower_map f b

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA
