module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.Defs

/-! # Closed constructor-known primitive operands -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Obstruction

abbrev U := (Ty.unit : Ty Empty)

def source (label b : Bool) := call label (caseOperand (literal b))

def target (label b : Bool) := call label (literal b)

theorem source_typed (label b : Bool) : ValueBranches [U] (source label b) Exits :=
  call_typed label (.case (constructorBit_value b .unit).hasType
    (constructorBit_value false .unit).hasType (constructorBit_value true .unit).hasType)

theorem target_typed (label b : Bool) : ValueBranches [U] (target label b) Exits :=
  call_typed label (constructorBit_value b .unit).hasType

def sourcePacked (label b : Bool) :=
  Paper.TypeCategory.ofRegion (source_typed label b).packExits

def targetPacked (label b : Bool) :=
  Paper.TypeCategory.ofRegion (target_typed label b).packExits

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Obstruction
