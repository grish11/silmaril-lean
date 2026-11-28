module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Joined.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch.Defs

/-! # Computed call operands in the constructor join -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.CallOperand

open RawBranch (Op)
open RetainedLet (returnOnce)

local notation "U" => (Ty.unit : Ty Empty)

/-- The first call reads the original packed input. Its reply is used as the
argument of a second call. -/
def argument : Tm Op := .let₁ (.op .call (.var 0)) (.var 0)

def nested : Tm Op := .op .call argument

def sequenced : Tm Op := .let₁ argument (.op .call (.var 0))

theorem argument_typed : Tm.HasType [U] argument U := .let₁ (.op (.var rfl)) (.var rfl)
theorem nested_typed : Tm.HasType [U] nested U := .op argument_typed
theorem sequenced_typed : Tm.HasType [U] sequenced U :=
  .let₁ argument_typed (.op (.var rfl))

abbrev nestedReturn : Region Op := returnOnce nested
abbrev sequencedReturn : Region Op := returnOnce sequenced

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.CallOperand
