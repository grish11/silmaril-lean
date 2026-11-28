module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.ConstructorJoin.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch.Defs

/-! # A typed pair with an effectful left operand -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.CallPair

open RawBranch (Op)
open RetainedLet (returnOnce)
open UnaryReturn.Beta.Constructors (pairSequence)

abbrev U := (Ty.unit : Ty Empty)
abbrev Packet := Ty.product U U
def left : Tm Op := .op .call (.var 0)
def right : Tm Op := .let₁ (.var 0) (.var 0)

abbrev paired : Region Op := returnOnce (.pair left right)
abbrev sequenced : Region Op := pairSequence left right

theorem left_typed : Tm.HasType [U] left U := .op (.var rfl)
theorem right_typed : Tm.HasType [U] right U := .let₁ (.var rfl) (.var rfl)

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.CallPair
