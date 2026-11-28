module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.CallOperand.Defs

/-! # A packed unit interface with a computed primitive argument -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.CallBoundary

open Region.Paper.BoundSimulation.Obstruction.PairSequencing
open Region.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch (Op)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

scoped instance : LetCase.Structural.Finite.Signature Op where
  source _ := .unit
  target _ := .unit

abbrev U := (Ty.unit : Ty Empty)
abbrev input : BoundCtx (Ty Empty) 1 := .snoc .nil U

def argument : Operand Op input U := ⟨.let₁ (.op .call (.bv 0)) (.bv 0), .let₁ (.op .bv) .bv⟩

def nested : Operand Op input U := ⟨.op .call argument.1, .op argument.2⟩

def sequenced : Operand Op input U := ⟨.let₁ argument.1 (.op .call (.bv 0)), .let₁ argument.2 (.op .bv)⟩

/-- The original guarded return, as written in native region syntax. -/
def nestedEndpoint : Endpoint Op input U :=
  ⟨CallOperand.nestedReturn, .let₁ CallOperand.nested_typed (.br rfl (.var rfl)), .let₁ _ (.br _)⟩

/-- The original guarded return with the operand let exposed. -/
def sequencedEndpoint : Endpoint Op input U :=
  ⟨CallOperand.sequencedReturn, .let₁ CallOperand.sequenced_typed (.br rfl (.var rfl)), .let₁ _ (.br _)⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.CallBoundary
