module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Defs

/-! # The case conversion at the actual selected table terminal -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.SelectedTerminal

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement CaseTree.ReplyAgreement.NativeReplay
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.RetainedCase (boundCase)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local instance : HasEff signature.Instr Bool := signature.hasEff

abbrev Seed := WithCaseBind.JoinedStep (WithPairReturns.JoinedStep (τ := Ty Empty) (Φ := signature.Instr) false)

def tableArm (pos : Position Exits) : CaseTree signature.Instr (product TerminalInput unit) Exits :=
  selectTerminal pos (Finite.Expr.quote 1 (fun env => env 0))
    (fun i : Fin 1 => retainSlot (A := unit) (terminalSlots i.succ)) []

def emitTrue : Tm signature.Instr := .op (show signature.Instr from Op.emit true) .unit

def tableDiscriminator : Term signature.Instr TerminalInput Bit :=
  emitPrefix [true] (terminalSlots 0)

/-- The actual residual continuation receives the evaluated bit and the original packet. -/
def tableContinuation (pos : Position Exits) : Region signature.Instr :=
  let arm := PackedBody.applyPacked (tableArm pos).elaborate.val
  boundCase arm arm

/-- The bound discriminator retains the complete computed term, including its emit. -/
def boundTable (pos : Position Exits) : Region signature.Instr :=
  .let₁ tableDiscriminator.elaborate.val (tableContinuation pos)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.SelectedTerminal
