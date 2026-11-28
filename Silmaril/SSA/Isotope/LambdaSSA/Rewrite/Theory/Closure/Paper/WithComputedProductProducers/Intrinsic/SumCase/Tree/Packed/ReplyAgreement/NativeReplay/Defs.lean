module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Defs

/-! # Native selected replay at the witnessed request interface -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement.NativeReplay

open Silmaril CategoryTheory
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithProjectionReturnsAndUnitEta.ExitPacking (packArrow)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

abbrev Seed := Paper.WithProjectionReturnsAndUnitEta.Step (τ := Ty Empty) (Φ := signature.Instr)
abbrev Exits : List (Ty Empty) := [Bit, Bit]

def first : Position Exits := ⟨0, rfl⟩
def second : Position Exits := ⟨1, rfl⟩

/-- The three-request regression from the closed selected-arrow comparison.
The first reply chooses the third request, whose continuation reads a bit or its table. -/
def fixture (bound : Bool) (result : Finite.Expr 2) : ReadTree Exits 0 :=
  .request [false] true bound
    (.request [] false bound (.retExpr [] first (.literal false))
      (.testRequest [false] 1 false bound bound
        (.retExpr [true] first result) (.ret [] first 0)
        (.retExpr [true] second result) (.ret [] second 0)))
    (.ret [] second 0)

def direct : ReadTree Exits 0 := fixture true (.read 1)
def table : ReadTree Exits 0 := fixture false (Finite.Expr.quote 2 (fun env => env 1))

/-- The actual packed singleton class in the projection-return and unit-η join. -/
def packed (p : ReadTree Exits 0) :
    (Paper.Extension.Singleton.ofType Seed (Ty.unit : Ty Empty) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType Exits)) :=
  packArrow p.selected.elaborate.property

/-- Product input at the chosen continuation after the third request.
The pure guard supplies a unit binder between the prior input and the new reply. -/
abbrev TerminalInput : Ty Empty := product (product (replyContext 2) unit) Bit

/-- The terminal slots on that path skip the tested oldest bit and keep the
second reply alongside the new reply. -/
def terminalSlots : Fin 2 → Term signature.Instr TerminalInput Bit :=
  bindReply (fun i : Fin 1 => retainSlot (A := unit) (readReply 2 ((1 : Fin 2).succAbove i)))

/-- The actual local terminal tree in either selected request arm of the fixture. -/
def terminal (pos : Position Exits) (result : Finite.Expr 2) : CaseTree signature.Instr TerminalInput Exits :=
  selectTerminal pos result terminalSlots [true]

/-- Put a term in the effect-prefixed discriminator context used by the table. -/
def prefixedTest (a : Term signature.Instr Bit Bit) : CaseTree signature.Instr Bit Exits :=
  .case unit unit (emitPrefix [true] a)
    (selectTerminal first (.literal false) Fin.elim0 [])
    (selectTerminal second (.literal true) Fin.elim0 [])

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement.NativeReplay
