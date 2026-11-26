module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Defs

/-! # A direct survivor read and its full projection quote -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.ComparisonGap

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

abbrev Exits : List (Ty Empty) := [Bit, Bit]

def firstExit : Position Exits := ⟨0, rfl⟩
def secondExit : Position Exits := ⟨1, rfl⟩

/-- The right-hand presentation names the newest original field twice. -/
def quoteSlots : Fin 3 → ReplyFrame.Slot (ReplyFrame.standard 2) :=
  Fin.cases (ReplyFrame.standardSlots 2 1) (fun _ => ReplyFrame.standardSlots 2 0)

def directGuard : ReadTree Exits 3 :=
  .testRequest [false] 2 true true false
    (.ret [] firstExit 1) (.ret [true, false] secondExit 2)
    (.ret [false] firstExit 0) (.ret [false] firstExit 0)

def rightGuard (result : Finite.Expr 4) : ReadTree Exits 4 :=
  .testRequest [false] 1 true false true
    (.ret [] firstExit 1) (.retExpr [true, false] secondExit result)
    (.ret [false] firstExit 0) (.ret [false] firstExit 0)

/-- The retained original bit is tested after one intervening request.
The live request's right reply selects a direct survivor read. -/
def directSplit : SelectedGuardSplit Exits 2 :=
  ⟨1, [true],
    .request [true] false true directGuard (.ret [true, false] secondExit 1),
    .ret [false] secondExit 0⟩

/-- The second input has a different logical slot map and a supplied
expression at the live exit. -/
def rightSplit (result : Finite.Expr 4) : SelectedGuardSplit Exits 3 :=
  ⟨0, [true],
    .request [true] false false (rightGuard result) (.ret [true, false] secondExit 2),
    .ret [false] secondExit 1⟩

def direct : SelectedAt (replyContext 2) Exits := directSplit.atStandard

def withTerminal (result : Finite.Expr 4) : SelectedAt (replyContext 2) Exits :=
  ⟨3, rightSplit result, ReplyFrame.standard 2, quoteSlots⟩

/-- The actual wider presentation using a full projection quote. -/
def quoted : SelectedAt (replyContext 2) Exits :=
  withTerminal (Finite.Expr.quote 4 (fun row => row 2))

/-- Change only the quoted terminal to a read at the same wider slot map. -/
def contracted : SelectedAt (replyContext 2) Exits := withTerminal (.read 2)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.ComparisonGap
