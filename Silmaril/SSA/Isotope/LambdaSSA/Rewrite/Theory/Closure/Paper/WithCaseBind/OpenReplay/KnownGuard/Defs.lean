module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Defs

/-! # A prior case and an already-determined selected guard -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open CategoryTheory

local instance knownGuardDefsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The four branches of one actual retained-bit ReadTree guard. -/
structure GuardRequest (L : List (Ty Empty)) (n : Nat) where
  emits : List Bool
  low : Bool
  falseLeft : ReadTree L n
  falseRight : ReadTree L n
  trueLeft : ReadTree L n
  trueRight : ReadTree L n

/-- The ordinary selected compiler supplies the original guard. -/
def GuardRequest.tree {L : List (Ty Empty)} {n : Nat} (g : GuardRequest L (n + 1))
    (test : Fin (n + 1)) : ReadTree L (n + 1) :=
  .testRequest g.emits test g.low false false g.falseLeft g.falseRight g.trueLeft g.trueRight

/-- Keep the selected request and both of its reply arms at the literal
guard survivor map. The input still includes the guard's unit field. -/
def GuardRequest.live {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} (g : GuardRequest L (n + 1))
    (test : Fin (n + 1)) (slots : Fin (n + 1) → Term signature.Instr X Bit) (b : Bool) :
    CaseTree signature.Instr (product X unit) L :=
  let survivors := guardReplies slots test
  if b then
    selectRequest [] (!g.low) (g.trueLeft.selectedWith survivors) (g.trueRight.selectedWith survivors)
  else
    selectRequest [] g.low (g.falseLeft.selectedWith survivors) (g.falseRight.selectedWith survivors)

/-- A pure prior split keeps the tested slot available. Each of its arms
runs a selected guard that tests that same slot. -/
structure RepeatedGuard (L : List (Ty Empty)) (n : Nat) where
  test : Fin (n + 1)
  emits : List Bool
  onFalse : GuardRequest L (n + 1)
  onTrue : GuardRequest L (n + 1)

def RepeatedGuard.sourceWith {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} (p : RepeatedGuard L n)
    (slots : Fin (n + 1) → Term signature.Instr X Bit) : CaseTree signature.Instr X L :=
  let retained := fun j => retainSlot (A := unit) (slots j)
  .case unit unit (emitPrefix p.emits (slots p.test))
    ((p.onFalse.tree p.test).selectedWith retained) ((p.onTrue.tree p.test).selectedWith retained)

/-- Enter the surviving request by forwarding the prior case's unit
payload in place of the inner guard's freshly bound unit. -/
def GuardRequest.prunedArm {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} (g : GuardRequest L (n + 1))
    (test : Fin (n + 1)) (slots : Fin (n + 1) → Term signature.Instr (product X unit) Bit)
    (b : Bool) : Region signature.Instr :=
  prependEmits g.emits
    (.let₁ (Term.snd (Φ := signature.Instr) X unit).elaborate.val
      (Paper.PackedBody.applyPacked (g.live test slots b).elaborate.val))

/-- The prior case still executes. Its arms enter the corresponding request
directly, with the original emit prefixes and unit-frame layout. -/
def RepeatedGuard.prunedWith {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} (p : RepeatedGuard L n)
    (slots : Fin (n + 1) → Term signature.Instr X Bit) : Region signature.Instr :=
  let retained := fun j => retainSlot (A := unit) (slots j)
  .case (emitPrefix p.emits (slots p.test)).elaborate.val
    (Paper.PackedBody.applyPacked (p.onFalse.prunedArm p.test retained false))
    (Paper.PackedBody.applyPacked (p.onTrue.prunedArm p.test retained true))

/-- Pack the actual compiled source, including both repeated guards. -/
def RepeatedGuard.packedSource {L : List (Ty Empty)} {n : Nat} (p : RepeatedGuard L n) :
    Paper.Extension.Singleton.ofType Seed (replyContext (n + 1)) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed (p.sourceWith (readReply (n + 1))).elaborate.property.packExits

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
