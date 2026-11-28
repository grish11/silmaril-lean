module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Defs

/-! # A known guard after one intervening reply -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open CategoryTheory

local instance acrossReplyDefsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Both reply arms of the intervening request enter a selected guard. -/
structure RequestBeforeGuard (L : List (Ty Empty)) (n : Nat) where
  emits : List Bool
  label : Bool
  onLeft : GuardRequest L n
  onRight : GuardRequest L n

def RequestBeforeGuard.tree {L : List (Ty Empty)} {n : Nat} (r : RequestBeforeGuard L (n + 2))
    (test : Fin (n + 2)) : ReadTree L (n + 1) :=
  .request r.emits r.label false (r.onLeft.tree test) (r.onRight.tree test)

/-- The prior case's test and the later guard's test have independently typed
indices. The survival predicate below relates the projections they name. -/
structure GuardAcrossReply (L : List (Ty Empty)) (n : Nat) where
  beforeTest : Fin (n + 1)
  afterTest : Fin (n + 2)
  emits : List Bool
  onFalse : RequestBeforeGuard L (n + 2)
  onTrue : RequestBeforeGuard L (n + 2)

/-- The later test projects the bit retained by the prior case and then by
the intervening request. This is an equality at the actual extended frame. -/
def GuardAcrossReply.Survives {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (p : GuardAcrossReply L n) (slots : Fin (n + 1) → ReplyFrame.Slot frame) : Prop :=
  ReplyFrame.bindSlots (fun j => ReplyFrame.Slot.retainUnit (slots j)) p.afterTest =
    .retainBit (.retainUnit (slots p.beforeTest))

def GuardAcrossReply.sourceWith {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} (p : GuardAcrossReply L n)
    (slots : Fin (n + 1) → Term signature.Instr X Bit) : CaseTree signature.Instr X L :=
  let retained := fun j => retainSlot (A := unit) (slots j)
  .case unit unit (emitPrefix p.emits (slots p.beforeTest))
    ((p.onFalse.tree p.afterTest).selectedWith retained) ((p.onTrue.tree p.afterTest).selectedWith retained)

/-- Enter the surviving second request with the exact guard survivor map
and the prior unit payload, read through the intervening reply field. -/
def GuardRequest.prunedAfterReply {L : List (Ty Empty)} {n : Nat} {X : Ty Empty}
    (g : GuardRequest L (n + 2)) (test : Fin (n + 2))
    (slots : Fin (n + 2) → Term signature.Instr (product (product X unit) Bit) Bit)
    (b : Bool) : Region signature.Instr :=
  prependEmits g.emits
    (.let₁ (priorCaseUnit X).elaborate.val
      (Paper.PackedBody.applyPacked (g.live test slots b).elaborate.val))

/-- Keep the intervening request, including both of its reply choices. -/
def RequestBeforeGuard.prunedWith {L : List (Ty Empty)} {n : Nat} {X : Ty Empty}
    (r : RequestBeforeGuard L (n + 2)) (test : Fin (n + 2))
    (slots : Fin (n + 1) → Term signature.Instr (product X unit) Bit)
    (b : Bool) : Region signature.Instr :=
  let scope := bindReply slots
  .case (emitPrefix (X := product X unit) r.emits (.call (show signature.Instr from Op.ask r.label) .unit)).elaborate.val
    (Paper.PackedBody.applyPacked (r.onLeft.prunedAfterReply test scope b))
    (Paper.PackedBody.applyPacked (r.onRight.prunedAfterReply test scope b))

def GuardAcrossReply.prunedWith {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} (p : GuardAcrossReply L n)
    (slots : Fin (n + 1) → Term signature.Instr X Bit) : Region signature.Instr :=
  let retained := fun j => retainSlot (A := unit) (slots j)
  .case (emitPrefix p.emits (slots p.beforeTest)).elaborate.val
    (Paper.PackedBody.applyPacked (p.onFalse.prunedWith p.afterTest retained false))
    (Paper.PackedBody.applyPacked (p.onTrue.prunedWith p.afterTest retained true))

def GuardAcrossReply.packedSource {L : List (Ty Empty)} {n : Nat} (p : GuardAcrossReply L n) :
    Paper.Extension.Singleton.ofType Seed (replyContext (n + 1)) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed (p.sourceWith (readReply (n + 1))).elaborate.property.packExits

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
