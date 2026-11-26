module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Thms

/-! # Find certified known guards in selected request trees -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance discoveryDefsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Compare two literal projections of the same typed frame. -/
def ReplyFrame.Slot.decEq : {X : Ty Empty} → (frame : ReplyFrame X) →
    (a b : Slot frame) → Decidable (a = b)
  | _, .base, a, _ => nomatch a
  | _, .unit frame, .retainUnit a, .retainUnit b =>
    match decEq frame a b with
    | .isTrue h => .isTrue (congrArg retainUnit h)
    | .isFalse h => .isFalse (fun eq => h (by cases eq; rfl))
  | _, .bit _, .newest _, .newest _ => .isTrue rfl
  | _, .bit _, .newest _, .retainBit _ => .isFalse (by intro h; cases h)
  | _, .bit _, .retainBit _, .newest _ => .isFalse (by intro h; cases h)
  | _, .bit frame, .retainBit a, .retainBit b =>
    match decEq frame a b with
    | .isTrue h => .isTrue (congrArg retainBit h)
    | .isFalse h => .isFalse (fun eq => h (by cases eq; rfl))

/-- Discover every matched guard reached through ordinary requests. The term
indices are the actual selected compiler inputs. Their equalities to the slot
coordinates let the certificate use the same maps without casting either tree. -/
def KnownGuardContext.discoverWith {L : List (Ty Empty)} :
    {n : Nat} → ReadTree L n → {X : Ty Empty} → {frame : ReplyFrame X} →
    (slots : Fin n → ReplyFrame.Slot frame) → (known : ReplyFrame.Slot frame) →
    {terms : Fin n → Term signature.Instr X Bit} → {tested : Term signature.Instr X Bit} →
    (fun i => (slots i).term) = terms → known.term = tested → KnownGuardContext L terms tested
  | _, .ret emits pos i, _, _, _, _, _, _, _, _ => .keep (.ret emits pos i)
  | _, .retExpr emits pos e, _, _, _, _, _, _, _, _ => .keep (.retExpr emits pos e)
  | _, .request emits label _ left right, _, _, slots, known, _, _, slotTerms, testedTerm =>
    let nextTerms := (bindSlots_term slots).trans (congrArg bindReply slotTerms)
    let nextTest := congrArg (retainSlot (A := Bit)) testedTerm
    .request emits label
      (discoverWith left (ReplyFrame.bindSlots slots) (.retainBit known) nextTerms nextTest)
      (discoverWith right (ReplyFrame.bindSlots slots) (.retainBit known) nextTerms nextTest)
  | _, .testRequest emits test low lowBound highBound fl fr tl tr, _, frame, slots, known, _, _, slotTerms, testedTerm =>
    letI : Decidable (slots test = known) := ReplyFrame.Slot.decEq frame (slots test) known
    if h : slots test = known then
      .prune test ⟨emits, low, fl, fr, tl, tr⟩
        ((congrFun slotTerms test).symm.trans ((congrArg ReplyFrame.Slot.term h).trans testedTerm))
    else
      .keep (.testRequest emits test low lowBound highBound fl fr tl tr)

/-- The unchanged input to discovery: a prior structural case with two
selected request trees under its retained input and unit payload. -/
structure SelectedGuardSplit (L : List (Ty Empty)) (n : Nat) where
  test : Fin n
  emits : List Bool
  onFalse : ReadTree L n
  onTrue : ReadTree L n

def SelectedGuardSplit.source {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n) :
    CaseTree signature.Instr (replyContext n) L :=
  let retained := fun j => retainSlot (A := unit) (readReply n j)
  .case unit unit (emitPrefix p.emits (readReply n p.test))
    (p.onFalse.selectedWith retained) (p.onTrue.selectedWith retained)

/-- Run discovery in both arms, starting with the tested slot carried under
the unit binder. Each subsequent request carries it under one more reply. -/
def SelectedGuardSplit.discover {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n) :
    KnownGuardSplit L (readReply n) :=
  let slots := fun j => ReplyFrame.Slot.retainUnit (ReplyFrame.standardSlots n j)
  have terms : (fun j => (slots j).term) = fun j => retainSlot (A := unit) (readReply n j) :=
    congrArg (fun read j => retainSlot (A := unit) (read j)) (standardSlots_term n)
  ⟨p.test, p.emits,
    KnownGuardContext.discoverWith p.onFalse slots (slots p.test) terms (congrFun terms p.test),
    KnownGuardContext.discoverWith p.onTrue slots (slots p.test) terms (congrFun terms p.test)⟩

def SelectedGuardSplit.packedSource {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n) :
    Paper.Extension.Singleton.ofType Seed (replyContext n) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed p.source.elaborate.property.packExits

/-- Reply tags address the request path. The empty path is at the current
node. A route cannot traverse a keep or prune leaf. -/
def KnownGuardContext.prunesAt {L : List (Ty Empty)} :
    {X : Ty Empty} → {n : Nat} → {slots : Fin n → Term signature.Instr X Bit} →
    {tested : Term signature.Instr X Bit} → KnownGuardContext L slots tested → List Bool → Bool
  | _, _, _, _, .prune .., [] => true
  | _, _, _, _, .request _ _ left right, b :: rest => if b then right.prunesAt rest else left.prunesAt rest
  | _, _, _, _, _, _ => false

/-- The exact projection criterion at the first guard on an ordinary request
path. A guard's own limbs, terminal expressions, and other cases are outside
this search. -/
def matchesAt {L : List (Ty Empty)} :
    {n : Nat} → ReadTree L n → {X : Ty Empty} → {frame : ReplyFrame X} →
    (Fin n → ReplyFrame.Slot frame) → ReplyFrame.Slot frame → List Bool → Prop
  | _, .testRequest _ test _ _ _ _ _ _ _, _, _, slots, known, [] => (slots test).term = known.term
  | _, .request _ _ _ left right, _, _, slots, known, b :: rest =>
    let next := ReplyFrame.bindSlots slots
    if b then matchesAt right next (.retainBit known) rest
    else matchesAt left next (.retainBit known) rest
  | _, _, _, _, _, _, _ => False

/-- Search criterion in one arm of the outer prior case. -/
def SelectedGuardSplit.matchesAt {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n)
    (onTrue : Bool) (route : List Bool) : Prop :=
  let slots := fun j => ReplyFrame.Slot.retainUnit (ReplyFrame.standardSlots n j)
  OpenReplay.matchesAt (if onTrue then p.onTrue else p.onFalse) slots (slots p.test) route

/-- Inspect whether the certificate prunes at a path in one outer arm. -/
def KnownGuardSplit.prunesAt {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} (p : KnownGuardSplit L slots)
    (onTrue : Bool) (route : List Bool) : Bool :=
  if onTrue then p.onTrue.prunesAt route else p.onFalse.prunesAt route

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
