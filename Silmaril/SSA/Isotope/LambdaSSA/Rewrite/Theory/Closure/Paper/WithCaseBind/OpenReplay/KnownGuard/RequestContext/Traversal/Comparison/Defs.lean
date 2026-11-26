module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Thms

/-! # Exact comparison of normalized selected regions -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance comparisonHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy
/-- Exact opcode comparison for selected syntax and its readback. -/
@[instance_reducible]
def payloadInstrDecEq : DecidableEq signature.Instr
  | Op.emit a, Op.emit b =>
    if h : a = b then .isTrue (congrArg Op.emit h) else .isFalse (fun eq => h (Op.emit.inj eq))
  | Op.ask a, Op.ask b =>
    if h : a = b then .isTrue (congrArg Op.ask h) else .isFalse (fun eq => h (Op.ask.inj eq))
  | Op.emit _, Op.ask _ => .isFalse (by intro eq; cases eq)
  | Op.ask _, Op.emit _ => .isFalse (by intro eq; cases eq)

attribute [local instance] payloadInstrDecEq

/-- Exact acyclic syntax. Branch arguments and discriminators include their
original instruction, variable and binder syntax. -/
inductive AcyclicSyntax (Φ : Type) where
  | br (label : Nat) (arg : Tm Φ)
  | case (discr : Tm Φ) (left right : AcyclicSyntax Φ)
  | let₁ (value : Tm Φ) (body : AcyclicSyntax Φ)
  | let₂ (value : Tm Φ) (body : AcyclicSyntax Φ)
  deriving DecidableEq

namespace AcyclicSyntax

def region {Φ : Type} : AcyclicSyntax Φ → Region Φ
  | .br i a => .br i a
  | .case a l r => .case a l.region r.region
  | .let₁ a r => .let₁ a r.region
  | .let₂ a r => .let₂ a r.region

/-- Read the exact emitted constructors, with a proof that re-emission
recovers the input region at every successful readback. -/
def read {Φ : Type} : (r : Region Φ) → Option {s : AcyclicSyntax Φ // s.region = r}
  | .br i a => some ⟨.br i a, rfl⟩
  | .case a l r => do
    let ⟨left, hl⟩ ← read l
    let ⟨right, hr⟩ ← read r
    pure ⟨.case a left right, congrArg₂ (Region.case a) hl hr⟩
  | .let₁ a r => do
    let ⟨body, h⟩ ← read r
    pure ⟨.let₁ a body, congrArg (Region.let₁ a) h⟩
  | .let₂ a r => do
    let ⟨body, h⟩ ← read r
    pure ⟨.let₂ a body, congrArg (Region.let₂ a) h⟩
  | .cfg .. => none

/-- The checked comparison uses the entire readback. Equal keys cannot
erase a difference in a binding, primitive request or exit position. -/
theorem read_eq_region {Φ : Type} {r s : Region Φ}
    (a : {x : AcyclicSyntax Φ // x.region = r}) (b : {x : AcyclicSyntax Φ // x.region = s})
    (h : a.val = b.val) : r = s :=
  a.property.symm.trans ((congrArg region h).trans b.property)

end AcyclicSyntax

/-- A successful comparison supplies a proof. Unknown carries no claim. -/
inductive EqualityVerdict (claim : Prop) where
  | equal (proof : claim)
  | unknown

def EqualityVerdict.accepted {claim : Prop} : EqualityVerdict claim → Bool
  | .equal _ => true
  | .unknown => false

/-- The computed region at its exact input and ordered exit scope. -/
abbrev ScopedTarget (X : Ty Empty) (L : List (Ty Empty)) :=
  {r : Region signature.Instr // ValueBranches [X] r L}

def ScopedTarget.packed {X : Ty Empty} {L : List (Ty Empty)} (t : ScopedTarget X L) :
    Paper.Extension.Singleton.ofType Seed X ⟶ Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed t.property.packExits

/-- Compare exact readbacks at a shared scope. No type or effect normalization
is performed in this comparison. -/
def ScopedTarget.compare {X : Ty Empty} {L : List (Ty Empty)} (left right : ScopedTarget X L) :
    EqualityVerdict (left = right) :=
  match AcyclicSyntax.read left.val, AcyclicSyntax.read right.val with
  | some a, some b =>
    if h : a.val = b.val then .equal (Subtype.ext (AcyclicSyntax.read_eq_region a b h)) else .unknown
  | _, _ => .unknown

/-- A selected source and its own exact structural input slot map. Two
selections can have different logical widths and maps at the same interface. -/
structure SelectedAt (X : Ty Empty) (L : List (Ty Empty)) where
  width : Nat
  split : SelectedGuardSplit L width
  frame : ReplyFrame X
  slots : Fin width → ReplyFrame.Slot frame

def SelectedAt.source {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    CaseTree signature.Instr X L :=
  p.split.sourceWith (fun j => (p.slots j).term)

def SelectedAt.packedSource {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    Paper.Extension.Singleton.ofType Seed X ⟶ Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed p.source.elaborate.property.packExits

def SelectedAt.traversal {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    GuardSplitTraversal p.split (fun j => (p.slots j).term) :=
  p.split.traverseWith p.slots rfl

/-- The normalized target is the region produced by the existing traversal. -/
def SelectedAt.normalized {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) : ScopedTarget X L :=
  ⟨p.traversal.pruned, p.traversal.pruned_typed⟩

theorem SelectedAt.packed_normalized {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    p.packedSource = p.normalized.packed :=
  p.traversal.packed_eq_pruned p.slots rfl

/-- Normalize the two actual sources independently and certify positive
equality at their original packed interface. -/
def SelectedAt.compare {X : Ty Empty} {L : List (Ty Empty)} (left right : SelectedAt X L) :
    EqualityVerdict (left.packedSource = right.packedSource) :=
  match left.normalized.compare right.normalized with
  | .equal h => .equal (left.packed_normalized.trans ((congrArg ScopedTarget.packed h).trans
      right.packed_normalized.symm))
  | .unknown => .unknown

def SelectedGuardSplit.atStandard {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n) :
    SelectedAt (replyContext n) L :=
  ⟨n, p, ReplyFrame.standard n, ReplyFrame.standardSlots n⟩

theorem SelectedGuardSplit.atStandard_packedSource {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n) :
    p.atStandard.packedSource = p.packedSource :=
  congrArg (fun slots => Paper.Extension.Singleton.ofRegion Seed (p.sourceWith slots).elaborate.property.packExits)
    (standardSlots_term n)

/-- The standard reply packet consumer uses the original public packed arrows. -/
def SelectedGuardSplit.compare {L : List (Ty Empty)} {n : Nat} (left right : SelectedGuardSplit L n) :
    EqualityVerdict (left.packedSource = right.packedSource) :=
  match left.atStandard.compare right.atStandard with
  | .equal h => .equal (left.atStandard_packedSource.symm.trans (h.trans right.atStandard_packedSource))
  | .unknown => .unknown

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
