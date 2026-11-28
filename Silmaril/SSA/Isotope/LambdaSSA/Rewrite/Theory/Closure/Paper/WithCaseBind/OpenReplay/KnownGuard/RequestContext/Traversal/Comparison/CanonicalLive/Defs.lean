module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.ProjectionQuotes.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.SelectedTerminal.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms

/-! # Canonical live selected requests and typed returns -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply (Trace)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance canonicalLiveDefsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Canonical live selected syntax on the standard packet. Values return by
a direct typed slot or a literal bit at an ordered Bit exit. Each request
exposes both reply tags and retains each reply's bit in its arm. A guard
drops the tested slot and uses complementary next request labels. -/
inductive CanonicalLive (L : List (Ty Empty)) : Nat → Type where
  | ret {n : Nat} (exit : Position L) (slot : Fin n) : CanonicalLive L n
  | literal {n : Nat} (exit : Position L) (bit : Bool) : CanonicalLive L n
  | emit {n : Nat} (label : Bool) (next : CanonicalLive L n) : CanonicalLive L n
  | request {n : Nat} (label : Bool) (left right : CanonicalLive L (n + 1)) : CanonicalLive L n
  | guard {n : Nat} (test : Fin (n + 1)) (low : Bool)
      (falseLeft falseRight trueLeft trueRight : CanonicalLive L (n + 1)) : CanonicalLive L (n + 1)

namespace CanonicalLive

/-- The validated model's existing normal form sees every ordered emit,
request label, exposed reply arm, ordered exit and bit result. -/
def normal {L : List (Ty Empty)} : {n : Nat} → CanonicalLive L n → Finite.Normal L n
  | _, .ret exit slot => .ret exit (fun env => env slot)
  | _, .literal exit bit => .ret exit (fun _ => bit)
  | _, .emit label next => .emit label next.normal
  | _, .request label l r => .request label l.normal r.normal
  | _, .guard test low fl fr tl tr => .testRequest test low fl.normal fr.normal tl.normal tr.normal

/-- Append an emit at the head of the next selected node's original prefix. -/
def pushEmit {L : List (Ty Empty)} {n : Nat} (label : Bool) : ReadTree L n → ReadTree L n
  | .ret emits exit read => .ret (label :: emits) exit read
  | .retExpr emits exit result => .retExpr (label :: emits) exit result
  | .request emits req bound l r => .request (label :: emits) req bound l r
  | .testRequest emits test low lowBound highBound fl fr tl tr =>
    .testRequest (label :: emits) test low lowBound highBound fl fr tl tr

/-- The actual selected compiler groups the ordered prefix at each node. -/
def readTree {L : List (Ty Empty)} : {n : Nat} → CanonicalLive L n → ReadTree L n
  | _, .ret exit slot => .ret [] exit slot
  | _, .literal exit bit => .retExpr [] exit (.literal bit)
  | _, .emit label next => pushEmit label next.readTree
  | _, .request label l r => .request [] label false l.readTree r.readTree
  | _, .guard test low fl fr tl tr =>
    .testRequest [] test low false false fl.readTree fr.readTree tl.readTree tr.readTree

def target {L : List (Ty Empty)} {n : Nat} (p : CanonicalLive L n) : ScopedTarget (replyContext n) L :=
  p.readTree.selected.elaborate

def readback {L : List (Ty Empty)} {n : Nat} (p : CanonicalLive L n) : Option (AcyclicSyntax signature.Instr) :=
  (AcyclicSyntax.read p.target.val).map Subtype.val

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

/-- The existing payload trace model descends along the exact selected
native seed, including the code's shared tensor and region coherence. -/
noncomputable def payloadDenote :=
  letI := Kleisli.instructions model
  let := modelCoherent
  Paper.Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)
    (Paper.WithCaseBind.SelectedTerminal.seed_denotes J M (fun _ _ => ⟨rfl, rfl⟩))

end CanonicalLive

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
