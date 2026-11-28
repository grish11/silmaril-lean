module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Defs

/-! # Recognize compact terminals on exact framed projections -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

namespace CompactTerminal

/-- The only possible replacements for a compact table. -/
inductive Terminal (n : Nat) where
  | literal (bit : Bool)
  | read (slot : Fin n)

def Terminal.expr {n : Nat} : Terminal n → Finite.Expr n
  | .literal b => .literal b
  | .read i => .read i

abbrev Known {X : Ty Empty} (frame : ReplyFrame X) := ReplyFrame.Slot frame → Option Bool
abbrev Atom {X : Ty Empty} (frame : ReplyFrame X) := Bool ⊕ ReplyFrame.Slot frame

def Terminal.atom {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin n → ReplyFrame.Slot frame) : Terminal n → Atom frame
  | .literal b => .inl b
  | .read i => .inr (slots i)

def remember {X : Ty Empty} {frame : ReplyFrame X} (known : Known frame)
    (slot : ReplyFrame.Slot frame) (tag : Bool) : Known frame :=
  fun query =>
    letI := ReplyFrame.Slot.decEq frame
    if query = slot then some tag else known query

def resolve {X : Ty Empty} {frame : ReplyFrame X} (known : Known frame) : Atom frame → Atom frame
  | .inl tag => .inl tag
  | .inr slot =>
    match known slot with
    | some tag => .inl tag
    | none => .inr slot

/-- Check a requested terminal on both arms of each new test. A repeated
projection follows only the arm fixed earlier on that path, even when its
logical index differs. Leaves compare exact fields or their known tags. -/
def check {X : Ty Empty} {frame : ReplyFrame X} :
    {n : Nat} → Finite.Expr n → (Fin n → ReplyFrame.Slot frame) → Known frame → Atom frame → Bool
  | _, .literal b, _, known, target =>
    letI := ReplyFrame.Slot.decEq frame
    decide (resolve known target = .inl b)
  | _, .read i, slots, known, target =>
    letI := ReplyFrame.Slot.decEq frame
    decide (resolve known target = resolve known (.inr (slots i)))
  | _, .split low high, slots, known, target =>
    let older := fun j => slots j.succ
    match known (slots 0) with
    | some false => check low older known target
    | some true => check high older known target
    | none => check low older (remember known (slots 0) false) target &&
        check high older (remember known (slots 0) true) target

/-- Search literal and direct-field candidates without building a full table. -/
def infer? {X : Ty Empty} {frame : ReplyFrame X} {n : Nat} (e : Finite.Expr n)
    (slots : Fin n → ReplyFrame.Slot frame) : Option (Terminal n) :=
  ([Terminal.literal false, Terminal.literal true] ++ (List.finRange n).map Terminal.read).find? fun candidate =>
    check e slots (fun _ => none) (candidate.atom slots)

/-- Change only terminal expressions that pass the structural check. The
literal request and guard frames determine the slots seen at each leaf. -/
def reduceTree {L : List (Ty Empty)} :
    {n : Nat} → ReadTree L n → {X : Ty Empty} → {frame : ReplyFrame X} →
      (Fin n → ReplyFrame.Slot frame) → ReadTree L n
  | _, .ret emits pos i, _, _, _ => .ret emits pos i
  | _, .retExpr emits pos e, _, _, slots =>
    match infer? e slots with
    | some (.literal b) => .retExpr emits pos (.literal b)
    | some (.read i) => .ret emits pos i
    | none => .retExpr emits pos e
  | _, .request emits label bound l r, _, _, slots =>
    .request emits label bound (reduceTree l (ReplyFrame.bindSlots slots)) (reduceTree r (ReplyFrame.bindSlots slots))
  | _, .testRequest emits test low lowBound highBound fl fr tl tr, _, _, slots =>
    let next := ReplyFrame.guardSlots slots test
    .testRequest emits test low lowBound highBound
      (reduceTree fl next) (reduceTree fr next) (reduceTree tl next) (reduceTree tr next)

end CompactTerminal

/-- Reduce compact terminals at the selected program's actual frames. -/
def SelectedAt.reduceCompact {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) : SelectedAt X L :=
  let slots := fun j => ReplyFrame.Slot.retainUnit (p.slots j)
  { p with split := { p.split with
      onFalse := CompactTerminal.reduceTree p.split.onFalse slots
      onTrue := CompactTerminal.reduceTree p.split.onTrue slots } }

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
