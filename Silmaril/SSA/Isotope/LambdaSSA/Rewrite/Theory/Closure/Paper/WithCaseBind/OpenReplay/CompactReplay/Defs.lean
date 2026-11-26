module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Defs

/-! # Compact terminals over a shared finite guarded request skeleton -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance compactReplayDefsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- A compact terminal and the permutation selecting its logical slots from the physical reply packet. -/
structure OrderedExpr (n : Nat) where
  expr : Finite.Expr n
  order : Equiv.Perm (Fin n)

/-- Evaluate the terminal in physical packet coordinates. -/
def OrderedExpr.packetEval {n : Nat} (e : OrderedExpr n) : Finite.Table n :=
  fun row => e.expr.eval (row ∘ e.order)

/-- Compare the right terminal at the same packet, expressed in the left terminal’s logical coordinates. -/
def OrderedExpr.Agrees {n : Nat} (e f : OrderedExpr n) : Prop :=
  ∀ row, e.expr.eval row = f.expr.eval ((row ∘ e.order.symm) ∘ f.order)

/-- Compile the compact expression with its actual ordered slot map. -/
def OrderedExpr.selected {n : Nat} {L : List (Ty Empty)} (e : OrderedExpr n)
    (emits : List Bool) (pos : Position L) : CaseTree signature.Instr (replyContext n) L :=
  selectTerminal pos e.expr (readReply n ∘ e.order) emits

/-- A shared tree of effectful requests, retained-bit tests, and terminal emits. Each terminal fixes its typed outward position. -/
inductive RequestSkeleton (L : List (Ty Empty)) : Nat → Type where
  | ret {n : Nat} (emits : List Bool) (pos : Position L) : RequestSkeleton L n
  | request {n : Nat} (emits : List Bool) (label : Bool)
      (left right : RequestSkeleton L (n + 1)) : RequestSkeleton L n
  | testRequest {n : Nat} (emits : List Bool) (test : Fin (n + 1)) (low : Bool)
      (falseLeft falseRight trueLeft trueRight : RequestSkeleton L (n + 1)) : RequestSkeleton L (n + 1)

/-- Supply a compact expression and independent slot order at each terminal. -/
def RequestSkeleton.Leaves {L : List (Ty Empty)} : {n : Nat} → RequestSkeleton L n → Type
  | n, .ret _ _ => OrderedExpr n
  | _, .request _ _ left right => left.Leaves × right.Leaves
  | _, .testRequest _ _ _ fl fr tl tr => fl.Leaves × fr.Leaves × tl.Leaves × tr.Leaves

/-- Compile compact leaves against the slot map reached by their request path. -/
def RequestSkeleton.selectedWith {L : List (Ty Empty)} : {n : Nat} → (s : RequestSkeleton L n) →
    s.Leaves → {X : Ty Empty} → (Fin n → Term signature.Instr X Bit) → CaseTree signature.Instr X L
  | _, .ret emits pos, e, _, slots => selectTerminal pos e.expr (slots ∘ e.order) emits
  | _, .request emits label left right, leaves, _, slots =>
    selectRequest emits label (left.selectedWith leaves.1 (bindReply slots))
      (right.selectedWith leaves.2 (bindReply slots))
  | _, .testRequest emits test low fl fr tl tr, leaves, _, slots =>
    let scope := guardReplies slots test
    .case unit unit (emitPrefix emits (slots test))
      (selectRequest [] low (fl.selectedWith leaves.1 scope) (fr.selectedWith leaves.2.1 scope))
      (selectRequest [] (!low) (tl.selectedWith leaves.2.2.1 scope) (tr.selectedWith leaves.2.2.2 scope))

/-- Compile the shared guarded skeleton from the standard reply packet. -/
def RequestSkeleton.selected {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (leaves : s.Leaves) : CaseTree signature.Instr (replyContext n) L :=
  s.selectedWith leaves (readReply n)

/-- Keep the same guarded request shape and quote each terminal in the order
of its live slot map. -/
def RequestSkeleton.quoted {L : List (Ty Empty)} : {n : Nat} → (s : RequestSkeleton L n) →
    s.Leaves → ReadTree L n
  | n, .ret emits pos, e => .retExpr emits pos (Finite.Expr.quote n e.packetEval)
  | _, .request emits label left right, leaves =>
    .request emits label false (left.quoted leaves.1) (right.quoted leaves.2)
  | _, .testRequest emits test low fl fr tl tr, leaves =>
    .testRequest emits test low false false (fl.quoted leaves.1) (fr.quoted leaves.2.1)
      (tl.quoted leaves.2.2.1) (tr.quoted leaves.2.2.2)

/-- Require extensional agreement separately at each terminal of the common skeleton. -/
def RequestSkeleton.Agrees {L : List (Ty Empty)} : {n : Nat} → (s : RequestSkeleton L n) →
    s.Leaves → s.Leaves → Prop
  | _, .ret _ _, e, f => e.Agrees f
  | _, .request _ _ left right, l, r => left.Agrees l.1 r.1 ∧ right.Agrees l.2 r.2
  | _, .testRequest _ _ _ fl fr tl tr, l, r =>
    fl.Agrees l.1 r.1 ∧ fr.Agrees l.2.1 r.2.1 ∧ tl.Agrees l.2.2.1 r.2.2.1 ∧ tr.Agrees l.2.2.2 r.2.2.2

/-- Pack the actual compact elaboration at the original input and exit interface. -/
def RequestSkeleton.packed {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (leaves : s.Leaves) :
    Paper.Extension.Singleton.ofType Seed (replyContext n) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed (s.selected leaves).elaborate.property.packExits

/-- Admission for the existing selected trees whose internal nodes are ordinary requests. -/
inductive RequestOnly {L : List (Ty Empty)} : {n : Nat} → ReadTree L n → Type where
  | ret {n : Nat} (emits : List Bool) (pos : Position L) (i : Fin n) :
      RequestOnly (.ret emits pos i)
  | retExpr {n : Nat} (emits : List Bool) (pos : Position L) (e : Finite.Expr n) :
      RequestOnly (.retExpr emits pos e)
  | request {n : Nat} {l r : ReadTree L (n + 1)} (emits : List Bool) (label bound : Bool)
      (hl : RequestOnly l) (hr : RequestOnly r) : RequestOnly (.request emits label bound l r)

/-- A presentation of the actual selected tree by the shared request grammar. -/
structure RequestPresentation {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n) where
  skeleton : RequestSkeleton L n
  leaves : skeleton.Leaves
  selected_eq : skeleton.selected leaves = p.selected

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
